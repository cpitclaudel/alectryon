;;; alectryon-tests.el --- Tests for alectryon.el  -*- lexical-binding: t; -*-

;; Run with: etc/test-elisp.sh

;;; Code:

(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
(package-initialize)
(require 'use-package)

(use-package flycheck :ensure t)
(use-package proof-general :ensure t)
(use-package boogie-friends :ensure t)
(use-package lean4-mode :ensure t
  :vc (:url "https://github.com/leanprover-community/lean4-mode"))

(eval-and-compile
  (defconst alectryon-test--directory
    (file-name-directory (or load-file-name buffer-file-name default-directory))
    "Directory containing this test file."))

(require 'alectryon (expand-file-name "alectryon.el" alectryon-test--directory))
(require 'ert)

;;;; Helpers

(defun alectryon-test--converter-available-p ()
  "Return non-nil if the Alectryon converter binary is available."
  (let ((exec (executable-find alectryon-executable)))
    (and exec (file-executable-p exec))))

(defun alectryon-test--convert (input frontend backend)
  "Convert INPUT string from FRONTEND to BACKEND, return output string."
  (with-temp-buffer
    (insert input)
    (let ((in (current-buffer)))
      (with-temp-buffer
        (alectryon--run-converter in (list "--frontend" frontend "--backend" backend))
        (buffer-substring-no-properties (point-min) (point-max))))))

(defmacro alectryon-test--with-buffer (mode contents &rest body)
  "Set up a temp buffer in MODE with CONTENTS and run BODY."
  (declare (indent 2))
  `(with-temp-buffer
     (funcall ,mode)
     (insert ,contents)
     ,@body))

;;;; Text mode selection

(ert-deftest alectryon-test-guess-text-mode ()
  "Filename suffix detection for _rst and _md."
  (with-temp-buffer
    (let ((buffer-file-name "/tmp/foo_rst.abc"))
      (should (eq 'rst-mode (alectryon--guess-text-mode))))
    (let ((buffer-file-name "/tmp/foo_md.xyz"))
      (should (eq 'markdown-mode (alectryon--guess-text-mode))))
    (let ((buffer-file-name "/tmp/foo.uvw"))
      (should-not (alectryon--guess-text-mode)))))

(ert-deftest alectryon-test-ensure-text-mode ()
  "ensure-text-mode auto-detects from filename suffix."
  (with-temp-buffer
    (setq-local alectryon-prog-mode 'coq-mode)
    (setq-local alectryon-text-mode nil)
    (let ((buffer-file-name "/tmp/test_md.v"))
      (alectryon--ensure-text-mode-set)
      (should (eq 'markdown-mode alectryon-text-mode)))))

;;;; Annotations regex

(ert-deftest alectryon-test-annotations-re ()
  "Annotations regex matches markers like (* .show *) but not regular comments."
  (let ((re (alectryon--config :annotations-re 'prog)))
    (should (string-match-p re "(* .show *)"))
    (should (string-match-p re "(* .show .unfold *)"))
    (should-not (string-match-p re "(* regular comment *)"))))

(ert-deftest alectryon-test-lean4-annotations-re ()
  "Lean 4 annotations regex matches /- .show -/ but not regular comments."
  (with-temp-buffer
    (setq-local alectryon-prog-mode 'lean4-mode)
    (let ((re (alectryon--config :annotations-re 'prog)))
      (should (string-match-p re "/- .unfold -/"))
      (should (string-match-p re "/- .unfold .no-in -/"))
      (should-not (string-match-p re "/- regular comment -/")))))

;;;; Literate comment detection and editing

(ert-deftest alectryon-test-literate-comment ()
  "Literate comment detection distinguishes (*| |*) from (* *) and code."
  (alectryon-test--with-buffer 'coq-mode "(*| hello |*)"
    (goto-char 6)
    (should (alectryon--in-literate-comment-p)))
  (alectryon-test--with-buffer 'coq-mode "Lemma foo. (*| hello |*)"
    (goto-char 3)
    (should-not (alectryon--in-literate-comment-p)))
  (alectryon-test--with-buffer 'coq-mode "(* regular *)"
    (goto-char 6)
    (should-not (alectryon--in-literate-comment-p))))

(ert-deftest alectryon-test-insert-literate-block ()
  "Inserting a literate block produces exact output with point between delimiters."
  (alectryon-test--with-buffer 'coq-mode ""
    (alectryon-insert-literate-markers)
    (should (equal "(*|\n\n|*)" (buffer-string)))
    (should (equal 5 (point)))))

(ert-deftest alectryon-test-lean4-literate-comment ()
  "Literate comment detection distinguishes /-| |-/ from /- -/ and code."
  (alectryon-test--with-buffer 'lean4-mode "/-| hello |-/"
    (goto-char 6)
    (should (alectryon--in-literate-comment-p)))
  (alectryon-test--with-buffer 'lean4-mode "def x := 1 /-| hello |-/"
    (goto-char 3)
    (should-not (alectryon--in-literate-comment-p)))
  (alectryon-test--with-buffer 'lean4-mode "/- regular -/"
    (goto-char 6)
    (should-not (alectryon--in-literate-comment-p))))

(ert-deftest alectryon-test-lean4-insert-literate-block ()
  "Inserting a literate block in Lean 4 produces /-| and |-/ delimiters."
  (alectryon-test--with-buffer 'lean4-mode ""
    (alectryon-insert-literate-markers)
    (should (equal "/-|\n\n|-/" (buffer-string)))
    (should (equal 5 (point)))))

(ert-deftest alectryon-test-dafny-literate-comment ()
  "Literate comment detection distinguishes /// from // and code."
  (alectryon-test--with-buffer 'dafny-mode "/// hello"
    (goto-char 6)
    (should (alectryon--in-literate-comment-p)))
  (alectryon-test--with-buffer 'dafny-mode "// regular"
    (goto-char 6)
    (should-not (alectryon--in-literate-comment-p))))

(ert-deftest alectryon-test-dafny-insert-literate-markers ()
  "Inserting literate markers in gutter mode."
  ;; Empty line: insert /// prefix
  (alectryon-test--with-buffer 'dafny-mode ""
    (alectryon-insert-literate-markers)
    (should (equal "/// " (buffer-string))))
  ;; In code: open a new /// line
  (alectryon-test--with-buffer 'dafny-mode "method Foo() {}"
    (alectryon-insert-literate-markers)
    (should (equal "method Foo() {}\n\n/// \n" (buffer-string))))
  ;; In /// comment: break out into code
  (alectryon-test--with-buffer 'dafny-mode "/// hello"
    (alectryon-insert-literate-markers)
    (should (equal "/// hello\n\n\n" (buffer-string)))))

(ert-deftest alectryon-test-gutter-newline ()
  "RET in a /// comment auto-inserts /// prefix on the new line."
  (alectryon-test--with-buffer 'dafny-mode "/// hello"
    (goto-char (point-max))
    (alectryon-newline nil)
    (should (equal "/// hello\n/// " (buffer-string)))
    (should (equal (point) (point-max)))))

(ert-deftest alectryon-test-gutter-backspace-safeguard ()
  "Backspacing into /// with content after it deletes the whole prefix."
  (alectryon-test--with-buffer 'dafny-mode "/// hello"
    (font-lock-mode 1)
    (font-lock-ensure)
    ;; Point after "/// ", backspace should delete whole "/// " (not just space)
    (goto-char 5)
    (delete-char -1)
    (should (equal "hello" (buffer-string)))))

(ert-deftest alectryon-test-gutter-newline-outside-comment ()
  "RET outside a /// comment inserts a plain newline; backspace undoes it."
  (alectryon-test--with-buffer 'dafny-mode "method Foo() {}"
    (let ((original (buffer-string)))
      (goto-char (point-max))
      (alectryon-newline nil)
      (should (equal "method Foo() {}\n" (buffer-string)))
      (delete-char -1)
      (should (equal original (buffer-string))))))

(ert-deftest alectryon-test-gutter-newline-not-in-block-modes ()
  "RET in a block-style literate comment does not insert gutter prefixes."
  (alectryon-test--with-buffer 'coq-mode "(*| hello |*)"
    (let ((original (buffer-string)))
      (goto-char 8)
      (alectryon-newline nil)
      (delete-char -1)
      (should (equal original (buffer-string))))))

;;;; Conversion (requires alectryon binary)

(cl-defstruct (alectryon-test--lang (:constructor alectryon-test--lang))
  "Per-language test data: matched conversion triplet plus round-trip input."
  tag mode code rst md round-trip)

(defconst alectryon-test--lang-data
  (list
   (alectryon-test--lang
    :tag "coq" :mode 'coq-mode
    :code "(*|\nHello\n|*)\n\nLemma foo : True.\n"
    :rst "Hello\n\n.. coq::\n\n   Lemma foo : True.\n"
    :md  "Hello\n\n```{coq}\nLemma foo : True.\n```\n"
    :round-trip "(*|\nHello\n|*)\n\nLemma foo : True. Proof. auto. Qed.\n")
   (alectryon-test--lang
    :tag "lean4" :mode 'lean4-mode
    :code "/-|\nHello\n|-/\n\ntheorem foo : ∀ n : Nat, n = n := fun _ → rfl\n"
    :rst  "Hello\n\n.. lean4::\n\n   theorem foo : ∀ n : Nat, n = n := fun _ → rfl\n"
    :md   "Hello\n\n```{lean4}\ntheorem foo : ∀ n : Nat, n = n := fun _ → rfl\n```\n"
    :round-trip "/-|\nHello\n|-/\n\ndef x : Nat := 5\n")
   (alectryon-test--lang
    :tag "dafny" :mode 'dafny-mode
    :code "/// Hello\n\nmethod Foo() {}\n"
    :rst  "Hello\n\n.. dafny::\n\n   method Foo() {}\n"
    :md   "Hello\n\n```{dafny}\nmethod Foo() {}\n```\n"
    :round-trip "/// Hello\n\nmethod Foo() {}\n"))
  "Test data for each supported language.")

(defmacro alectryon-test--deftest (name docstring &rest body)
  "Define an ERT test NAME that runs BODY in a temp buffer for each language.
BODY can use `.tag', `.mode', `.code', `.rst', `.md', `.round-trip'."
  (declare (indent 2) (doc-string 2))
  `(ert-deftest ,name ()
     ,docstring
     (skip-unless (alectryon-test--converter-available-p))
     (dolist (.lang alectryon-test--lang-data)
       (let ((.tag        (alectryon-test--lang-tag .lang))
             (.mode       (alectryon-test--lang-mode .lang))
             (.code       (alectryon-test--lang-code .lang))
             (.rst        (alectryon-test--lang-rst .lang))
             (.md         (alectryon-test--lang-md .lang))
             (.round-trip (alectryon-test--lang-round-trip .lang)))
         (with-temp-buffer
           ,@body)))))

(alectryon-test--deftest alectryon-test-convert-to-markup
  "Code converts to exact expected RST and Markdown output."
  (should (equal .rst (alectryon-test--convert .code (concat .tag "+rst") "rst")))
  (should (equal .md  (alectryon-test--convert .code (concat .tag "+md") "md"))))

(alectryon-test--deftest alectryon-test-convert-markup-to-code
  "RST and Markdown convert to exact expected code output."
  (should (equal .code (alectryon-test--convert .rst "rst" (concat .tag "+rst"))))
  (should (equal .code (alectryon-test--convert .md "md" (concat .tag "+md")))))

(alectryon-test--deftest alectryon-test-convert-round-trips
  "Code -> markup -> code round-trips are identity for both RST and Markdown."
  (should (equal .round-trip (alectryon-test--convert
                              (alectryon-test--convert .round-trip (concat .tag "+rst") "rst")
                              "rst" (concat .tag "+rst"))))
  (should (equal .round-trip (alectryon-test--convert
                              (alectryon-test--convert .round-trip (concat .tag "+md") "md")
                              "md" (concat .tag "+md")))))

(ert-deftest alectryon-test-convert-edge-cases ()
  "Conversion handles empty, code-only, and prose-only inputs."
  (skip-unless (alectryon-test--converter-available-p))
  (should (equal "" (string-trim (alectryon-test--convert "" "coq+rst" "rst"))))
  (should (equal ".. coq::\n\n   Lemma foo : True.\n"
                 (alectryon-test--convert "Lemma foo : True.\n" "coq+rst" "rst")))
  (should (equal "Just prose.\n"
                 (alectryon-test--convert "(*| Just prose. |*)\n" "coq+rst" "rst"))))

(alectryon-test--deftest alectryon-test-lint
  "Lint backend accepts code+markup without errors."
  (should (equal "" (alectryon-test--convert .code (concat .tag "+rst") "lint"))))

;;;; In-buffer conversion (alectryon--convert-from)

(alectryon-test--deftest alectryon-test-convert-from
  "alectryon--convert-from replaces buffer contents in-place and round-trips."
  (setq-local alectryon-prog-mode .mode)
  (setq-local alectryon-text-mode 'rst-mode)
  (insert .code)
  (alectryon--convert-from .mode)
  (should (equal .rst (buffer-string)))
  (alectryon--convert-from 'rst-mode)
  (should (equal .code (buffer-string))))

(alectryon-test--deftest alectryon-test-convert-from-preserves-point
  "alectryon--convert-from preserves point position via --mark-point."
  (setq-local alectryon-prog-mode .mode)
  (setq-local alectryon-text-mode 'rst-mode)
  (insert .code)
  (goto-char (point-min))
  (search-forward "Hel") ;; point is now between the two l's of "Hello"
  (should (equal ?l (char-after)))
  (alectryon--convert-from .mode)
  (should (equal ?l (char-after))))

;;;; Toggle lifecycle


(alectryon-test--deftest alectryon-test-toggle-lifecycle
  "Toggle converts content and switches modes; disable reverts; undo restores."
  (funcall .mode)
  (setq-local alectryon-text-mode 'rst-mode)
  (buffer-enable-undo)
  (insert .code)
  (alectryon-mode 1)
  (should (eq .mode major-mode))
  (should alectryon-mode)
  ;; Toggle: code -> RST
  (alectryon--toggle)
  (should (eq 'rst-mode major-mode))
  (should alectryon-mode)
  (should (equal .rst (buffer-string)))
  ;; Disable alectryon-mode (should revert to code mode)
  (alectryon-mode -1)
  (should (eq .mode major-mode))
  (should-not alectryon-mode)
  (should (equal .code (buffer-string)))
  ;; Undo the disable: should restore RST + alectryon-mode
  (primitive-undo 2 buffer-undo-list)
  (should (eq 'rst-mode major-mode))
  (should alectryon-mode)
  (should (equal .rst (buffer-string))))

(alectryon-test--deftest alectryon-test-toggle-undo-preserves-original-mode
  "After undo-of-disable, alectryon--original-mode must still be set."
  (funcall .mode)
  (setq-local alectryon-text-mode 'rst-mode)
  (buffer-enable-undo)
  (insert .code)
  (alectryon-mode 1)
  (alectryon--toggle)
  (alectryon-mode -1)
  (primitive-undo 2 buffer-undo-list)
  (should (eq .mode alectryon--original-mode)))

(alectryon-test--deftest alectryon-test-disable-without-toggle
  "Disabling alectryon-mode while in original mode skips conversion."
  (funcall .mode)
  (setq-local alectryon-text-mode 'rst-mode)
  (insert .code)
  (alectryon-mode 1)
  (should (eq .mode major-mode))
  (should alectryon-mode)
  (alectryon-mode -1)
  (should (eq .mode major-mode))
  (should-not alectryon-mode)
  (should (equal .code (buffer-string))))

(alectryon-test--deftest alectryon-test-toggle-undo
  "Undoing a normal toggle restores original mode and content."
  (funcall .mode)
  (setq-local alectryon-text-mode 'rst-mode)
  (buffer-enable-undo)
  (insert .code)
  (alectryon-mode 1)
  (alectryon--toggle)
  (should (eq 'rst-mode major-mode))
  (should (equal .rst (buffer-string)))
  (primitive-undo 2 buffer-undo-list)
  (should (eq .mode major-mode))
  (should alectryon-mode)
  (should (equal .code (buffer-string)))
  (should (eq .mode alectryon--original-mode)))

(ert-deftest alectryon-test-original-mode-not-poisoned ()
  "Enabling alectryon-mode from an unsupported mode must not poison
alectryon--original-mode for future activations.
Issue: alectryon--record-mode runs before alectryon--mode-case validation."
  (with-temp-buffer
    (fundamental-mode)
    ;; Attempt to enable from fundamental-mode (unsupported) -- should error
    (condition-case nil
        (alectryon-mode 1)
      (error nil))
    ;; Now switch to a supported mode and enable
    (coq-mode)
    ;; alectryon--original-mode should be coq-mode, not fundamental-mode
    (should (or (null alectryon--original-mode)
                (eq 'coq-mode alectryon--original-mode)))))

(alectryon-test--deftest alectryon-test-failed-disable-cleanup
  "If the converter fails during disable, hooks must still be cleaned up."
  (funcall .mode)
  (setq-local alectryon-text-mode 'rst-mode)
  (insert .code)
  (alectryon-mode 1)
  (alectryon--toggle)
  ;; Now in rst-mode. Break the converter.
  (let ((alectryon-executable "nonexistent-binary-xyz"))
    (condition-case nil
        (alectryon-mode -1)
      (error nil)))
  ;; Even after error, the save hook should not be installed
  (should-not (memq 'alectryon--save
                     (buffer-local-value 'write-contents-functions (current-buffer)))))

(provide 'alectryon-tests)
;;; alectryon-tests.el ends here
