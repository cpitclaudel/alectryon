;;; alectryon-tests.el --- Tests for alectryon.el  -*- lexical-binding: t; -*-

;; Run with: emacs --batch -Q -l alectryon-tests.el -f ert-run-tests-batch-and-exit

;;; Code:

(require 'package)
(package-initialize)

(when (and (getenv "CI") (not (package-installed-p 'flycheck)))
  (add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
  (package-refresh-contents)
  (package-install 'flycheck))

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

(defun alectryon-test--coq-syntax-table ()
  "Return a syntax table with Coq-style (* *) comments."
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\( "()1" st)
    (modify-syntax-entry ?\) ")(4" st)
    (modify-syntax-entry ?*  ". 23" st)
    st))

(defmacro alectryon-test--with-coq-buffer (contents &rest body)
  "Set up a temp buffer with Coq config, CONTENTS, and run BODY."
  (declare (indent 1))
  `(with-temp-buffer
     (set-syntax-table (alectryon-test--coq-syntax-table))
     (setq-local alectryon-prog-mode 'coq-mode)
     (setq-local alectryon-text-mode 'rst-mode)
     (insert ,contents)
     ,@body))

;;;; Configuration and mode dispatching

(ert-deftest alectryon-test-config ()
  "Config returns correct tags, delimiters, and frontend/backend ids for RST and Markdown."
  (with-temp-buffer
    (setq-local alectryon-prog-mode 'coq-mode)
    ;; RST
    (setq-local alectryon-text-mode 'rst-mode)
    (should (equal "coq" (alectryon--config :tag 'prog)))
    (should (equal "rst" (alectryon--config :tag 'text)))
    (should (equal "coq+rst" (alectryon--config-frontend 'coq-mode)))
    (should (equal "rst" (alectryon--config-backend 'coq-mode)))
    ;; Markdown
    (setq-local alectryon-text-mode 'markdown-mode)
    (should (equal "md" (alectryon--config :tag 'text)))
    (should (equal "coq+md" (alectryon--config-frontend 'coq-mode)))
    (should (equal "md" (alectryon--config-backend 'coq-mode)))
    ;; Delimiters (same for both markups -- they're a Coq property)
    (let ((delims (alectryon--config :comment-delimiters 'prog)))
      (should (equal "(*|" (car delims)))
      (should (equal "|*)" (cdr delims))))))

(ert-deftest alectryon-test-mode-dispatch ()
  "prog-mode-p and mode-case dispatch correctly for all registered modes."
  (should (eq t (alectryon--prog-mode-p 'coq-mode)))
  (should (eq nil (alectryon--prog-mode-p 'rst-mode)))
  (should (eq nil (alectryon--prog-mode-p 'markdown-mode)))
  (should-error (alectryon--prog-mode-p 'fundamental-mode) :type 'error)
  (should (eq 'code (alectryon--mode-case 'code 'text 'coq-mode)))
  (should (eq 'text (alectryon--mode-case 'code 'text 'rst-mode)))
  (should (eq 'text (alectryon--mode-case 'code 'text 'markdown-mode))))

;;;; Text mode selection

(ert-deftest alectryon-test-guess-text-mode ()
  "Filename suffix detection for _rst and _md."
  (with-temp-buffer
    (let ((buffer-file-name "/tmp/foo_rst.v"))
      (should (eq 'rst-mode (alectryon--guess-text-mode))))
    (let ((buffer-file-name "/tmp/foo_md.v"))
      (should (eq 'markdown-mode (alectryon--guess-text-mode))))
    (let ((buffer-file-name "/tmp/foo.v"))
      (should-not (alectryon--guess-text-mode)))))

(ert-deftest alectryon-test-fallback-text-mode ()
  "Config uses fallback when alectryon-text-mode is nil."
  (with-temp-buffer
    (setq-local alectryon-prog-mode 'coq-mode)
    (setq-local alectryon-text-mode nil)
    (let ((alectryon-fallback-text-mode 'rst-mode))
      (should (equal "rst" (alectryon--config :tag 'text))))
    (let ((alectryon-fallback-text-mode 'markdown-mode))
      (should (equal "md" (alectryon--config :tag 'text))))))

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

;;;; Literate comment detection and editing

(ert-deftest alectryon-test-literate-comment ()
  "Literate comment detection distinguishes (*| |*) from (* *) and code."
  (alectryon-test--with-coq-buffer "(*| hello |*)"
    (goto-char 6)
    (should (alectryon--in-literate-comment-p)))
  (alectryon-test--with-coq-buffer "Lemma foo. (*| hello |*)"
    (goto-char 3)
    (should-not (alectryon--in-literate-comment-p)))
  (alectryon-test--with-coq-buffer "(* regular *)"
    (goto-char 6)
    (should-not (alectryon--in-literate-comment-p))))

(ert-deftest alectryon-test-insert-literate-block ()
  "Inserting a literate block produces exact output with point between delimiters."
  (alectryon-test--with-coq-buffer ""
    (alectryon-insert-literate-block)
    (should (equal "(*|\n\n|*)" (buffer-string)))
    (should (equal 5 (point)))))

;;;; Conversion (requires alectryon binary)

;; Matched conversion triplet: these three represent the same document.
(defconst alectryon-test--coq "(*|\nHello\n|*)\n\nLemma foo : True.\n")
(defconst alectryon-test--rst "Hello\n\n.. coq::\n\n   Lemma foo : True.\n")
(defconst alectryon-test--md  "Hello\n\n```{coq}\nLemma foo : True.\n```\n")

(ert-deftest alectryon-test-convert-coq-to-markup ()
  "Coq converts to exact expected RST and Markdown output."
  (skip-unless (alectryon-test--converter-available-p))
  (should (equal alectryon-test--rst
                 (alectryon-test--convert alectryon-test--coq "coq+rst" "rst")))
  (should (equal alectryon-test--md
                 (alectryon-test--convert alectryon-test--coq "coq+md" "md"))))

(ert-deftest alectryon-test-convert-markup-to-coq ()
  "RST and Markdown convert to exact expected Coq output."
  (skip-unless (alectryon-test--converter-available-p))
  (should (equal alectryon-test--coq
                 (alectryon-test--convert alectryon-test--rst "rst" "coq+rst")))
  (should (equal alectryon-test--coq
                 (alectryon-test--convert alectryon-test--md "md" "coq+md"))))

(ert-deftest alectryon-test-convert-round-trips ()
  "Coq -> markup -> Coq round-trips are identity for both RST and Markdown."
  (skip-unless (alectryon-test--converter-available-p))
  (let ((original "(*|\nHello\n|*)\n\nLemma foo : True. Proof. auto. Qed.\n"))
    (should (equal original
                   (alectryon-test--convert
                    (alectryon-test--convert original "coq+rst" "rst")
                    "rst" "coq+rst")))
    (should (equal original
                   (alectryon-test--convert
                    (alectryon-test--convert original "coq+md" "md")
                    "md" "coq+md")))))

(ert-deftest alectryon-test-convert-edge-cases ()
  "Conversion handles empty, code-only, and prose-only inputs."
  (skip-unless (alectryon-test--converter-available-p))
  (should (equal "" (string-trim (alectryon-test--convert "" "coq+rst" "rst"))))
  (should (equal ".. coq::\n\n   Lemma foo : True.\n"
                 (alectryon-test--convert "Lemma foo : True.\n" "coq+rst" "rst")))
  (should (equal "Just prose.\n"
                 (alectryon-test--convert "(*| Just prose. |*)\n" "coq+rst" "rst"))))

;;;; In-buffer conversion (alectryon--convert-from)

(ert-deftest alectryon-test-convert-from ()
  "alectryon--convert-from replaces buffer contents in-place and round-trips."
  (skip-unless (alectryon-test--converter-available-p))
  (with-temp-buffer
    (setq-local alectryon-prog-mode 'coq-mode)
    (setq-local alectryon-text-mode 'rst-mode)
    (insert alectryon-test--coq)
    (goto-char (point-min))
    ;; Coq -> RST
    (alectryon--convert-from 'coq-mode)
    (should (equal alectryon-test--rst (buffer-string)))
    ;; RST -> Coq
    (alectryon--convert-from 'rst-mode)
    (should (equal alectryon-test--coq (buffer-string)))))

(ert-deftest alectryon-test-convert-from-preserves-point ()
  "alectryon--convert-from preserves point position via --mark-point."
  (skip-unless (alectryon-test--converter-available-p))
  (with-temp-buffer
    (setq-local alectryon-prog-mode 'coq-mode)
    (setq-local alectryon-text-mode 'rst-mode)
    (insert alectryon-test--coq)
    (goto-char 7) ;; "l" in "Hello"
    (alectryon--convert-from 'coq-mode)
    ;; "Hello" starts at position 1 in RST output; "l" is at 3
    (should (equal 3 (point)))))

;;;; Toggle lifecycle

;; Stub coq-mode for testing (real coq-mode may not be installed)
(unless (fboundp 'coq-mode)
  (define-derived-mode coq-mode prog-mode "Coq"
    (set-syntax-table (alectryon-test--coq-syntax-table))))

(ert-deftest alectryon-test-toggle-lifecycle ()
  "Toggle converts content and switches modes; disable reverts; undo restores."
  (skip-unless (alectryon-test--converter-available-p))
  (with-temp-buffer
    (coq-mode)
    (setq-local alectryon-text-mode 'rst-mode)
    (buffer-enable-undo)
    (insert alectryon-test--coq)
    (alectryon-mode 1)
    ;; Preconditions
    (should (eq 'coq-mode major-mode))
    (should alectryon-mode)
    ;; Toggle: Coq -> RST
    (goto-char (point-min))
    (alectryon--toggle)
    (should (eq 'rst-mode major-mode))
    (should alectryon-mode)
    (should (equal alectryon-test--rst (buffer-string)))
    ;; Disable alectryon-mode (should revert to Coq)
    (goto-char (point-min))
    (alectryon-mode -1)
    (should (eq 'coq-mode major-mode))
    (should-not alectryon-mode)
    (should (equal alectryon-test--coq (buffer-string)))
    ;; Undo the disable: should restore RST + alectryon-mode
    (primitive-undo 2 buffer-undo-list)
    (should (eq 'rst-mode major-mode))
    (should alectryon-mode)
    (should (equal alectryon-test--rst (buffer-string)))))

(ert-deftest alectryon-test-toggle-undo-preserves-original-mode ()
  "After undo-of-disable, alectryon--original-mode must still be set."
  (skip-unless (alectryon-test--converter-available-p))
  (with-temp-buffer
    (coq-mode)
    (setq-local alectryon-text-mode 'rst-mode)
    (buffer-enable-undo)
    (insert alectryon-test--coq)
    (alectryon-mode 1)
    (goto-char (point-min))
    (alectryon--toggle)
    (goto-char (point-min))
    (alectryon-mode -1)
    ;; Undo the disable
    (primitive-undo 2 buffer-undo-list)
    ;; The critical check: original-mode must be coq-mode, not rst-mode
    (should (eq 'coq-mode alectryon--original-mode))))

(ert-deftest alectryon-test-disable-without-toggle ()
  "Disabling alectryon-mode while in original mode skips conversion."
  (skip-unless (alectryon-test--converter-available-p))
  (with-temp-buffer
    (coq-mode)
    (setq-local alectryon-text-mode 'rst-mode)
    (insert alectryon-test--coq)
    (alectryon-mode 1)
    (should (eq 'coq-mode major-mode))
    (should alectryon-mode)
    ;; Disable without ever toggling
    (alectryon-mode -1)
    (should (eq 'coq-mode major-mode))
    (should-not alectryon-mode)
    ;; Content unchanged
    (should (equal alectryon-test--coq (buffer-string)))))

(ert-deftest alectryon-test-toggle-undo ()
  "Undoing a normal toggle restores original mode and content."
  (skip-unless (alectryon-test--converter-available-p))
  (with-temp-buffer
    (coq-mode)
    (setq-local alectryon-text-mode 'rst-mode)
    (buffer-enable-undo)
    (insert alectryon-test--coq)
    (alectryon-mode 1)
    ;; Toggle: Coq -> RST
    (goto-char (point-min))
    (alectryon--toggle)
    (should (eq 'rst-mode major-mode))
    (should (equal alectryon-test--rst (buffer-string)))
    ;; Undo the toggle
    (primitive-undo 2 buffer-undo-list)
    (should (eq 'coq-mode major-mode))
    (should alectryon-mode)
    (should (equal alectryon-test--coq (buffer-string)))
    (should (eq 'coq-mode alectryon--original-mode))))

(provide 'alectryon-tests)
;;; alectryon-tests.el ends here
