;;; alectryon-tests.el --- Tests for alectryon.el  -*- lexical-binding: t; -*-

;; Run with: emacs --batch -Q -l alectryon-tests.el -f ert-run-tests-batch-and-exit

;;; Code:

;; Needed to find MELPA-installed flycheck on the load-path.
(require 'package)
(package-initialize)

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

;;;; Configuration and mode dispatching

(ert-deftest alectryon-test-config ()
  "Config system returns correct tags, delimiters, and frontend/backend ids."
  (with-temp-buffer
    (setq-local alectryon-prog-mode 'coq-mode)
    (setq-local alectryon-text-mode 'rst-mode)
    ;; Tags
    (should (equal "coq" (alectryon--config :tag 'prog)))
    (should (equal "rst" (alectryon--config :tag 'text)))
    ;; Delimiters
    (let ((delims (alectryon--config :comment-delimiters 'prog)))
      (should (equal "(*|" (car delims)))
      (should (equal "|*)" (cdr delims))))
    ;; Frontend/backend
    (should (equal "coq+rst" (alectryon--config-frontend 'coq-mode)))
    (should (equal "rst" (alectryon--config-backend 'coq-mode)))
    ))

(ert-deftest alectryon-test-mode-dispatch ()
  "mode-case and provided-mode-derived-p dispatch correctly."
  ;; mode-case
  (should (eq 'code (alectryon--mode-case 'code 'text 'coq-mode)))
  (should (eq 'text (alectryon--mode-case 'code 'text 'rst-mode)))
  ;; provided-mode-derived-p: alist lookup
  (should (alectryon--provided-mode-derived-p 'coq-mode 'prog-mode))
  (should (alectryon--provided-mode-derived-p 'rst-mode 'text-mode))
  ;; provided-mode-derived-p: real inheritance
  (should (alectryon--provided-mode-derived-p 'emacs-lisp-mode 'prog-mode)))

;;;; Literate comment detection

(ert-deftest alectryon-test-literate-comment ()
  "Literate comment detection distinguishes (*| |*) from (* *) and code."
  (with-temp-buffer
    (set-syntax-table (alectryon-test--coq-syntax-table))
    (setq-local alectryon-prog-mode 'coq-mode)
    (setq-local alectryon-text-mode 'rst-mode)
    ;; Inside literate comment
    (erase-buffer)
    (insert "(*| hello |*)")
    (goto-char 6)
    (should (alectryon--in-literate-comment-p))
    ;; Outside any comment
    (erase-buffer)
    (insert "Lemma foo. (*| hello |*)")
    (goto-char 3)
    (should-not (alectryon--in-literate-comment-p))
    ;; Inside regular comment
    (erase-buffer)
    (insert "(* regular *)")
    (goto-char 6)
    (should-not (alectryon--in-literate-comment-p))))

;;;; Conversion (requires alectryon binary)

(ert-deftest alectryon-test-convert-coq-to-rst ()
  "Coq with literate comments converts to RST with directives."
  (skip-unless (alectryon-test--converter-available-p))
  (let ((rst (alectryon-test--convert
              "(*|\nHello\n|*)\n\nLemma foo : True.\n"
              "coq+rst" "rst")))
    (should (string-match-p "Hello" rst))
    (should (string-match-p "\\.\\. coq::" rst))))

(ert-deftest alectryon-test-convert-rst-to-coq ()
  "RST with coq directives converts to Coq with literate comments."
  (skip-unless (alectryon-test--converter-available-p))
  (let ((coq (alectryon-test--convert
              "Hello\n\n.. coq::\n\n   Lemma foo : True.\n"
              "rst" "coq+rst")))
    (should (string-match-p "(\\*|" coq))
    (should (string-match-p "|\\*)" coq))))

(ert-deftest alectryon-test-convert-round-trips ()
  "Coq -> RST -> Coq and RST -> Coq -> RST are identity."
  (skip-unless (alectryon-test--converter-available-p))
  ;; Coq round-trip
  (let* ((coq-orig "(*|\nHello\n|*)\n\nLemma foo : True. Proof. auto. Qed.\n")
         (rst (alectryon-test--convert coq-orig "coq+rst" "rst"))
         (coq-back (alectryon-test--convert rst "rst" "coq+rst")))
    (should (equal coq-orig coq-back)))
  ;; RST round-trip
  (let* ((rst-orig "Hello\n\n.. coq::\n\n   Lemma foo : True.\n")
         (coq (alectryon-test--convert rst-orig "rst" "coq+rst"))
         (rst-back (alectryon-test--convert coq "coq+rst" "rst")))
    (should (equal rst-orig rst-back))))

(ert-deftest alectryon-test-convert-edge-cases ()
  "Conversion handles empty, code-only, and prose-only inputs."
  (skip-unless (alectryon-test--converter-available-p))
  ;; Empty
  (should (equal "" (string-trim (alectryon-test--convert "" "coq+rst" "rst"))))
  ;; Code only
  (let ((rst (alectryon-test--convert "Lemma foo : True.\n" "coq+rst" "rst")))
    (should (string-match-p "Lemma foo" rst))
    (should (string-match-p "\\.\\. coq::" rst)))
  ;; Prose only
  (should (string-match-p "Just prose"
            (alectryon-test--convert "(*| Just prose. |*)\n" "coq+rst" "rst"))))

(ert-deftest alectryon-test-convert-multiple-blocks ()
  "Multiple code/prose blocks survive conversion."
  (skip-unless (alectryon-test--converter-available-p))
  (let ((rst (alectryon-test--convert
              (concat "(*| First |*)\n\nLemma a : True.\n\n"
                      "(*| Second |*)\n\nLemma b : True.\n")
              "coq+rst" "rst")))
    (should (string-match-p "First" rst))
    (should (string-match-p "Second" rst))
    (should (string-match-p "Lemma a" rst))
    (should (string-match-p "Lemma b" rst))))

(provide 'alectryon-tests)
;;; alectryon-tests.el ends here
