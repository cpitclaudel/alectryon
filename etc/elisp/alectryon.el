;;; alectryon.el --- Toggle between Coq and reStructuredText  -*- lexical-binding: t; -*-

;; Copyright (C) 2020  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; Keywords: convenience, languages, tools
;; Version: 0.1

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This package is a thin wrapper around Alectryon's editor support
;; (https://github.com/cpitclaudel/alectryon).  The idea is to easily switch
;; between a code-first and a text-first view of a literate file.
;;
;; Concretely, Alectryon converts back and forth between this:
;;
;;     =============================
;;      Writing decision procedures
;;     =============================
;;
;;     Here's an inductive type:
;;
;;     .. coq::
;;
;;        Inductive Even : nat -> Prop :=
;;        | EvenO : Even O
;;        | EvenS : forall n, Even n -> Even (S (S n)).
;;
;;     .. note::
;;
;;        It has two constructors:
;;
;;        .. coq:: unfold out
;;
;;           Check EvenO.
;;           Check EvenS.
;;
;; … and this:
;;
;;     (*|
;;     =============================
;;      Writing decision procedures
;;     =============================
;;
;;     Here's an inductive type:
;;     |*)
;;
;;     Inductive Even : nat -> Prop :=
;;     | EvenO : Even O
;;     | EvenS : forall n, Even n -> Even (S (S n)).
;;
;;     (*|
;;     .. note::
;;
;;        It has two constructors:
;;
;;        .. coq:: unfold out
;;     |*)
;;
;;     Check EvenO.
;;     Check EvenS.

;;; Code:

(require 'flycheck)
(require 'proof-general nil t)

(defgroup alectryon nil
  "reStructuredText support Coq files."
  :prefix "alectryon-"
  :group 'languages)

;;;; Utilities

(defconst alectryon--script-full-path
  (or (and load-in-progress load-file-name)
      (bound-and-true-p byte-compile-current-file)
      (buffer-file-name))
  "Full path of this script.")

(defconst alectryon--directory
  (expand-file-name "../../" (file-name-directory alectryon--script-full-path))
  "Full path to directory of this script.")

(defvaralias 'flycheck-alectryon-executable 'alectryon-python-executable)

(defcustom alectryon-python-executable "python3"
  "Where to find Python 3."
  :group 'alectryon
  :type 'file
  :risky t)

(defmacro alectryon--widened (&rest body)
  "Run BODY widened."
  (declare (indent 0) (debug t))
  `(save-restriction (widen) ,@body))

(defmacro alectryon--widened-excursion (&rest body)
  "Run BODY widened in a `save-excursion' block."
  (declare (indent 0) (debug t))
  `(save-excursion (alectryon--widened ,@body)))

(defun alectryon--invoke (fn &rest args)
  "Call FN on ARGS, if FN is bound."
  (when (fboundp fn)
    (apply fn args)))

(defun alectryon--buffer-string ()
  "Return contents of widened current buffer without properties."
  (alectryon--widened (buffer-substring-no-properties (point-min) (point-max))))

(defun alectryon--locate-executable ()
  "Find the full path to alectryon.py."
  (expand-file-name "alectryon.py" alectryon--directory))

(defun alectryon--refontify ()
  "Recompute fontification for visible part of current buffer."
  (if (and (fboundp 'font-lock-flush) (fboundp 'font-lock-ensure))
      (progn (setq font-lock-fontified t)
             (font-lock-flush) (font-lock-ensure))
    (with-no-warnings (font-lock-fontify-buffer))))

;;; Conversion between Coq and reST

(defun alectryon--run-converter (input args)
  "Convert contents of buffer INPUT with ARGS.

The output goes into the current buffer."
  (let* ((python (executable-find alectryon-python-executable))
         (converter (alectryon--locate-executable))
         (buffer (current-buffer))
         (args `(,@args "-")))
    (let* ((ex (with-current-buffer input
                 (alectryon--widened
                   (apply #'call-process-region nil nil python
                          nil buffer nil converter args)))))
      (unless (eq 0 ex)
        (error "Conversion error (%s):\n%s" ex (alectryon--buffer-string))))))

(defmacro alectryon--mode-case (coq rst &optional mode)
  "Choose between COQ and RST based on MODE."
  (let ((m (make-symbol "mode")))
    `(progn
       (let ((,m (or ,mode major-mode)))
         (cond
          ((provided-mode-derived-p ,m 'coq-mode) ,coq)
          ((provided-mode-derived-p ,m 'rst-mode) ,rst)
          (t (user-error "Unrecognized mode: %S" ,m)))))))

(defun alectryon--converter-args (&optional mode)
  "Compute conversion arguments to convert from MODE."
  (alectryon--mode-case
   `("--frontend" "coq+rst" "--backend" "rst")
   `("--frontend" "rst" "--backend" "coq+rst")
   mode))

(defun alectryon--convert-from (mode)
  "Convert current buffer from MODE."
  (let* ((pt (point))
         (marker "")
         (pt-str (number-to-string (1- pt)))
         (args `("--mark-point" ,pt-str ,marker ,@(alectryon--converter-args mode)))
         (input (current-buffer)))
    (with-temp-buffer
      (alectryon--run-converter input args)
      (let ((output (current-buffer)))
        (with-current-buffer input
          (widen)
          (setq buffer-read-only nil)
          (delete-region (point-min) (point-max))
          (insert-buffer-substring output))))
    (goto-char (point-min))
    (if (search-forward marker nil t)
        (delete-char -1)
      (message "Point marker missing from Alectryon's output.
Please open an issue at https://github.com/cpitclaudel/alectryon.")
      (goto-char (min pt (point-max))))))

(defun alectryon--set-mode (mode)
  "Switch to MODE and enable `alectryon-mode'."
  (alectryon--invoke mode)
  (funcall #'alectryon-mode))

(defun alectryon--toggle ()
  "Switch between Coq and reST views of the same file."
  (alectryon--record-original-mode)
  (when (derived-mode-p 'coq-mode)
    (ignore-errors (alectryon--invoke 'proof-shell-exit t)))
  (let ((modified (buffer-modified-p)))
    (alectryon--convert-from major-mode)
    (push `(apply ,(apply-partially #'alectryon--set-mode major-mode))
          buffer-undo-list)
    (alectryon--set-mode (alectryon--mode-case 'rst-mode 'coq-mode))
    (set-buffer-modified-p modified)))

(defun alectryon-toggle ()
  "Switch between Coq and reST views of the same file."
  (interactive)
  (alectryon--toggle)
  (message "Switched to %s mode.  Press %s to go back." mode-name
           (substitute-command-keys "\\[alectryon-toggle]")))

;;; Flycheck

(defvar alectryon-mode)

(defconst alectryon--error-levels
  '(("debug" . info) ("info" . info)
    ("warning" . warning)
    ("error" . error) ("severe" . error)))

(defun alectryon--parse-errors (output checker buffer)
  "Parse alectryon.docutils.JsErrorPrinter messages in OUTPUT.

OUTPUT is the result of Flychecking BUFFER with CHECKER."
  (mapcar
   (lambda (js)
     (flycheck-error-new-at
      (alist-get 'line js) (alist-get 'column js)
      (or (cdr (assoc (alist-get 'level js) alectryon--error-levels)) 'error)
      (alist-get 'message js)
      :checker checker
      :filename (alist-get 'source js)
      :buffer buffer
      :end-line (alist-get 'end_line js)
      :end-column (alist-get 'end_column js)))
   (flycheck-parse-json output)))

(defun alectryon--flycheck-verify-enabled ()
  "Check whether `alectryon-mode' is enabled, as a verification result."
  (list
   (flycheck-verification-result-new
    :label "Checker selection"
    :message (if alectryon-mode "OK, using `alectryon-mode'."
               (substitute-command-keys "Use \\[alectryon-mode] to enable."))
    :face (if alectryon-mode 'success '(bold error)))))

(flycheck-define-command-checker 'alectryon
  "Flycheck checker for literate Coq."
  :command '("python3"
             (eval (alectryon--locate-executable))
             "--stdin-filename" source-original
             "--frontend" (eval (alectryon--mode-case "coq+rst" "rst"))
             "--backend" "lint"
             "-")
  :standard-input t
  :error-parser #'alectryon--parse-errors
  :enabled (lambda () (or (not (fboundp 'flycheck-python-find-module))
                     (flycheck-python-find-module 'alectryon "docutils")))
  :predicate (lambda () alectryon-mode)
  :verify (lambda (_checker)
            (append (alectryon--flycheck-verify-enabled)
                    (when (fboundp 'flycheck-python-verify-module)
                      (flycheck-python-verify-module 'alectryon "docutils"))))
  :modes '(coq-mode rst-mode))

(add-to-list 'flycheck-checkers 'alectryon)

;;; Font-locking

(defface alectryon-comment
  '((t :inherit font-lock-doc-face))
  "Face used to highlight (*| … |*) comments."
  :group 'alectryon)

(defface alectryon-comment-marker
  '((t :strike-through t :height 0.5))
  "Face used to highlight (*| … |*) marker."
  :group 'alectryon)

(defun alectryon--coq-syntactic-face-function (state)
  "Determine which face to use based on parsing state STATE."
  (let ((comment-opener-pos (nth 8 state)))
    (when comment-opener-pos
      (save-excursion
        (goto-char comment-opener-pos)
        (when (looking-at-p (regexp-quote "(*|"))
          'alectryon-comment)))))

(defconst alectryon--coq-font-lock-keywords
  '(("^\\(([*][|]\\|[|][*])\\)$"
     ;; No space allowed at EOL (the :align-to would push it to the next line)
     1 '(face alectryon-comment-marker display (space :align-to right)) append)))

;; TODO highlight .. coq:: blocks in reST mode

;;; Editing

(defun alectryon-insert-literate-block ()
  "Insert a pair of (*| … |*) markers."
  (interactive)
  (insert "(*|\n")
  (save-excursion (insert "\n|*)\n")))

;;; Minor mode

(defvar-local alectryon--original-mode nil
  "Major mode when `alectryon-mode' was enabled.")
(put 'alectryon--original-mode 'permanent-local t)

(defun alectryon--in-original-mode ()
  "Check if current buffer is in its original mode."
  (eq major-mode (or alectryon--original-mode major-mode)))

(defun alectryon--save ()
  "Translate back to `alectryon--original-mode' and save the result.
Current document must have a file name."
  (unless (alectryon--in-original-mode)
    (let ((mode major-mode)
          (input (current-buffer))
          (fname buffer-file-name))
      (with-temp-buffer
        (alectryon--run-converter input (alectryon--converter-args mode))
        (write-region (point-min) (point-max) fname)))
    (set-buffer-modified-p nil)
    (set-visited-file-modtime)
    t))

(defvar alectryon-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-S-a") #'alectryon-toggle)
    map))

(defvar alectryon-coq-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map alectryon-mode-map)
    (define-key map (kbd "C-c C-=") #'alectryon-insert-literate-block)
    map))

(define-minor-mode alectryon--coq-mode
  "Enable or disable the Coq-specific parts of `alectryon-mode'."
  :keymap alectryon-coq-mode-map
  (cond
   (alectryon--coq-mode
    (visual-line-mode)
    (font-lock-add-keywords nil alectryon--coq-font-lock-keywords)
    (add-to-list 'font-lock-extra-managed-props 'display)
    (add-function :before-until (local 'font-lock-syntactic-face-function)
                  #'alectryon--coq-syntactic-face-function '((depth . -100))))
   (t
    (visual-line-mode -1)
    (font-lock-remove-keywords nil alectryon--coq-font-lock-keywords)
    (remove-function (local 'font-lock-syntactic-face-function)
                     #'alectryon--coq-syntactic-face-function))))

(defvar alectryon-rst-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map alectryon-mode-map)
    map))

(define-minor-mode alectryon--rst-mode
  "Enable or disable the reST-specific parts of `alectryon-mode'."
  :keymap alectryon-rst-mode-map)

(defun alectryon--record-original-mode ()
  "Initialize `alectryon--original-mode'."
  (setq-local alectryon--original-mode (or alectryon--original-mode major-mode)))

(define-minor-mode alectryon-mode
  "Mode for Literate Coq files.

In Coq mode:
\\{alectryon-coq-mode-map}
In reST mode:
\\{alectryon-rst-mode-map}"
  :lighter " 📚"
  (cond
   (alectryon-mode
    (alectryon--record-original-mode)
    (alectryon--invoke 'flycheck-mode)
    (add-hook 'write-contents-functions #'alectryon--save t t)
    (alectryon--mode-case (alectryon--coq-mode 1) (alectryon--rst-mode 1)))
   (t
    (unless (alectryon--in-original-mode)
      (alectryon--toggle)
      (message "Reverted to %s mode." mode-name))
    (kill-local-variable 'alectryon--original-mode)
    (remove-hook 'write-contents-functions #'alectryon--save t)
    (alectryon--mode-case (alectryon--coq-mode -1) (alectryon--rst-mode -1))))
  (alectryon--refontify))

;;;###autoload
(add-hook 'coq-mode-hook #'alectryon-mode t)

(provide 'alectryon)
;;; alectryon.el ends here
