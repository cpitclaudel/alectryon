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

(require 'flycheck nil t)
(require 'proof-general nil t)
(require 'proof-shell nil t)

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

;;; Conversion between Coq and reST

(defun alectryon--run-converter (input args)
  "Convert INPUT with ARGS.

The output goes into the current buffer."
  (let* ((python (executable-find alectryon-python-executable))
         (converter (alectryon--locate-executable))
         (args `(,@args "-")))
    (print (cons converter args))
    (let* ((ex (apply #'call-process-region input nil python
                      nil (current-buffer) nil converter args)))
      (unless (eq 0 ex)
        (error "Conversion error (%s):\n%s" ex (alectryon--buffer-string))))))

(defun alectryon--mode-case (coq rst &optional mode)
  "Choose between COQ and RST based on MODE."
  (setq mode (or mode major-mode))
  (cond
   ((provided-mode-derived-p mode 'coq-mode) coq)
   ((provided-mode-derived-p mode 'rst-mode) rst)
   (t (user-error "Unrecognized mode: %S" mode))))

(defun alectryon--converter-args (&optional mode)
  "Compute conversion arguments to convert from MODE."
  (alectryon--mode-case
   `("--frontend" "coq+rst" "--backend" "rst")
   `("--frontend" "rst" "--backend" "coq+rst")
   mode))

(defun alectryon--toggle (mode)
  "Convert current buffer from MODE."
  (let* ((input (alectryon--buffer-string))
         (buffer (current-buffer))
         (pt (point)))
    (with-temp-buffer
      (alectryon--run-converter input (alectryon--converter-args mode))
      (let ((output (current-buffer)))
        (with-current-buffer buffer
          (setq buffer-read-only nil)
          (widen)
          (unless (replace-buffer-contents output 1)
            (goto-char (min pt (point-max)))))))))

(defun alectryon--set-mode (mode)
  "Switch to MODE and enable `alecrtyon-mode'."
  (alectryon--invoke mode)
  (funcall #'alectryon-mode))

(defun alectryon-toggle ()
  "Switch between Coq and reST views of the same file."
  (interactive)
  (alectryon-mode) ;; Set alectryon--original-mode
  (when (derived-mode-p 'coq-mode)
    (ignore-errors (alectryon--invoke 'proof-shell-exit t)))
  (let ((modified (buffer-modified-p)))
    (alectryon--toggle major-mode)
    (push `(apply ,(apply-partially #'alectryon--set-mode major-mode))
          buffer-undo-list)
    (alectryon--set-mode (alectryon--mode-case 'rst-mode 'coq-mode))
    (set-buffer-modified-p modified))
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
      (alist-get 'line js) nil
      (or (cdr (assoc (alist-get 'level js) alectryon--error-levels)) 'error)
      (alist-get 'message js)
      :checker checker
      :filename (alist-get 'source js)
      :buffer buffer))
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

(defun alectryon--syntactic-face-function (state)
  "Determine which face to use based on parsing state STATE."
  (let ((comment-opener-pos (nth 8 state)))
    (when comment-opener-pos
      (save-excursion
        (goto-char comment-opener-pos)
        (when (looking-at-p (regexp-quote "(*|"))
          'alectryon-comment)))))

(defconst alectryon--coq-font-lock-keywords
  '(("^\\(([*][|]\\|[|][*])\\)$"
     1 '(face alectryon-comment-marker display (space :align-to right)) append)))

(defconst alectryon--rst-font-lock-keywords
  '())

;;; Minor mode

(defvar-local alectryon--original-mode nil
  "Major mode when `alectryon-mode' was enabled.")
(put 'alectryon--original-mode 'permanent-local t)

(defun alectryon--save ()
  "Translate back to `alectryon--original-mode' and save the result.
Current document must have a file name."
  (unless (eq major-mode (or alectryon--original-mode major-mode))
    (let ((mode major-mode)
          (input (alectryon--buffer-string))
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

(define-minor-mode alectryon-mode
  "Mode for Literate Coq files.

\\{alectryon-mode-map}."
  :lighter " 📚"
  (cond
   (alectryon-mode
    (visual-line-mode)
    (alectryon--invoke 'flycheck-mode)
    (add-to-list 'font-lock-extra-managed-props 'display)
    (font-lock-add-keywords
     nil (alectryon--mode-case alectryon--coq-font-lock-keywords alectryon--rst-font-lock-keywords))
    (add-function :before-until (local 'font-lock-syntactic-face-function)
                  #'alectryon--syntactic-face-function '((depth . -100)))
    (setq-local alectryon--original-mode (or alectryon--original-mode major-mode))
    (add-hook 'write-contents-functions #'alectryon--save t t))
   (t
    (visual-line-mode -1)
    (font-lock-remove-keywords
     nil (alectryon--mode-case alectryon--coq-font-lock-keywords alectryon--rst-font-lock-keywords))
    (remove-function (local 'font-lock-syntactic-face-function)
                     #'alectryon--syntactic-face-function)
    (kill-local-variable 'alectryon--original-mode)
    (remove-hook 'write-contents-functions #'alectryon--save t)))
  (if (and (fboundp 'font-lock-flush) (fboundp 'font-lock-ensure))
      (progn (setq font-lock-fontified t)
             (font-lock-flush) (font-lock-ensure))
    (with-no-warnings (font-lock-fontify-buffer))))

;;;###autoload
(add-hook 'coq-mode-hook #'alectryon-mode t)

(provide 'alectryon)
;;; alectryon.el ends here
