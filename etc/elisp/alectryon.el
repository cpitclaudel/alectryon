;;; alectryon.el --- Toggle between Code and markup  -*- lexical-binding: t; -*-

;; Copyright (C) 2020-2023  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; Keywords: convenience, languages, tools
;; Version: 0.1
;; Url: https://github.com/cpitclaudel/alectryon
;; Package-Requires: ((flycheck "31") (emacs "25.1"))

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
  "Bidirectional literate programming support."
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

(defvaralias 'flycheck-alectryon-executable 'alectryon-executable)

(defcustom alectryon-executable
  (let ((exec (expand-file-name "alectryon.py" alectryon--directory)))
    (if (file-executable-p exec) exec
      "alectryon"))
  "Where to find the Alectryon binary."
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

(defun alectryon--refontify ()
  "Recompute fontification for visible part of current buffer."
  (if (and (fboundp 'font-lock-flush) (fboundp 'font-lock-ensure))
      (progn (setq font-lock-fontified t)
             (font-lock-flush) (font-lock-ensure))
    (with-no-warnings (font-lock-fontify-buffer))))

;;;; Modes selection

(defun alectryon--coq-exit-hook ()
  "Exit Proof General."
  (ignore-errors (alectryon--invoke 'proof-shell-exit t)))

(defconst alectryon-prog-modes
  '(( coq-mode
      :tag "coq"
      :exit-hooks (alectryon--coq-exit-hook)
      :comment-delimiters ("(*|" . "|*)")
      :comment-delimiters-re ("([*][|]" . "[|][*])")
      :annotations-re "([*]\s*\\(\\(?:\s*[.][-a-z]+\\)+\\)\s*[*])")))

(defconst alectryon-text-modes
  '(( rst-mode
      :tag "rst")))

(defvar-local alectryon-prog-mode 'coq-mode
  "Programming mode to use with Alectryon in this buffer.

This variable is initialized when Alectryon is switched on, based
on the current mode.")
(put 'alectryon-prog-mode 'permanent-local t)

(defvar-local alectryon-text-mode 'rst-mode
  "Markup mode to use with Alectryon in this buffer.

This variable is initialized when Alectryon is switched on, based
on the current mode.")
(put 'alectryon-text-mode 'permanent-local t)

(defun alectryon--prog-plist ()
  "Return the `prog-mode' Alectryon configuration for the current buffer."
  (or (alist-get alectryon-prog-mode alectryon-prog-modes)
      (error "Unrecognized Alectryon programming mode: %s" alectryon-prog-mode)))

(defun alectryon--text-plist ()
  "Return the `text-mode' Alectryon configuration for the current buffer."
  (or (alist-get alectryon-text-mode alectryon-text-modes)
      (error "Unrecognized Alectryon markup mode: %s" alectryon-text-mode)))

(defun alectryon--provided-mode-derived-p (mode &rest modes)
  "Check if MODE is derived from MODES."
  (or (apply #'provided-mode-derived-p mode modes)
      ;; Special override for coq-mode, which doesn't inherit from `prog-mode'.
      (and (eq mode 'coq-mode) (member 'prog-mode modes))))

(defmacro alectryon--mode-case (if-code if-markup &optional mode)
  "Choose between IF-CODE and IF-MARKUP based on MODE."
  (let ((m (make-symbol "mode")))
    `(progn
       (let ((,m (or ,mode major-mode)))
         (cond
          ((alectryon--provided-mode-derived-p ,m 'prog-mode) ,if-code)
          ((alectryon--provided-mode-derived-p ,m 'text-mode) ,if-markup)
          (t (error "Unrecognized mode: %s" ,m)))))))

(defun alectryon--config (prop &optional text-or-prog)
  "Get value of configuration variable PROP.

If TEXT-OR-PROG is `text', return the `text-mode' value of the
variable.  If it is `prog', return the `prog-mode' value of the
variable.  If it is nil, choose based on the current mode."
  (unless text-or-prog
    (setq text-or-prog (alectryon--mode-case 'prog 'text)))
  (plist-get
   (pcase text-or-prog
     (`prog (alectryon--prog-plist))
     (`text (alectryon--text-plist)))
   prop))

(defun alectryon--config-code+markup ()
  "Compute an id such as `coq+rst' based on `alectryon-config'."
  (format "%s+%s" (alectryon--config :tag 'prog) (alectryon--config :tag 'text)))

(defun alectryon--config-markup ()
  "Get an id such as `rst' for Alectryon."
  (alectryon--config :tag 'text))

(defun alectryon--config-frontend (&optional mode)
  "Get a frontend id for MODE."
  (alectryon--mode-case (alectryon--config-code+markup) (alectryon--config-markup) mode))

(defun alectryon--config-backend (&optional mode)
  "Get a frontend id for MODE."
  (alectryon--mode-case (alectryon--config-markup) (alectryon--config-code+markup) mode))

(defun alectryon-set-text-mode (mode)
  "Set markup mode to MODE."
  (interactive (completing-read "Markup mode to use in this buffer: "
                                (mapcar #'car alectryon-text-modes) nil t))
  (setf alectryon-text-mode mode)
  (when (and (derived-mode-p 'text-mode)
             (not (derived-mode-p mode)))
    (alectryon--set-mode mode)))

(defun alectryon-set-prog-mode (mode)
  "Set markup mode to MODE."
  (interactive (completing-read "Programming mode to use in this buffer: "
                                (mapcar #'car alectryon-prog-modes) nil t))
  (setf alectryon-prog-mode mode)
  (when (and (derived-mode-p 'prog-mode)
             (not (derived-mode-p mode)))
    (alectryon--set-mode mode)))

;;;; Conversion between code and markup

(defun alectryon--run-converter (input args)
  "Run Alectryon with ARGS on contents of buffer INPUT.

The output goes into the current buffer."
  (let* ((alectryon (executable-find alectryon-executable))
         (buffer (current-buffer))
         (args `(,@args "--traceback" "-")))
    (unless (and alectryon (file-executable-p alectryon))
      (user-error "Alectryon binary not found; try `pip install alectryon'"))
    (let* ((ex (with-current-buffer input
                 (alectryon--widened
                   (apply #'call-process-region nil nil alectryon
                          nil buffer nil args)))))
      (unless (eq 0 ex)
        (error "Conversion error (%s):\n%s" ex (alectryon--buffer-string))))))

(defun alectryon--converter-args (&optional mode)
  "Compute conversion arguments to convert from MODE."
  `("--frontend" ,(alectryon--config-frontend mode)
    "--backend" ,(alectryon--config-backend mode)))

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
  "Switch between code and markup views of the same file."
  (alectryon--record-mode)
  (apply #'run-hooks (alectryon--config :exit-hooks))
  (let ((modified (buffer-modified-p)))
    (alectryon--convert-from major-mode)
    (push `(apply ,(apply-partially #'alectryon--set-mode major-mode))
          buffer-undo-list)
    (alectryon--set-mode (alectryon--mode-case alectryon-text-mode alectryon-prog-mode))
    (set-buffer-modified-p modified)))

(defun alectryon-toggle ()
  "Switch between code and markup views of the same file."
  (interactive)
  (alectryon--toggle)
  (message "Switched to %s mode.  Press %s to go back." mode-name
           (substitute-command-keys "\\[alectryon-toggle]")))

;;;; Flycheck

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
  "Flycheck checker for literate code."
  :command '("alectryon"
             "--stdin-filename" source-original
             "--frontend" (eval (alectryon--config-frontend))
             "--backend" "lint"
             "-")
  :standard-input t
  :error-parser #'alectryon--parse-errors
  :predicate (lambda () alectryon-mode)
  :modes '(coq-mode rst-mode))

(add-to-list 'flycheck-checkers 'alectryon)

;;;; Font-locking

(defface alectryon-comment
  '((t :inherit font-lock-doc-face))
  "Face used to highlight Alectryon comments."
  :group 'alectryon)

(defface alectryon-comment-marker
  '((t :strike-through t :height 0.5))
  "Face used to highlight Alectryon comment delimiters."
  :group 'alectryon)

(defun alectryon--prog-syntactic-face-function (state)
  "Determine which face to use based on parsing state STATE."
  (let ((comment-opener-pos (nth 8 state)))
    (when comment-opener-pos
      (save-excursion
        (goto-char comment-opener-pos)
        (when (looking-at-p (car (alectryon--config :comment-delimiters-re 'prog)))
          'alectryon-comment)))))

;; TODO: display as a solid line even when it's on the same line.
(defun alectryon--prog-font-lock-keywords ()
  "Compute `font-lock' keywords for Alectryon delimiters in `prog-mode'."
  `((,(pcase-let ((`(,open . ,close) (alectryon--config :comment-delimiters-re 'prog)))
        (format "^\\(%s\\|%s\\)$" open close))
     ;; No space allowed at EOL (the :align-to would push it to the next line)
     1 '(face alectryon-comment-marker display (space :align-to right)) append)))

;; TODO highlight .. coq:: blocks in reST mode

;;;; Editing

(defun alectryon-insert-literate-block ()
  "Insert a pair of Alectryon comment delimiters."
  (interactive)
  (pcase-let*
      ((face (get-text-property (point) 'face))
       (`(,open . ,close) (alectryon--config :comment-delimiters 'prog))
       (in-lit (and (nth 4 (syntax-ppss))
                    (memq 'alectryon-comment (if (listp face) face (list face)))))
       (delim (if in-lit
                  `(,(format "%s\n\n" close) . ,(format "\n\n%s" open))
                `(,(format "%s\n" open) . ,(format "\n%s" close)))))
    (insert (car delim))
    (save-excursion (insert (cdr delim)))))

;;;; Preview

(defun alectryon-preview ()
  "Display an HTML preview of the current buffer."
  (interactive)
  (let* ((html-fname (make-temp-file "alectryon" nil ".html"))
         (input (current-buffer))
         (frontend (alectryon--mode-case (alectryon--config-code+markup) (alectryon--config-markup)))
         (args `("--frontend" ,frontend "--backend" "webpage"
                 "-o" ,html-fname)))
    (with-temp-buffer
      (alectryon--run-converter input args)
      (let ((msg (string-trim (buffer-string))))
        (message "Compilation complete%s%s"
                 (if (string-empty-p msg) "" ": ") msg)))
    (browse-url html-fname)))

;;;; Minor mode

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

(defun alectryon-customize ()
  "Open `alectryon-mode''s customization menu."
  (interactive)
  (customize-group 'alectryon))

(defvar alectryon-prog-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map alectryon-mode-map)
    (define-key map (kbd "C-c C-=") #'alectryon-insert-literate-block)
    map))

(defvar-local alectryon--prog-font-lock-keywords nil
  "Cache variable for `alectryon--prog-font-lock-keywords'.")

(define-minor-mode alectryon--prog-mode
  "Enable or disable the code-specific parts of `alectryon-mode'."
  :keymap alectryon-prog-mode-map
  (cond
   (alectryon--prog-mode
    (visual-line-mode)
    (setq alectryon--prog-font-lock-keywords (alectryon--prog-font-lock-keywords))
    (font-lock-add-keywords nil alectryon--prog-font-lock-keywords)
    (add-to-list 'font-lock-extra-managed-props 'display)
    (add-function :before-until (local 'font-lock-syntactic-face-function)
                  #'alectryon--prog-syntactic-face-function '((depth . -100))))
   (t
    (visual-line-mode -1)
    (font-lock-remove-keywords nil alectryon--prog-font-lock-keywords)
    (remove-function (local 'font-lock-syntactic-face-function)
                     #'alectryon--prog-syntactic-face-function))))

(defvar alectryon-text-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map alectryon-mode-map)
    map))

(define-minor-mode alectryon--text-mode
  "Enable or disable the markup-specific parts of `alectryon-mode'."
  :keymap alectryon-text-mode-map)

(defun alectryon--record-mode ()
  "Initialize `alectryon--original-mode'."
  (setq-local alectryon--original-mode (or alectryon--original-mode major-mode))
  (alectryon--mode-case
   (setq alectryon-prog-mode major-mode)
   (setf alectryon-text-mode major-mode)))

;; Adding the menu to a parent keymap causes it to be duplicated (?!), so add it
;; to both submaps instead.
(easy-menu-define alectryon-mode-menu (list alectryon-prog-mode-map alectryon-text-mode-map)
  "Alectryon's main menu."
  '("Alectryon"
    ["Convert to markup" alectryon-toggle :visible (alectryon--mode-case t nil)]
    ["Convert to code" alectryon-toggle :visible (alectryon--mode-case nil t)]
    ["Preview the current buffer as a webpage." alectryon-preview]
    ["Configure alectryon-mode" alectryon-customize]))

(defvar flyspell-prog-text-faces)

(defun alectryon--flyspell-hook ()
  "Hook run when Flyspell is loaded in this buffer."
  (when (bound-and-true-p flyspell-mode)
    (make-local-variable 'flyspell-prog-text-faces)
    (cl-pushnew 'alectryon-comment flyspell-prog-text-faces)))

(defun alectryon--flyspell-unhook ()
  "Remove Flyspell customizations."
  (when (bound-and-true-p flyspell-mode)
    (setq-local flyspell-prog-text-faces
                (remq 'alectryon-comment flyspell-prog-text-faces))))

;;;###autoload
(define-minor-mode alectryon-mode
  "Mode for Alectryon files.

In code mode:
\\{alectryon-prog-mode-map}
In markup mode:
\\{alectryon-text-mode-map}"
  :lighter " 📚"
  (cond
   (alectryon-mode
    (alectryon--record-mode)
    (alectryon--invoke 'flycheck-mode)
    (add-hook 'write-contents-functions #'alectryon--save t t)
    (add-hook 'flyspell-mode-hook #'alectryon--flyspell-hook)
    (alectryon--flyspell-hook)
    (alectryon--mode-case (alectryon--prog-mode 1) (alectryon--text-mode 1)))
   (t
    (unless (alectryon--in-original-mode)
      (alectryon--toggle)
      (message "Reverted to %s mode." mode-name))
    (kill-local-variable 'alectryon--original-mode)
    (remove-hook 'write-contents-functions #'alectryon--save t)
    (remove-hook 'flyspell-mode-hook #'alectryon--flyspell-hook)
    (alectryon--flyspell-unhook)
    (alectryon--mode-case (alectryon--prog-mode -1) (alectryon--text-mode -1))))
  (alectryon--refontify))

;;;; Presentation mode

(defun alectryon--prog-presentation-font-lock-keywords ()
  "Compute `font-lock' keywords for Alectryon annotations in `prog-mode'."
  `((,(alectryon--config :code-annotations-re)
     0 '(face '(:height 0.5) display "👻") append)))

(defvar-local alectryon--prog-presentation-font-lock-keywords nil
  "Cache variable for `alectryon--prog-presentation-font-lock-keywords'.")

(define-minor-mode alectryon-presentation-mode
  "Hide Alectryon annotations in code files."
  :lighter ""
  (cond
   (alectryon-presentation-mode
    (setq alectryon--prog-font-lock-keywords (alectryon--prog-presentation-font-lock-keywords))
    (font-lock-add-keywords nil alectryon--prog-presentation-font-lock-keywords))
   (t
    (font-lock-remove-keywords nil alectryon--prog-presentation-font-lock-keywords)))
  (font-lock-flush))

;;;###autoload
(add-hook 'coq-mode-hook #'alectryon-mode t)

(provide 'alectryon)
;;; alectryon.el ends here
