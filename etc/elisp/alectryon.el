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

(require 'cl-lib)
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
  "Full path to the root of the Alectryon repo.")

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

(defmacro alectryon--atomic (&rest body)
  "Run BODY as a single undoable step.
Errors roll back all changes.  Undo boundaries before and after
ensure BODY is one undo group."
  (declare (indent 0) (debug t))
  `(progn
     (undo-boundary)
     (atomic-change-group
       ,(if (fboundp 'with-undo-amalgamate)
            `(with-undo-amalgamate ,@body)
          `(progn ,@body)))
     (undo-boundary)))

(defun alectryon--invoke (fn &rest args)
  "Call FN on ARGS, if FN is bound."
  (when (fboundp fn)
    (apply fn args)))

(defun alectryon--buffer-string ()
  "Return contents of widened current buffer without properties."
  (alectryon--widened (buffer-substring-no-properties (point-min) (point-max))))

(defun alectryon--refontify ()
  "Recompute fontification for visible part of current buffer."
  (setq font-lock-fontified t)
  (font-lock-flush)
  (font-lock-ensure))

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
      :annotations-re "[(][*]\\(\\(?:\\s-*[.][-a-z]+\\)+\\)\\s-*[*][)]")))

(defconst alectryon-text-modes
  '(( rst-mode
      :tag "rst"
      :suffixes ("_rst[.][^./]+$"))
    ( markdown-mode
      :tag "md"
      :suffixes ("_md[.][^./]+$"))))

(defvar-local alectryon-prog-mode 'coq-mode
  "Programming mode to use with Alectryon in this buffer.

This variable is initialized when Alectryon is switched on, based
on the current mode.")
(put 'alectryon-prog-mode 'permanent-local t)

(defvar alectryon-fallback-text-mode 'rst-mode
  "Default markup mode to use with Alectryon.

Only used when asking the user is impractical, e.g. from
Flycheck, and when `alectryon-text-mode' is unset.  To set a global
default, set `alectryon-text-mode'.")

(defvar-local alectryon-text-mode nil
  "Markup mode to use with Alectryon in this buffer.

This variable is initialized when Alectryon is switched on in
text mode (based on the current mode), or just before switching
to text mode.  Its default value (nil) means ask the user before
switching.")
(put 'alectryon-text-mode 'permanent-local t)

(defun alectryon--text-mode-with-fallback ()
  "Return `alectryon-text-mode', falling back to `alectryon-fallback-text-mode'."
  (or alectryon-text-mode alectryon-fallback-text-mode))

(defun alectryon--prog-plist ()
  "Return the `prog-mode' Alectryon configuration for the current buffer."
  (or (alist-get alectryon-prog-mode alectryon-prog-modes)
      (error "Unrecognized Alectryon programming mode: %s" alectryon-prog-mode)))

(defun alectryon--text-plist ()
  "Return the `text-mode' Alectryon configuration for the current buffer."
  (let ((mode (alectryon--text-mode-with-fallback)))
    (or (alist-get mode alectryon-text-modes)
        (error "Unrecognized Alectryon markup mode: %s" mode))))

(defun alectryon--prog-mode-p (&optional mode)
  "Return t if MODE is a code mode, nil if a text mode.

Error out if neither."
  (setq mode (or mode major-mode))
  (cond
   ((assq mode alectryon-prog-modes) t)
   ((assq mode alectryon-text-modes) nil)
   (t (error "Unrecognized mode: %s (expecting one of %s)"
             mode (mapcar #'car (append alectryon-text-modes alectryon-prog-modes))))))

(defmacro alectryon--mode-case (if-prog if-markup &optional mode)
  "Choose between IF-PROG and IF-MARKUP based on MODE."
  (declare (indent 0) (debug t))
  `(if (alectryon--prog-mode-p ,mode) ,if-prog ,if-markup))

(defun alectryon--config (prop &optional text-or-prog)
  "Get value of configuration variable PROP.

If TEXT-OR-PROG is `text', return the `text-mode' value of the
variable.  If it is `prog', return the `prog-mode' value of the
variable.  If it is nil, choose based on the current mode."
  (unless text-or-prog
    (setq text-or-prog (alectryon--mode-case 'prog 'text)))
  (plist-get
   (pcase-exhaustive text-or-prog
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
  "Get a backend id for MODE."
  (alectryon--mode-case (alectryon--config-markup) (alectryon--config-code+markup) mode))

(defun alectryon--read-mode (prog-p)
  "Read a mode depending on PROG-P."
  (let* ((modes (mapcar #'car (if prog-p alectryon-prog-modes alectryon-text-modes)))
         (prompt (format "%s mode to use: " (if prog-p "Programming" "Markup")))
         (mode (intern (completing-read prompt modes nil t))))
    (unless (fboundp mode)
      (user-error "Not installed: %s" mode))
    mode))

(defun alectryon--set-mode-variable (prog-p mode)
  "Set alectryon-text-mode or alectryon-prog-mode to MODE depending on PROG-P."
  (setf (if prog-p alectryon-prog-mode alectryon-text-mode) mode)
  (when (and (not (derived-mode-p mode))
             (eq prog-p (alectryon--prog-mode-p)))
    (alectryon--set-mode mode)))

(defun alectryon-set-text-mode (mode)
  "Set markup mode to MODE."
  (interactive (list (alectryon--read-mode nil)))
  (alectryon--set-mode-variable nil mode))

(defun alectryon-set-prog-mode (mode)
  "Set programming mode to MODE."
  (interactive (list (alectryon--read-mode t)))
  (alectryon--set-mode-variable t mode))

(defun alectryon--guess-text-mode ()
  "Guess the markup mode to use from the buffer's filename."
  (let ((path (or buffer-file-name (buffer-name))))
    (and path
         (car-safe
          (cl-find-if
           (lambda (props) (cl-some (lambda (suffix) (string-match-p suffix path))
                               (plist-get (cdr props) :suffixes)))
           alectryon-text-modes)))))

(defun alectryon--available-text-modes ()
  "Filter supported text modes by availability."
  (let* ((available (cl-remove-if-not (lambda (entry) (fboundp (car entry))) alectryon-text-modes)))
    (mapcar (lambda (entry) (symbol-name (car entry))) available)))

(defun alectryon--read-text-mode ()
  "Ask the user which text mode to use."
  (intern
   (pcase-exhaustive (alectryon--available-text-modes)
     (`nil (error "No supported text mode found"))
     (`(,single) single)
     (choices (completing-read "Markup mode: " choices nil t)))))

(defun alectryon--ensure-text-mode-set ()
  "Ensure `alectryon-text-mode' is set, prompting if needed."
  (setq-local alectryon-text-mode
              (or alectryon-text-mode
                  (alectryon--guess-text-mode)
                  (alectryon--read-text-mode))))

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
      (unless (eql 0 ex)
        (error "Conversion error (%s) when running `%s':\n%s"
               ex (mapconcat #'shell-quote-argument (cons alectryon args) " ")
               (alectryon--buffer-string))))))

(defun alectryon--converter-args (&optional mode)
  "Compute conversion arguments to convert from MODE."
  `("--frontend" ,(alectryon--config-frontend mode)
    "--backend" ,(alectryon--config-backend mode)))

(defconst alectryon--point-marker "")

(defun alectryon--convert-from (mode)
  "Convert current buffer from MODE."
  (let* ((pt (point))
         (marker alectryon--point-marker)
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
        (replace-match "") ;; Avoid `delete-char'/`undo-auto-amalgamate'
      (message "Point marker missing from Alectryon's output.
Please open an issue at https://github.com/cpitclaudel/alectryon.")
      (goto-char (min pt (point-max))))))

(defvar alectryon--winding-down nil
  "Indicates whether we're in the process of disabling `alectryon-mode'.")

(defvar alectryon-mode)

(defun alectryon--set-mode (mode)
  "Switch to MODE.

Also enable `alectryon-mode' if `alectryon--winding-down' is nil."
  (alectryon--invoke mode)
  (unless (or alectryon--winding-down alectryon-mode)
    (alectryon-mode 1)))

(defun alectryon--toggle ()
  "Switch between code and markup views of the same file.

With REENABLE, turn `alectryon-mode' back on after switching major modes."
  (alectryon--record-mode)
  (alectryon--ensure-text-mode-set)
  (mapc #'funcall (alectryon--config :exit-hooks))
  (let ((modified (buffer-modified-p)))
    (alectryon--atomic
      (alectryon--convert-from major-mode)
      (push `(apply ,(apply-partially #'alectryon--set-mode major-mode))
            buffer-undo-list)
      (alectryon--set-mode (alectryon--mode-case alectryon-text-mode alectryon-prog-mode)))
    (set-buffer-modified-p modified)))

;;;###autoload
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
  :verify (lambda (_) (alectryon--flycheck-verify-enabled))
  :modes '(coq-mode rst-mode markdown-mode))

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

(defun alectryon--in-literate-comment-p (&optional ppss)
  "Check if PPSS is inside a literate comment.

Defaults to `syntax-ppss' if PPSS is nil."
  (setq ppss (or ppss (syntax-ppss)))
  (let* ((comment-opener-pos (nth 8 ppss)))
    (and comment-opener-pos
         (save-excursion
           (goto-char comment-opener-pos)
           (looking-at-p (car (alectryon--config :comment-delimiters-re 'prog)))))))

(defun alectryon--prog-syntactic-face-function (state)
  "Determine which face to use based on parsing state STATE."
  (when (alectryon--in-literate-comment-p state)
    'alectryon-comment))

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
      ((`(,open . ,close) (alectryon--config :comment-delimiters 'prog))
       (delim (if (alectryon--in-literate-comment-p)
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
    (cl-assert buffer-file-name)
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
    (visual-line-mode 1)
    (setq alectryon--prog-font-lock-keywords (alectryon--prog-font-lock-keywords))
    (font-lock-add-keywords nil alectryon--prog-font-lock-keywords)
    (make-local-variable 'font-lock-extra-managed-props)
    (cl-pushnew 'display font-lock-extra-managed-props)
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
   (setq alectryon-text-mode major-mode)))

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
    (add-hook 'flyspell-mode-hook #'alectryon--flyspell-hook nil t)
    (alectryon--flyspell-hook)
    (alectryon--mode-case (alectryon--prog-mode 1) (alectryon--text-mode 1)))
   (t
    (unless (alectryon--in-original-mode)
      (let ((alectryon--winding-down t))
        (alectryon--toggle))
      (message "Reverted to %s mode." mode-name))
    (remove-hook 'write-contents-functions #'alectryon--save t)
    (remove-hook 'flyspell-mode-hook #'alectryon--flyspell-hook t)
    (alectryon--flyspell-unhook)
    (alectryon--mode-case (alectryon--prog-mode -1) (alectryon--text-mode -1))))
  (alectryon--refontify))

;;;; Presentation mode

(defun alectryon--prog-presentation-font-lock-keywords ()
  "Compute `font-lock' keywords for Alectryon annotations in `prog-mode'."
  `((,(alectryon--config :annotations-re)
     0 '(face '(:height 0.5) display "👻") append)))

(defvar-local alectryon--prog-presentation-font-lock-keywords nil
  "Cache variable for `alectryon--prog-presentation-font-lock-keywords'.")

(define-minor-mode alectryon-presentation-mode
  "Hide Alectryon annotations in code files."
  :lighter ""
  (cond
   (alectryon-presentation-mode
    (unless alectryon--prog-mode
      (setq alectryon-presentation-mode nil)
      (user-error "`alectryon-presentation-mode' needs Alectryon in programming mode"))
    (setq alectryon--prog-presentation-font-lock-keywords (alectryon--prog-presentation-font-lock-keywords))
    (font-lock-add-keywords nil alectryon--prog-presentation-font-lock-keywords))
   (t
    (font-lock-remove-keywords nil alectryon--prog-presentation-font-lock-keywords)))
  (font-lock-flush))

;;;###autoload
(defun alectryon-mode-maybe-enable ()
  "Enable `alectryon-mode', except when winding down."
  (unless alectryon--winding-down
    (alectryon-mode 1)))

;;;###autoload
(add-hook 'coq-mode-hook #'alectryon-mode-maybe-enable t)

(provide 'alectryon)
;;; alectryon.el ends here
