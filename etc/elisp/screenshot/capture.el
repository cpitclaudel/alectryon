;;; capture.el --- Make a screenshot of alectryon-mode  -*- lexical-binding: t; -*-
;; Run with (cd ..; cask exec emacs -Q -l screenshot/capture.el)

(require 'proof-general)
(require 'company-coq)
(require 'adaptive-wrap)

(defvar ~/fringe-width 8)

(defconst ~/script-full-path
  (or (and load-in-progress load-file-name)
      (bound-and-true-p byte-compile-current-file)
      (buffer-file-name))
  "Full path of this script.")

(defconst ~/directory
  (file-name-directory ~/script-full-path)
  "Full path to directory of this script.")

(defun ~/prepare ()
  (ido-mode)
  (tool-bar-mode -1)
  (menu-bar-mode -1)
  (scroll-bar-mode -1)
  (column-number-mode)
  (fringe-mode (cons ~/fringe-width ~/fringe-width))
  (blink-cursor-mode -1)
  (setq-default cursor-type 'bar
                x-gtk-use-system-tooltips nil
                tooltip-delay 0.01)
  (load-theme 'tango t)
  (set-face-attribute 'match nil :background "yellow1")
  (set-face-attribute 'default nil :family "Iosevka" :height 90)
  (set-face-attribute 'mode-line nil :foreground "gray60" :background "black")
  (set-face-attribute 'mode-line-inactive nil :foreground "gray60" :background "#404045")
  (set-face-attribute 'mode-line-buffer-id nil :foreground "#eab700")
  (set-fontset-font t 'unicode "Iosevka")
  (set-fontset-font t 'unicode "XITS Math Monospacified for Ubuntu Mono" nil 'append)
  (set-fontset-font t 'unicode "Noto Color Emoji" nil 'append)
  (setq-default proof-splash-enable nil)
  (setq-default split-height-threshold nil)
  (setq-default split-width-threshold 0)
  (setq-default frame-title-format "Alectryon | Logical foundations, Chapter “ProofObjects”")
  (setq-default company-coq-disabled-features '(hello))
  (setq-default header-line-format
                (propertize " " 'display '(space :align-to (+ right right-fringe))
                            'face '((:height 50) fringe)))
  (add-hook 'rst-mode-hook 'alectryon-mode)
  (add-hook 'coq-mode-hook 'company-coq-mode)
  (add-hook 'prog-mode-hook 'adaptive-wrap-prefix-mode)
  (add-hook 'text-mode-hook 'visual-line-mode)
  (redisplay t))

(defun ~/capture ()
  (package-initialize)
  (~/prepare)
  (setq debug-on-error t)
  (add-to-list 'load-path ~/directory)
  (require 'alectryon (expand-file-name "../alectryon.el" ~/directory))
  (set-frame-size nil 109 57)
  (let* ((fname (expand-file-name "example.v" ~/directory))
         (coq-buf (get-buffer-create "example.v/Coq"))
         (rst-buf (find-file fname)))
    (rename-buffer "example.v/reST")
    (split-window-sensibly)
    (with-current-buffer coq-buf
      (coq-mode)
      (setq buffer-file-name fname)
      (save-excursion (insert-buffer-substring rst-buf))
      (set-buffer-modified-p nil)
      (pop-to-buffer-same-window (current-buffer))
      (search-forward "Conjunction")
      (beginning-of-line)
      (recenter 0 t)
      (search-forward "split.")
      (proof-init-segmentation)
      (proof-set-locked-endpoints (point-min) (point))
      (flycheck-buffer))
    (alectryon-toggle)
    (with-selected-window (get-buffer-window rst-buf)
      (search-forward "split."))
    (flycheck-buffer)
    (add-hook 'flycheck-after-syntax-check-hook
              (lambda ()
                (when (and (buffer-local-value 'flycheck-current-errors coq-buf)
                           (buffer-local-value 'flycheck-current-errors rst-buf))
                  (redisplay t)
                  (~/export))))))

(defun ~/export ()
  (dolist (type '(svg png))
    (message nil)
    (with-temp-buffer
      (insert (x-export-frames nil type))
      (write-region (point-min) (point-max)
                    (expand-file-name (format "alectryon.%S" type)
                                      ~/directory))))
  (process-lines "optipng" (expand-file-name "alectryon.png" ~/directory))
  (kill-emacs))

(run-with-idle-timer 0 nil #'~/capture)
