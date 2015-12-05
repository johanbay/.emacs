(require 'package)

(add-to-list 'package-archives '("org" . "http://orgmode.org/elpa/") t)

(unless (assoc-default "melpa" package-archives)
  (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
  (package-refresh-contents))

(package-initialize)

;; cmd is meta, alt is alt
;; (setq mac-option-key-is-meta nil)
;; (setq mac-command-key-is-meta t)
(setq mac-command-modifier 'meta)
(setq mac-option-modifier nil)

(setenv "PATH" (concat (getenv "PATH") ":/usr/local/bin"))
(setq exec-path (append exec-path '("/usr/local/bin")))

(setq-default ispell-program-name "aspell")

(fset 'yes-or-no-p 'y-or-n-p) ;; enable y/n answers
(setq inhibit-startup-screen t) ;; disable GNU splash
(setq visible-bell nil) ;; disable visual alarm
;; Menlo (probably) only available on OS X
; (set-face-attribute 'default nil :family "Menlo" :height 135)
(set-face-attribute 'default nil :height 135)

;; indent with spaces instead of tabs
(setq indent-tabs-mode nil)

;; bind C-æ to comment-region
(global-set-key (kbd "C-æ") 'comment-dwim)

(unless (package-installed-p 'use-package)
  (package-refresh-contents)
  (package-install 'use-package))

(require 'use-package)
;; auto install if package not present:
(setq use-package-always-ensure t)

;;;; usage of use-package see:
;; https://github.com/jwiegley/use-package/blob/master/README.md

(use-package better-defaults
  :bind ("C-x u" . undo-tree-visualize))

(use-package undo-tree)

;; https://github.com/magit/magit
(use-package magit
  :bind ("C-x g" . magit-status))

(use-package powerline)

(use-package moe-theme
  :ensure powerline
  :config
  (moe-dark)
  (powerline-moe-theme))

;; https://github.com/nonsequitur/smex
(use-package smex
  :config (smex-initialize)
  :bind (("M-x" . smex)
         ("M-X" . smex-major-mode-commands)))

;; http://company-mode.github.io/
(use-package company
  :config (progn (setq company-idle-delay .2)
                 (bind-key "C-n" 'company-select-next company-active-map)
                 (bind-key "C-p" 'company-select-previous company-active-map)
                 (global-company-mode)))

;;;; https://github.com/bbatsov/projectile
;; (use-package projectile
;;   :config
;;   (projectile-global-mode t))

;; https://github.com/leoliu/easy-kill
(use-package easy-kill
  :config
  (global-set-key [remap kill-ring-save] 'easy-kill)
  (global-set-key [remap mark-sexp] 'easy-mark))

;; https://github.com/abo-abo/avy
(use-package avy
  :bind (("C-å" . avy-goto-char)
         ("C-ø" . avy-goto-char-2)
         ("M-g M-g" . avy-goto-line)
         ("M-g w" . avy-goto-word-1)
         ("M-g e" . avy-goto-word-0)
         ("C-M-ø" . avy-goto-char-timer))
  :config
  (setq avy-timeout-seconds 0.3))

;; https://github.com/abo-abo/ace-window
(use-package ace-window
  :bind ("C-o" . ace-window))

;; http://orgmode.org/manual/index.html
(use-package org
  :mode (("\\.org$" . org-mode))
  :ensure org-plus-contrib
  :config
  (progn
    (global-set-key "\C-cl" 'org-store-link)
     (global-set-key "\C-ca" 'org-agenda)
     (global-set-key "\C-cc" 'org-capture)
     (global-set-key "\C-cb" 'org-iswitchb)
    ))

(use-package no-easy-keys
  :config
  (no-easy-keys 1))

(use-package paredit)
;; (use-package rainbow-delimiters         
;;   :config
;;   (add-hook 'prog-mode-hook 'rainbow-delimiters-mode))

;;;;;;;
;; Language specific packages:
;;;;;;;
(add-to-list 'load-path "~/.emacs.d/lang-support/")
(use-package sml-mode
  :mode "\\.sml\\'"
  :interpreter "sml")

(load-library "clojure")

;; https://github.com/clojure-emacs/squiggly-clojure
(use-package flycheck
  :ensure t
  :config
  (progn (use-package flycheck-clojure ; load clojure specific flycheck features
           :ensure t
           :config (flycheck-clojure-setup))
         ;; initialize flycheck
         (use-package popup
           :ensure t)
         (use-package flycheck-pos-tip
           :ensure t)
         (setq flycheck-display-errors-function 'flycheck-pos-tip-error-messages)
         (global-flycheck-mode)))
