(require 'package)
(setq package-archives '(("melpa" . "http://melpa.milkbox.net/packages/")
                         ("marmalade" . "http://marmalade-repo.org/packages/")
                         ("gnu" . "http://elpa.gnu.org/packages/")
                         ("org" . "http://orgmode.org/elpa/")))
(package-initialize)

;; cmd is meta, alt is alt
(setq mac-option-key-is-meta nil)
(setq mac-command-key-is-meta t)
(setq mac-command-modifier 'meta)
(setq mac-option-modifier nil)


(fset 'yes-or-no-p 'y-or-n-p) ;; enable y/n answers
(setq inhibit-startup-screen t) ;; disable GNU splash
(setq visible-bell nil) ;; disable visual alarm
;; Menlo (probably) only available on OS X
(set-face-attribute 'default nil :family "Menlo" :height 135)

;; indent with spaces instead of tabs
(setq indent-tabs-mode nil)

;; bind C-æ to comment-region
(global-set-key (kbd "C-æ") 'comment-region)

(if (not (package-installed-p 'use-package))
    (progn
      (package-install 'use-package)))

(require 'use-package)
;; auto install if package not present:
(setq use-package-always-ensure t)

;;;; usage of use-package see:
;; https://github.com/jwiegley/use-package/blob/master/README.md

(use-package better-defaults
  :bind ("C-x u" . undo-tree-visualize))

(use-package undo-tree)

(use-package magit
  :bind ("C-x g" . magit-status))

(use-package zenburn-theme
  :config
  (load-theme 'zenburn t t))

;; https://github.com/bbatsov/projectile
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
  :bind (("C-'" . avy-goto-char)
         ("C-ø" . avy-goto-char-2)
         ("M-g g" . avy-goto-line)
         ("M-g w" . avy-goto-word-1)
         ("M-g e" . avy-goto-word-0)))

;; https://github.com/abo-abo/ace-window
(use-package ace-window
  :bind ("C-o" . ace-window))

;; http://orgmode.org/manual/index.html
(use-package org-plus-contrib
  :pin org)

;; Language specific packages:
(use-package sml-mode
  :mode "\\.sml\\'"
  :interpreter "sml")

(use-package no-easy-keys
  :config
  (no-easy-keys 1))
