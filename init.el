(require 'package)

(unless (assoc-default "melpa" package-archives)
  (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
  (add-to-list 'package-archives '("org" . "http://orgmode.org/elpa/") t)
  )

  (package-initialize)

(unless (package-installed-p 'use-package)
  (progn
    (package-refresh-contents)
    (package-install 'use-package)))
(setq use-package-verbose t)
(require 'use-package)
(use-package auto-compile
  :ensure t
  :config (auto-compile-on-load-mode))
(setq load-prefer-newer t)
(setq use-package-always-ensure t)

;; https://github.com/jwiegley/use-package/blob/master/README.md
(eval-when-compile
  (require 'use-package))
(require 'diminish)                ;; if you use :diminish
(require 'bind-key)                ;; if you use any :bind variant

(use-package better-defaults)

(global-auto-revert-mode 1)
(diminish 'auto-revert-mode)

(set-terminal-coding-system 'utf-8)
(set-keyboard-coding-system 'utf-8)
(set-language-environment "UTF-8")
(prefer-coding-system 'utf-8)
(setq require-final-newline t)

;; stop opening new frames when visiting files
(setq ns-pop-up-frames nil)

;; cmd is meta, alt is alt
(setq mac-command-modifier 'meta)
(setq mac-option-modifier 'nil)

(setq mouse-wheel-scroll-amount '(1 ((shift) . 5)))

(setq-default ispell-program-name "aspell")
(fset 'yes-or-no-p 'y-or-n-p) ;; enable y/n answers
(setq inhibit-startup-screen t) ;; disable GNU splash
(setq visible-bell nil) ;; disable visual alarm
;; Menlo (probably) only available on OS X
(set-face-attribute 'default nil :family "Menlo" :height 135)
(set-face-attribute 'default nil :height 145)

;; indent with spaces instead of tabs
(setq-default indent-tabs-mode nil)
(defcustom indent-sensitive-modes
  '(python-mode)
  "Modes for which auto-indenting is suppressed."
  :type 'list)

;; http://timothypratley.blogspot.fr/2015/07/seven-specialty-emacs-settings-with-big.html
(defun save-all ()
  (interactive)
  (save-some-buffers t))
(add-hook 'focus-out-hook 'save-all)

;; bind C-æ to comment-region
(global-set-key (kbd "C-æ") 'comment-dwim)

;; make scroll-up/down preserve 18 lines instead of default 2
;; (setq next-screen-context-lines 18)

;; https://gist.github.com/johnmastro/508fb22a2b4e1ce754e0
(defun isearch-delete-something ()
  "Delete non-matching text or the last character."
  ;; Mostly copied from `isearch-del-char' and Drew's answer on the page above
  (interactive)
  (if (= 0 (length isearch-string))
      (ding)
    (setq isearch-string
          (substring isearch-string
                     0
                     (or (isearch-fail-pos) (1- (length isearch-string)))))
    (setq isearch-message
          (mapconcat #'isearch-text-char-description isearch-string "")))
  (if isearch-other-end (goto-char isearch-other-end))
  (isearch-search)
  (isearch-push-state)
  (isearch-update))

(define-key isearch-mode-map (kbd "<backspace>")
  #'isearch-delete-something)

(use-package undo-tree
  :bind ("C-x u" . undo-tree-visualize))

(use-package hydra
  :bind
  ("C-x o" . hydra-window)
  :config
  (global-set-key
 (kbd "C-n")
 (defhydra hydra-move
   (:body-pre (next-line))
   "move"
   ("n" next-line)
   ("p" previous-line)
   ("f" forward-char)
   ("b" backward-char)
   ("a" beginning-of-line)
   ("e" move-end-of-line)
   ("v" scroll-up-command)
   ;; Converting M-v to V here by analogy.
   ("V" scroll-down-command)
   ("l" recenter-top-bottom)))
  (defhydra hydra-page (ctl-x-map "" :pre (widen))
  "page"
  ("]" forward-page "next")
  ("[" backward-page "prev")
  ("n" narrow-to-page "narrow" :bind nil :exit t))
)

;; https://github.com/magit/magit
(use-package magit
  :bind ("C-x g" . magit-status))

;; (use-package powerline
;;   :config
;;    (powerline-default-theme)
;;   )

;; (use-package smart-mode-line
;;   :config
;;   (sml/setup)
;;   )

;; (use-package spaceline
;;   :config
;;   (require 'spaceline-config)
;;   (spaceline-emacs-theme)
;;   )

;; (use-package moe-theme
;;   :config
;;   ;; Resize titles (optional).
;;   ;; (setq moe-theme-resize-markdown-title '(1.5 1.4 1.3 1.2 1.0 1.0))
;;   ;; (setq moe-theme-resize-org-title '(1.5 1.4 1.3 1.2 1.1 1.0 1.0 1.0 1.0))
;;   ;; (setq moe-theme-resize-rst-title '(1.5 1.4 1.3 1.2 1.1 1.0))
;;   ;; Choose a color for mode-line.(Default: blue)
;;   ;; (moe-theme-set-color 'blue)
;;   ;; (powerline-moe-theme)
;;   (moe-dark)
;;   )

(use-package color-theme-sanityinc-tomorrow
  :config
  (load-theme 'sanityinc-tomorrow-night t))

;; (use-package solarized-theme
;;   :config
;;   ;; make the modeline high contrast
;;   (setq solarized-high-contrast-mode-line t)
;;   (load-theme 'solarized-light t))

;; (use-package leuven-theme
;;   :config
;;   (load-theme 'leuven t)
;; )


(use-package material-theme
  :config
  (load-theme 'material t))

;; https://github.com/purcell/exec-path-from-shell
(use-package exec-path-from-shell
  :config
  (exec-path-from-shell-initialize))

;; https://github.com/nonsequitur/smex
(use-package smex
  :config (smex-initialize)
  :bind (("M-x" . smex)
         ("M-X" . smex-major-mode-commands)))

;; http://company-mode.github.io/
(use-package company
  :init
  ;; https://github.com/company-mode/company-mode/issues/50#issuecomment-33338334
  (defun add-pcomplete-to-capf ()
    (add-hook 'completion-at-point-functions 'pcomplete-completions-at-point nil t))
  :config
  (setq company-idle-delay 0.6)
  (setq company-minimum-prefix-length 4)
  (bind-key "C-n" 'company-select-next company-active-map)
  (bind-key "C-p" 'company-select-previous company-active-map)
  (bind-key "M-p" 'company-complete)
  (global-company-mode))

;;;; https://github.com/bbatsov/projectile
;; (use-package projectile
;;   :config
;;   (projectile-global-mode t))

(use-package speed-type)

(use-package expand-region
  :bind
  ("M-2" . er/expand-region))

(use-package multiple-cursors
  :bind
  ("C->" . mc/mark-next-like-this)
  ("C-<" . mc/mark-previous-like-this)
  ("C-c C-<" . mc/mark-all-like-this)
)

;; https://github.com/leoliu/easy-kill
(use-package easy-kill
  :config
  (global-set-key [remap kill-ring-save] 'easy-kill)
  (global-set-key [remap mark-sexp] 'easy-mark))

(use-package smart-region
  :config
  (global-set-key [remap set-mark-command] 'smart-region))

;; https://github.com/chrisdone/god-mode
;; (use-package god-mode
;;   :config
;;   (global-set-key (kbd "<escape>") 'god-mode-all)
;;   (defun my-update-cursor ()
;;   (setq cursor-type (if (or god-local-mode buffer-read-only)
;;                         'box
;;                       'bar)))
;;   (add-hook 'god-mode-enabled-hook 'my-update-cursor)
;;   (add-hook 'god-mode-disabled-hook 'my-update-cursor)
;;   )

;; https://github.com/justbur/emacs-which-key
(use-package which-key
  :diminish ""
  :config
  (which-key-mode)
  (which-key-setup-minibuffer)
;  (which-key-setup-side-window-right-bottom)
  (setq which-key-idle-delay 1)
  (setq which-key-special-keys nil)
  )

;; https://github.com/jaypei/emacs-neotree
(use-package neotree
  :bind ("C-å" . neotree-toggle))

;; https://github.com/abo-abo/avy
(use-package avy
  :bind (("C-M-å"   . avy-goto-char-2)
         ("C-ø"     . avy-goto-char)
         ("M-g M-g" . avy-goto-line)
         ("M-s"   . avy-goto-word-1)
         ("M-g e"   . avy-goto-word-0)
         ("C-M-ø"   . avy-goto-char-timer))
  :config
  (setq avy-timeout-seconds 0.3)
  (setq avy-all-windows nil)
  (setq avy-keys
      '(?c ?a ?s ?d ?e ?f ?h ?w ?y ?j ?k ?l ?n ?m ?v ?r ?u ?p))
  )

(use-package zzz-to-char
  :bind ("M-z" . zzz-to-char)
  )

;; https://github.com/abo-abo/ace-window
(use-package ace-window
  :bind ("C-o" . ace-window)
  :config
  (setq aw-keys '(?a ?s ?d ?f ?g ?h ?j ?k ?l))
  (setq aw-scope 'frame)
  (setq aw-dispatch-always t))

(use-package auctex
  :mode (("\\.tex$" . TeX-Latex-mode))
  :config
  (progn
    (setq TeX-auto-save t)
    (setq TeX-parse-self t)
    (setq TeX-save-query nil)
    ))

(use-package cdlatex
  :config
  (add-hook 'LaTeX-mode-hook 'turn-on-cdlatex)   ; with AUCTeX LaTeX mode
  (setq cdlatex-command-alist
        '(("tx" "Insert \\text{}" "\\text{?}" cdlatex-position-cursor nil nil t)
          ("bb" "Insert \\mathbb{}" "\\mathbb{?}" cdlatex-position-cursor nil nil t)
          ("lm" "Insert \\lim_{}" "\\lim_{?}" cdlatex-position-cursor nil nil t)
          ("dm" "Insert display math equation" "\\[\n?\n\\]" cdlatex-position-cursor nil t nil)
          ("equ*" "Insert equation* environment" "\\begin{equation*}\n?\n\\end{equation*}" cdlatex-position-cursor nil t nil)
          )
        )
  )

;; http://orgmode.org/manual/index.html
(use-package org
  :diminish visual-line-mode org-cdlatex-mode smartparens-mode company-mode
  :ensure org-plus-contrib
  :mode (("\\.\\(org\\|org_archive\\|txt\\)$" . org-mode))
  :bind (("C-c c" . org-capture)
         ("C-c l" . org-store-link)
         ("C-c a" . org-agenda)
         ("C-c b" . org-iswitchb)
         ("C-'"   . org-cycle-agenda-files)
         ("<f8>" . org-toggle-latex-fragment)
         )
  :config
  (add-hook 'org-mode-hook 'turn-on-org-cdlatex)
  (add-hook 'org-mode-hook 'visual-line-mode)
  (add-hook 'org-mode-hook #'add-pcomplete-to-capf)
  (add-hook 'org-mode-hook (lambda () (diminish 'org-indent-mode)))
  (plist-put org-format-latex-options :scale 1.8)
  ;; (setq org-fontify-whole-heading-line t)
  (defun my/org-use-speed-commands-for-headings-and-lists ()
  "Activate speed commands on list items too."
  (and
   (not (org-inside-LaTeX-fragment-p))  ; ignore lines starting with minus in latex-fragments
   (or (and (looking-at org-outline-regexp) (looking-back "^\**"))
      (save-excursion (and (looking-at (org-item-re)) (looking-back "^[ \t]*"))))))
  (setq org-use-speed-commands 'my/org-use-speed-commands-for-headings-and-lists)
  (add-to-list 'org-speed-commands-user '("w" widen))
  (setq org-default-notes-file "~/Notes/refile.org")
  (setq org-agenda-files (list "~/Notes/cs.org" "~/Notes/personal.org"))
  (setq org-deadline-warning-days 7)
  (setq org-confirm-babel-evaluate nil)
  (setq org-export-backends '(ascii beamer html icalendar latex md org))
  (setq org-startup-indented t)
  (setq org-agenda-todo-ignore-deadlines t)
  (setq org-agenda-todo-ignore-scheduled t)
  (setq org-babel-results-keyword "results")
  (org-babel-do-load-languages
        'org-babel-load-languages
        '((calc . t)
          (dot . t)
          (ditaa . t)
          (sh . t)
          (shell . t)
          (latex . t)))
  (add-to-list 'org-src-lang-modes '("dot" . graphviz-dot))
  (server-start)
  (add-to-list 'load-path "~/path/to/org/protocol/")
  (require 'org-protocol)
  )

(use-package ido-describe-bindings
  :config
  (define-key help-map (kbd "b") 'ido-describe-bindings)
  )

(use-package visual-regexp
  :bind
  (("C-c r" . vr/replace)
   ("C-c q" . vr/query-replace))
  )

(use-package buffer-move
  :config
  (global-set-key (kbd "<C-M-up>")     'buf-move-up)
  (global-set-key (kbd "<C-M-down>")   'buf-move-down)
  (global-set-key (kbd "<C-M-left>")   'buf-move-left)
  (global-set-key (kbd "<C-M-right>")  'buf-move-right))

(use-package golden-ratio-scroll-screen
  :config
  (global-set-key [remap scroll-down-command] 'golden-ratio-scroll-screen-down)
  (global-set-key [remap scroll-up-command] 'golden-ratio-scroll-screen-up))

(use-package whitespace-cleanup-mode
  :config
  (global-whitespace-cleanup-mode))

(use-package smartparens
  :config
  (smartparens-global-mode 1)
  )

(use-package markdown-mode
  :mode "\\.md'")

(use-package sicp)

;; (use-package rainbow-delimiters
;;   :config
;;   (add-hook 'prog-mode-hook 'rainbow-delimiters-mode))

;;;;;;;
;; Language specific packages:
;;;;;;;
(use-package sml-mode
  :mode "\\.sml\\'"
  :interpreter "sml")


(defun fd-switch-dictionary()
  (interactive)
  (let* ((dic ispell-current-dictionary)
         (change (if (string= dic "dansk") "english" "english")))
    (ispell-change-dictionary change)
    (message "Dictionary switched from %s to %s" dic change)
    ))
(global-set-key (kbd "<f9>")   'fd-switch-dictionary)

(define-key ctl-x-map "\C-i"
  #'endless/ispell-word-then-abbrev)

(defun endless/ispell-word-then-abbrev (p)
  "Call `ispell-word', then create an abbrev for it.
With prefix P, create local abbrev. Otherwise it will
be global.
If there's nothing wrong with the word at point, keep
looking for a typo until the beginning of buffer. You can
skip typos you don't want to fix with `SPC', and you can
abort completely with `C-g'."
  (interactive "P")
  (let (bef aft)
    (save-excursion
      (while (if (setq bef (thing-at-point 'word))
                 ;; Word was corrected or used quit.
                 (if (ispell-word nil 'quiet)
                     nil ; End the loop.
                   ;; Also end if we reach `bob'.
                   (not (bobp)))
               ;; If there's no word at point, keep looking
               ;; until `bob'.
               (not (bobp)))
        (backward-word))
      (setq aft (thing-at-point 'word)))
    (if (and aft bef (not (equal aft bef)))
        (let ((aft (downcase aft))
              (bef (downcase bef)))
          (define-abbrev
            (if p local-abbrev-table global-abbrev-table)
            bef aft)
          (message "\"%s\" now expands to \"%s\" %sally"
                   bef aft (if p "loc" "glob")))
      (user-error "No typo at or before point"))))

(setq save-abbrevs 'silently)
(setq-default abbrev-mode t)
