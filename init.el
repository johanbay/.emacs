(require 'package)

(unless (assoc-default "melpa" package-archives)
  (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
  (add-to-list 'package-archives '("org" . "http://orgmode.org/elpa/") t))

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

;; Override buffer choice
(global-set-key (kbd "C-x k") 'kill-this-buffer)

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
;; (defun isearch-delete-something ()
;;   "Delete non-matching text or the last character."
;;   ;; Mostly copied from `isearch-del-char' and Drew's answer on the page above
;;   (interactive)
;;   (if (= 0 (length isearch-string))
;;       (ding)
;;     (setq isearch-string
;;           (substring isearch-string
;;                      0
;;                      (or (isearch-fail-pos) (1- (length isearch-string)))))
;;     (setq isearch-message
;;           (mapconcat #'isearch-text-char-description isearch-string "")))
;;   (if isearch-other-end (goto-char isearch-other-end))
;;   (isearch-search)
;;   (isearch-push-state)
;;   (isearch-update))

;; (define-key isearch-mode-map (kbd "<backspace>")
;;   #'isearch-delete-something)

(use-package keyfreq
  :config
  (keyfreq-mode 1)
  (keyfreq-autosave-mode 1))

(use-package undo-tree
  :bind ("C-x u" . undo-tree-visualize))

(use-package transpose-frame)

(use-package winner
  :config
  (winner-mode 1))

(use-package discover-my-major
  :bind ("C-h C-m" . discover-my-major))

(use-package popwin
  :ensure t
  :config
  (add-to-list 'popwin:special-display-config `("*Swoop*" :height 0.5 :position bottom))
  (add-to-list 'popwin:special-display-config `("*Warnings*" :height 0.5 :noselect t))
  (add-to-list 'popwin:special-display-config `("*Procces List*" :height 0.5))
  (add-to-list 'popwin:special-display-config `("*Messages*" :height 0.5 :noselect t))
  (add-to-list 'popwin:special-display-config `("*Backtrace*" :height 0.5))
  (add-to-list 'popwin:special-display-config `("*Compile-Log*" :height 0.5 :noselect t))
  (add-to-list 'popwin:special-display-config `("*Remember*" :height 0.5))
  (add-to-list 'popwin:special-display-config `("*All*" :height 0.5))
  (add-to-list 'popwin:special-display-config `("*Go Test*" :height 0.3))
  (add-to-list 'popwin:special-display-config `(flycheck-error-list-mode :height 0.5 :regexp t :position bottom))
  (popwin-mode 1)
  (global-set-key (kbd "C-z") popwin:keymap))


;; stolen from https://github.com/vdemeester/emacs-config
(defun my/switch-to-previous-buffer ()
  "Switch to previously open buffer.
Repeated invocations toggle between the two most recently open buffers."
  (interactive)
  (switch-to-buffer (other-buffer (current-buffer) 1)))

(use-package key-chord
  :config 
  (setq key-chord-one-key-delay 0.26)
  (key-chord-mode 1)
  ;; k can be bound too
  (key-chord-define-global "uu"     'undo)
  (key-chord-define-global "jw"     'ace-window)
  (key-chord-define-global "jj" 'avy-goto-word-1)
  (key-chord-define-global "jl" 'avy-goto-line)
  (key-chord-define-global "jk" 'avy-goto-char)   
  ;; commands
  (key-chord-define-global "FF"     'find-file)
  (key-chord-define-global "xb"     'ido-switch-buffer)
  (key-chord-define-global "xo"     'hydra-window//body)
  (key-chord-define-global "xx"     'er/expand-region)
  (key-chord-define-global "JJ"     'my/switch-to-previous-buffer)
  )

(use-package hydra
  :bind
  (("C-n" . hydra-move/body)
   ("C-x o" . hydra-window/body)
   ("C-¨" . hydra-multiple-cursors/body)
   ("C-c C-v" . hydra-toggle-simple/body)
   ("C-x SPC" . hydra-rectangle/body)
   )
  :config
  (require 'hydra-examples)

  (defhydra hydra-rectangle (:body-pre (rectangle-mark-mode 1)
                                       :color pink
                                       :post (deactivate-mark))
    "
  ^_k_^     _d_elete    _s_tring
_h_   _l_   _o_k        _y_ank  
  ^_j_^     _n_ew-copy  _r_eset 
^^^^        _e_xchange  _u_ndo  
^^^^        ^ ^         _p_aste
"
    ("h" backward-char nil)
    ("l" forward-char nil)
    ("k" previous-line nil)
    ("j" next-line nil)
    ("e" exchange-point-and-mark nil)
    ("n" copy-rectangle-as-kill nil)
    ("d" delete-rectangle nil)
    ("r" (if (region-active-p)
             (deactivate-mark)
           (rectangle-mark-mode 1)) nil)
    ("y" yank-rectangle nil)
    ("u" undo nil)
    ("s" string-rectangle nil)
    ("p" kill-rectangle nil)
    ("o" nil nil))
  
  (defhydra hydra-toggle-simple (:color blue)
    "toggle"
    ("a" abbrev-mode "abbrev")
    ("d" toggle-debug-on-error "debug")
    ("f" auto-fill-mode "fill")
    ("t" toggle-truncate-lines "truncate")
    ("w" whitespace-mode "whitespace")
    ("q" nil "cancel"))
  
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
    ("l" recenter-top-bottom))
  
  (defhydra hydra-window (:color red
                                 :hint nil)
    "
 Split: _v_ert  _x_:horz
Delete: _o_nly  _da_ce  _dw_indow  _db_uffer  _df_rame
  Move: _s_wap  _t_ranspose  _b_uffer
Frames: _f_rame new  _df_ delete
Resize: _h_:left  _j_:down  _k_:up  _l_:right
  Misc: _a_ce  a_c_e  _u_ndo  _r_edo"
    ;; ("h" windmove-left)
    ;; ("j" windmove-down)
    ;; ("k" windmove-up)
    ;; ("l" windmove-right)
    ("h" hydra-move-splitter-left)
    ("j" hydra-move-splitter-down)
    ("k" hydra-move-splitter-up)
    ("l" hydra-move-splitter-right)
    ("|" (lambda ()
           (interactive)
           (split-window-right)
           (windmove-right)))
    ("_" (lambda ()
           (interactive)
           (split-window-below)
           (windmove-down)))
    ("v" split-window-right)
    ("x" split-window-below)
    ("t" transpose-frame)
    ;; winner-mode must be enabled
    ("u" winner-undo)
    ("r" winner-redo) ;;Fixme, not working?
    ("o" delete-other-windows :exit t)
    ("a" ace-window :exit t)
    ("c" ace-window)
    ("f" new-frame :exit t)
    ("s" ace-swap-window)
    ("b" ivy-switch-buffer)
    ("da" ace-delete-window)
    ("dw" delete-window)
    ("db" kill-this-buffer)
    ("df" delete-frame :exit t)
    ("q" nil)
                                        ;("i" ace-maximize-window "ace-one" :color blue)
                                        ;("b" ido-switch-buffer "buf")
                                        ;("m" headlong-bookmark-jump)
    )
  
  (defhydra hydra-multiple-cursors (:hint nil)
    "
     ^Up^            ^Down^        ^Other^
----------------------------------------------
[_p_]   Next    [_n_]   Next    [_l_] Edit lines
[_P_]   Skip    [_N_]   Skip    [_a_] Mark all
[_M-p_] Unmark  [_M-n_] Unmark  [_r_] Mark by regexp
^ ^             ^ ^             [_q_] Quit
"
  ("l" mc/edit-lines :exit t)
  ("a" mc/mark-all-like-this :exit t)
  ("n" mc/mark-next-like-this)
  ("N" mc/skip-to-next-like-this)
  ("M-n" mc/unmark-next-like-this)
  ("p" mc/mark-previous-like-this)
  ("P" mc/skip-to-previous-like-this)
  ("M-p" mc/unmark-previous-like-this)
  ("r" mc/mark-all-in-region-regexp :exit t)
  ("q" nil))


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

(use-package moe-theme
  :config
  ;; Resize titles (optional).
  ;; (setq moe-theme-resize-markdown-title '(1.5 1.4 1.3 1.2 1.0 1.0))
  ;; (setq moe-theme-resize-org-title '(1.5 1.4 1.3 1.2 1.1 1.0 1.0 1.0 1.0))
  ;; (setq moe-theme-resize-rst-title '(1.5 1.4 1.3 1.2 1.1 1.0))
  ;; Choose a color for mode-line.(Default: blue)
  ;; (moe-theme-set-color 'blue)
  ;; (powerline-moe-theme)
  (moe-dark)
  )

;; (use-package color-theme-sanityinc-tomorrow
;;   :config
;;   (load-theme 'sanityinc-tomorrow-night t))

;; (use-package solarized-theme
;;   :config
;;   ;; make the modeline high contrast
;;   (setq solarized-high-contrast-mode-line t)
;;   (load-theme 'solarized-light t))

;; (use-package leuven-theme
;;   :config
;;   (load-theme 'leuven t)
;; )

;; (use-package material-theme
;;   :config
;;   (load-theme 'material t))

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
  :diminish ""
  :init
  ;; https://github.com/company-mode/company-mode/issues/50#issuecomment-33338334
  (defun add-pcomplete-to-capf ()
    (add-hook 'completion-at-point-functions 'pcomplete-completions-at-point nil t))
  :config
  (use-package company-quickhelp
    :config
    (company-quickhelp-mode 1))
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
  :bind ("C-c C-t" . neotree-toggle))

(use-package browse-kill-ring
  :config
  (browse-kill-ring-default-keybindings))

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

(use-package ace-link
  :config
  (ace-link-setup-default)
  )

(use-package avy-zap
  :bind (
         ("M-z" . avy-zap-to-char-dwim)
         ("M-Z" . avy-zap-up-to-char-dwim))
  )

(use-package ace-popup-menu
  :config
  (ace-popup-menu-mode 1))

;; https://github.com/abo-abo/ace-window
(use-package ace-window
  :bind ("C-o" . ace-window)
  :config
  (setq aw-keys '(?a ?s ?d ?f ?g ?h ?j ?k ?l))
  (setq aw-scope 'frame)
  )

(use-package ace-flyspell
  :config
  (ace-flyspell-setup))

(use-package tex
  :ensure auctex
  :mode ("\\.tex\\'" . TeX-latex-mode)
  :config
  (setq TeX-auto-save t)
  (setq TeX-parse-self t)
  (setq TeX-save-query nil)
  )

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
  :diminish visual-line-mode org-cdlatex-mode
  :ensure org-plus-contrib
  :mode (("\\.\\(org\\|org_archive\\|txt\\)$" . org-mode))
  :bind (("C-c c" . org-capture)
         ("C-c l" . org-store-link)
         ("C-c a" . org-agenda)
         ("C-c b" . org-iswitchb)
         ("C-å"   . org-cycle-agenda-files)
         ("<f8>" . org-toggle-latex-fragment)
         )
  :config
  (define-key org-mode-map (kbd "M-o") 'ace-link-org)
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

(use-package swiper
  :diminish 'ivy-mode
  :ensure counsel
  :config
  (ivy-mode 1)
  (setq ivy-use-virtual-buffers t)
  (global-set-key (kbd "C-s") 'swiper)
  (global-set-key (kbd "M-x") 'counsel-M-x)
  (global-set-key (kbd "C-x C-f") 'counsel-find-file)
  (global-set-key (kbd "<f1> f") 'counsel-describe-function)
  (global-set-key (kbd "<f1> v") 'counsel-describe-variable)
  (global-set-key (kbd "<f1> l") 'counsel-load-library)
  (global-set-key (kbd "<f2> i") 'counsel-info-lookup-symbol)
  (global-set-key (kbd "<f2> u") 'counsel-unicode-char)
  (global-set-key (kbd "C-r") 'ivy-resume))

(use-package visual-regexp
  :bind
  (("C-c r" . vr/replace)
   ("C-c q" . vr/query-replace))
  )

(use-package golden-ratio-scroll-screen
  :config
  (global-set-key [remap scroll-down-command] 'golden-ratio-scroll-screen-down)
  (global-set-key [remap scroll-up-command] 'golden-ratio-scroll-screen-up))

(use-package whitespace-cleanup-mode
  :diminish 'whitespace-cleanup-mode
  :config
  (global-whitespace-cleanup-mode))

(use-package smartparens
  :diminish ""
  :config
  (smartparens-global-mode 1)
  )

(use-package abbrev
  :ensure nil
  :diminish abbrev-mode
  :config
  (if (file-exists-p abbrev-file-name)
      (quietly-read-abbrev-file)))

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
         (change (if (string= dic "english") "dansk" "english")))
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
