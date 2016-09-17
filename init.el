(require 'package)

(unless (assoc-default "melpa" package-archives)
  (add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
  (add-to-list 'package-archives '("org" . "http://orgmode.org/elpa/") t))

(package-initialize)

(unless (package-installed-p 'use-package)
  (progn
    (package-refresh-contents)
    (package-install 'use-package)))

(add-to-list 'load-path "~/.emacs.d/etc/")

;; https://github.com/jwiegley/use-package/blob/master/README.md
(eval-when-compile
  (require 'use-package))
(require 'diminish)                ;; if you use :diminish
(require 'bind-key)                ;; if you use any :bind variant

(setq use-package-always-ensure t)

(add-to-list 'default-frame-alist '(height . 47))
(add-to-list 'default-frame-alist '(width . 110))

(setq cursor-type 'bar)
(setq blink-cursor nil)
(setq scroll-bar-mode nil)
(setq display-battery-mode 1
      display-time 1
      display-time-24hr-format t
      display-time-day-and-date t)
(setq battery−mode−line−format " [%L %p%% %dC]")

(setq ring-bell-function 'ignore)
(setq inhibit-startup-screen t)
(tool-bar-mode -1)
(add-hook 'prog-mode-hook 'linum-mode)

(setq
 scroll-margin 3
 scroll-conservatively 30
 scroll-preserve-screen-position 1
 )

(fset 'yes-or-no-p 'y-or-n-p)

(show-paren-mode 1)
(require 'saveplace)
(setq-default save-place t)

(setq
 x-select-enable-clipboard t
 x-select-enable-primary t
 save-place-file (concat user-emacs-directory "places")
 backup-directory-alist `(("." . ,(concat user-emacs-directory
                                          "backups"))))

(require 'uniquify)
(setq uniquify-buffer-name-style 'forward)

(set-terminal-coding-system 'utf-8)
(set-keyboard-coding-system 'utf-8)
(set-language-environment "UTF-8")
(prefer-coding-system 'utf-8)

;; mode line stuff:
(line-number-mode t)
(column-number-mode t)
(size-indication-mode t)

;; stop opening new frames when visiting files
(setq ns-pop-up-frames nil)

;; cmd is meta, alt is alt
(setq mac-command-modifier 'meta)
(setq mac-option-modifier 'nil)

;; use spotlight for 'locate'
(setq locate-command "mdfind")

(setq mouse-wheel-scroll-amount '(1 ((shift) . 5)))

(setq-default ispell-program-name "hunspell")
(setq ispell-dictionary "english")
(setq ispell-really-hunspell t)
(setq ispell-dictionary-alist
      '((nil				; default
         "[A-Za-z]" "[^A-Za-z]" "[']"
         t ("-d" "en_GB") nil utf-8)
        ("english"
         "[A-Za-z]" "[^A-Za-z]" "[']"
         t ("-d" "en_GB") nil utf-8)
        ("american"
         "[A-Za-z]" "[^A-Za-z]" "[']"
         t ("-d" "en_US") nil utf-8)
        ("dansk"
         "[A-Za-zÆØÅæøå]" "[^A-Za-zÆØÅæøå]" "[\"]" nil
         ("-d" "da_DK") "~list" utf-8)))

;; Menlo (probably) only available on OS X
;; (set-face-attribute 'default nil :family "Menlo" :height 135)
(set-face-attribute 'default nil :height 145)

;; Override buffer choice
(global-set-key (kbd "C-x k") 'kill-this-buffer)

;; indent with spaces instead of tabs
(setq-default indent-tabs-mode nil)

(setq-default fill-column 80)
(setq-default sentence-end-double-space nil)

;; bind C-æ to comment-region
(global-set-key (kbd "C-æ") 'comment-dwim)

(use-package undo-tree
  :bind (("C-x u" . undo-tree-visualize)
         ("C--" . undo)))

(use-package transpose-frame)

(use-package winner
  :config
  (winner-mode 1))

(use-package aggressive-indent
  :diminish aggressive-indent-mode
  :config
  (global-aggressive-indent-mode 1)
  (add-to-list 'aggressive-indent-excluded-modes 'html-mode 'org-mode)
  )

(use-package autorevert
  :diminish auto-revert-mode
  :config
  (global-auto-revert-mode 1))

(use-package discover-my-major
  :bind ("C-h C-m" . discover-my-major))

(use-package popwin
  :ensure t
  :bind
  (("C-z" popwin:keymap))
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
  (popwin-mode 1))

(use-package hydra
  :ensure t
  :bind
  (
   ("C-M-k" . hydra-pause-resume)
   ("C-c C-h" . hydra-proof-general/body)
   ("C-x o" . hydra-window/body)
   ("C-¨" . hydra-multiple-cursors/body)
   ("C-c C-v" . hydra-toggle-simple/body)
   ("C-x SPC" . hydra-rectangle/body)
   ("C-c h" . hydra-apropos/body)
   :map Buffer-menu-mode-map
   ("." . hydra-buffer-menu/body)
   :map org-mode-map
   ("C-c C-," . hydra-ox/body)
   )
  :config
  (require 'hydra-examples)
  (require 'hydra-ox)
  (defhydra hydra-toggle-simple (:color blue)
    "toggle"
    ("a" abbrev-mode "abbrev")
    ("d" toggle-debug-on-error "debug")
    ("f" auto-fill-mode "fill")
    ("t" toggle-truncate-lines "truncate")
    ("w" whitespace-mode "whitespace")
    ("q" nil "cancel"))

  (defhydra hydra-window (:color red
                                 :hint nil)
    "
 Split: _v_ert  _x_:horz
Delete: _o_nly (_i_: ace)  _da_ce  _dw_indow  _db_uffer  _df_rame
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
    ("i" ace-maximize-window :color blue)
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
                                        ;("m" headlong-bookmark-jump)
    )
  (defhydra hydra-multiple-cursors (:hint nil)
    "
     ^Up^            ^Down^        ^Other^
----------------------------------------------
[_p_]   Next    [_n_]   Next    [_e_] Edit lines
[_P_]   Skip    [_N_]   Skip    [_a_] Mark all
[_M-p_] Unmark  [_M-n_] Unmark  [_r_] Mark by regexp
^ ^             ^ ^             [_l_] Recenter
"
  ("e" mc/edit-lines :exit t)
  ("l" recenter-top-bottom)
  ("a" mc/mark-all-like-this :exit t)
  ("n" mc/mark-next-like-this)
  ("N" mc/skip-to-next-like-this)
  ("M-n" mc/unmark-next-like-this)
  ("p" mc/mark-previous-like-this)
  ("P" mc/skip-to-previous-like-this)
  ("M-p" mc/unmark-previous-like-this)
  ("r" mc/mark-all-in-region-regexp :exit t)
  ("q" nil))
  (defhydra hydra-proof-general (:hint nil)
    "
^Assert^            ^Toggle^        ^Other^
----------------------------------------------
[_n_]   Next    [_._]   Autosend    [_r_] Retract
[_u_]   Undo    [_>_]   Electric    [_o_] Display
[_b_]   Buffer  ^ ^                 [_l_] Layout
"
("n" proof-assert-next-command-interactive)
("u" proof-undo-last-successful-command)
("b" proof-process-buffer :exit)
("." proof-electric-terminator-toggle)
(">" proof-autosend-toggle)
("r" proof-retract-buffer)
("o" proof-display-some-buffers)
("l" proof-layout-windows))
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

)

;; https://github.com/magit/magit
(use-package magit
  :bind ("C-x g" . magit-status))

(use-package smart-mode-line
  :config
  (setq sml/no-confirm-load-theme t)
  (sml/setup)
  )

(use-package moe-theme
  :config
  (moe-light)
  )

(use-package diff-hl
  :config
  (add-hook 'magit-post-refresh-hook 'diff-hl-magit-post-refresh)
  (global-diff-hl-mode))

;; (use-package zenburn-theme
;;   :ensure t
;;   :config (load-theme 'zenburn t))

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
  :diminish company-mode
  :init
  ;; https://github.com/company-mode/company-mode/issues/50#issuecomment-33338334
  (defun add-pcomplete-to-capf ()
    (add-hook 'completion-at-point-functions 'pcomplete-completions-at-point nil t))
  :config
  (setq company-idle-delay 0.2)
  (setq company-minimum-prefix-length 2)
  (bind-key "C-n" 'company-select-next company-active-map)
  (bind-key "C-p" 'company-select-previous company-active-map)
  (bind-key "C-M-i" 'company-complete)
  (global-company-mode))

;;;; https://github.com/bbatsov/projectile
;; (use-package projectile
;;   :config
;;   (projectile-global-mode t))

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

;; https://github.com/justbur/emacs-which-key
(use-package which-key
  :diminish which-key-mode
  :config
  (which-key-mode)
  (which-key-setup-minibuffer)
  ;; (which-key-setup-side-window-right-bottom)
  (setq which-key-idle-delay 1)
  (setq which-key-special-keys nil)
  )

;; https://github.com/jaypei/emacs-neotree
(use-package neotree
  :bind ("C-c C-t" . neotree-toggle))

;; https://github.com/abo-abo/avy
(use-package avy
  :bind (("M-s"   . avy-goto-char-2)
         ("M-p"     . avy-pop-mark)
         ("M-j"     . avy-goto-char)
         ("M-k"     . avy-goto-word-1)
         ("C-ø"     . avy-goto-char)
         ("M-g M-g" . avy-goto-line)
         ("M-g e"   . avy-goto-word-0)
         ("C-M-ø"   . avy-goto-char-timer))
  :config
  (setq avy-timeout-seconds 0.3)
  (setq avy-all-windows nil)
  ;; (setq avy-keys
  ;;       '(?c ?a ?s ?d ?e ?f ?h ?w ?y ?j ?k ?l ?n ?m ?v ?r ?u ?p))
  )

(use-package ace-link
  :config
  (ace-link-setup-default)
  )

(use-package avy-zap
  :bind (
         ("M-Z" . avy-zap-to-char-dwim)
         ("M-z" . avy-zap-up-to-char-dwim)))

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
  (setq-default TeX-master nil)
  (add-hook 'LaTeX-mode-hook 'visual-line-mode)
  (add-hook 'LaTeX-mode-hook 'flyspell-mode)
  (add-hook 'LaTeX-mode-hook 'LaTeX-math-mode)
  (add-hook 'LaTeX-mode-hook 'turn-on-reftex)
  (setq reftex-plug-into-AUCTeX t)
  (setq TeX-PDF-mode t)
  (add-hook 'TeX-language-dk-hook
            (lambda () (ispell-change-dictionary "dansk")))

  ;; Use Skim as viewer, enable source <-> PDF sync
  ;; make latexmk available via C-c C-c
  ;; Note: SyncTeX is setup via ~/.latexmkrc (see below)
  (add-to-list 'TeX-command-list '("latexmk" "latexmk -pdf %s" TeX-run-TeX nil t
                                   :help "Run latexmk on file"))
  (add-to-list 'TeX-command-list '("make" "make" TeX-run-TeX nil t
                                   :help "Runs make"))
  (add-hook 'TeX-mode-hook '(lambda () (setq TeX-command-default "latexmk")))

  ;; use Skim as default pdf viewer
  ;; Skim's displayline is used for forward search (from .tex to .pdf)
  ;; option -b highlights the current line; option -g opens Skim in the background
  (setq TeX-view-program-selection '((output-pdf "PDF Viewer")))
  (setq TeX-view-program-list
        '(("PDF Viewer" "/Applications/Skim.app/Contents/SharedSupport/displayline -b -g %n %o %b")))

  )

(use-package cdlatex
  :config
  (add-hook 'LaTeX-mode-hook 'turn-on-cdlatex)   ; with AUCTeX LaTeX mode
  (setq cdlatex-command-alist
        '(("ww" "Insert \\text{}" "\\text{?}" cdlatex-position-cursor nil nil t)
          ("bb" "Insert \\mathbb{}" "\\mathbb{?}" cdlatex-position-cursor nil nil t)
          ("lm" "Insert \\lim_{}" "\\lim_{?}" cdlatex-position-cursor nil nil t)
          ("dm" "Insert display math equation" "\\[\n?\n\\]" cdlatex-position-cursor nil t nil)
          ("equ*" "Insert equation* environment" "\\begin{equation*}\n?\n\\end{equation*}" cdlatex-position-cursor nil t nil)
          )
        )
  )

(use-package git-auto-commit-mode)

;; http://orgmode.org/manual/index.html
(use-package org
  :diminish visual-line-mode org-cdlatex-mode org-indent-mode
  :ensure org-plus-contrib
  :mode (("\\.\\(org\\|org_archive\\|txt\\)$" . org-mode))
  :bind (("C-c c" . org-capture)
         ("C-c l" . org-store-link)
         ("C-c a" . org-agenda)
         ("C-c b" . org-iswitchb)
         :map org-mode-map
         ("C-å"   . org-cycle-agenda-files)
         ("<f8>" . org-toggle-latex-fragment)
         ("M-o" 'ace-link-org)
         )
  :config
  ;;  (add-hook 'org-mode-hook 'worf-mode)
  (add-to-list 'org-speed-commands-user '("a" . org-attach))
  (setq org-use-speed-commands t)
  (add-hook 'org-mode-hook 'turn-on-org-cdlatex)
  (add-hook 'org-mode-hook 'visual-line-mode)
  (add-hook 'org-mode-hook 'add-pcomplete-to-capf)
  (plist-put org-format-latex-options :scale 1.6)
  ;; (setq org-fontify-whole-heading-line t)
  (org-babel-do-load-languages
   'org-babel-load-languages
   '((calc . t)
     (dot . t)
     (ditaa . t)
     (sh . t)
     (shell . t)
     (latex . t)))
  (add-to-list 'org-src-lang-modes '("dot" . graphviz-dot)))

(use-package paradox
  :config
  (paradox-enable))

(use-package recentf
  :config
  (setq recentf-exclude '("COMMIT_MSG" "COMMIT_EDITMSG" "github.*txt$"
                          ".*png$" ".*cache$"))
  (setq recentf-max-saved-items 10))

(use-package swiper
  :diminish ivy-mode
  :ensure t
  :bind
  (
   ( "C-s" . swiper)
   ( "M-y" . counsel-yank-pop)
   ( "M-x" . counsel-M-x)
   ( "C-x C-f" . counsel-find-file)
   ( "<f1> f" . counsel-describe-function)
   ( "<f1> v" . counsel-describe-variable)
   ( "<f1> l" . counsel-load-library)
   ( "<f2> i" . counsel-info-lookup-symbol)
   ( "<f2> u" . counsel-unicode-char)
   ( "C-h b" . counsel-descbinds)
   ( "C-c g" . counsel-git)
   ( "C-c j" . counsel-git-grep)
   ( "C-c k" . counsel-ag)
   ( "C-x l" . counsel-locate)
   ( "C-r" . ivy-resume)
   ( "C-c g" . counsel-git)
   ( "C-c j" . counsel-git-grep)
   ("M-y" . counsel-yank-pop)
   :map ivy-minibuffer-map
   ("M-y" . ivy-next-line))
  :config
  (ivy-mode 1)
  (setq ivy-use-virtual-buffers t)
  (use-package ivy-hydra)
  (use-package counsel)
  (setq ivy-height 10)
  (setq ivy-count-format "%d/%d | ")
  (setq ivy-extra-directories nil)
  (setq counsel-locate-cmd 'counsel-locate-cmd-mdfind)
  (setq ivy-display-style 'fancy)
  (setq magit-completing-read-function 'ivy-completing-read))

(use-package visual-regexp
  :bind
  (("C-c r" . vr/replace)
   ("C-c q" . vr/query-replace))
  )

(use-package beacon
  :diminish beacon-mode
  :config
  (beacon-mode 1))

(use-package whitespace-cleanup-mode
  :diminish whitespace-cleanup-mode
  :config
  (global-whitespace-cleanup-mode))

(use-package abbrev
  :ensure nil
  :diminish abbrev-mode
  :config
  (if (file-exists-p abbrev-file-name)
      (quietly-read-abbrev-file)))

;; (use-package rainbow-delimiters
;;   :config
;;   (add-hook 'prog-mode-hook 'rainbow-delimiters-mode))

(use-package typit)

;;;;;;;
;; Language specific packages:
;;;;;;;
(use-package sml-mode
  :mode "\\.sml\\'"
  :interpreter "sml")

(setq scheme-program-name "petite")
(load-file                "~/.emacs.d/scheme-setup.el")


;;; load coq
(require 'proof-site "~/.emacs.d/lisp/PG/generic/proof-site")
(use-package company-coq
  :config
  (add-hook 'coq-mode-hook #'company-coq-mode))
(setq proof-three-window-mode-policy 'hybrid)
(setq proof-script-fly-past-comments t)

(with-eval-after-load 'coq
  (define-key coq-mode-map "\M-n"
    #'proof-assert-next-command-interactive)
  ;; Small convenience for commonly written commands.
  (define-key coq-mode-map "\C-c\C-m" "\nend\t")
  (define-key coq-mode-map "\C-c\C-e"
    #'endless/qed)
  (defun endless/qed ()
    (interactive)
    (unless (memq (char-before) '(?\s ?\n ?\r))
      (insert " "))
    (insert "Qed.")
    (proof-assert-next-command-interactive)))
(define-abbrev-table 'coq-mode-abbrev-table '())
(define-abbrev coq-mode-abbrev-table "re" "reflexivity.")
(define-abbrev coq-mode-abbrev-table "id" "induction")
(define-abbrev coq-mode-abbrev-table "si" "simpl.")
(advice-add 'proof-assert-next-command-interactive
            :before #'expand-abbrev)
(defun open-after-coq-command ()
  (when (looking-at-p " *(\\*")
    (open-line 1)))
(advice-add 'proof-assert-next-command-interactive
            :after #'open-after-coq-command)


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

(require 'personal-init)
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(package-selected-packages
   (quote
    (diff-hl git-auto-commit-mode git-auto-commit zenburn-theme whitespace-cleanup-mode which-key visual-regexp use-package undo-tree typit transpose-frame sml-mode smex smart-mode-line popwin paradox org-plus-contrib neotree multiple-cursors moe-theme magit linum-relative ivy-hydra git-gutter-fringe expand-region exec-path-from-shell easy-kill discover-my-major cursor-chg counsel company-coq cdlatex browse-kill-ring better-defaults beacon avy-zap auto-compile auctex aggressive-indent ace-window ace-popup-menu ace-link ace-flyspell))))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )
(put 'upcase-region 'disabled nil)
