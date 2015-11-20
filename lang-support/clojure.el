;; https://github.com/clojure-emacs/clojure-mode
(use-package clojure-mode
  :config
  (add-hook 'clojure-mode-hook 'yas-minor-mode))

;; https://github.com/clojure-emacs/cider
(use-package cider
  :config
  (progn (add-hook 'clojure-mode-hook 'cider-mode)
         (add-hook 'clojure-mode-hook 'cider-turn-on-eldoc-mode)
         (add-hook 'cider-repl-mode-hook 'subword-mode)
         (setq cider-annotate-completion-candidates t
               cider-prompt-for-symbol nil)))

;; https://github.com/clojure-emacs/clj-refactor.el
(use-package clj-refactor
  :config
  (progn (setq cljr-suppress-middleware-warnings t)
         (add-hook 'clojure-mode-hook (lambda ()
                                        (clj-refactor-mode 1)
                                        (cljr-add-keybindings-with-prefix "C-c C-m")))))
