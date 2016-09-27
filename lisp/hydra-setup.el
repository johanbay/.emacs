(defhydra hydra-toggle-simple (:color blue)
  "toggle"
  ("a" abbrev-mode "abbrev")
  ("d" toggle-debug-on-error "debug")
  ("f" auto-fill-mode "fill")
  ("t" toggle-truncate-lines "truncate")
  ("w" whitespace-mode "whitespace")
  ("q" nil "cancel"))

(defhydra hydra-yasnippet (:color blue :hint nil)
  "
              ^YASnippets^
--------------------------------------------
  Modes:    Load/Visit:    Actions:

 _g_lobal  _d_irectory    _i_nsert
 _m_inor   _f_ile         _t_ryout
 _e_xtra   _l_ist         _n_ew
         _a_ll
"
  ("d" yas-load-directory)
  ("e" yas-activate-extra-mode)
  ("i" yas-insert-snippet)
  ("f" yas-visit-snippet-file :color blue)
  ("n" yas-new-snippet)
  ("t" yas-tryout-snippet)
  ("l" yas-describe-tables)
  ("g" yas/global-mode)
  ("m" yas/minor-mode)
  ("a" yas-reload-all))

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

(provide 'hydra-setup)
