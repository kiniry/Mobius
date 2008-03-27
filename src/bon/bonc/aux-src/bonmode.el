;; ===== bon mode
(defvar bon-mode-hook nil)
(defvar bon-mode-map
  (let ((bon-mode-map (make-keymap)))
    (define-key bon-mode-map "\C-j" 'newline-and-indent)
    bon-mode-map)
  "Keymap for BON major mode")

(add-to-list 'auto-mode-alist '("\\.bon\\'" . bon-mode))

(defconst bon-font-lock-keywords-1
  (list 
   '("\\<end\\>" . font-lock-builtin-face)
   '("\\<class_chart\\>" . font-lock-builtin-face)
   '("\\<cluster_chart\\>" . font-lock-builtin-face)
   '("\\<scenario_chart\\>" . font-lock-builtin-face)
   '("\\<event_chart\\>" . font-lock-builtin-face)
   '("\\<creation_chart\\>" . font-lock-builtin-face)
   '("\\<cluster\\>" . font-lock-builtin-face)
   '("\\<scenario\\>" . font-lock-builtin-face)
   '("\\<class\\>" . font-lock-builtin-face)
   '("system_chart" . font-lock-builtin-face)
   '("\\<outgoing\\>" . font-lock-builtin-face) 
   '("\\<incoming\\>" . font-lock-builtin-face) 
   '("indexing" . font-lock-constant-face)
   '("query" . font-lock-constant-face)
   '("inherit" . font-lock-constant-face)
   '("command" . font-lock-constant-face)
   '("constraint" . font-lock-constant-face)
   '("explanation" . font-lock-constant-face)
   '("description" . font-lock-constant-face) 
   '("\\<event\\>" . font-lock-constant-face) 
   '("\\<involves\\>" . font-lock-constant-face) 
   '("\\<part\\>" . font-lock-constant-face) 
  ) 
  "Minimal highlighting expressions for BON mode.")

(defvar bon-font-lock-keywords bon-font-lock-keywords-1 "Default highlighting expressions for BON mode.")

(defun bon-mode ()
  (interactive)
  (kill-all-local-variables)
  (use-local-map bon-mode-map)
  ;; Set up font-lock
  (set (make-local-variable 'font-lock-defaults) '(bon-font-lock-keywords))
  (setq major-mode 'bon-mode)
  (setq mode-name "BON")
  (run-hooks 'bon-mode-hook))

(provide 'bon-mode)
;; ===== end of bon-mode
