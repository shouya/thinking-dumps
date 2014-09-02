;; Configurations for emacs

(add-hook 'coq-mode-hook
	  (lambda ()
	    (progn
	      ;; automatically clean up bad whitespace
	      (proof-unicode-tokens-enable)
	      (proof-electric-terminator-toggle)
	      ;; only show bad whitespace
	      (setq whitespace-style '(trailing
				       space-before-tab
				       indentation empty
				       space-after-tab))
	      (setq tab-width 4)
	      (defun replsf (begin end)
		"rewrite unicode math symbols in ascii forms test"
		(interactive "r")
		(save-restriction
		  (narrow-to-region begin end)
		  (mapc (lambda (x)
			  (goto-char (point-min))
			  (while (search-forward (car x) nil t)
			    (replace-match (cdr x) nil t)))
			'(("→" . "->")
			  ("∨" . "\\/")
			  ("↔" . "<->")
			  ("∀" . "forall ")
			  ("∧" . "/\\")
			  ("¬" . "~")
			  ("≠" . "<>")
			  ("×" . "*")
			  ("≤" . "<=")
			  ("⇒" . "=>")
			  ("∃" . "exists ")
			  ("⇓" . "||")
			  ))
		  )))))
