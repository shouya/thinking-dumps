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
	      (defun replsf ()
		"rewrite unicode math symbols in ascii forms test"
		(interactive)
		(mapc (lambda (x) (perform-replace (car x) (cadr x) nil nil nil))
			'(("→" "->")
			  ("∨" "\\/")
			  ("↔" "<->")
			  ("∀" "forall")
			  ("∧" "/\\")))))))
