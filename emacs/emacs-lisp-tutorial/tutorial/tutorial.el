
(define-lex lx "" 
  semantic-lex-ignore-newline  
  semantic-lex-ignore-whitespace
  semantic-lex-number
  semantic-lex-default-action)

(defun doparse2 () 
  (interactive)
  (calc-wy--install-parser)
  (setq  semantic-lex-analyzer 'lx)
  (setq semantic-lex-syntax-table (standard-syntax-table))
    (setq wisent-lex-istream (semantic-lex-buffer))
    (insert (format "Total is %s\n" (wisent-parse calc-wy--parse-table 'wisent-lex))))
