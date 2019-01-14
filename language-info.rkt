#lang racket

(provide language-info)

; For use with #:language-info in the reader
(define (language-info data)
  (lambda (key default)
    (case key
      ; Replaces default reader in REPL so that REPL can take commands instead of Racket expressions
      [(configure-runtime)    
       ; Note: LIST of vectors... allows for multiple config functions to be run
      '(#(emcsabac/runtime-config configure #f))]
      [(drracket:submit-predicate)       
       repl-submit-predicate]          
      [else default])))


; **********************************************************

; ALWAYS pass to our reader (REPL input)
(define (repl-submit-predicate interactions-port only-whitespace)
  #t)
