#lang racket

(require emcsarbac/lang/reader)

(provide configure)

(define (configure data)  
  ;(current-prompt-read repl-prompt-read)
  ;(current-print repl-print)
  (current-read-interaction repl-read-interaction))

; Replace default REPL handling
(define (repl-read-interaction src in)
  (read-syntax-arbac-single src in))

;(define orig-print (current-print))
;(define (repl-print proc)    
;   ; (printf "In m-r-print~nCPR was: ~a~n"(current-prompt-read))
;  (if (procedure? proc)                                       
;      (let ()                                     
;        (define a-result (proc))
;        (when (not (void? a-result))
;          (display (response->string a-result))))
;      (orig-print proc)))
;
;(define (margrave-repl-prompt-read)
;  (display ":> ") (flush-output)
;  (let ([in (current-input-port)])
;    ((current-read-interaction) (object-name in) in)))