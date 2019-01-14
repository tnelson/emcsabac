#lang s-exp syntax/module-reader

#:language 'emcsarbac

; Define our own readers
#:read read-arbac
#:read-syntax read-syntax-arbac

; Yes, read the whole body with one call of the reader
#:whole-body-readers? #t

; #:info is for *SOURCE* manipulation
; key: kind of info requested
; default value if symbol is not recognized
; default-filtering function that takes the first two and returns a result
#:info (lambda (key defval default)
         (case key           
           [(color-lexer)            
            (dynamic-require 'syntax-color/default-lexer 'default-lexer)]

           ; Just use ordinary .rkt file extension.
           ;[(drracket:default-filters)
           ; '(("Policy Files" "*.pol"))]

           ; Opt out of these buttons, they might confuse users
           [(drracket:opt-out-toolbar-buttons)
            '(debug-tool macro-stepper drracket:syncheck)]
           
           [else (default key defval)]))

; #:language-info is for *COMPILE-TIME* manipulation
#:language-info '#(emcsarbac/language-info language-info #f)


(require racket
         syntax/strip-context         
         "../lexparse.rkt")

(provide read-syntax-arbac
         read-arbac
         read-syntax-arbac-single
         read-arbac-single) 

; **********************************************************

(define (read-arbac in)
  (syntax->datum
   (read-syntax-arbac #f in)))

; **********************************************************
  
(define (read-syntax-arbac src in)  
  (error-print-source-location #f) ; Don't say "unsaved-editor34228"
  ; Parse here, so we have syntax-location info for parse errors
  (define ast (parse-all-commands src in))  
  (define result-syntax    
    (with-syntax ([ast `(list ,@ast)]) 
      (strip-context 
       #`( (require emcsarbac/runner)              
           (set-box! boxed-env (run-commands (unbox boxed-env) ast))))))  
  result-syntax)

; **********************************************************

; Single-command readers. Used by the REPL.

(define (read-syntax-arbac-single src in)  
  ; REPL will keep calling this over and over (because of runtime-configuration).
  ; Check to make sure there is a character waiting.
  ; If there isn't one, stop looking for one until triggered again.
  (cond [(char-ready? in)            
         (define ast (parse-single-command src in))
         (cond [(empty? ast) ; If trailing semicolon, will be treated as a separate entity by the parser. ignore.
                eof]
               [else                
                (define result-syntax
                  (with-syntax ([ast `(list ,ast)]) ; no @, because not a list
                    #'(begin               
                        (set-box! boxed-env (run-commands (unbox boxed-env) ast))
                        (void))))
                ;; DEBUG
                ;(printf "single result-syntax: ~a~n" result-syntax)
                result-syntax])]
        [else
         eof]))

; TODO: environments shared
; TODO: if not terminated with ;, it hangs? (in parser?)

(define (read-arbac-single in)
  (syntax->datum
   (read-syntax-arbac-single #f in)))


