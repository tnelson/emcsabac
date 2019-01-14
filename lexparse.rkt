#lang racket

; With thanks to https://gist.github.com/danking/1068185

(require parser-tools/lex
         (prefix-in re- parser-tools/lex-sre)         
         parser-tools/yacc
         syntax/readerr
         racket/struct
         rackunit)
(provide parse-all-commands
         parse-single-command
         (struct-out policy)
         (struct-out command)
         (struct-out rule)
         (struct-out condition))

(define-tokens the-tokens (id))
(define-empty-tokens the-empty-tokens (comma not EOF pol end po do nop
                                             lparen rparen if dot semicolon true
                                             info compare test))

(define-lex-abbrevs
  (identifier-characters (re-or (char-range "A" "z")
                                "-" "_"
                                (char-range "0" "9")))
  (identifier (re-+ identifier-characters))
  [lex:comment  (re-: #\/ #\/ (re-* (char-complement (re-or #\newline #\return))))])

(define policy-lexer
  (lexer-src-pos
   ("info" (token-info))
   ("compare" (token-compare))
   ("test" (token-test))
   
   ("." (token-dot))
   ("if:" (token-if))
   ("true" (token-true))
   ("(" (token-lparen))
   (")" (token-rparen))
   ("policy" (token-pol))
   ("end" (token-end))   
   ("po" (token-po))
   ("do" (token-do))
   ("nop" (token-nop))
   ("," (token-comma))  
   ("not" (token-not))
   (";" (token-semicolon))
   (identifier (token-id (string->symbol lexeme)))
   ; Note: without return-without-pos, the resulting position-token will be *wrapped* in another.
   ; See docs for return-without-pos
   (whitespace (return-without-pos (policy-lexer input-port)))
   ; comments
   [lex:comment (return-without-pos (policy-lexer input-port))]
   
   ((eof) (token-EOF))
   ; Custom error behavior
   (any-char (raise-read-error
              (format "Couldn't understand \"~a\"; it's not a recognized keyword or identifier.~n" lexeme)
              (object-name input-port)
              (position-line start-pos)
              (position-col start-pos)
              (position-offset start-pos)      
              (- (position-offset end-pos) (position-offset start-pos))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DESIGN NOTE
; This is technically not the "right" way to do this in Racket. 
; Instead, we should be producing syntax. However, I built on
; some prior code that did this already. Unless we need syntax
; info post-parse, keeping this.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Need these to write identically to their constructor.
; make-constructor-style-printer will not produce the correct write format.
(struct condition (sign pred args)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc
     (lambda (obj port mode)
       (write-string (format "(condition ~a ~a ~a)" (condition-sign obj) (condition-pred obj) (condition-args obj)) port)))])   

(struct rule (decision conditions)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc
     (lambda (obj port mode)
       (write-string (format "(rule ~a ~a)" (rule-decision obj) (rule-conditions obj)) port)))])

(struct policy (name rules)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc
     (lambda (obj port mode)
       (write-string (format "(policy ~a ~a)" (policy-name obj) (policy-rules obj)) port)))])  
(struct command (name args)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc
     (lambda (obj port mode)
       (write-string (format "(command ~a ~a)" (command-name obj) (command-args obj)) port)))])  

(define (general-error-message tok-ok? tok-name tok-value start-pos end-pos)
  (cond [(and tok-ok? (not (equal? tok-name 'id)))
         (format "Failed to understand command around the ~a on line ~a, column ~a.~n"
                 tok-name
                 (position-line end-pos)
                 (position-col end-pos))]
        [else
         (format "Failed to recognize word around line ~a, column ~a.~n"
                 (position-line end-pos)
                 (position-col end-pos))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; In order to give better error messages, we remember each token in a command (or a malformed command)
;   and clear out the history when done or when presenting an error
; We do this by changing the lexer function that the caller gives us before sending it on to the parser.
(define token-history empty)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Helpers

(define (get-reversed-tokens-so-far-no-eof)
  (filter (lambda (t) (not (equal? 'EOF t)))
          (reverse (map position-token-token token-history))))

(define (started-with token-list)  
  (define rev-tokens (get-reversed-tokens-so-far-no-eof))
  (printf "started-with: history:~a case:~a ~n" rev-tokens token-list)
  (cond [(>= (length rev-tokens) (length token-list))
         (define other-tokens (take rev-tokens (length token-list)))
         
         (define pairlist (map list token-list other-tokens))
         (andmap (lambda (pr) (cond [(equal? (first pr) (second pr)) #t]
                                    ; IMPORTANT: match any token of the same type (this is used for parse errors)
                                    [(and (token? (first pr))
                                          (token? (second pr))
                                          (equal? (token-name (first pr)) (token-name (second pr)))) #t]
                                    [else #f])) pairlist)]
        [else #f]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (command-parser source-name)

  (define internal-command-parse
    (parser
   (src-pos)
   (start COMMAND)
   (end EOF semicolon)
   (error 
    (lambda (tok-ok? token-name token-value start-pos end-pos) 
      ; Token-history is reversed here.
      (printf "(DEBUG) History: ~a~n" (map position-token-token token-history))
      
      ; Can we guess at the kind of command they were trying to use?
      ; customize an error message depending on history:
      (define error-message
        (cond [(empty? token-history)
               "Please enter a command."]
              ;[(token? first-token) ; token? is not true of empty-tokens like all the correct command keywords.
              ; "Please enter a valid command."]
              
              [(started-with '(compare))
               "To compare the behavior of two policies, use 'COMPARE <policy name> <policy name>' (without the quotes or angle-brackets)."]
              
              [(started-with `(pol ,(token-id 'x)))
               "A policy must be given a name. Please name the policy."]                        
                            
              [(started-with '(LOAD POLICY))
               "To load a .p policy file, use LOAD POLICY <desired name> = <file name>;"]
              
              [(started-with '(LOAD XACML))
               "To load an XACML policy file, use LOAD XACML <desired name> = <file name>;"]
              
              [(started-with '(LOAD SQS))
               "To load an Amazon SQS policy file, use LOAD SQS <desired name> = <file name>;"]
              
              [(started-with '(LOAD))
               "Load what? (LOAD POLICY to load a .p file, LOAD IOS to load a Cisco IOS configuration, etc.)" ]
              
              ;[(improper-query-name?)                         
              ; (format "LET: The query name must begin with a lowercase letter, and must not be a reserved word.~n")]              
              ;[(improper-var-decls?)
              ; (format "LET: Square brackets must contain a comma-separated list of declarations.~nEach declaration should have the form <varname>:<Type>~n")]
              
              [(started-with '(LET))                         
               (format "Usage: LET <name>[<variable-declarations>] BE <condition>.~n")]
                            
              ; Last resort              
              [else (general-error-message tok-ok? token-name token-value start-pos end-pos)]))
                       
      (set! token-history empty)
      (raise-read-error error-message
                        source-name
                        (position-line start-pos)
                        (position-col start-pos)
                        (position-offset start-pos)      
                        (- (position-offset end-pos) (position-offset start-pos)))))
   
   ;(debug "emcsabac-debug.txt")
   (tokens the-tokens the-empty-tokens)
   ;(precs (left + -))
   (grammar    
    
    ; single command (may be a policy definition)
    ; if able to complete parsing one of these, clear out the token history for next attempt
    (COMMAND
     ((info)
      (begin
        (set! token-history empty)
        (command 'info empty)))
     ((compare id id)
      (begin
        (set! token-history empty)
        (command 'compare (list $2 $3))))
     ((test id NONEMPTYCONDITIONLIST)
      (begin
        (set! token-history empty)
        (command 'test (cons $2 $3))))
     ((POL)
      (begin
        (set! token-history empty)
        $1))
     ; Prevent trailing whitespace and comments from clogging the parser
     (()
      (begin
        (set! token-history empty)
        '())))
    
    ; single policy definition
    (POL
     ((pol id NONEMPTYRULELIST end)
      (policy $2 $3)))
     
    (NONEMPTYRULELIST ((RULE NONEMPTYRULELIST) (cons $1 $2))
                      ((RULE) (list $1)))
    (RULE ((id if true dot)
           (rule $1 empty))
          ((id if NONEMPTYCONDITIONLIST dot)
          (rule $1 $3)))
    (NONEMPTYCONDITIONLIST ((CONDITION comma NONEMPTYCONDITIONLIST) (cons $1 $3))
                           ((CONDITION) (list $1)))
    (CONDITION ((not id NONEMPTYVARLIST)
               (condition #f $2 $3))
               ((id NONEMPTYVARLIST)                
                (condition #t $1 $2)))
    ; For now, no nullary conditions
    (NONEMPTYVARLIST ((VAR NONEMPTYVARLIST) (cons $1 $2))
                     ((VAR) (list $1)))
    ; Not just s/a/r, may need existentials
    (VAR ((id)
          $1)) )))
  
  ; wrap the parser func. wrapper has same type
  (lambda (gen)             
    (define (new-gen) 
      (let ([token-result (gen)])
        (set! token-history (cons token-result token-history)) ; backwards. reverse later
        token-result))    
    (internal-command-parse new-gen)))

(define (get-lexer-for input)
  (lambda ()
    (port-count-lines! input)
    (policy-lexer input)))


; Prints out the tokens generated for a given input string
; Taken from Margrave

(define (pretty-position pos)
  (list (position-offset pos)
        (position-line pos)
        (position-col pos)))
(define (debug-lexer-on str)
  (printf "Debugging lexer on string: ~a:~n~n" str)
  (define pt (open-input-string str))  
  (define lex-func (get-lexer-for pt))
  
  (define (inner-func)
    (define my-token (lex-func))
    (printf "~a @ start: ~a, end: ~a. ~n~n" 
            (position-token-token my-token)
            (pretty-position (position-token-start-pos my-token))
            (pretty-position (position-token-end-pos my-token)))
    (unless (equal? 'EOF (position-token-token my-token))
      (inner-func)))
  (inner-func))

; TODO: reconstructing the parser for each input can't possibly be efficient?

; Parse entire string into a list of commands/definitions
(define (parse-all-commands src input)  
  (define cmd ((command-parser src) (get-lexer-for input)))
  ;(printf "cmd: ~a~n" cmd)
  (if (empty? cmd)
      empty        
      (cons cmd  
            (parse-all-commands src input))))

; Parse a *single* command from the port
(define (parse-single-command src input)
  ((command-parser src) (get-lexer-for input)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TESTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (parser-error? x)
  (and (list? x) (not (empty? x)) (equal? (first x) 'error)))

;(define lp-tests
;  (test-suite
;   "Tests for lexparse.rkt"
;
;   (check-true (rule? 
;                (let ((input (open-input-string "permit <- admin s, write a, disk r.")))  
;                  (rule-parser (get-lexer-for input)))))
;   (check-true (rule? (let ((input (open-input-string "deny <- not admin s, write a.")))  
;                  (rule-parser (get-lexer-for input)))))
;
;   (check-true (policy? (let ((input (open-input-string "policy test1 permit <- admin s, write a, disk r. deny <- not admin s. end")))
;                    (policy-parser (get-lexer-for input)))))
;
;   (check-true (parser-error? (let ((input (open-input-string "policy permit <- admin s, write a, disk r. deny <- not admin s. end")))
;                    (policy-parser (get-lexer-for input)))))
;
;   (check-true (command? (let ((input (open-input-string "compare mypolicy theirpolicy")))
;                     (command-parser (get-lexer-for input)))))
;   (check-true (policy? (let ((input (open-input-string "policy test1 permit <- admin s, write a, disk r. deny <- not admin s. end")))
;                     (command-parser (get-lexer-for input)))))
;
;   (for-each (lambda (x) (check-true (or (command? x) (policy? x))))
;             (parse-all-commands (open-input-string
;"policy test1 permit <- admin s, write a, disk r. deny <- not admin s. end ;
;policy test2 permit <- admin s, write a, disk r. deny <- not admin s, write a. end;
;info;
;compare test1 test2;")))))