#lang rosette

;(require racket/base)

(require "lexparse.rkt")
; DO NOT REQUIRE THIS! Replaces "and" with symbolic version so that (and #f #f) is truthy
;(require rosette/solver/smt/smtlib2)
; Rosette itself is all syntax, and having to eval or work in phase 1 seems overcomplicated.
; Instead, use Ocelot.
(require ocelot)
;(require (only-in ocelot/lang/ast quantified-formula))
(require (only-in ocelot/lang/ast relation-arity relation-name))
(require rackunit)

(provide run-commands
         boxed-env)

; State of policy environment, so that REPL can access it after definitions have been run
(define boxed-env (box empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; We know what the relations are in advance (since this is just for one exercise).
; We do NOT necessarily know what rules they might write/modify. But we're working in EPL,
; so just count unique identifiers (will possibly over-estimate).

(define Subject (declare-relation 1 "Subject"))
(define Action (declare-relation 1 "Action"))
(define Resource (declare-relation 1 "Resource"))

(define Admin (declare-relation 1 "Admin"))
(define Accountant (declare-relation 1 "Accountant"))
(define Customer (declare-relation 1 "Customer"))

(define Read (declare-relation 1 "Read"))
(define Write (declare-relation 1 "Write"))

(define File (declare-relation 1 "File"))
(define Audit (declare-relation 1 "Under-Audit")) ; under audit
(define Training (declare-relation 1 "In-Training")) ; employee in training

(define Owner (declare-relation 2 "Owner-Of"))
(define reqS (declare-relation 1 "reqS"))
(define reqA (declare-relation 1 "reqA"))
(define reqR (declare-relation 1 "reqR"))

(define relations (hash "Admin" Admin     "Accountant" Accountant "Customer" Customer
                        "Read" Read       "Write" Write           
                        "File" File       "Under-Audit" Audit     "Owner-Of" Owner                        
                        "In-Training" Training
                        "Subject" Subject "Action" Action "Resource" Resource
                        "reqS" reqS "reqA" reqA "reqR" reqR))

(define structural-axioms
  (and
   (in Write Action)    ; base sigs
   (in Read Action)
   (in Accountant Subject)
   (in Customer Subject)
   (in Admin Subject)
   (in File Resource)
  
   (no (& Subject Action))
   (no (& Action Resource))
   (no (& Subject Resource))
   (no (& Customer Admin))
   (no (& Customer Accountant))
   (no (& Read Write))

   (one reqS) ; Skolem constants
   (one reqA)
   (one reqR)
     
   (in Audit File)
   (in Training (+ Accountant Admin)) ; only employees can be in training
   (in Owner (-> Customer File))
   ))

; Build a bound struct for relation <r> that has an empty lower bound and maximal upper bound.
(define (bound-rel atoms r)
  (cond
    ; Subject, Action, and Resource must contain specific atoms
    [(equal? (relation-name r) "Subject")
     (make-bound r '((s$0)) (map list atoms))]
    [(equal? (relation-name r) "Action")
     (make-bound r '((a$0)) (map list atoms))]
    [(equal? (relation-name r) "Resource")
     (make-bound r '((r$0)) (map list atoms))]
    ; Skolem relations:
    [(equal? (relation-name r) "reqS")     
     (make-exact-bound r '((s$0)))]
    [(equal? (relation-name r) "reqA")
     (make-exact-bound r '((a$0)))]
    [(equal? (relation-name r) "reqR")
     (make-exact-bound r '((r$0)))]
    ; Everything else:
    [(equal? 1 (relation-arity r))
     (make-bound r '() (map list atoms))]
    [(equal? 2 (relation-arity r))     
     (make-bound r '() (cartesian-product atoms atoms))]
    [else
     (raise (format "Error: relation ~a had invalid arity" r))]))

; Bound overall bounds struct containing bound for every relation
(define (make-bounds U)
  (define atoms (universe-atoms U)) ; note, not "atom" in the sense of atomic fmla  
  (bounds U (map (lambda (r) (bound-rel atoms r))
                 (hash-values relations))))
                 

; Must support (not necessarily efficiently):
;  - policy COMPARISON
;  - rule blaming
;  - testing a single request
;  - policy comparison WHERE <conjunction>
; NO support for:
;  - equality
;  - arbitrary queries (just conjunctive ones allowed)
;

(struct atom (pred args) #:transparent)

(define (lit->atom c)
  (atom (condition-pred c) (condition-args c)))

(define (extract-atoms-rule r)
  (remove-duplicates (foldl (lambda (c acc) (cons (lit->atom c) acc))
                              empty
                              (rule-conditions r))))

(define (extract-atoms-policy pol)
  (remove-duplicates (foldl (lambda (r acc) (append (extract-atoms-rule r) acc))
                              empty
                              (policy-rules pol))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (run-info env)
  (printf "You have loaded ~a policies so far.~n" (length env))  
  (for-each (lambda (p)
              (printf "  Policy: ~a~n" (policy-name p)))
              ;(printf "  Atoms used: ~a~n" (extract-atoms-policy p)))
            env))


; Convert a list of identifiers to a product
(define (list->product l)
  (foldl (lambda (i acc) `(-> ,acc ,i)) (first l) (rest l)))

(define (var->maybe-skolem v)
  (cond [(equal? v 's) reqS]
        [(equal? v 'a) reqA]
        [(equal? v 'r) reqR]
        [else v]))

; Build a formula for a specific rule condition
(define (build-condition c)
  (cond [(condition-sign c)
         `(in ,(list->product (map var->maybe-skolem (condition-args c)))
              ,(hash-ref relations (string-titlecase (symbol->string (condition-pred c)))))]
        [else
         `(! ,(build-condition (condition #t (condition-pred c) (condition-args c))))]))

(define (apply-quantifiers todo f)
  (if (empty? todo)
      f
      `(some ([,(first todo) univ]) ,(apply-quantifiers (rest todo) f))
      ;(quantified-formula ([(first todo) univ]) (apply-quantifiers (rest todo) f))
      ))

(define request-vars '(s a r))
; Build a formula that is true IFF this rule matches
(define (build-rule-matches r)
  ; Embed "some" quantifier if needed
  (define vars-used (remove-duplicates
                           (flatten (map (lambda (a) (atom-args a))
                                         (append (extract-atoms-rule r))))))
  (define to-quantify (filter (lambda (v) (equal? #f (member v request-vars))) vars-used))
  ;(printf "to quantify: ~a~n" to-quantify)
  (define basef `(and ,@(map build-condition (rule-conditions r))))
  (apply-quantifiers to-quantify basef))


; Walk the policy and build the conditions under which a request is <dec>
(define (build-dec dec pol)      
  (define disjuncts (first ; returns (<dec> fmlas, <nondec>-predicate-so-far)
                     (foldl (lambda (r acc)
                             (cond [(equal? (rule-decision r) dec)
                                    ; Possible to get <dec> if this rule matches and not <nondec so far>
                                    
                                    (define newrule
                                      (if (empty? (second acc))
                                          (build-rule-matches r)
                                          `(and (! (or ,@(second acc)))
                                                ,(build-rule-matches r))))
                                        
                                    (list (cons newrule (first acc))
                                          (second acc))]
                                   [else
                                    ; No new ways to get <dec>, but other-decisions get another possibility
                                    (list (first acc)
                                          (cons (build-rule-matches r) (second acc)))]))
                           (list empty empty) ; no <dec>, no <nondec>
                           (policy-rules pol))))  
  `(or ,@disjuncts))

(define (find-pol env pname)
  (define filtered-env (filter (lambda (p) (equal? (policy-name p) pname)) env))
  (if (not (empty? filtered-env))
      (first filtered-env)
      (raise (format "No policy named ~a found.~n" pname))))

(define-namespace-anchor anchor)
(define ns (namespace-anchor->namespace anchor))

(define (make-universe atoms)
  (universe (map (lambda (a) (string->symbol (string-append (symbol->string a) "$0"))) atoms)))

(define (run-query env args)
  (define polname (first args))
  (define conditions (rest args))
  (define conditions-fmla (map build-condition conditions))
  (define pol (find-pol env polname))
  (cond [(equal? pol #f) ; don't try to use not
         (raise (format "Unknown policy: ~a~n" polname))]
        [else
         (define varset (remove-duplicates
                         (flatten (map (lambda (a) (atom-args a))
                                       (extract-atoms-policy pol)))))
         (define permit (build-dec 'permit pol))
         (define U (make-universe varset))
         ;(printf "universe: ~a~n" (universe-atoms U))
         (define allBounds (make-bounds U))
         ;(printf "bounds: ~a~n" allBounds)
         (define instantiatedBounds (instantiate-bounds allBounds))
         (define query `(and ,permit ,@conditions-fmla))
         ; Is there at least one request with these conditions that is permitted?
         ; (unspecified literals -> left free to vary)
         (define fmla (eval `(and ,structural-axioms
                                  ,query) ns))
         ;(printf "fmla: ~a~n" (pretty-format fmla))
         (define rosette-fmla (interpret* fmla instantiatedBounds))
         (define rosette-result (solve (assert rosette-fmla)))
         (define rules (policy-rules pol))
         (pretty-printf-rosette-result #:inst-bounds instantiatedBounds #:rosette-result rosette-result #:ruleset1 rules) 
         ]))

(define (pretty-printf-rosette-result #:inst-bounds instantiatedBounds #:rosette-result rosette-result
                                      #:ruleset1 ruleset1 #:ruleset2 [ruleset2 empty] #:msg [msg #f])
  (cond [(sat? rosette-result)
         (define result (interpretation->relations (evaluate instantiatedBounds rosette-result)))
         ;(printf "~n~n(debug) result ~a~n" (pretty-format result))

         ; * Scenario *
         (define strout (pretty-format-scenario result))
         (printf "~n~n~a~n" strout)

         ; * Rule blaming *
         (define (rule-blaming qualifier ruleset) 
           (foldl (lambda (r acc)
                    ; Ocelot doesn't have an "evaluator" per se. So use *Rosette's*
                    ; evaluator on the *Rosette* version of the condition, compiled via the same instantiated bounds.
                    (define condition-fmla (build-rule-matches r))
                    (define ros-condition (interpret* (eval condition-fmla ns) instantiatedBounds))
                    (define tf (evaluate ros-condition rosette-result))
                    (cond [(and tf acc)
                           (printf "This rule applied~a: ~a~n" qualifier (pretty-format-rule r))
                           #f]
                          [else acc]))
                  #t ruleset))

         (if (empty? ruleset2)
             (rule-blaming "" ruleset1)
             (begin
               (rule-blaming " in the first policy" ruleset1)
               (rule-blaming " in the second policy" ruleset2)))
         
         ; * Message *
         (when msg
           (printf "~a~n" msg))
         ]
        [else (printf "No scenario existed matching those conditions.~n")]))

(define (pretty-format-condition c)
  (define signis (cond [(condition-sign c) "is"]
                       [else "not is"]))
  (define firstvar (first (condition-args c)))
  (cond [(> (length (condition-args c)) 1)
         (format "~a ~a ~a ~a" firstvar signis (condition-pred c) (second (condition-args c)))]
        [else
         (format "~a ~a ~a" firstvar signis (condition-pred c))]))

(define (pretty-format-rule r)
  (define conds (map pretty-format-condition (rule-conditions r)))
  (format "~a if: ~a." (rule-decision r) (string-join conds ", ")))


(define (run-compare env args)
  (define where (cond [(empty? (rest (rest args)))
                       empty]
                      [else
                       (first (rest (rest args)))]))
  (printf "Comparing policies ~a and ~a where ~a...~n" (first args) (second args) (map pretty-format-condition where))
  (cond [(and (find-pol env (first args))
              (find-pol env (second args)))
         (let ([pol1 (find-pol env (first args))]
               [pol2 (find-pol env (second args))])
           (define permit1 (build-dec 'permit pol1))
           (define permit2 (build-dec 'permit pol2))
           ;(printf "P1: ~a;~n P2: ~a~n" permit1 permit2)
           (define varset (remove-duplicates
                           (flatten (map (lambda (a) (atom-args a))
                                         (append (extract-atoms-policy pol1)
                                                 (extract-atoms-policy pol2))))))
           (define U (make-universe varset))           
           ;(printf "universe: ~a~n" (universe-atoms U))
           (define allBounds (make-bounds U))
           ;(printf "bounds: ~a~n" allBounds)
           (define instantiatedBounds (instantiate-bounds allBounds))           
           ; (Skolemized) query
           (define queryP1NP2 `(and ,permit1 (! ,permit2))) ; first
           (define queryNP1P2 `(and ,permit2 (! ,permit1))) ; second           

           (define where-fmlas (map build-condition where))
           
           ; "Eval" as consequence of building atop prior code
           (define fmla1 (eval `(and ,@where-fmlas
                                     ,structural-axioms
                                     ,queryP1NP2) ns))
           (define fmla2 (eval `(and ,@where-fmlas
                                     ,structural-axioms
                                     ,queryNP1P2) ns))
  
           ; Try each direction separately so that we can print out which policy decides what.
           ; Try P1.permit is not subset of P2.permit                      
           (define rosette-fmla (interpret* fmla1 instantiatedBounds))         
           (define rosette-result (solve (assert rosette-fmla)))
           (cond [(sat? rosette-result)               
                  (pretty-printf-rosette-result #:inst-bounds instantiatedBounds
                                                #:rosette-result rosette-result
                                                #:ruleset1 (policy-rules pol1)
                                                #:ruleset2 (policy-rules pol2)
                                                #:msg (format "~a permitted; ~a denied" (first args) (second args)))]
                 [else
                  ; Try P2.permit is not subset of P1.permit
                  (define rosette-fmla2 (interpret* fmla2 instantiatedBounds))                  
                  (define rosette-result2 (solve (assert rosette-fmla2)))
                  (pretty-printf-rosette-result #:inst-bounds instantiatedBounds
                                                #:rosette-result rosette-result2
                                                #:ruleset1 (policy-rules pol1)
                                                #:ruleset2 (policy-rules pol2)
                                                #:msg (format "~a permitted; ~a denied" (second args) (first args)))])
           )]
        [(not (find-pol env (first args)))
         (printf "Unknown policy name: ~a~n" (first args))]
        [(not (find-pol env (second args)))
         (printf "Unknown policy name: ~a~n" (second args))]))

(define (run-commands env cmdlst)
  (define (run-commands-helper cmdlst env)
    (if (empty? cmdlst)
        env        
          (let ([cmd (first cmdlst)])
            ;(printf "processing cmd: ~a~n" cmd)
            (cond [(policy? cmd)
                   (run-commands-helper (rest cmdlst) (cons cmd env))]
                  [(and (command? cmd) (equal? (command-name cmd) 'info))                   
                   (run-info env)
                   (run-commands-helper (rest cmdlst) env)]
                  [(and (command? cmd) (equal? (command-name cmd) 'compare))                   
                   (run-compare env (command-args cmd))
                   (run-commands-helper (rest cmdlst) env)]
                  [(and (command? cmd) (equal? (command-name cmd) 'query))                   
                   (run-query env (command-args cmd))
                   (run-commands-helper (rest cmdlst) env)]
                  [else
                   (raise (format "Undefined command made it through parser: ~a" cmd))]))))  
  (if (empty? cmdlst)
      ""
      (run-commands-helper cmdlst env)))

(define REQUEST-SKOLEM-RELATIONS '("reqS" "reqA" "reqR"))
(define REQUEST-ATOMS '(s$0 a$0 r$0))

; Return a list of unary relations, minus the Skolem relations, that this atom is a member of.
(define (unaries-in relhash at)
  (define pertinent-unaries (filter (lambda (x) (and (equal? #f (member (relation-name x) REQUEST-SKOLEM-RELATIONS))
                                                     (equal? 1 (relation-arity x))))
                                    (hash-values relations)))
  (filter-map (lambda (ur)
                (if (member (list at) (hash-ref relhash ur))
                    (relation-name ur)
                    #f))
              pertinent-unaries))

; Format a tuple prettily (concretely, turn atom names into variables where appropriate)
(define (pretty-format-tuple t)
  (map (lambda (a)
         (cond [(equal? a 's$0) '<s>]
               [(equal? a 'a$0) '<a>]
               [(equal? a 'r$0) '<r>]
               [else a])) t))

; Return a list of formatted statements about membership in binary relations.
; Say nothing about empty binary relations.
(define (format-binaries relhash)
  (define binaries (filter (lambda (x) (equal? 2 (relation-arity x)))
                           (hash-values relations)))
  (define allatoms (remove-duplicates (flatten (map (lambda (br) (hash-ref relhash br)) binaries))))
  (define extras (filter (lambda (a) (equal? #f (member a REQUEST-ATOMS))) allatoms))
  (define ground-atom-list
    (filter-map (lambda (br)
                  (if (empty? (hash-ref relhash br))
                      #f 
                      (map (lambda (tup)
                             (format "~a~a" (relation-name br) (pretty-format-tuple tup)))
                           (hash-ref relhash br))))
                binaries))
  (values
   extras
   (apply append ground-atom-list)))

; Print the result in a marginally readable way.
(define (pretty-format-scenario relhash)
  (define-values (extras binary-ground) (format-binaries relhash))
  (define formatted (lambda (x) (format "~a" x)))
  (define binary-ground-str (string-join (map formatted binary-ground) "\n  "))
  
  (format "-----------------------------------~nFound example request!~n<s>: ~a~n<a>: ~a~n<r>: ~a~n~a"
          (unaries-in relhash 's$0)
          (unaries-in relhash 'a$0)
          (unaries-in relhash 'r$0)
          (if (empty? binary-ground)
              ""
              (if (empty? extras)
                  (format "Also,~n  ~a~n" binary-ground-str)
                  (begin
                    (define extras-unary-str (string-join (map (lambda (a) (format "~a: ~a" a (unaries-in relhash a))) extras) "\n  "))
                    (format "Also, for some ~a,~n  ~a~n  ~a~n" extras extras-unary-str binary-ground-str))))))

(printf "ABAC Policy Analyzer...loaded!~n")


