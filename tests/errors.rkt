#lang racket

(require emcsabac/runner
         emcsabac/lexparse
         rackunit
         rackunit/text-ui)

(define (parse-test polstr)
  (parse-single-command 'errors-tests (open-input-string polstr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parser-error-tests
  (test-suite
   "Tests for ABAC parser errors"
   
   ;; TODO: unrecognized relation name error?
   ;; TODO: permit/deny only decisions allowed
   ;; owner -> owns, better binary rel? but need a way to distinguish lex for ids and relations? or not?
   
   (check-exn #rx"A policy must be given a name." (lambda () (parse-test "policy permit if: true. end")))

   (check-exn #rx"Couldn't understand" (lambda () (parse-test "policy permit : true. end")))
   
   ))



