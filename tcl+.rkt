#lang s-exp rosette

(require rosette/lib/render rosette/lib/synthax rosette/query/debug)

(provide (all-defined-out) ! && || <=> define/debug
         #%datum #%app #%module-begin #%top-interaction
         quote (for-syntax #%datum))
(define-syntax-rule (define-circuit (id in ...) expr)
  (define (id in ...) expr))

(define (dynamic-choose)
  (define-symbolic* v boolean?)
  v)

(define (symbolic-input spec)
  (for/list ([i (procedure-arity spec)]) (dynamic-choose)))

(define (correct impl spec input)
  (assert (eq? (apply impl input) (apply spec input))))

(define (verify-circuit impl spec)
  (define input (symbolic-input spec))
  (evaluate input (verify (correct impl spec input))))

(define (debug-circuit impl spec input)
  (render (debug [boolean?] (correct impl spec input))))

(define (solve-circuit impl spec inputs)
  (solve (for ([input inputs]) (correct impl spec input))))

(define (synthesize-circuit impl spec)
  (define input (symbolic-input spec))
  (generate-forms
    (synthesize #:forall input #:guarantee (correct impl spec input))))

(define-synthax (nnf x y depth)
 #:base (choose x (! x) y (! y))
 #:else (choose
         x (! x) y (! y)
         ((choose && ||) (nnf x y (- depth 1))
                         (nnf x y (- depth 1)))))

(define-circuit (xor x y) (! (<=> x y)))

(define-circuit (RBC-parity a b c d)
  (xor (<=> a b) (<=> c d)))

(define/debug (AIG-parity a b c d)
  (&&
  (! (&& (! (&& (! (&& a b)) (&& (! a) (! b))))
         (! (&& (&& (! c) (! d)) (! (&& c d))))))
  (! (&& (&& (! (&& a b)) (! (&& (! a) (! b))))
         (&& (! (&& (! c) (! d))) (! (&& c d)))))))

(verify-circuit AIG-parity RBC-parity)
