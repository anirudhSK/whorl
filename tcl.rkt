#lang racket

(provide ! && || <=> define-circuit verify-circuit
         #%datum #%app #%module-begin #%top-interaction)

(define-syntax-rule (define-circuit (id in ...) expr)
  (define (id in ...) expr))

(define (verify-circuit impl spec)
  (define n (procedure-arity spec))
  (for ([i (expt 2 n)])
    (define bits (for/list ([j n]) (bitwise-bit-set? i j)))
    (unless (eq? (apply impl bits) (apply spec bits))
      (error "verification failed on" bits))))

(define (! a) (if a #f #t))
(define (&& a b) (if a b #f))
(define (|| a b) (if a #t b))
(define (<=> a b) (if a b (! b)))

(define-circuit (xor x y) (! (<=> x y)))

(define-circuit (RBC-parity a b c d)
  (xor (<=> a b) (<=> c d)))

(define-circuit (AIG-parity a b c d)
  (&&
  (! (&& (! (&& (! (&& a b)) (&& (! a) (! b))))
         (! (&& (&& (! c) (! d)) (! (&& c d))))))
  (! (&& (&& (! (&& a b)) (! (&& (! a) (! b))))
         (&& (! (&& (! c) (! d))) (! (&& c d)))))))

(verify-circuit AIG-parity RBC-parity)
