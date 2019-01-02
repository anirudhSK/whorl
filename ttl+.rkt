#lang s-exp rosette

(require rosette/lib/render rosette/lib/synthax rosette/query/debug)
(require pict)

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

(define core
  (debug [boolean?]
         (assert (eq? (AIG-parity #t #t #t #f)
                      (RBC-parity #t #t #t #f)))))
(render core)
(show-pict (render core) 10 10)

(struct circuit () #:transparent)
(struct And circuit (left right))
(struct Or circuit (left right))
(struct Iff circuit (left right))
(struct Not circuit (left))

(define (interpret ast)
  (match ast
    [(And l r) (&& (interpret l) (interpret r))]
    [(Or l r) (|| (interpret l) (interpret r))]
    [(Iff l r) (<=> (interpret l) (interpret r))]
    [(Not l) (! (interpret l))]
    [_ ast]))

(define (correct-xform xform ast)
  (assert (eq? (interpret ast) (interpret (xform ast)))))

(define (verify-transform xform circ)
  (define input (symbolic-input circ))
  (define ast (apply circ input))
  (define cex (verify (correct-xform xform ast)))
  (values (evaluate input cex) (generate-forms cex)))

(define (synthesize-transform xform circ)
  (define ast (apply circ (symbolic-input circ)))
  (generate-forms
    (synthesize #:forall (symbolics ast)
    #:guarantee (correct-xform xform ast))))
