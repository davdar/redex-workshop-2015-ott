#lang racket
(require redex
         rackunit
         (prefix-in racket: racket)
         "Syntax.rkt")

(provide (all-defined-out))

(define-extended-language ITT-deBruijn-C ITT-deBruijn
  (C ::= hole
         (C e)
         (e C)
         (Vbind b-C e)
         (Vbind b C)
         (if C e e e)
         (if e C e e)
         (if e e C e)
         (if e e e C)
         (pair C e e e)
         (pair e C e e)
         (pair e e C e)
         (pair e e e C)
         (π1 C)
         (π2 C))
  (b-C ::= (λ C)
           (Π C)
           (Σ C)))

(module+ test
  (test-equal (term (instantiate unit (V 0))) (term unit))
  (test-equal (term (instantiate/n 1
                      (Vbind (Π unit) unit)
                      (Vbind (λ ★) (V 2))))
              (term (Vbind (λ ★) (Vbind (Π unit) unit))))
  (test-equal (term (instantiate
                      (resolve (bind x (λ unit) x))
                      (resolve (bind x (λ unit) ((V 1) x)))))
              (term (resolve (bind z (λ unit) ((bind z (λ unit) z) z))))))

(define-metafunction ITT-deBruijn
  instantiate/n : n e e -> e
  [(instantiate/n n e_1 (V n)) e_1]
  [(instantiate/n n_1 e_1 (V n_2))
   (V ,(if (> (term n_2) (term n_1))
         (racket:- (term n_2) 1)
         (term n_2)))]
  [(instantiate/n n e_1 (e_2 e_3))
   ((instantiate/n n e_1 e_2) (instantiate/n n e_1 e_3))]
  [(instantiate/n n e_1 (Vbind b e_2))
   (Vbind (instantiate/n-bind n e_1 b)
          (instantiate/n ,(+ (term n) 1) e_1 e_2))]
  [(instantiate/n n e_1 (any e_2 ...))
   (any (instantiate/n n e_1 e_2) ...)]
  [(instantiate/n n e_1 any) any])

(define-metafunction ITT-deBruijn
  instantiate/n-bind : n e b -> b
  [(instantiate/n-bind n e_1 (λ e_2)) (λ (instantiate/n n e_1 e_2))]
  [(instantiate/n-bind n e_1 (Π e_2)) (Π (instantiate/n n e_1 e_2))]
  [(instantiate/n-bind n e_1 (Σ e_2)) (Σ (instantiate/n n e_1 e_2))])

(define-metafunction ITT-deBruijn
  instantiate : e e -> e
  [(instantiate e_1 e_2) (instantiate/n 0 e_1 e_2)])

(define test-term-1
  (term ((bind y (λ (=> unit unit)) (bind x (λ unit) (y x)))
         (bind x (λ unit) x))))

(define test-term-2
  (term ((bind f (λ (=> unit unit))
               ((bind id (λ (=> (=> unit unit) (=> unit unit))) id)
                f))
         (bind x (λ unit) x))))

(module+ test
  (test--> -->β
           (term (resolve ,test-term-1))
           (term (resolve (bind x (λ unit) ((bind x (λ unit) x) x)))))
  (test-->> -->β
            (term (resolve ,test-term-1))
            (term (resolve
                   (bind x (λ unit) x)))))

(define -->β
  (reduction-relation
   ITT-deBruijn-C
   (--> (in-hole C ((Vbind (λ e_1) e_2) e_3))
        (in-hole C (instantiate e_3 e_2))
        β)))

#;
(traces -->β (term (resolve ,test-term-1)))

#;
(traces -->β (term (resolve ,test-term-2)))

(define-metafunction ITT-deBruijn-C
  normalize : e -> e
  [(normalize e) e_1
   (where (e_1) ,(apply-reduction-relation* -->β (term e)))])

(module+ test
  (test-results))