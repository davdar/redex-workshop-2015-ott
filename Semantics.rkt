#lang racket
(require redex
         rackunit
         (prefix-in racket: racket)
         "Syntax.rkt")

(provide (all-defined-out))

(define-extended-language ITT-C ITT-core
  (C ::= hole
         (C e)
         (e C)
         (bind b-C e)
         (bind b C)
         (if C e e e)
         (if e C e e)
         (if e e C e)
         (if e e e C)
         (pair C e)
         (pair e C)
         (exfalso C e)
         (exfalso e C)
         (π1 C)
         (π2 C))
  (b-C ::= (lam C)
           (Pi C)
           (Sig C)))

(module+ test
  (test-equal (term (instantiate unit (V 0))) (term unit))
  (test-equal (term (instantiate/n 1
                      (bind (Pi unit) unit)
                      (bind (lam ★) (V 2))))
              (term (bind (lam ★) (bind (Pi unit) unit))))
  (test-equal (term (instantiate
                      (lower (λ (x unit) x))
                      (lower (λ (x unit) ((V 1) x)))))
              (term (lower (λ (z unit) ((λ (z unit) z) z))))))

(define-metafunction ITT-core
  instantiate/n : n e e -> e
  [(instantiate/n n e_1 (V n)) e_1]
  [(instantiate/n n_1 e_1 (V n_2))
   (V ,(if (> (term n_2) (term n_1))
         (racket:- (term n_2) 1)
         (term n_2)))]
  [(instantiate/n n e_1 (e_2 e_3))
   ((instantiate/n n e_1 e_2) (instantiate/n n e_1 e_3))]
  [(instantiate/n n e_1 (bind b e_2))
   (bind (instantiate/n-bind n e_1 b)
         (instantiate/n ,(+ (term n) 1) e_1 e_2))]
  [(instantiate/n n e_1 (any e_2 ...))
   (any (instantiate/n n e_1 e_2) ...)]
  [(instantiate/n n e_1 any) any])

(define-metafunction ITT-core
  instantiate/n-bind : n e b -> b
  [(instantiate/n-bind n e_1 (lam e_2)) (lam (instantiate/n n e_1 e_2))]
  [(instantiate/n-bind n e_1 (Pi e_2)) (Pi (instantiate/n n e_1 e_2))]
  [(instantiate/n-bind n e_1 (Sig e_2)) (Sig (instantiate/n n e_1 e_2))])

(define-metafunction ITT-core
  instantiate : e e -> e
  [(instantiate e_1 e_2) (instantiate/n 0 e_1 e_2)])

(define test-term-1
  (term ((λ (y (=> unit unit))
           (λ (x unit) (y x)))
         (λ (x unit) x))))

(define test-term-2
  (term ((λ (f (=> unit unit))
           ((λ (id (=> (=> unit unit) (=> unit unit))) id)
            f))
         (λ (x unit) x))))

(module+ test
  (test--> -->β
           (term (lower ,test-term-1))
           (term (lower (λ (x unit) ((λ (x unit) x) x)))))
  (test-->> -->β
            (term (lower ,test-term-1))
            (term (lower
                   (λ (x unit) x))))
  (test-->> -->β
            (term (lower (if (λ (x bool) bool) true false true)))
            (term (lower false)))
  (test-->> -->β
            (term (lower (if (λ (x bool) bool) false false true)))
            (term (lower true)))
  (test-->> -->β
            (term (lower ((λ (x bool)
                            (if (λ (x bool) bool) x false true))
                          false)))
            (term (lower true)))
  (test-->> -->β
            (term (lower (π1 (pair true tt))))
            (term (lower true)))
  (test-->> -->β
            (term (lower (π2 (pair true tt))))
            (term (lower tt))))

(define -->β
  (reduction-relation
   ITT-C
   (--> (in-hole C ((bind (lam ty) tm_body) tm_arg))
        (in-hole C (instantiate tm_arg tm_body))
        β)
   (--> (in-hole C (if _ true tm_t tm_f))
        (in-hole C tm_t)
        β-if-true)
   (--> (in-hole C (if _ false tm_t tm_f))
        (in-hole C tm_f)
        β-if-false)
   (--> (in-hole C (π1 (pair tm _)))
        (in-hole C tm)
        β-pair-π1)
   (--> (in-hole C (π2 (pair _ tm)))
        (in-hole C tm)
        β-pair-π2)))
   

#;
(traces -->β (term (lower ,test-term-1)))

#;
(traces -->β (term (lower ,test-term-2)))

(define-metafunction ITT-C
  normalize : e -> e
  [(normalize e) e_1
   (where (e_1) ,(apply-reduction-relation* -->β (term e)))])

(module+ test
  (test-results))