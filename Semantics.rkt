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
         (sigma C e)
         (sigma e C)
         (pair C e e e)
         (pair e C e e)
         (pair e e C e)
         (pair e e e C)
         (exfalso C e)
         (exfalso e C)
         (π1 C)
         (π2 C)
         (embed C)
         (coe C e e e)
         (coe e C e e)
         (coe e e C e)
         (coe e e e C)
         (: C e)
         (: e C))
  (b-C ::= (lam C)
           (Pi C)
           (forall C)))

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



(define-metafunction ITT-core
  bump-deBruijn : n e -> e
  [(bump-deBruijn n_threshold (V n))
   (V ,(if (>= (term n) (term n_threshold))
           (+ (term n) 1)
           (term n)))]
  [(bump-deBruijn n_threshold (bind b tm))
   (bind (bump-deBruijn-b n_threshold b)
         (bump-deBruijn ,(+ (term n_threshold) 1)
                        tm))]
  [(bump-deBruijn n_threshold (tm_f tm_x))
   ((bump-deBruijn n_threshold tm_f)
    (bump-deBruijn n_threshold tm_x))]
  [(bump-deBruijn n_threshold (embed prop))
   (embed (bump-deBruijn n_threshold prop))]
  [(bump-deBruijn n_threshold (any tm ...))
   (any (bump-deBruijn n_threshold tm) ...)]
  [(bump-deBruijn _ any) any])

(define-metafunction ITT-core
  bump-deBruijn-b : n b -> b
  [(bump-deBruijn-b n_threshold (any tm))
   (any (bump-deBruijn n_threshold tm))])


(define test-term-1
  (term ((λ (y (=> unit unit))
           (λ (x unit) (y x)))
         (λ (x unit) x))))

(define test-term-2
  (term ((λ (f (=> unit unit))
           ((λ (id (=> (=> unit unit) (=> unit unit))) id)
            f))
         (λ (x unit) x))))

(define not-bool
  (term (lower (λ (x bool)
                 (if (λ (y bool) bool)
                     x
                     false
                     true)))))

(module+ test
  (test--> -->β
           (term (lower ,test-term-1))
           (term (lower (λ (x unit) ((λ (x unit) x) x)))))
  (test-->> -->β
            (term (lower ,test-term-1))
            (term (bind (lam unit) (V 0))))
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
            (term (lower (π1 (pair bool (λ (x bool) unit) true tt))))
            (term (lower true)))
  (test-->> -->β
            (term (lower (π2 (pair bool (λ (x bool) unit) true tt))))
            (term (lower tt)))
  (test-->> -->β
            (term (lower (: true (: bool ★))))
            (term (lower true)))
  (test-->> -->β
            (term (embed (∧ ⊤ ⊥)))
            (term (sigma unit (bind (lam unit) void))))
  (test-->> -->β
            lam-void-coerce
            (term (bind (lam void) (V 0))))
  (test-->> -->β
            (term (lower (embed (= (=> bool bool)
                                   (=> bool bool)))))
            (term (lower (sigma unit
                                (λ (x unit)
                                  (Π (b1 bool)
                                     (Π (b2 bool)
                                        (Π (prf (≡ b1 bool b2 bool))
                                           unit))))))))
  (test-->> -->β
            (term (lower (embed (≡ (λ (x bool) (,not-bool (,not-bool x)))
                                   (=> bool bool)
                                   (λ (x bool) x)
                                   (=> bool bool)))))
            (term (lower (Π (x bool)
                            (Π (y bool)
                               (Π (eq-args (embed (≡ x bool
                                                     y bool)))
                                  (embed (≡ ((λ (x bool) (,not-bool (,not-bool x))) x)
                                            bool
                                            ((λ (x bool) x) y)
                                            bool))))))))
  )

(define-metafunction ITT-C
  =--> : val val -> prop
  [(=--> unit unit) ⊤]
  [(=--> void void) ⊤]
  [(=--> bool bool) ⊤]
  [(=--> (bind (Pi ty_1) ty_2)
         (bind (Pi ty_3) ty_4))
   (∧ (= ty_3 ty_1)
      (bind (forall ty_3)
            (bind (forall ty_1)
                  (bind (forall (≡ (V 1) ty_3 (V 0) ty_1))
                        (= (instantiate (V 0) ty_2)
                           (instantiate (V 1) ty_4))))))]
                        
  [(=--> _ _) ⊥])

;;; Here, we don't assume canonicity of anything, and we check for it explicitly at
;;; the end of the pattern match
(define-metafunction ITT-C
  ≡--> : tm tm tm tm -> prop or stuck
  [(≡--> _ void _ void) ⊤]
  [(≡--> _ unit _ unit) ⊤]
  [(≡--> true bool true bool) ⊤]
  [(≡--> true bool false bool) ⊥]
  [(≡--> false bool true bool) ⊥]
  [(≡--> false bool false bool) ⊤]
  [(≡--> _ bool _ bool) stuck]
  [(≡--> tm_f1 (bind (Pi ty_1a) ty_1b)
         tm_f2 (bind (Pi ty_2a) ty_2b))
   (bind (forall ty_1a)
         (bind (forall ty_2a)
               (bind (forall (embed (≡ (V 1) ty_1a (V 0) ty_2a)))
                     (≡ (tm_f1 (V 2)) (instantiate (V 2) ty_1b)
                        (tm_f2 (V 1)) (instantiate (V 1) ty_2b)))))]
  [(≡--> _ val_1 _ val_2) ⊥]
  [(≡--> _ _ _ _)
    stuck]
  )

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
   (--> (in-hole C (π1 (pair _ _ tm _)))
        (in-hole C tm)
        β-pair-π1)
   (--> (in-hole C (π2 (pair _ _ _ tm)))
        (in-hole C tm)
        β-pair-π2)
   ;; OTT stuff
   (--> (in-hole C (embed ⊤))
          (in-hole C unit)
          β-prop-⊤)
   (--> (in-hole C (embed ⊥))
        (in-hole C void)
        β-prop-⊥)
   (--> (in-hole C (embed (∧ prop_1 prop_2)))
        (in-hole C (sigma (embed prop_1)
                          (bind (lam (embed prop_1))
                                (bump-deBruijn 0 (embed prop_2)))))                           
        β-prop-∧)
   (--> (in-hole C (embed (bind (forall ty) prop)))
        (in-hole C (bind (Pi ty) (embed prop)))
        β-prop-∀)
   (--> (in-hole C (coe tm _ _ _))
        (in-hole C tm)
        β-coe-does-nothing)
   ;; Prop computations at equality types
   (--> (in-hole C (embed (= val_1 val_2)))
        (in-hole C (embed prop_out))
        (where prop_out (=--> val_1 val_2))
        β-=)
   (--> (in-hole C (embed (≡ tm_1 ty_1 tm_2 ty_2)))
        (in-hole C (embed prop_out))
        (where prop_out (≡--> tm_1 ty_1 tm_2 ty_2)))
   ;; BiDi stuff
   (--> (in-hole C (: e _))
        (in-hole C e)
        β-strip-:)))


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