#lang racket
(require redex
         rackunit
         (prefix-in racket: racket)
         "Syntax.rkt"
         "Semantics.rkt")

(provide (all-defined-out))


(define not-not-equals-id-ty
    (term (lower (embed (≡ (λ (x bool) (,not-bool (,not-bool x)))
                           (=> bool bool)
                           (λ (x bool) x)
                           (=> bool bool))))))

(define-extended-language ITT-C-Check ITT-C
  (Γ ::= (e ...)))

(module+ test
  (test-equal (term (lookup (★ unit) 1)) (term unit))
  (test-exn "empty context not allowed!"
            (lambda (_) #t)
            (lambda () (term (lookup () 3)))))

(define-metafunction ITT-C-Check
  lookup : Γ n -> e
  [(lookup (e_1 e_2 ...) 0) e_1]
  [(lookup (e_1 e_2 ...) n) (lookup (e_2 ...) ,(racket:- (term n) 1))])

(module+ test
  (test-equal (judgment-holds (infer-type () unit ★)) #true)
  (test-equal (judgment-holds (infer-type ()
                                          (lower (=> unit unit))
                                          ★))
              #true)
  (test-equal (judgment-holds (infer-type (★)
                                       (lower/ctx (a) (=> a a))
                                       ★))
              #true)
  (test-equal (judgment-holds (infer-type ()
                                        (lower (λ (x unit) bool))
                                        (bind (Pi unit) ★)))
              #true)
  (test-equal (judgment-holds (check-type ()
                                        (lower (λ (x unit) bool))
                                        ((bind (lam ★) (V 0))
                                         (bind (Pi unit) ★))))
              #true)
  (test-equal (judgment-holds (check-type (void)
                                          (lower/ctx (nope)
                                                     (exfalso unit nope))
                                          unit))
              #true)
  (test-equal (judgment-holds (check-type ()
                                          (lower (Σ (x bool) bool))
                                          ★))
              #true)
  (current-traced-metafunctions '())
  (test-equal (judgment-holds (check-type (bool)
                                          (if (bind (lam bool) ★)
                                              (V 0)
                                              unit bool)
                                          ★))
              #t)
  
  (test-equal (judgment-holds (check-type ()
                                          (lower (Σ (x bool)
                                                    (if (λ (y bool) ★)
                                                        x
                                                        unit
                                                        bool)))
                                          ★))
              #true)
  (current-traced-metafunctions '())

  (test-equal (judgment-holds (check-type ()
                                          (lower (pair bool
                                                       (λ (x bool)
                                                         (if (λ (y bool) ★)
                                                             x
                                                             unit
                                                             bool))
                                                       true tt))
                                          (lower (Σ (x bool)
                                                    (if (λ (y bool) ★)
                                                        x
                                                        unit
                                                        bool)))))
              #true)
  (current-traced-metafunctions '())
  (test-equal (judgment-holds (check-type ()
                                          (lower
                                           (pair bool
                                                (λ (x bool)
                                                  (if (λ (y bool) ★)
                                                        x
                                                        unit
                                                        bool))
                                                false true))
                                          (lower (Σ (x bool)
                                                    (if (λ (y bool) ★)
                                                        x
                                                        unit
                                                        bool)))))
              #true)
  (test-equal (judgment-holds (check-type ()
                                          (lower (π1 (pair bool (λ (x bool) bool) true false)))
                                          bool))
              #true)
  (test-equal (judgment-holds (check-type ()
                                          (lower (π2 (pair bool
                                                           (λ (x bool)
                                                             (if (λ (y bool)
                                                                   ★)
                                                                 x
                                                                 bool
                                                                 unit))
                                                           true
                                                           false)))
                                          bool))
              #true)
  (test-equal (judgment-holds (is-prop () (∧ (= unit unit) (= unit bool))))
              #t)
  
  (test-equal (judgment-holds (check-type () (coe tt unit tt unit) unit)) #t)
            
  (test-equal (judgment-holds (check-type ()
                                          ,lam-void-coerce
                                          (lower (=> void void))))
              #t)
  (current-traced-metafunctions '())
  #;(current-traced-metafunctions 'all)
  #;(current-traced-metafunctions '())
  
  #;(current-traced-metafunctions 'all)
  (test-equal (judgment-holds (check-type ()
                                          ,not-not-equals-id-ty
                                          ★))
              #t)
  (current-traced-metafunctions 'all)
  #;(test-equal (judgment-holds (check-type ()
                                          (lower (λ (x bool)
                                                   (λ (y bool)
                                                     tt)))
                                          ,not-not-equals-id-ty))
              #t)
  (current-traced-metafunctions '())
                                          
)

(define-judgment-form ITT-C-Check
  #:mode (is-prop I I)
  #:contract (is-prop Γ prop)
  [------------------ "top-prop"
   (is-prop Γ ⊤)]
  [------------------ "bot-prop"
   (is-prop Γ ⊥)]
  [(is-prop Γ prop_1)
   (is-prop Γ prop_2)
   ------------------ "conj-prop"
   (is-prop Γ (∧ prop_1 prop_2))]
  [(check-type (ty_Γ ...) ty ★)
   (is-prop (ty ty_Γ ...) prop)
   ---------------------------- "forall-prop"
   (is-prop (ty_Γ ...) (bind (∀ ty) prop))]
  [(check-type Γ ty_1 ★)
   (check-type Γ ty_2 ★)
   ---------------------------- "=-f"
   (is-prop Γ (= ty_1 ty_2))]
  [(check-type Γ tm_1 ty_1)
   (check-type Γ tm_2 ty_2)
   ------------------------ "≡-f"
   (is-prop Γ (≡ tm_1 ty_1 tm_2 ty_2))])

(define-judgment-form ITT-C-Check
  #:mode (infer-type I I O)
  #:contract (infer-type Γ e e)
  [------------------- "★ is type"
   (infer-type Γ ★ ★)]
  [------------------- "unit is type"
   (infer-type Γ unit ★)]
  [----------------------- "tt has type unit"
   (infer-type Γ tt unit)]
  [------------------- "void is type"
   (infer-type Γ void ★)]
  [------------------- "bool is type"
   (infer-type Γ bool ★)]
  [----------------------- "true has type bool"
   (infer-type Γ true bool)]  
  [----------------------- "false has type bool"
   (infer-type Γ false bool)]
  [(check-type Γ ty_fam (bind (Pi bool) ★))
   (check-type Γ tm_b bool)
   (check-type Γ tm_t (ty_fam true))
   (check-type Γ tm_f (ty_fam false))
   --------------------------------- "bool elim"
   (infer-type Γ (if ty_fam tm_b tm_t tm_f) (ty_fam tm_b))]
  [(where ty (lookup Γ n))
   ------------------- "var has type from Γ"
   (infer-type Γ (V n) ty)]
  [(check-type (e_Γ ...) ty_1 ★)
   (check-type (ty_1 e_Γ ...) ty_2 ★)
   ---------------------------- "pi-formation"
   (infer-type (e_Γ ...) (bind (Pi ty_1) ty_2) ★)]
  [(check-type (e_Γ ...) ty_1 ★)
   (infer-type (ty_1 e_Γ ...) tm_2 ty_2)
   ---------------------------- "pi-intro"
   (infer-type (e_Γ ...)
               (bind (lam ty_1) tm_2)
               (bind (Pi ty_1) ty_2))]
  [(infer-type Γ e_f (bind (Pi e_xt) e_body))
   (check-type Γ e_x e_xt)
   ---------------------------- "pi-elim"
   (infer-type Γ (e_f e_x) (instantiate e_x e_body))]
  [----------------------------- "void-formation"
   (infer-type Γ void ★)]
  [(check-type Γ ty ★)
   (check-type Γ tm_yikes void)
   ---------------------------------------- "void-elim"
   (infer-type Γ (exfalso ty tm_yikes) ty)]
  [(check-type Γ ty_fst ★)
   (check-type Γ ty_snd (bind (Pi ty_fst) ★))
   ------------------------------------------ "Σ-formation"
   (infer-type Γ
               (sigma ty_fst ty_snd)
               ★)]
  [(check-type Γ tm_fst ty_fst)
   (check-type Γ tm_snd (ty_snd tm_fst))
   (check-type Γ (sigma ty_fst ty_snd) ★)
   ------------------------------------------------- "Σ-introduction"
   (infer-type Γ
               (pair ty_fst ty_snd tm_fst tm_snd)
               (sigma ty_fst ty_snd))]
  [(infer-type Γ tm (sigma ty_fst ty_snd))
   -------------------------------------------- "fst"
   (infer-type Γ (π1 tm) ty_fst)]
  [(infer-type Γ tm (sigma ty_fst ty_snd))
   -------------------------------------------- "snd"
   (infer-type Γ (π2 tm) (ty_snd (π1 tm)))]
  [(is-prop Γ prop)
   ---------------- "embed-ty"
   (infer-type Γ (embed prop) ★)]
  [(check-type Γ tm_s ty_S)
   (check-type Γ tm_Q (embed (= ty_S ty_T)))
   ---------------------------------------- "coercion"
   (infer-type Γ (coe tm_s ty_S tm_Q ty_T) ty_T)]
  [(check-type Γ tm ty)
   -------------------- "mode-switch"
   (infer-type Γ (: tm ty) ty)]
  )

(define-judgment-form ITT-C-Check
  #:mode (check-type I I I)
  #:contract (check-type Γ e e)
  [(infer-type Γ e_1 e_t1)
   (equal-types Γ e_t1 e_t2)
   ---------------------------- "conversion"
   (check-type Γ e_1 e_t2)]
  

  [(check-type Γ tm_Q (embed (= ty_S ty_T)))
   (check-type Γ tm_s ty_S)
   ---------------------------------------- "reflexivity"
   (check-type Γ
               (refl tm_s tm_Q)
               (embed (≡ tm_s ty_S
                         (coe tm_s tm_Q) ty_T)))]
 )
   
(module+ test
  (test-equal (judgment-holds (equal-types () unit unit)) #true)
  (test-equal (judgment-holds (equal-types (★)
                                           (lower/ctx (a) (=> a a))
                                           (lower/ctx (a)
                                                      ((λ (x ★) x)
                                                       (=> a a)))))
                              #true))

(define-judgment-form ITT-C-Check
  #:mode (equal-types I I I)
  #:contract (equal-types Γ e e)
  [(where e_1n (normalize e_1))
   (where e_2n (normalize e_2))
   (infer-type Γ e_1n ★)
   (infer-type Γ e_2n ★)
   (where e_3 e_1n)
   (where e_3 e_2n)
   ----------------------------------- "α-equiv normal forms"
   (equal-types Γ e_1 e_2)])

(module+ test
  (test-results))