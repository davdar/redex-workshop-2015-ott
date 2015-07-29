#lang racket
(require redex
         rackunit
         (prefix-in racket: racket)
         "Syntax.rkt"
         "Semantics.rkt")

(provide (all-defined-out))

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
  #;(current-traced-metafunctions 'all)
  #;(current-traced-metafunctions '()))

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
   (infer-type Γ e_x e_xt)
   ---------------------------- "pi-elim"
   (infer-type Γ (e_f e_x) (instantiate e_x e_body))]
  [----------------------------- "void-formation"
   (infer-type Γ void ★)]
  [(check-type Γ ty ★)
   (check-type Γ tm_yikes void)
   ---------------------------------------- "void-elim"
   (infer-type Γ (exfalso ty tm_yikes) ty)]
  )

(define-judgment-form ITT-C-Check
  #:mode (check-type I I I)
  #:contract (check-type Γ e e)
  [(infer-type Γ e_1 e_t1)
   (equal-types Γ e_t1 e_t2)
   ---------------------------- "conversion"
   (check-type Γ e_1 e_t2)])
   
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