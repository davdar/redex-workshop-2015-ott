#lang racket
(require redex
         rackunit
         (prefix-in racket: racket)
         "Syntax.rkt"
         "Semantics.rkt")

(provide (all-defined-out))

(define-extended-language ITT-deBruijn-C-Check ITT-deBruijn-C
  (Γ ::= (e ...)))

(module+ test
  (test-equal (term (lookup (★ unit) 1)) (term unit))
  (test-exn "empty context not allowed!"
            (lambda (_) #t)
            (lambda () (term (lookup () 3)))))

(define-metafunction ITT-deBruijn-C-Check
  lookup : Γ n -> e
  [(lookup (e_1 e_2 ...) 0) e_1]
  [(lookup (e_1 e_2 ...) n) (lookup (e_2 ...) ,(racket:- (term n) 1))])

(module+ test
  (test-equal (judgment-holds (infer-type () unit ★)) #true)
  (test-equal (judgment-holds (infer-type ()
                                        (resolve (=> unit unit))
                                        ★))
              #true)
  (test-equal (judgment-holds (infer-type (★)
                                       (resolve/ctx (=> a a) (a))
                                       ★))
              #true)
  (test-equal (judgment-holds (infer-type ()
                                        (resolve (bind x (λ unit) bool))
                                        (Vbind (Π unit) ★)))
              #true)
  (test-equal (judgment-holds (check-type ()
                                        (resolve (bind x (λ unit) bool))
                                        ((Vbind (λ ★) (V 0)) (Vbind (Π unit) ★))))
              #true)
  #;(current-traced-metafunctions 'all)
  #;(current-traced-metafunctions '()))

(define-judgment-form ITT-deBruijn-C-Check
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
  [(where e_t (lookup Γ n))
   ------------------- "var has type from Γ"
   (infer-type Γ (V n) e_t)]
  [(infer-type (e_Γ ...) e_1 ★)
   (infer-type (e_1 e_Γ ...) e_2 ★)
   ---------------------------- "pi-formation"
   (infer-type (e_Γ ...) (Vbind (Π e_1) e_2) ★)]
  [(infer-type (e_Γ ...) e_1 ★)
   (infer-type (e_1 e_Γ ...) e_2 e_2t)
   ---------------------------- "pi-intro"
   (infer-type (e_Γ ...) (Vbind (λ e_1) e_2) (Vbind (Π e_1) e_2t))]
  [(infer-type Γ e_f (Vbind (Π e_xt) e_body))
   (infer-type Γ e_x e_xt)
   ---------------------------- "pi-elim"
   (infer-type Γ (e_f e_x) (instantiate e_x e_body))]
  )

(define-judgment-form ITT-deBruijn-C-Check
  #:mode (check-type I I I)
  #:contract (check-type Γ e e)
  [(infer-type Γ e_1 e_t1)
   (equal-types Γ e_t1 e_t2)
   ---------------------------- "conversion"
   (check-type Γ e_1 e_t2)])
   
(module+ test
  (test-equal (judgment-holds (equal-types () unit unit)) #true)
  (test-equal (judgment-holds (equal-types (★)
                                           (resolve/ctx (=> a a) (a))
                                           (resolve/ctx ((bind x (λ ★) x)
                                                         (=> a a))
                                                        (a))))
                              #true))

(define-judgment-form ITT-deBruijn-C-Check
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