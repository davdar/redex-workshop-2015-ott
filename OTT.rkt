#lang racket
(require redex
         rackunit
         (prefix-in racket: racket))

(define-language ITT
  (e ::= x
        (e e)
        (bind x b e)
        unit
        tt
        ★
        void
        two
        true
        false
        (if e e e e)
        (pair e e e e)
        (π1 e)
        (π2 e))
  (b ::= (λ e)
         (Π e)
         (Σ e))
  (x ::= variable-not-otherwise-mentioned))

(define-metafunction ITT
  ∪ : (x ...) ... -> (x ...)
  [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...)
   (∪ (x_1 ... x_2 ...) (x_3 ...) ...)]
  [(∪ (x_1 ...))
   (x_1 ...)]
  [(∪) ()])
 
(define-metafunction ITT
  - : (x ...) (x ...) -> (x ...)
  [(- (x ...) ()) (x ...)]
  [(- (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (- (x_1 ... x_3 ...) (x_2 x_4 ...))
   (side-condition (not (memq (term x_2) (term (x_3 ...)))))]
  [(- (x_1 ...) (x_2 x_3 ...))
   (- (x_1 ...) (x_3 ...))])

(module+ test
  (test-equal (term (α= (=> unit unit) (Vbind (Π unit) unit))) #t))

(define-metafunction ITT
  => : e e -> e
  [(=> e_1 e_2) (bind ,(variable-not-in (term e_2) 'arr_x) (Π e_1) e_2)])

(define-extended-language ITT-deBruijn ITT
  (e ::= .... (V n) (Vbind b e))
  (n ::= natural))

(define-metafunction ITT
  in : x (x ...) -> boolean
  [(in x (x_1 ... x x_2 ...)) #t]
  [(in x _) #f])

(module+ test
  (test-equal (term (resolve (bind x (λ unit) x)))
              (term (Vbind (λ unit) (V 0))))
  (test-equal (term (resolve (bind x (λ unit) (bind x (λ unit) x))))
              (term (Vbind (λ unit) (Vbind (λ unit) (V 0)))))
  (test-equal (term (resolve (pair (bind x (λ unit) x) tt tt tt)))
              (term (pair (Vbind (λ unit) (V 0)) tt tt tt))))

(define-metafunction ITT-deBruijn
  resolve/ctx-bind : b (x ...) -> b
  [(resolve/ctx-bind (λ e) (x ...)) (λ (resolve/ctx e (x ...)))]
  [(resolve/ctx-bind (Π e) (x ...)) (Π (resolve/ctx e (x ...)))])

(define-metafunction ITT-deBruijn
  resolve/ctx : e (x ...) -> e
  [(resolve/ctx x (x_1 ... x x_2 ...))
   (V n)
   (where n  ,(length (term (x_1 ...))))
   (where #f (in x (x_1 ...)))]
  [(resolve/ctx (e_1 e_2) (x ...))
   ((resolve/ctx e_1 (x ...)) (resolve/ctx e_2 (x ...)))]
  [(resolve/ctx (bind x_1 b e) (x_2 ...))
   (Vbind (resolve/ctx-bind b (x_2 ...)) (resolve/ctx e (x_1 x_2 ...)))]
  [(resolve/ctx (any e ...) (x ...))
   (any (resolve/ctx e (x ...)) ...)]
  [(resolve/ctx any (x ...)) any])

(define-metafunction ITT-deBruijn
  resolve : e -> e
  [(resolve e) (resolve/ctx e ())])

(define dapp (term (bind a (λ ★)
                     (bind P (λ (=> a ★))
                       (bind f (λ (bind x (Π a) (P x)))
                         (bind y (λ a)
                           (f y)))))))

(module+ test
  (test-equal (term (α= ,dapp
                        (bind b (λ ★)
                          (bind Q (λ (=> b ★))
                            (bind g (λ (bind x (Π b) (Q x)))
                              (bind y (λ b)
                                (g y)))))))
              #t))
                        
(define-metafunction ITT-deBruijn
  α= : e e -> boolean
  [(α= e_1 e_2) ,(equal? (term (resolve e_1)) (term (resolve e_2)))])

(module+ test
  (test-equal (term (free-vars ,dapp)) (term ()))
  (test-equal (term (free-vars x)) (term (x)))
  (test-equal (term (free-vars (bind x (λ unit) (x y)))) (term (y))))

(define-metafunction ITT
  free-vars-bind : b -> (x ...)
  [(free-vars-bind (λ e)) (free-vars e)]
  [(free-vars-bind (Π e)) (free-vars e)])

(define-metafunction ITT
  free-vars : e -> (x ...)
  [(free-vars x)
   (x)]
  [(free-vars (e_1 e_2))
   (∪ (free-vars e_1) (free-vars e_2))]
  [(free-vars (bind x b e))
   (∪ (- (free-vars e) (x)) (free-vars-bind b))]
  [(free-vars _) ()])

(module+ test
  (test-results))

;; ----------------------------------------------------------------------------------------------

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
  (test-equal (judgment-holds (is-type () unit)) #true)
  (test-equal (judgment-holds (is-type ()
                                       (resolve (=> unit unit))))
              #true)
  (test-equal (judgment-holds (is-type (★)
                                       (resolve/ctx (=> a a) (a))))
              #true))



(define-judgment-form ITT-deBruijn-C-Check
  #:mode (is-type I I)
  #:contract (is-type Γ e)
  [------------------- "unit is type"
   (is-type Γ unit)]
  [------------------- "★ is type"
   (is-type Γ ★)]
  [------------------- "void is type"
   (is-type Γ void)]
  [------------------- "bool is type"
   (is-type Γ two)]
  [(where ★ (lookup Γ n))
   ------------------- "var type"
   (is-type Γ (V n))]
  [(is-type (e_99 ...) e_1)
   (is-type (e_1 e_99 ...) e_2)
   ---------------------------- "pi-formation"
   (is-type (e_99 ...) (Vbind (Π e_1) e_2))]
  )

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
  [(is-type Γ e_1)
   (is-type Γ e_2)
   (where e_3 (normalize e_1))
   (where e_3 (normalize e_2))
   ----------------------------------- "α-equiv normal forms"
   (equal-types Γ e_1 e_2)]
)  