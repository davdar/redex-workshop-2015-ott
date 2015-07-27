#lang racket
(require redex)

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
  (test-equal (term (resolve (bind x (λ unit) x) ()))
              (term (Vbind (λ unit) (V 0))))
  (test-equal (term (resolve (bind x (λ unit) (bind x (λ unit) x)) ()))
              (term (Vbind (λ unit) (Vbind (λ unit) (V 0)))))
  (test-equal (term (resolve (pair (bind x (λ unit) x) tt tt tt) ()))
              (term (pair (Vbind (λ unit) (V 0)) tt tt tt))))

(define-metafunction ITT-deBruijn
  resolve-bind : b (x ...) -> b
  [(resolve-bind (λ e) (x ...)) (λ (resolve e (x ...)))]
  [(resolve-bind (Π e) (x ...)) (Π (resolve e (x ...)))])

(define-metafunction ITT-deBruijn
  resolve : e (x ...) -> e
  [(resolve x (x_1 ... x x_2 ...))
   (V n)
   (where n  ,(length (term (x_1 ...))))
   (where #f (in x (x_1 ...)))]
  [(resolve (e_1 e_2) (x ...))
   ((resolve e_1 (x ...)) (resolve e_2 (x ...)))]
  [(resolve (bind x_1 b e) (x_2 ...))
   (Vbind (resolve-bind b (x_2 ...)) (resolve e (x_1 x_2 ...)))]
  [(resolve (any e ...) (x ...))
   (any (resolve e (x ...)) ...)]
  [(resolve any (x ...)) any])

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
  [(α= e_1 e_2) ,(equal? (term (resolve e_1 ())) (term (resolve e_2 ())))])

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