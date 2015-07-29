#lang racket
(require redex
         rackunit
         (prefix-in racket: racket))

(provide (all-defined-out))

;; ITT core language

(define-language ITT-core
  (e ::= (V n)
         (bind b e)
         (e e)
         ★
         unit
         tt
         void
         exfalso
         bool
         true
         false
         (if e e e e)
         (pair e e e e)
         (π1 e)
         (π2 e))
  (b ::= (lam e)
         (Pi e)
         (Sig e))
  (n ::= natural))

;; ITT source language, which desugars to ITT-core

(define-extended-language ITT ITT-core
  (e ::= ....
         x
        (λ x e e)
        (Π x e e)
        (Σ x e e))
  (x ::= variable-not-otherwise-mentioned))

;; helpers for sets of variables

(define-metafunction ITT
  in : x (x ...) -> boolean
  [(in x (x_1 ... x x_2 ...)) #t]
  [(in x _) #f])

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

;; lowering ITT to ITT-core

(define-metafunction ITT
  lower/ctx : (x ...) e -> e
  [(lower/ctx (x_c1 ... x x_c2 ...) x)
   (V n)
   (where n  ,(length (term (x_c1 ...))))
   (where #f (in x (x_c1 ...)))]
  [(lower/ctx (x_c ...) (λ x e_t e_b))
   (bind (lam (lower/ctx (x_c ...) e_t)) (lower/ctx (x x_c ...) e_b))]
  [(lower/ctx (x_c ...) (Π x e_t1 e_t2))
   (bind (Pi (lower/ctx (x_c ...) e_t1)) (lower/ctx (x x_c ...) e_t2))]
  [(lower/ctx (x_c ...) (Σ x e_t1 e_t2))
   (bind (Sig (lower/ctx (x_c ...) e_t1)) (lower/ctx (x x_c ...) e_t2))]
  [(lower/ctx (x ...) (V n)) (V n)]
  [(lower/ctx (x ...) (bind b e))
   (bind (lower/ctx-bind (x ...) b) (lower/ctx (x ...) e))]
  [(lower/ctx  (x ...) (e_1 e_2))
   ((lower/ctx (x ...) e_1) (lower/ctx (x ...) e_2 ))]
  [(lower/ctx (any e ...) (x ...))
   (any (lower/ctx e (x ...)) ...)]
  [(lower/ctx any (x ...)) any])

(define-metafunction ITT
  lower/ctx-bind : (x ...) b -> b
  [(lower/ctx-bind (x ...) (lam e))
   (lam (lower/ctx (x ...) e))]
  [(lower/ctx-bind (x ...) (Pi e))
   (Pi (lower/ctx (x ...) e))]
  [(lower/ctx-bind (x ...) (Sig e))
   (Sig (lower/ctx (x ...) e))])

(define-metafunction ITT
  lower : e -> e
  [(lower e) (lower/ctx () e)])

;; ITT source sugar helpers

(define-metafunction ITT
  => : e e -> e
  [(=> e_t1 e_t2) (Π ,(variable-not-in (term e_t2) 'arr_x) e_t1 e_t2)])

;; ITT source terms

(define (id-e e_t) (term (λ x ,e_t x)))
(define (id-t e_t) (term (=> ,e_t ,e_t)))

(module+ test
  ;; test '=>' sugar
  (test-equal (term (lower (=> unit unit)) (bind (pi unit) unit))
              #t)
  ;; test lower
  (test-equal (term (lower (λ x unit x)))
              (term (bind (lam unit) (V 0))))
  (test-equal (term (lower (λ x unit (λ x unit) x)))
              (term (bind (lam unit) (bind (lam unit) (V 0)))))
  (test-equal (term (lower (pair (λ x unit x) tt tt tt)))
              (term (pair (bind (lam unit) (V 0)) tt tt tt))))

;;--------------------------------------------------------------------------------------

;; stopped here -DCD
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

;;---------------------------------------------------------------------

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
  (test-results))