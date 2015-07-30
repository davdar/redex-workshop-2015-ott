#lang racket
(require redex
         rackunit
         (prefix-in racket: racket))

(provide (all-defined-out))

;; ITT core language

(define-language ITT-core
  (e tm ty ::= (V n)
               (bind b e)
               (e e)
               ★
               unit
               tt
               void
               (exfalso ty tm)
               bool
               true
               false
               (if e e e e)
               (pair e e)
               (π1 e)
               (π2 e))
  (b ::= (lam ty)
         (Pi ty)
         (Sig ty))
  (n ::= natural))

;; ITT source language, which desugars to ITT-core

(define-extended-language ITT ITT-core
  (e ::= ....
         x
        (λ (x ty) tm)
        (Π (x ty) tm)
        (Σ (x ty) tm))
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
  [(lower/ctx (x_c ...) (λ (x ty) e_b))
   (bind (lam (lower/ctx (x_c ...) ty))
         (lower/ctx (x x_c ...) e_b))]
  [(lower/ctx (x_c ...) (Π (x e_t1) e_t2))
   (bind (Pi (lower/ctx (x_c ...) e_t1))
         (lower/ctx (x x_c ...) e_t2))]
  [(lower/ctx (x_c ...) (Σ (x e_t1) e_t2))
   (bind (Sig (lower/ctx (x_c ...) e_t1))
         (lower/ctx (x x_c ...) e_t2))]
  [(lower/ctx (x ...) (V n)) (V n)]
  [(lower/ctx (x ...) (bind b e))
   (bind (lower/ctx-bind (x ...) b)
         (lower/ctx (x ...) e))]
  [(lower/ctx  (x ...) (e_1 e_2))
   ((lower/ctx (x ...) e_1) (lower/ctx (x ...) e_2 ))]
  [(lower/ctx (x ...) (any e ...))
   (any (lower/ctx (x ...) e) ...)]
  [(lower/ctx (x ...) any) any])

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

;; Free variables and closing them

#|
(define-metafunction ITT
  free-vars : e -> (x ...)
  [(free-vars x) (x)

(define-metafunction Lambda
  close : any any -> any
  [(close any_1 any_2)
   (let ([x any_2] ...) any_1)
   (where (x ...) (fv any_1))])

; Stolen from Matthias
(define ((close-over-fv-with lambda?) e
         #:init (i (term (lambda (x) x))))
  ; this is to work around a bug in redex-check; doesn't always work
  (if (lambda? e) (term (close ,e ,i)) i))

|#

;; ITT source sugar helpers

(define-metafunction ITT
  => : e e -> e
  [(=> ty_1 ty_2)
   (Π (,(variable-not-in (term ty_2) 'arr_x) ty_1) ty_2)])

;; ITT source terms

(define (id-e e_t) (term (λ (x ,e_t) x)))
(define (id-t e_t) (term (=> ,e_t ,e_t)))

(module+ test
  ;; test '=>' sugar
  (test-equal (term (lower (=> unit unit))) (term (bind (Pi unit) unit)))
  ;; test lower
  (test-equal (term (lower (λ (x unit) x)))
              (term (bind (lam unit) (V 0))))
  (test-equal (term (lower (λ (x unit) (λ (x unit) x))))
              (term (bind (lam unit) (bind (lam unit) (V 0)))))
  (test-equal (term (lower (pair (λ (x unit) x) tt)))
              (term (pair (bind (lam unit) (V 0)) tt)))
  #;
  (redex-check ITT e (equal? (lower e) (lower (lower e)))
               #:prepare (close-all-fv (redex-match? ITT e))))


;;---------------------------------------------------------------------

(define dapp (term
              (λ (a ★)
                (λ (P (=> a ★))
                  (λ (f (Π (x a) (P x)))
                    (λ (y a)
                      (f y)))))))

(module+ test
  (test-equal (term (α= ,dapp
                         (λ (b ★)
                           (λ (Q (=> b ★))
                             (λ (g (Π (x b) (Q x)))
                               (λ (y b)
                                 (g y)))))))
              #t))
                        
(define-metafunction ITT
  α= : e e -> boolean
  [(α= e_1 e_2) ,(equal? (term (lower e_1)) (term (lower e_2)))])


(module+ test
  (test-results))