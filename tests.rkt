#lang racket

(require
 redex/reduction-semantics
 "cic.rkt"
 redex-chk)

;; Tests
;; Requires forked version of redex-chk found https://github.com/wilbowma/redex-chk

(default-language cicL)
(default-equiv (curry alpha-equivalent? cicL))

(redex-chk
 #f (Δ-in-constructor-dom · Ix))

(redex-relation-chk
 (type-check · ·)
 [(Type 0) (Type 1)]
 [#:f (Π (x : (Type 0)) (Type 0)) (Type 0)]
 [(Π (x : (Type 0)) (Type 0)) (Type 1)]
 [#:f (Π (x : (Type 0)) x) (Type 0)]
 [#:f Prop (Type 0)]
 [Set (Type 1)]
 [Prop (Type 1)]
 [Prop (Type 2)]
 [(Π (x : Prop) x) Prop]
 [(Π (x : Prop) Prop) (Type 1)]
 [(Π (x : Prop) x) Prop]
 [(λ (x : Set) x) (Π (x : Set) Set)]
 [(λ (x : Set) x) (-> Set Set)])

(redex-judgment-holds-chk
 (type-infer · ·)
 [(Type 0) (Type 1)]
 [(Π (a : Prop) Prop) U])

(define-term Δnb
  ((· (Nat : 0 Set ((· (z : Nat)) (s : (Π (x : Nat) Nat)))))
   (Bool : 0 Set ((· (true : Bool)) (false : Bool)))))

;; Tests parameters
(define-term Δlist
  (Δnb (List : 1 (Π (A : Set) Set)
              ((· (nil : (Π (A : Set) (@ List A))))
               (cons : (-> (A : Set) (a : A) (ls : (@ List A)) (@ List A)))))))
;; Bad; this syntax is surface syntax, not core syntax
(define-term Δbadlist
  (Δnb (List : 1 (Π (A : Set) Set)
              ((· (nil : (@ List A)))
               (cons : (-> (a : A) (ls : (@ List A)) (@ List A)))))))
(redex-chk
 #f (not-free-in D D)
 hole (substitute hole D y)
 #t (not-free-in D hole)
 Nat (reduce Δnb · Nat))

(redex-judgment-holds-chk
 (strict-positivity-cond Δnb ·)
 [Bool Bool]
 [Nat Nat]
 [Nat (Π (x : Nat) Nat)])

;; TODO: Some of these tests are in the wrong order; i.e., actual/expected are flipped
(redex-chk
 #:lang cicL
 #:m (cross e) hole
 #:m (cross e) (@ (λ (x : t) hole) z)
 z (reduce (@ (λ (x : (Type 0)) x) z))
 0 (Ξ-length hole)
 1 (Ξ-length (Π (x : Set) hole))
 f (reduce f)
  Nat (Δ-ref-constructor-type Δnb z)
 (Π (x : Nat) Nat) (Δ-ref-constructor-type Δnb s)
 hole (Δ-ref-index-Ξ Δnb Nat hole)
 ((z : Nat) (s : (Π (x : Nat) Nat))) (Δ-ref-constructor-map Δnb Nat)
 (hole (Π (x : Nat) hole)) ((Δ-constructor-ref-index-Ξ Δnb z hole)
                             (Δ-constructor-ref-index-Ξ Δnb s hole))
 hole (Δ-constructor-ref-index-Ξ Δlist nil (@ hole Nat))
 Nat (reduce (in-hole (@ hole z) (λ (x : Nat) Nat)))
 Nat (Ξ-apply hole Nat)
 (Π (x : Nat) Set) (in-hole hole (Π (x : (Ξ-apply hole Nat)) Set))
 Nat (Δ-key-by-constructor Δnb z)
 z (reduce Δnb · (case z (λ (x : Nat) Nat) (z (λ (x : Nat) x))))
 #:m (in-hole hole (Π (x : D) U)) (Π (x : Nat) Set)
 #:m (in-hole Ξ_D (Π (x : D) U)) (Π (x : Nat) Set)
 (reduce Δlist · (case (@ nil Nat) (λ (ls : (@ List Nat)) Bool) (true false))) true)

(redex-judgment-holds-chk
 (convert Δnb ((· (f : (Π (x : Set) Set))) (y : Set)))
 [(@ f y) (@ f y)]
 [(λ (x : Set) (@ f x)) f]
 [(λ (x : Nat) (@ s x)) s])

(redex-relation-chk
 wf
 [· ·]
 [Δnb ·]
 [Δnb (· (x : Nat))]
 [Δlist ·]
 [#:f Δbadlist ·])

(redex-judgment-holds-chk
 (type-infer Δlist ·)
 [(λ (x : Nat) Nat) t]
 [(λ (x : Nat) Nat) t]
 [(case z (λ (x : Nat) Nat) (z (λ (x : Nat) x))) t]
 [#:f nil (@ List A)]
 [(@ nil Nat) t])

(redex-relation-chk
 type-check
 [· (· (Nat : (Type 0))) (Π (n : Nat) Nat) (Type 1)]
 [· (· (Nat : Set)) (Π (n : Nat) Nat) (Type 1)]
 [Δnb (· (x : Nat)) Nat Set])

(redex-relation-chk
 (type-check Δlist ·)
 [Nat Set]
 [z Nat]
 [(@ s z) Nat]
 [(Π (x : Nat) Set) (Type 1)]
 [(λ (x : Nat) Nat) (Π (x : Nat) Set)]
 [(λ (x : Nat) Nat) (Π (x : Nat) Set)]
 [(λ (x : Nat) x) (Π (x : Nat) Nat)]
 [(case z (λ (x : Nat) Nat) (z (λ (x : Nat) x))) Nat]
 [(case true (λ (x : Bool) Nat) (z (@ s z))) Nat]
 [(fix f : (-> Nat Nat)
       (λ (x : Nat)
         (case x (λ (x : Nat) Nat)
               (z
                (λ (x : Nat) (@ s x))))))
  (Π (x : Nat) Nat)]
 [(fix f : (-> Nat Nat)
       (λ (x : Nat)
         (case x (λ (x : Nat) Nat)
               (z
                (λ (x : Nat) (@ f x))))))
  (Π (x : Nat) Nat)]
 [#:f (fix f : (-> Nat Nat)
           (λ (x : Nat)
             (case x (λ (x : Nat) Nat)
                   ((@ f x)
                    (λ (y : Nat) (@ f x))))))
  (Π (x : Nat) Nat)]
 [(λ (x : Nat) x) (Π (x : Nat) Nat)]
 [(let ([n = z : Nat]) z) Nat]
 [(let ([n = z : Nat]) n) Nat]
 [(let ([Nat^ = Nat : Set] [n = z : Nat^]) n) Nat]
 [(@ cons Nat z (@ nil Nat)) (@ List Nat)]
 [(case (@ cons Nat z (@ nil Nat)) (λ (ls : (@ List Nat)) Bool)
        (true (λ (n : Nat) (ls : (@ List Nat)) false))) Bool])
