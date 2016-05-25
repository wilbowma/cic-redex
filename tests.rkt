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
  ((· (INat : 0 Set ((· (Iz : INat)) (Is : (Π (x : INat) INat)))))
   (IBool : 0 Set ((· (Itrue : IBool)) (Ifalse : IBool)))))

;; Tests parameters
(define-term Δlist
  (Δnb (IList : 1 (Π (A : Set) Set)
              ((· (Inil : (Π (A : Set) (@ IList A))))
               (Icons : (-> (A : Set) (a : A) (ls : (@ IList A)) (@ IList A)))))))
;; Bad; this syntax is surface syntax, not core syntax
(define-term Δbadlist
  (Δnb (IList : 1 (Π (A : Set) Set)
              ((· (Inil : (@ IList A)))
               (Icons : (-> (a : A) (ls : (@ IList A)) (@ IList A)))))))
(redex-chk
 #f (not-free-in D D)
 hole (substitute hole D y)
 #t (not-free-in D hole)
 INat (reduce Δnb · INat))

(redex-judgment-holds-chk
 (strict-positivity-cond Δnb ·)
 [IBool IBool]
 [INat INat]
 [INat (Π (x : INat) INat)])

;; TODO: Some of these tests are in the wrong order; i.e., actual/expected are flipped
(redex-chk
 #:lang cicL
 #:m (cross e) hole
 #:m (cross e) (@ (λ (x : t) hole) z)
 Iz (reduce (@ (λ (x : (Type 0)) x) Iz))
 0 (λC-length hole)
 1 (λC-length (λ (x : Set) hole))
 0 (Ξ-length hole)
 1 (Ξ-length (Π (x : Set) hole))
 f (reduce f)
 #:eq (λ (x : Set) (@ f x)) (reduce (· (f : (Π (x : Set) Set))) f)
 ;; TODO: Some kind of bug in redex-chk #:eq here; have to manually specify default-equiv
 #:eq (default-equiv) (λ (x : INat) (@ Is x)) (reduce Δnb · Is)
 INat (Δ-ref-constructor-type Δnb Iz)
 (Π (x : INat) INat) (Δ-ref-constructor-type Δnb Is)
 hole (Δ-ref-index-Ξ Δnb INat hole)
 ((Iz : INat) (Is : (Π (x : INat) INat))) (Δ-ref-constructor-map Δnb INat)
 (hole (Π (x : INat) hole)) ((Δ-constructor-ref-index-Ξ Δnb Iz hole)
                             (Δ-constructor-ref-index-Ξ Δnb Is hole))
 hole (Δ-constructor-ref-index-Ξ Δlist Inil (@ hole INat))
 INat (reduce (in-hole (@ hole Iz) (λ (x : INat) INat)))
 INat (Ξ-apply hole INat)
 (Π (x : INat) Set) (in-hole hole (Π (x : (Ξ-apply hole INat)) Set))
 INat (Δ-key-by-constructor Δnb Iz)
 Iz (reduce Δnb · (case Iz () (λ (x : INat) INat) (Iz (λ (x : INat) x))))
 #:m (in-hole hole (Π (x : D) U)) (Π (x : INat) Set)
 #:m (in-hole Ξ_D (Π (x : D) U)) (Π (x : INat) Set)
 (reduce Δlist · (case (@ Inil INat) () (λ (ls : (@ IList INat)) IBool) (Itrue Ifalse))) Itrue)

(redex-relation-chk
 wf
 [· ·]
 [Δnb ·]
 [Δnb (· (x : INat))]
 [Δlist ·]
 [#:f Δbadlist ·])

(redex-judgment-holds-chk
 (type-infer Δlist ·)
 [(λ (x : INat) INat) t]
 [(λ (x : INat) INat) t]
 [(case Iz () (λ (x : INat) INat) (Iz (λ (x : INat) x))) t]
 [#:f Inil (@ IList A)]
 [(@ Inil INat) t])

(redex-relation-chk
 type-check
 [· (· (INat : (Type 0))) (Π (n : INat) INat) (Type 1)]
 [· (· (INat : Set)) (Π (n : INat) INat) (Type 1)]
 [Δnb (· (x : INat)) INat Set])

(redex-relation-chk
 (type-check Δlist ·)
 [INat Set]
 [Iz INat]
 [(@ Is Iz) INat]
 [(Π (x : INat) Set) (Type 1)]
 [(λ (x : INat) INat) (Π (x : INat) Set)]
 [(λ (x : INat) INat) (Π (x : INat) Set)]
 [(λ (x : INat) x) (Π (x : INat) INat)]
 [(case Iz () (λ (x : INat) INat) (Iz (λ (x : INat) x))) INat]
 [(case Itrue () (λ (x : IBool) INat) (Iz (@ Is Iz))) INat]
 [(fix f : (-> INat INat)
       (λ (x : INat)
         (case x () (λ (x : INat) INat)
               (Iz
                (λ (x : INat) (@ Is x))))))
  (Π (x : INat) INat)]
 [(fix f : (-> INat INat)
       (λ (x : INat)
         (case x () (λ (x : INat) INat)
               (Iz
                (λ (x : INat) (@ f x))))))
  (Π (x : INat) INat)]
 [#:f (fix f : (-> INat INat)
           (λ (x : INat)
             (case x () (λ (x : INat) INat)
                   ((@ f x)
                    (λ (y : INat) (@ f x))))))
  (Π (x : INat) INat)]
 [(λ (x : INat) x) (Π (x : INat) INat)]
 [(let ([n = Iz : INat]) Iz) INat]
 [(let ([n = Iz : INat]) n) INat]
 [(let ([INat^ = INat : Set] [n = Iz : INat^]) n) INat]
 [(@ Icons INat Iz (@ Inil INat)) (@ IList INat)]
 [(case (@ Icons INat Iz (@ Inil INat)) () (λ (ls : (@ IList INat)) IBool)
        (Itrue (λ (n : INat) (ls : (@ IList INat)) Ifalse)) )IBool])
