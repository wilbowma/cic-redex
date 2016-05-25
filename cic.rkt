#lang racket/base

(require
 redex/reduction-semantics
 racket/dict
 racket/function
 (only-in racket/list take)
 "snoc-env.rkt")

(provide
 (all-defined-out)
 (all-from-out "snoc-env.rkt"))

;; Language and syntax sugar
;; This submodule exists just to use λ, let, and @ both as symbols in the language and as syntax sugar
;; via metafunctions
(module lang racket/base
  (require redex/reduction-semantics)
  (provide
   (all-defined-out)
   ;; Use syntax sugar by default
   (rename-out
    [λ* λ]
    [let* let]
    [@* @]
    ;; NB: This sugar caused problems, for some reason.
    #;[-> Π]))
  (define-language cicL
    (i j k n ::= natural)
    ;; It is useful to distinguish variables and constants. Variables are anything, while constants
    ;; (inductives and their constructors) must be prefixed by I
    (x y f ::= variable-not-otherwise-mentioned)
    (c D ::= (variable-prefix I))
    (U   ::= (Type i) Set Prop)
    (^case ::= (case e_D ;; Discriminant
                 ;; The indices for the type D
                 (e_i ...)
                 ;; Motive: takes indices of D, binds e_D.
                 e_motive
                 ;; Methods.
                 (e_methods ...)))
    (e t ::= c x (λ (x : t) e) (@ e e) (Π (x : t) t) U
       (let ([x = e : t]) e)
       ^case
       ;; Per Ch. 4 of Coq reference manual, fix is syntactically restricted more or less to the
       ;; following + termination checker to ensure termination.
       ;; NB: Must be defined by induction on the first argument of fix body; no support for mutual
       ;; recursion.
       (fix f : t fix-body))
    ;; fix-body ⊂ e
    (fix-body ::= (λ (x : t) ^case) (λ (x : t) fix-body))
    ;; Local environment
    (Γ-decl ::= (x : t) (x = e : t))
    (Γ   ::= · (Γ Γ-decl))
    ;; Global environment
    ;; NB: Only contains inductives, no global assumptions or definitions
    ;; NB: No mututal inductive types; they can be encoded via indexed types
    ;; NB: Δc ⊂ Γ; I don't take advantage of this yet, not sure if I will.
    (Δc  ::= · (Δc (c : t)))
    (Δ   ::= · (Δ (D : n t Δc)))
    ;; Telescopes, represented as Π contexts
    (Ξ ::= hole (Π (x : t) Ξ))
    ;; Arguments lists, represented as applications contexts
    (Θ ::= hole (@ Θ e))
    ;; Values
    (v   ::= c x (in-hole Θv c) (λ (x : t) e) U (Π (x : t) e))
    ;; a beta normal application context, used for constructors applied to their arguments
    (Θv ::= hole (@ Θv v))
    ;; eta normal forms
    (nf  ::= (in-hole E x))
    (λC ::= hole (λ (x : t) λC))
    ;; Evaluation contexts; call-by-value
    (E   ::= hole
         (let ([x = E : t]) e)
         (@ E e) (@ v E)
         (case E (e ...) e (e ...))
         (case v (v ... E e ...) e (e ...))
         (case v (v ...) E (e ...))
         (case v (v ...) v (v ... E e ...)))
    #:binding-forms
    (λ (x : any_t) any #:refers-to x)
    (Π (x : any_t) any #:refers-to x)
    (let ([x = any_e : any_t]) any_body #:refers-to x)
    (fix f : t e #:refers-to f))

  ;; ------------------------------------------------------------------------
  ;; Handy meta-functions and syntax sugar

  ;; TODO: Proper definitions pending https://github.com/racket/redex/issues/54
  (define-extended-language cic-sugarL cicL
    #;(C ::= (cross t))
    (me mt ::= any #;t #;C)
    (ann ::= (x : mt) mt))

  (define-metafunction cic-sugarL
    -> : ann ann ... mt -> mt
    [(-> (x : mt_0) mt_1)
     (Π (x : mt_0) mt_1)]
    [(-> (x : mt_0) ann ... mt)
     (Π (x : mt_0) (-> ann ... mt))]
    [(-> mt_0 ann ... mt)
     (-> (x : mt_0) ann ... mt)])

  (define-metafunction cic-sugarL
    λ* : (x : mt) (x : mt) ... me -> me
    [(λ* (x : mt) me)
     (λ (x : mt) me)]
    [(λ* (x : mt) (x_r : mt_r) ... me)
     (λ (x : mt) (λ* (x_r : mt_r) ... me))])

  (define-metafunction cic-sugarL
    let* : ([x = me : mt] ...) me -> mt
    [(let* () me)
     me]
    [(let* ([x = me : mt] any_0 ...) me_body)
     (let ([x = me : mt]) (let* (any_0 ...) me_body))])

  (define-metafunction cic-sugarL
    @* : me me ... -> me
    [(@* me) me]
    [(@* me_0 me_1 me ...)
     (@* (@ me_0 me_1) me ...)]))

(require 'lang)
(provide (all-from-out 'lang))

;;; ------------------------------------------------------------------------
;;; Vital meta-functions

;; --------------------------------------------------------
;; Γ defs

(define-metafunction cicL
  Γ-build : Γ Γ ... (Γ-decl ...) -> Γ
  [(Γ-build Γ ... (Γ-decl ...))
   (snoc-env-build Γ ... (Γ-decl ...))])

;; Make x : t ∈ Γ a little easier to use, prettier to render
(define-judgment-form cicL
  #:mode (Γ-in I I O)
  #:contract (Γ-in Γ x t)

  [(side-condition (snoc-env-in-dom Γ x))
   (where (x any ... : t) (snoc-env-ref Γ x))
   -------------------------------
   (Γ-in Γ x t)])

(define-judgment-form cicL
  #:mode (Γ-def-in I I O)
  #:contract (Γ-def-in Γ x e)

  [(side-condition (snoc-env-in-dom Γ x))
   (where (x = e : t) (snoc-env-ref Γ x))
   -------------------------------
   (Γ-def-in Γ x e)])

;; --------------------------------------------------------
;; Δ defs

(define-metafunction cicL
  Δ-in-dom : Δ D -> #t or #f
  [(Δ-in-dom Δ D) (snoc-env-in-dom Δ D)])

(define-metafunction cicL
  Δ-in-constructor-dom : Δ c -> #t or #f
  [(Δ-in-constructor-dom Δ c)
   ,(ormap (lambda (Δc) (term (snoc-env-in-dom ,Δc c))) (term (Δc ...)))
   (where ((_ _ _ _ Δc) ...) (snoc-env->als Δ))])

;; make D : t ∈ Δ a little easier to use, prettier to render
(define-judgment-form cicL
  #:mode (Δ-type-in I I O)
  #:contract (Δ-type-in Δ D t)

  [(side-condition (Δ-in-dom Δ D))
   (where (D : _ t _) (snoc-env-ref Δ D))
   -------------------------------
   (Δ-type-in Δ D t)])

;; Return the number of parameters for the inductive type D
(define-metafunction cicL
  Δ-ref-parameter-count : Δ_0 D_0 -> n
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-parameter-count Δ D)
   n
   (where (D : n _ _) (snoc-env-ref Δ D))])

;; Return the number of parameters for the inductive type D that has a constructor c_0
(define-metafunction cicL
  Δ-constructor-ref-parameter-count : Δ_0 c_0 -> n
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-constructor-ref-parameter-count Δ c)
   n
   (where (D : n _ _) (Δ-ref-by-constructor Δ c))])

;; Returns the inductively defined type that x constructs
(define-metafunction cicL
  Δ-key-by-constructor : Δ_0 c_0 -> D
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-key-by-constructor Δ c)
   D
   (where (_ ... (D _ _ _ Δc) _ ...) (snoc-env->als Δ))
   (side-condition (term (snoc-env-in-dom Δc c)))])

(define-metafunction cicL
  Δ-ref-by-constructor : Δ_0 c_0 -> (D : n t Δc)
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-ref-by-constructor Δ c)
   (snoc-env-ref Δ D)
   (where D (Δ-key-by-constructor Δ c))])

;; Returns the constructor map for the inductively defined type D in the signature Δ
(define-metafunction cicL
  Δ-ref-constructor-map : Δ_0 D_0 -> ((c : t) ...)
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-constructor-map Δ D)
   ;; NB: Need to return in reverse-dependency order, while ->als returns in dependency order
   ,(reverse (term (snoc-env->als Δc)))
   (where (_ _ _ _ Δc) (snoc-env-ref Δ D))])

(define-metafunction cicL
  Δ-ref-constructors : Δ_0 D_0 -> (c ...)
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-constructors Δ D)
   (c ...)
   (where ((c _ _) ...) (Δ-ref-constructor-map Δ D))])

;; Return the type of the constructor c_i
(define-metafunction cicL
  Δ-ref-constructor-type : Δ_0 c_0 -> t
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-ref-constructor-type Δ c)
   t
   (where (_ _ _ _ Δc) (Δ-ref-by-constructor Δ c))
   (judgment-holds (Γ-in Δc c t))])

;; Make c : t ∈ Δ a little easier to use, prettier to render
(define-judgment-form cicL
  #:mode (Δ-constr-in I I O)
  #:contract (Δ-constr-in Δ c t)

  [(side-condition (Δ-in-constructor-dom Δ c))
   (where t (Δ-ref-constructor-type Δ c))
   -------------------------------
   (Δ-constr-in Δ c t)])

(define-metafunction cicL
  Δ-ref-index-Ξ : Δ_0 D_0 -> Ξ
  #:pre (Δ-in-dom Δ_0 D_0)
  [(Δ-ref-index-Ξ Δ D)
   (Ξ-drop Ξ n)
   (where (D : n (in-hole Ξ U) _) (snoc-env-ref Δ D))])

(define-metafunction cicL
  Δ-constructor-ref-index-Ξ : Δ_0 c_0 -> Ξ
  #:pre (Δ-in-constructor-dom Δ_0 c_0)
  [(Δ-constructor-ref-index-Ξ Δ c)
   (Ξ-drop Ξ n)
   (where (D : n _ _) (Δ-ref-by-constructor Δ c))
   (where (in-hole Ξ (in-hole Θ D)) (Δ-ref-constructor-type Δ c))])


;; --------------------------------------------------------
;; aux defs

(define-metafunction cicL
  subst-all : e (x ...) (e ...) -> e
  [(subst-all e () ()) e]
  [(subst-all e (x x_r ...) (e_a e_r ...))
   (subst-all (substitute e x e_a) (x_r ...) (e_r ...))])

(define-metafunction cicL
  Ξ-apply : Ξ e_0 -> (in-hole Θ e_0)
  [(Ξ-apply hole e) e]
  [(Ξ-apply (Π (x : t) Ξ) e)
   (Ξ-apply Ξ (@ e x))])

;; Return the list of bindings from Ξ in reverse dependency order
(define-metafunction cicL
  Ξ-flatten : Ξ -> ((x : t) ...)
  [(Ξ-flatten hole)
   ()]
  [(Ξ-flatten (Π (x : t) Ξ))
   ((x : t) any ...)
   (where (any ...) (Ξ-flatten Ξ))])

(define-metafunction cicL
  Ξ-length : Ξ -> n
  [(Ξ-length Ξ)
   ,(length (term (Ξ-flatten Ξ)))])

(define-metafunction cicL
  λC-flatten : λC -> ((x : t) ...)
  [(λC-flatten hole)
   ()]
  [(λC-flatten (λ (x : t) λC))
   ((x : t) any ...)
   (where (any ...) (λC-flatten λC))])

(define-metafunction cicL
  λC-length : λC -> n
  [(λC-length λC)
   ,(length (term (λC-flatten λC)))])

(define-metafunction cicL
  λC->Γ : λC -> Γ
  [(λC->Γ hole) ·]
  [(λC->Γ (in-hole λC (λ (x : t) hole)))
   ((λC->Γ λC) (x : t))])

(define-metafunction cicL
  Ξ-drop : Ξ_0 n_0 -> Ξ
  #:pre ,(<= (term n_0) (term (Ξ-length Ξ_0)))
  [(Ξ-drop Ξ 0)
   Ξ]
  [(Ξ-drop (Π (x : t) Ξ) n)
   (Ξ-drop Ξ ,(sub1 (term n)))])

;; Return the list of operands from Θ in reverse dependency order
(define-metafunction cicL
  Θ-flatten : Θ -> (e ...)
  [(Θ-flatten hole)
   ()]
  [(Θ-flatten (@ Θ e))
   (any ... e)
   (where (any ...) (Θ-flatten Θ))])

(define-metafunction cicL
  Θ-length : Θ -> n
  [(Θ-length Θ)
   ,(length (term (Θ-flatten Θ)))])

(define-metafunction cicL
  Θ-drop : Θ_0 n_0 -> Θ
  #:pre ,(<= (term n_0) (term (Θ-length Θ_0)))
  [(Θ-drop Θ 0)
   Θ]
  [(Θ-drop (in-hole Θ (@ hole e)) n)
   (Θ-drop Θ ,(sub1 (term n)))])

(define-metafunction cicL
  Θ-take : Θ_0 n_0 -> Θ
  #:pre ,(<= (term n_0) (term (Θ-length Θ_0)))
  [(Θ-take Θ 0)
   hole]
  [(Θ-take (in-hole Θ (@ hole e)) n)
   (in-hole (Θ-take Θ ,(sub1 (term n))) (@ hole e))])

;; Instantiate a Π type
(define-metafunction cicL
  instantiate : t (e ...) -> t
  [(instantiate t ())
   t]
  [(instantiate (Π (x : t) t_1) (e any ...))
   (instantiate (substitute t_1 x e) (any ...))])

;; Select the method in e ... that corresponds to the constructor c
(define-metafunction cicL
  select-method : Δ c e ... -> e
  [(select-method Δ c e ..._0)
   e_mi
   (where D (Δ-key-by-constructor Δ c))
   ;; Methods must match number of constructors
   (where ((c_r _ _) ..._0) (Δ-ref-constructor-map Δ D))
   (where e_mi ,(dict-ref (term ((c_r . e) ...)) (term c)))])

;; constructors appear applied to their parameters and indices, but methods expect indices
;; create a new application context without the the parameters
(define-metafunction cicL
  drop-parameters : Δ c Θ -> Θ
  [(drop-parameters Δ c Θ)
   (Θ-drop Θ n)
   (where n (Δ-constructor-ref-parameter-count Δ c))])

;; small step reductions
(define (cicL--> Δ Γ)
  (reduction-relation
   cicL
   (--> x e
        (judgment-holds (Γ-def-in ,Γ x e))
        "E-Def")
   (--> (@ (λ (x : t) e_0) e_1)
        (substitute e_0 x e_1)
        "E-βΒ")
   (--> (let ([x = e : t]) e_body)
        (substitute e_body x e)
        "E-Let")
   ;; NB: Per CIC spec, must be applied to argument whose head is a constructor to maintain strong
   ;; normalization
   (--> (@ (name e_f (fix f : t_body (λ (x : t) e))) (name e_arg (in-hole Θ c)))
        (subst-all e (f x) (e_f e_arg))
        "E-Fix")
   (--> (case (in-hole Θ c) (e_i ..._1) e_motive (e_methods ..._0))
        (in-hole Θ_i e_mi)
        (where e_mi (select-method ,Δ c e_methods ...))
        (where Θ_i (drop-parameters ,Δ c Θ))
        "E-Case")))

;; eta expansion
(define cicLη-long
  (reduction-relation
   cicL
   (--> ((in-hole λC nf) (name t (in-hole Ξ (Π (_ : t_x) _))))
        ((λ (x : t_x) (in-hole λC (@ nf x))) t)
        (where (n n) ((Ξ-length Ξ) (λC-length λC)))
        (fresh x)
        "E-η")))

;; call-by-value context closure of small step reductions
(define (cicL-->cbv Δ Γ)
  (context-closure (cicL--> Δ Γ) cicL E))

;; run to beta-short form
(define-metafunction cicL
  beta-short : Δ Γ e -> v
  [(beta-short Δ Γ e)
   ,(car (apply-reduction-relation* (cicL-->cbv (term Δ) (term Γ)) (term e) #:cache-all? #t))])

;; run to eta-long form
(define-metafunction cicL
  eta-long : e t -> v
  [(eta-long e t)
   ,(caar (apply-reduction-relation* cicLη-long (term (e t)) #:cache-all? #t))])

;; Reduce e to v in the dynamic semantics
;; Only final syntax, (reduce Δ Γ e t), should be used in type system
;; Other syntaxes are for convenience of testing/use
;; NB: Relies on clause order
(define-metafunction cicL
  reduce : any ... e t ... -> v
  [(reduce e) (reduce · · e)]
  [(reduce Γ e) (reduce · Γ e)]
  [(reduce Δ Γ e)
   (reduce Δ Γ e t)
   (judgment-holds (type-infer Δ Γ e t))]
  [(reduce Δ Γ e)
   ;; NB: If can't infer a type, can't eta expand. (Type 9001) is one of many arbitrary choices that will prevent eta
   (reduce Δ Γ e (Type 9001))]
  [(reduce Δ Γ e t)
   (eta-long (beta-short Δ Γ e) t)])

;; What is the upper bound on two universes
;; NB: Relies on clause order
(define-metafunction cicL
  max-U : U U -> U
  [(max-U Prop U)
   U]
  [(max-U U Prop)
   U]
  [(max-U Set (Type i))
   (Type i)]
  [(max-U (Type i) Set)
   (Type i)]
  [(max-U U Set)
   Set]
  [(max-U Set U)
   Set]
  [(max-U (Type i) (Type j))
   (Type k)
   (where k ,(max (term i) (term j)))])

;; Is e_1 convertible to e_2?
(define-judgment-form cicL
  #:mode (convert I I I I)
  #:contract (convert Δ Γ e_1 e_2)

  [(where (e e) ((reduce Δ Γ e_0) (reduce Δ Γ e_1)))
   ----------------- "≡"
   (convert Δ Γ e_0 e_1)])

;; Is e_1 a subtype of e_2
(define-judgment-form cicL
  #:mode (subtype I I I I)
  #:contract (subtype Δ Γ e_1 e_2)

  [(convert Δ Γ e_0 e_1)
   ---------------------- "≼-≡"
   (subtype Δ Γ e_0 e_1)]

  [(where U_1 (max-U U_0 U_1))
   ---------------------- "≼-U"
   (subtype Δ Γ U_0 U_1)]

  [(convert Δ Γ t_0 t_1)
   (subtype Δ (Γ (x_0 : t_0)) e_0 (substitute e_1 x_1 x_0))
   ------------------------------------------------------ "≼-Π"
   (subtype Δ Γ (Π (x_0 : t_0) e_0) (Π (x_1 : t_1) e_1))])

(define-judgment-form cicL
  #:mode (valid-parameters I I I I)
  #:contract (valid-parameters Δ n t t)

  [-------------------------------
   (valid-parameters Δ 0 t_0 t_1)]

  [(valid-parameters Δ ,(sub1 (term n)) t_0 t_1)
   -------------------------------------------------------
   (valid-parameters Δ n (Π (x : t) t_0) (Π (y : t) t_1))])

;; Holds when the type t is a valid type for a constructor of D
(define-judgment-form cicL
  #:mode (valid-constructors I I I)
  #:contract (valid-constructors (Δ (D : n t Δc)) Γ Δc)

  [--------------------------- "VC-Empty"
   (valid-constructors Δ Γ ·)]

  [;; constructor's type must return the inductive type D
   (where (in-hole Ξ (in-hole Θ D)) t)
   ;; First n arguments (parameters) of the constructor must match those of the inductive
   (valid-parameters Δ n t t_D)
   (strict-positivity-cond Δ_0 Γ D t)
   (type-infer Δ Γ t U)
   (valid-constructors Δ_0 (Γ (c : t)) Δc)
   -----------------------------------------------------------------"VC-C"
   (valid-constructors (name Δ_0 (Δ (D : n t_D _))) Γ (Δc (c : t)))])

;; Under global declarations Δ, is the term environment well-formed?
(define-judgment-form cicL
  #:mode (wf I I)
  #:contract (wf Δ Γ)

  [--------- "W-Empty"
   (wf · ·)]

  [(wf Δ Γ)
   (type-infer Δ Γ t U)
   ------------------- "W-Local-Assum"
   (wf Δ (Γ (x : t)))]

  [(wf Δ Γ)
   (type-check Δ Γ e t)
   (type-infer Δ Γ t U)
   ----------------------- "W-Local-Def"
   (wf Δ (Γ (x = e : t)))]

  [(wf Δ ·)
   ;; NB: Not quite as specified:
   ;; * valid-constructors loops over constructors, rather than precomputing environments and using ... notation
   ;;   Primarily this is because ... notation makes checking the result type of each constructor
   ;;   awkward, but also ... notation makes random testing harder.
   ;; * check t_D directly rather than splitting parameter telescope manually.
   ;; * Γ must be empty, to guide search
   (where (c_!_0 ...) (Δ-ref-constructors Δ_0 D))
   (type-infer Δ · t_D U_D)
   (valid-constructors Δ_0 (· (D : t_D)) Δc)
   ---------------------------------------------------------- "W-Ind"
   (wf (name Δ_0 (Δ (D : n (name t_D (in-hole Ξ U)) Δc))) ·)])

;; Under global declarations Δ and term environment Γ, can we infer a type t for term e?
(define-judgment-form cicL
  #:mode (type-infer I I I O)
  #:contract (type-infer Δ Γ e t)

  [(wf Δ Γ)
   ------------------------------- "Ax-Prop"
   (type-infer Δ Γ Prop (Type 1))]

  [(wf Δ Γ)
   ------------------------------ "Ax-Set"
   (type-infer Δ Γ Set (Type 1))]

  [(wf Δ Γ)
   ;; TODO: Avoid escaping into Racket so we can use random testing
   (where j ,(add1 (term i)))
   ----------------------------------- "Ax-Type"
   (type-infer Δ Γ (Type i) (Type j))]

  [(Γ-in Γ x t)
   (wf Δ Γ)
   --------------------- "Var"
   (type-infer Δ Γ x t)]

  [(type-infer Δ Γ t_0 U)
   (type-check Δ (Γ (x : t_0)) t Prop)
   -------------------------------------- "Prod-Prop"
   (type-infer Δ Γ (Π (x : t_0) t) Prop)]

  [(type-infer Δ Γ t_0 U)
   (side-condition ,(member (term U) (term (Set Prop))))
   (type-check Δ (Γ (x : t_0)) t Set)
   -------------------------------------- "Prod-Set"
   (type-infer Δ Γ (Π (x : t_0) t) Set)]

  [(type-infer Δ Γ t_0 U_1)
   (type-infer Δ (Γ (x : t_0)) t U_2)
   (where U_3 (max-U U_1 U_2))
   -------------------------------------- "Prod-Type"
   (type-infer Δ Γ (Π (x : t_0) t) U_3)]

  [(type-infer Δ (Γ (x : t_0)) e t)
   (type-infer Δ Γ (Π (x : t_0) t) U)
   ------------------------------------------------- "Lam"
   (type-infer Δ Γ (λ (x : t_0) e) (Π (x : t_0) t))]

  [(type-infer Δ Γ e_0 (Π (x : t_1) t))
   (type-check Δ Γ e_1 t_1)
   -------------------------------------------------- "App"
   (type-infer Δ Γ (@ e_0 e_1) (substitute t x e_1))]

  [(type-check Δ Γ e t)
   (type-infer Δ (Γ (x = e : t)) e_body t_body)
   -------------------------------------------------------------------- "Let"
   (type-infer Δ Γ (let ([x = e : t]) e_body) (substitute t_body x e))]

  [(Δ-type-in Δ D t)
   (wf Δ Γ)
   --------------------- "Ind"
   (type-infer Δ Γ D t)]

  [(Δ-constr-in Δ c t)
   (wf Δ Γ)
   --------------------- "Constr"
   (type-infer Δ Γ c t)]

  [;; Must be case analyzing an inductive D applied to indices Θ
   (type-infer Δ Γ e (name t_I (in-hole Θ D)))

   ;; Extend Γ with parameters determined from Θ
   (where Γ_p (declare-parameters Δ Γ Θ D))
   (where Θ_p (take-parameters Δ D Θ))
   ;; check the indices match the inductive type
   (check-indices Δ Γ_p D (e_i ...))
   ;; Check the motive matches the inductive type
   (check-motive Δ Γ_p t_I D Θ_p e_motive)
   ;; Compute the return type from the motive
   (where t (@ e_motive e_i ... e))
   (type-infer Δ Γ_p t U)
   ;; Check the methods match their constructors, and return type from motive
   (check-methods Δ Γ_p D t (e_m ...))
   ------------------------------------------------------------- "match"
   (type-infer Δ Γ (case e (e_i ..._0) e_motive (e_m ..._1)) t)]

  [(terminates Δ e_fix)
   (type-check Δ (Γ (f : t)) e t)
   ---------------------------------------------- "Fix"
   (type-infer Δ Γ (name e_fix (fix f : t e)) t)])

;; Under global declarations Δ and term environment Γ, does e have a type that is convertible to t?
(define-judgment-form cicL
  #:mode (type-check I I I I)
  #:contract (type-check Δ Γ e t)

  [(type-infer Δ Γ e t_1)
   (type-infer Δ Γ t U)
   (subtype Δ Γ t_1 t)
   --------------------- "T-Conv"
   (type-check Δ Γ e t)])

;; ------------------------------------------------------------------------ 
;; Strict positivity

;; Determine if x appears free in any, by using substitution
(define-metafunction cicL
  not-free-in : x any -> #t or #f
  [(not-free-in x any)
   #t
   (where any (substitute any x x_fresh))
   (where x_fresh ,(variable-not-in (term (any x)) 'fresh))]
  [(not-free-in x any)
   #f])

;; t satisfied the strict positivity condition for D
;; translated from https://coq.inria.fr/doc/Reference-Manual006.html#Cic-inductive-definitions
(define-judgment-form cicL
  #:mode (strict-positivity-cond I I I I)
  #:contract (strict-positivity-cond Δ Γ D t)

  [(side-condition (not-free-in D Θ))
   ---------------------------------------- "SP-App"
   (strict-positivity-cond Δ Γ D (in-hole Θ D))]

  [(occurs-strictly-positively Δ Γ D t_0)
   (strict-positivity-cond Δ Γ D t_1)
   ---------------------------------------- "SP-Π"
   (strict-positivity-cond Δ Γ D (Π (x : t_0) t_1))])

;; D occurs strictly positively in t
(define-judgment-form cicL
  #:mode (occurs-strictly-positively I I I I)
  #:contract (occurs-strictly-positively Δ Γ D t)

  [(side-condition (not-free-in D t))
   ---------------------------------------- "OSP-NotIn"
   (occurs-strictly-positively Δ Γ D t)]

  ;; NB: positivity checking wants beta-short form rather than eta-long
  [(where (in-hole Θ D) (beta-short Δ Γ t))
   (side-condition (not-free-in D Θ))
   ---------------------------------------- "OSP-NotArg"
   (occurs-strictly-positively Δ Γ D t)]

  [(where (Π (x : t_0) t_1) (beta-short Δ Γ t))
   (side-condition (not-free-in D t_0))
   (occurs-strictly-positively Δ Γ D t_1)
   ---------------------------------------- "OSP-Π"
   (occurs-strictly-positively Δ Γ D t)]

  [(where (in-hole Θ D_i) (beta-short Δ Γ t))
   (where (D_!_0 D_!_0) (D D_i)) ;; D_i is a different inductive type
   (side-condition (Δ-in-dom Δ D_i))
   ;; TODO: Should not be using snoc-env-ref; interface should be  w.r.t. Δ
   (where (D_i _ n _ _) (snoc-env-ref Δ D_i))
   ;; NB: Can't use drop-parameters since that expects constructor
   ;; D not free in the index arguments of D_i
   (side-condition (not-free-in D (Θ-drop Θ n)))
   ;; Instantiated types of the constructors for D_i satisfy the nested positivity condition for D
   (where Θ_p (Θ-take Θ n))
   (where ((c : t_c) ...) (Δ-ref-constructor-map Δ D_i))
   (nested-positivity-condition Δ Γ D D_i (instantiate t_c (Θ-flatten Θ_p))) ...
   ---------------------------------------- "OSP-Ind"
   (occurs-strictly-positively Δ Γ D t)])

;; The type t of a constructor for D_i satisfied the nested positivity condition for D
(define-judgment-form cicL
  #:mode (nested-positivity-condition I I I I I)
  #:contract (nested-positivity-condition Δ Γ D D_i t)

  [(side-condition (Δ-in-dom Δ D_i))
   (where n (Δ-ref-parameter-count Δ D_i))
   (side-condition (not-free-in D (Θ-drop Θ n)))
   -------------------------------------------------------- "NPC-App"
   (nested-positivity-condition Δ Γ D D_i (in-hole Θ D_i))]

  [(occurs-strictly-positively Δ Γ D t_0)
   (nested-positivity-condition Δ Γ D D_i t_1)
   ---------------------------------------------------------- "NPC-Π"
   (nested-positivity-condition Δ Γ D D_i (Π (x : t_0) t_1))])

;; ------------------------------------------------------------------------ 
;; case helpers

;; Can an inductive type D that lives in U_A be eliminated to some type that lives in U_B?
;; NB: Omitting the prod rule as that rule is used to just "type checks" the motive, which we do
;; separately. This judgment is only responsible for checking the universes
(define-judgment-form cicL
  #:mode (elimable I I I I)
  #:contract (elimable Δ D U_A U_B)

  [(side-condition ,(not (eq? (term U_1) (term Prop))))
   ------------------------ "Set&Type"
   (elimable Δ D U_1 U_2)]

  [------------------------- "Prop"
   (elimable Δ D Prop Prop)]

  [(where () (Δ-ref-constructor-map Δ D))
   ---------------------- "Prop-extended-empty"
   (elimable Δ D Prop U)]

  [(where ((c : (in-hole Ξ (in-hole Θ_c D)))) (Δ-ref-constructor-map Δ D))
   (where ((_ : Prop) ...) (Ξ-flatten Ξ))
   ---------------------- "Prop-extended-singleton"
   (elimable Δ D Prop U)])

(define-metafunction cicL
  take-parameters : Δ_0 D_0 Θ -> Θ
  #:pre (Δ-in-dom Δ_0 D_0)
  [(take-parameters Δ D Θ)
   (Θ-take Θ n)
   (where n (Δ-ref-parameter-count Δ D))])

;; Extend Γ with the parameters for D, and let decls determined from Θ
(define-metafunction cicL
  declare-parameters : Δ_0 Γ Θ D_0 -> Γ
  #:pre (Δ-in-dom Δ_0 D_0)
  [(declare-parameters Δ Γ Θ D)
   (Γ-build Γ ((x = e : t) ...))
   (where (D : n (in-hole Ξ U) _) (snoc-env-ref Δ D))
   (where ((x : t) ..._0) ,(take (term (Ξ-flatten Ξ)) (term n)))
   (where (e ..._0) ,(take (term (Θ-flatten Θ)) (term n)))])

(define-judgment-form cicL
  #:mode (type-wrt-telescope I I I I)
  #:contract (type-wrt-telescope Δ Γ (e ...) Ξ)

  [(wf Δ Γ)
   ---------------------------------
   (type-wrt-telescope Δ Γ () hole)]

  [(type-check Δ Γ e t)
   (type-wrt-telescope Δ (Γ (x : t)) (e_i ...) Ξ)
   ---------------------------------------------------
   (type-wrt-telescope Δ Γ (e e_i ...) (Π (x : t) Ξ))])

(define-judgment-form cicL
  #:mode (check-indices I I I I)
  #:contract (check-indices Δ Γ D (e ...))

  [(where Ξ_D (Δ-ref-index-Ξ Δ D))
   ;; Check that the indices e ... match the inductive telescope
   (type-wrt-telescope Δ Γ (e ...) Ξ_D)
   -------------------------------
   (check-indices Δ Γ D (e ...))])

(define-judgment-form cicL
  #:mode (check-motive I I I I I I)
  #:contract (check-motive Δ Γ t D Θ e)

  [(where Ξ_D (Δ-ref-index-Ξ Δ D))
   ;; check that the motive matches the inductive index telescope, i.e., the telescope sans parameters.
   (type-infer Δ Γ e (in-hole Ξ_D (Π (x : t_D) U_B)))
   (subtype Δ Γ t_D (Ξ-apply Ξ_D (in-hole Θ_p D)))
   ;; Check that this is a valid elimination sort
   (type-infer Δ Γ t_I U_A)
   (elimable Δ D U_A U_B)
   -------------------------------
   (check-motive Δ Γ t_I D Θ_p e)])

(define-judgment-form cicL
  #:mode (check-methods I I I I I)
  #:contract (check-methods Δ Γ D t (e ...))

  [(where ((c _ _) ..._1) (Δ-ref-constructor-map Δ D))
   (where (Ξ_c ..._1) ((Δ-constructor-ref-index-Ξ Δ c) ...))
   (type-check Δ Γ e (in-hole Ξ_c t)) ...
   -------------------------------
   (check-methods Δ Γ D t (e ...))])

;; ------------------------------------------------------------------------
;; termination checking

;; Is e structurally smaller than y (of type D), with structurally smaller recursive arguments (x ...)?
(define-judgment-form cicL
  #:mode (structurally-smaller I I I I I)
  #:contract (structurally-smaller Δ y (x ...) D e)

  [-----------------------------------------------
   (structurally-smaller Δ y (_ ... x _ ...) D x)]

  [(structurally-smaller Δ y any D e)
   -----------------------------------------------
   (structurally-smaller Δ y any D (λ (x : t) e))]

  [(structurally-smaller Δ y any D e_1)
   ---------------------------------------------
   (structurally-smaller Δ y any D (@ e_1 e_2))]

  [(structurally-smaller Δ y any D e_method) ...
   ---------------------------------------------------------------
   (structurally-smaller Δ y any D (case e_c _ _ (e_method ...)))]

  [(where ((c _ _) ...) (Δ-ref-constructor-map Δ D))
   (where (((x_more ...) e_body) ...) (split-methods Δ D any))
   (structurally-smaller Δ y (x ... x_more ...) D e_body) ...
   -----------------------------------------------------------------
   (structurally-smaller Δ y (x ...) D (case y _ _ any))]

  [(structurally-smaller Δ y (x ...) D e_c)
   (where (((x_more ...) e_body) ...) (split-methods Δ D any))
   (structurally-smaller Δ y (x ... x_more ...) D e_body) ...
   -------------------------------------------------------------------
   (structurally-smaller Δ y (x ...) D (case e_c _ _ any))])

;; Check that the body of f, e, is guarded w.r.t y, an inductive argument of type D, with
;; accumulated recursive arguments (x ...).
(define-judgment-form cicL
  #:mode (guard I I I I I I)
  #:contract (guard Δ y D f (x ...) e)

  [(structurally-smaller Δ y any D e)
   --------------------------
   (guard Δ y D f any (@ f e))]

  [--------------------
   (guard _ _ _ _ _ U)]

  [--------------------
   (guard _ _ _ _ _ x)]

  [(guard Δ y D f any e_1)
   (guard Δ y D f any e_2)
   ----------------------------------------------------------
   (guard Δ y D (name f f_!_0) any (@ (name e_1 f_!_0) e_2))]

  [(guard Δ y D f any t)
   (guard Δ y D f any e)
   ------------------------------
   (guard Δ y D f any (λ (x : t) e))]

  [(guard Δ y D f any t)
   (guard Δ y D f any e)
   ------------------------------
   (guard Δ y D f any (Π (x : t) e))]

  [(guard Δ y D f any e)
   (guard Δ y D f any e_i) ...
   (guard Δ y D f any e_motive)
   (guard Δ y D f any e_methods) ...
   ----------------------------------------------------------------
   (guard Δ y D f any (case e (e_i ...) e_motive (e_methods ...)))]

  [(structurally-smaller Δ y (x ...) D e)
   (guard Δ y D f (x ...) e_i) ...
   (guard Δ y D f (x ...) e_motive)
   ;; structurally smaller variables.
   (where (((x_more ...) e_body) ...) (split-methods Δ D any))
   (guard Δ y D f (x ... x_more ...) e_body) ...
   ----------------------------------------------------------------
   (guard Δ y D f (x ...) (case e (e_i ...) e_motive any))]

  [(guard Δ y D f (x ...) e_i) ...
   (guard Δ y D f (x ...) e_motive)
   ;; structurally smaller variables.
   (where (((x_more ...) e_body) ...) (split-methods Δ D any))
   (guard Δ y D f (x ... x_more ...) e_body) ...
   --------------------------------------------------------
   (guard Δ y D f (x ...) (case y (e_i ...) e_motive any))])

;; Splits the methods into their structurally smaller arguments and the body of the method
(define-metafunction cicL
  split-methods : Δ D (e ...) -> (((x ...) e) ...)
  [(split-methods Δ D (e ..._0))
   ((split-method Ξ e) ...)
   (where ((c _ _) ..._0) (Δ-ref-constructor-map Δ D))
   (where (Ξ ..._0) ((Δ-constructor-ref-index-Ξ Δ c) ...))])

;; Splits a method into its structurally smaller arguments and the body of the method
(define-metafunction cicL
  split-method : Ξ e -> ((x ...) e)
  [(split-method hole e)
   (() e)]
  [(split-method (Π (x_0 : t_0) Ξ) (λ (x : t) e))
   ((x x_r ...) e_r)
   (where ((x_r ...) e_r) (split-method Ξ e))])

;; Does e terminate?
(define-judgment-form cicL
  #:mode (terminates I I)
  #:contract (terminates Δ e)

  [(Δ-type-in Δ D _)
   (guard Δ y D f () e)
   ------------------------------------------------------------------------
   (terminates Δ (fix f : t (λ (y : (in-hole Θ D)) e)))])
