#lang racket/base

(require
 redex/reduction-semantics
 racket/dict)
(provide (all-defined-out))

(define-language snocL
  (snoc-env ::= · (snoc-env (any any ...))))

;; Flatten a snoc-env into an als, in reverse dependency order
;; (i.e. the first element may depends all later elements)
(define-metafunction snocL
  _snoc-env->als : snoc-env -> ((any any ...) ...)
  [(_snoc-env->als ·) ()]
  [(_snoc-env->als (snoc-env (any any_r ...)))
   ,(cons (term (any any_r ...)) (term (_snoc-env->als snoc-env)))])

(define-metafunction snocL
  snoc-env->als : snoc-env -> ((any any ...) ...)
  [(snoc-env->als snoc-env)
   ,(reverse (term (_snoc-env->als snoc-env)))])

(define-metafunction snocL
  snoc-env-in-dom : snoc-env any -> #t or #f
  [(snoc-env-in-dom snoc-env any)
   ,(dict-has-key? (term (snoc-env->als snoc-env)) (term any))])

(define-metafunction snocL
  snoc-env-not-in-dom : snoc-env any -> #t or #f
  [(snoc-env-not-in-dom snoc-env any)
   ,(not (term (snoc-env-in-dom snoc-env any)))])

(define-metafunction snocL
  snoc-env-ref : snoc-env_0 any_0 -> any or #f
  [(snoc-env-ref snoc-env any_d)
   (any_d any_r ...)
   (where (any_r ...) ,(dict-ref (term (snoc-env->als snoc-env)) (term any_d) (lambda () #f)))]
  [(snoc-env-ref _ _) #f])

;; Merge any number of snoc-envs, given in dependency order
;; (i.e. the last snoc-env may depend on all previous snoc-envs)
(define-metafunction snocL
  snoc-env-merge : snoc-env snoc-env ... -> snoc-env
  [(snoc-env-merge snoc-env_0 snoc-env ...)
   ,(for/fold ([env (term snoc-env_0)])
              ([snoc-env (term (snoc-env ...))])
      (for/fold ([env env])
                ([decl (term (snoc-env->als ,snoc-env))])
        (term (,env ,decl))))])

;; Take any number of snoc-envs, and snoc-env members, in dependency order, and create a new snoc-env
(define-metafunction snocL
  snoc-env-build : snoc-env snoc-env ... ((any any ...) ...) -> snoc-env
  [(snoc-env-build snoc-env ... ((any ...) ...))
   ,(for/fold ([env (term (snoc-env-merge snoc-env ...))])
              ([decl (term ((any ...) ...))])
      (term (,env ,decl)))])


(define-judgment-form snocL
  #:mode (snoc-env-in I I O)
  #:contract (snoc-env-in snoc-env any any)

  [(side-condition (snoc-env-in-dom snoc-env any_k))
   (where (any_k any_v ...) (snoc-env-ref snoc-env any_k))
   -------------------------------
   (snoc-env-in snoc-env any_k (any_v ...))])
