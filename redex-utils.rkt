#lang racket/base

(require
 redex/reduction-semantics)

(provide (all-defined-out))

(define-language anyL)

(define-metafunction anyL
  subst-all : any (any ...) (any ...) -> any
  [(subst-all any () ()) any]
  [(subst-all any (any_x any_xs ...) (any_a any_as ...))
   (subst-all (substitute any any_x any_a) (any_xs ...) (any_as ...))])

  ;; Determine if x appears free in any, by using substitution
(define-metafunction anyL
  not-free-in : any any -> #t or #f
  [(not-free-in any_x any)
   #t
   (where any (substitute any any_x any_fresh))
   (where any_fresh ,(variable-not-in (term (any any_x)) 'fresh))]
  [(not-free-in any_x any)
   #f])

(define-metafunction anyL
  free-in : any any -> #t or #f
  [(free-in any_x any)
   ,(not (term (not-free-in any_x any)))])

(define-judgment-form anyL
  #:mode (in I I)
  #:contract (in any (any ...))

  [----------------------------------
   (in any (any_0 ... any any_r ...))])

(define-judgment-form anyL
  #:mode (not-in I I)
  #:contract (not-in any (any ...))

  [(side-condition ,(not (member (term any) (term (any_0 ...)))))
   ----------------------------------
   (not-in any (any_0 ...))])

(require
 (for-syntax
  racket/base
  syntax/parse
  (only-in redex/private/term-fn judgment-form-mode judgment-form-lang)
  (only-in racket/syntax format-id)))

(define-syntax (define-remoded-judgment-form syn)
  (syntax-parse syn
    [(_ lang j1 #:mode (j2 m ...))
     #:with (any ...) (build-list (length (attribute m)) (lambda (x) (format-id #f "any_~a" x)))

     (quasisyntax/loc syn
       (define-judgment-form lang
         #:mode (j2 m ...)

         [(j1 any ...)
          -------------
          (j2 any ...)]))]))

(define-syntax (define-input-judgment-form syn)
  (syntax-parse syn
    [(_ lang j1 j2)
     #:with (I ...) (map (lambda _ #'I) (judgment-form-mode (syntax-local-value #'j1)))
     (quasisyntax/loc syn
       (define-remoded-judgment-form lang j1 #:mode (j2 I ...)))]))

(require (only-in redex-chk redex-judgment-holds-chk))
(define-syntax (redex-judgment-holds-chk/t syn)
  (syntax-parse syn
    [(_ (~or j:id (j:id args ...)) tests ...)
     #:with j2 (format-id syn "~a/t" #'j)
     #:with tag (format-id syn "~a/tag" #'j)
     #`(begin
         #,(unless (syntax-local-value #'tag (lambda _ #f))
             #`(begin
                 (define-input-judgment-form #,(judgment-form-lang (syntax-local-value #'j)) j j2)
                 (define-syntax (tag) #t)))
         (redex-judgment-holds-chk
          #,(if (attribute args)
                #'(j2 args ...)
                #'j2)
          tests ...))]))

(define (maybe-project-judgment ans)
  (if (pair? ans)
      (if (> (length ans) 1)
          ans
          (car ans))
      (if (null? ans)
          #f
          ans)))

(define-syntax (pretty-judgment-holds syn)
  (syntax-parse syn
    [(_ (j arg ...) maybe ...)
     #`(maybe-project-judgment (judgment-holds (j arg ...) maybe ...))]))

(define-syntax (functionalize-judgment syn)
  (syntax-parse syn
    [(_ judgment-name:id n:nat pattern ...)
     #:with (args ...) (build-list (eval #'n) (lambda (x) (format-id syn "x~a" x)))
     #`(lambda (args ...) (pretty-judgment-holds (judgment-name ,args ... pattern ...) pattern ...))]))

(define-syntax (functionalize-metafunction syn)
  (syntax-parse syn
    [(_ metafunction-name:id)
     #`(lambda args (term (metafunction-name ,@args)))]))

(module+ test
  (require redex-chk)
  (default-language anyL)
  (define-judgment-form anyL
    #:mode (out I O)

    [(out any any)])

  (define-remoded-judgment-form anyL out #:mode (out2 I I))
  (define-input-judgment-form anyL out out3)

  (redex-chk
   #:lang anyL
   (not-free-in D D) #f
   (substitute hole D y) hole
   (not-free-in D hole) #t)

  (redex-judgment-holds-chk
   out
   [x x])

  (redex-judgment-holds-chk
   out2
   [x x])

  (redex-judgment-holds-chk
   out3
   [x x]))
