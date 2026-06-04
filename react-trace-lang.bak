#lang racket

(require redex)

;; React-tRace Language Definition
;; Based on Figure 1 of the React-tRace paper
;;
;; This is a tiny one-component model demonstrating:
;; - Persistent Hook state across renders (Init vs Succ)
;; - Setter queueing (updates don't mutate local variables immediately)
;; - Check phase that applies queued updates to the store
;;
;; NOT modeled: tree memory, paths, reconciliation, effects, component lookup.
;; This is much smaller than the paper's full semantics.


(define-language React-tRace

  ;; Programs and component definitions are syntax only.
  ;; This model does not implement component lookup or instantiation.
  (P ::= (program (D ...) e))
  (D ::= (let C x = e))

  ;; Expressions
  (e ::= ()
     true
     false
     n
     x
     (e op e)
     (e ...)
     (print e)
     (if e e e)
     (begin e e)
     (λ (x) e)
     (e e)
     (let ([x e]) e)

     ;; useState: (state l (x_state x_set) e_init e_body)
     ;; In Init phase, e_init is evaluated and stored at label l.
     ;; In Succ phase, e_init is ignored; we read from the store.
     ;; x_state and x_set are bound in e_body only.
     (state l (x_state x_set) e_init e_body)

     ;; Setter value (appears at runtime after state is processed)
     (setter l))

  (op + - * / < <= = > >= !=)

  ;; Values
  (v ::=
     k
     cl
     C
     cs
     (s ...)
     (l p))

  ;; Closures
  (cl ::= ((λ (x) e) σ))

  ;; ViewSpec
  (s ::= k cl cs (s ...))

  ;; ComSpec
  (cs ::= (C v))

  (x C y ::= variable-not-otherwise-mentioned)
  (l ::= natural)
  (n ::= integer)
  (p ::= natural -)

  (π ::= (view cs (d ...) ρ q t))
  (d ::= Check Effect)
  (ρ ::= ((v q) ...))  
  (q ::= (cl ...))
  (Σ ::= m π)
  (m ::= ((p π) ...) mt)
  (t ::= k cl p (t ...))

  ;; Runtime configurations for the one-component model

  (ϕ ::= Init Succ Normal) ;; Change phase to phi, or ϕ, to better follow paper 

  ;; Store: maps Hook labels to their persistent values
  (σ ::= ((l v) ...))

  ;; Queue: maps Hook labels to lists of pending updater functions
  (Q ::= ((l (v ...)) ...))

  #;(config ::=
          (render phase e σ Q)
          (check σ Q)
          (done v σ Q))

  (mode::= rendered ⟲ •) ;; "rendered" corresponds to neuron-looking thing

  ;; Effect queue: ordered list of effect thunks (closures)
  (ω () (ω (fun x -> e)))

  ;; Render result outcome
  (outcome Normal Throw)

  ;; Stable marker
  (status Stable Rerendering)

  ;; Top-level configuration before StepInit: ⟨e, δ⟩
  ;; δ is the external event queue (user events)
  (δ () (δ event))
  (event (click ι) (change ι v)) ; etc.

  ;; Top-level configuration after: ⟨t, m, ω, δ, status⟩
  (config (CONFIG t m ω δ mode))

  ;; Allow hook to take in either input, allowing initialization
  (hook-input ::= (e δ) (t m ω δ mode)))


(define-judgment-form React-tRace
  #:mode (hook I O)
  #:contract (hook hook-input (t m ω δ mode))

  ;; "StepInit"
  ;; Initialize the program
  [
   (eval () () e Normal - s () ω)     ;; [], [] ⊢ e ⇓ Normal - s, [], ω
   (init mt () s t m ω_prime)            ;; [] ⊢ init(s) = ⟨t, m, ω'⟩
   ----------------------------------- "StepInit"
   (hook (e δ)
         (t m (append-ω ω ω_prime) δ rendered))]

  ;; "StepCheck"
  ;; Check any for any state update
  [
   (check m_1 δ t μ m_2 ω_2)
   ----------------------------------- "StepCheck"
   (hook (t m_1 ω_1 δ ⟲)
         (t m_2 (append-ω ω_1 ω_2) δ μ))]

  ;; "StepEvent"
  ;; State update check based on input occuring
  [ ;; TODO
   ----------------------------------- "StepEvent"
   (hook (t m_1 ω δ •)
         (t m_2 (append-ω ω_1 ω_2) δ ⟲))]
  )


;; The append -|-|- helper function, extend output buffer
(define-metafunction React-tRace
  append-ω : ω ω -> ω
  [(append-ω () ω) ω]
  [(append-ω (ω_1 (fun x -> e)) ω_2)
   ((append-ω ω_1 ω_2) (fun x -> e))])


;;
;; ------------------------------ INIT
;;

(define-judgment-form React-tRace
  #:mode (init I I I O O O)
  #:contract (init m δ s t m ω)
  ;; init takes in a tree memory, a definition table, and a spec s
  ;; and renders into a tree t, modifies memory, and prints buffer ω

  ;; InitConst 
  ;; Constants pass through
  [-------- "InitConst"
   (init m δ k k m ())]

  ;; InitClos
  ;; Closures pass through the same way
  [-------- "InitClos"
   (init m δ cl cl m ())]

  ;; InitArray 
  ;; Init each element left-to-right, threading memory through.
  ;; Base Case: empty array
  [-------- "InitArray-Nil"
   (init m δ (view ()) (view ()) m ())]

  ;; Inductive Step: init head, then tail with updated memory
  [(init m_0 δ s_1 t_1 m_1 ω_1)
   (init m_1 δ (view (s_rest ...)) (view (t_rest ...)) m_2 ω_2)
   -------- "InitArray-Cons"
   (init m_0 δ (view (s_1 s_rest ...))
               (view (t_1 t_rest ...))
               m_2
               (append-ω ω_1 ω_2))])


;;
;; ------------------------------ EVAL
;;

(define-judgment-form React-tRace
  #:mode (eval I I I I I O O O)
  #:contract (eval Σ_1 σ e ϕ p v Σ_2 ω)
  ;; eval takes in a context Σ, an environment σ, an expression e, a phase ϕ, a path p
  ;; and returns a value v, a modified context Σ_2, and an output buffer ω

  ;; AppFunc
  ;; Apply the function evaluation
  [(eval Σ σ e_1 ϕ p ((λ (x) e) σ_1) Σ_1 ω_1)
   (eval Σ_1 σ e_2 ϕ p v_2 Σ_2 ω_2)
   (eval Σ_2 ((x v_2) σ_1) e ϕ p v Σ_3 ω_3)
   ---------------------------------------- "AppFunc"
   (eval Σ σ (e_1 e_2) ϕ p v Σ_3 (append (append-ω ω_1 ω_2) ω_3))]

  ;; AppCom
  ;; Evaluate a Component
  [(eval Σ σ e_1 ϕ p C Σ_1 ω_1)
   (eval Σ_1 σ e_2 ϕ p v Σ_2 ω_2)
   ------------------------------ "AppCom"
   (eval Σ σ (e_1 e_2) ϕ p (C v) Σ_2 (append-ω ω_1 ω_2))]

  ;; AppSetComp
  [(eval π   σ e_1 ϕ p (setter l p) π_1 ω_1)
   (eval π_1 σ e_2 ϕ p cl π_2 ω_2)
   (side-condition (member (term ϕ) '(Init Succ)))
   ;;(where - TODO: will check the big bracket on the bottom... eventually
   --------------------------------- "AppSetComp"
   (eval π σ (app e_1 e_2) ϕ p
         () π_3 (append-ω ω_1 ω_2))]

  ;; AppSetNormal
  [(eval m σ e_1 Normal - (l p) m_1 ω_1)
   (eval m_1 σ e_2 Normal - cl m_2 ω_2)
   ;; (where - TODO: will check big bracket on bottom... eventually
   -------- "AppSetNormal"
   (eval m σ (app e_1 e_2) Normal -
         () m_2 (append-ω ω_1 ω_2))]

  ;; SttBind
  #;[ ;; TODO
   -------------- "SttBind"
    ;; TODO
   ]

  ;; SttReBind
  #;[ ;; TODO
   -------------- "SttReBind"
    ;; TODO
   ]
  )

;;
;; ------------------------------ CHECK
;;

(define-judgment-form React-tRace
  #:mode (check I I I O O O)
  #:contract (check m_1 δ t μ m_2 ω)
  ;; check takes in tree memory m_1, a definition table δ, and a tree t,
  ;; then outputs modified tree memory m_2, updates the mode to rendered or • (event loop), and prints ω
  ;; re-renders only when mode is rendered. Otherwise just modifies tree memory when mode is •

  ;; CheckConst
  ;; Constants pass through
  [
   --------------------- "CheckConst"
   (check m δ k • m ())]

  ;; CheckClos
  ;; Closures also pass through
  [
   ------------------ "CheckClos"
   (check m δ cl • m ())]

  ;; CheckArray
  #;[ ;; TODO
   -------- "CheckArray"
   ;; TODO
   ]

  ;; CheckIdle
  [ ;; TODO
   -------- "CheckIdle"
   (check m_1 δ p μ m_2 ω)])



;; Substitution
;; Replaces free occurrences of x with v in e, respecting shadowing.

(define-metafunction React-tRace
  subst : e x v -> e

  [(subst x x v) v]
  [(subst y x v) y]

  [(subst unit x v) unit]
  [(subst true x v) true]
  [(subst false x v) false]
  [(subst n x v) n]
  [(subst (setter l) x v) (setter l)]

  [(subst (λ (x) e) x v) (λ (x) e)]
  [(subst (λ (y) e) x v) (λ (y) (subst e x v))]

  [(subst (let ([x e_bound]) e_body) x v)
   (let ([x (subst e_bound x v)]) e_body)]
  [(subst (let ([y e_bound]) e_body) x v)
   (let ([y (subst e_bound x v)]) (subst e_body x v))]

  ;; state: x_state and x_set shadow in e_body, not in e_init
  [(subst (state l (x x_set) e_init e_body) x v)
   (state l (x x_set) (subst e_init x v) e_body)]
  [(subst (state l (x_state x) e_init e_body) x v)
   (state l (x_state x) (subst e_init x v) e_body)]
  [(subst (state l (x x) e_init e_body) x v)
   (state l (x x) (subst e_init x v) e_body)]
  [(subst (state l (x_state x_set) e_init e_body) x v)
   (state l (x_state x_set) (subst e_init x v) (subst e_body x v))]

  [(subst (+ e_1 e_2) x v) (+ (subst e_1 x v) (subst e_2 x v))]
  [(subst (- e_1 e_2) x v) (- (subst e_1 x v) (subst e_2 x v))]
  [(subst (= e_1 e_2) x v) (= (subst e_1 x v) (subst e_2 x v))]
  [(subst (array e ...) x v) (array (subst e x v) ...)]
  [(subst (print e) x v) (print (subst e x v))]
  [(subst (if e_1 e_2 e_3) x v)
   (if (subst e_1 x v) (subst e_2 x v) (subst e_3 x v))]
  [(subst (begin e_1 e_2) x v)
   (begin (subst e_1 x v) (subst e_2 x v))]
  [(subst (e_1 e_2) x v)
   ((subst e_1 x v) (subst e_2 x v))])


;; Store operations
(define-metafunction React-tRace
  store-lookup : σ l -> any
  [(store-lookup ((l v) (l_rest v_rest) ...) l) v]
  [(store-lookup ((l_other v_other) (l_rest v_rest) ...) l)
   (store-lookup ((l_rest v_rest) ...) l)]
  [(store-lookup () l) #f])

(define-metafunction React-tRace
  store-update : σ l v -> σ
  [(store-update ((l v_old) (l_rest v_rest) ...) l v)
   ((l v) (l_rest v_rest) ...)]
  [(store-update ((l_other v_other) (l_rest v_rest) ...) l v)
   ,(cons (term (l_other v_other))
          (term (store-update ((l_rest v_rest) ...) l v)))]
  [(store-update () l v) ((l v))])




;; Queue operations

(define-metafunction React-tRace
  queue-get : Q l -> (v ...)
  [(queue-get ((l (v ...)) (l_rest (v_rest ...) ) ...) l) (v ...)]
  [(queue-get ((l_other (v_other ...)) (l_rest (v_rest ...) ) ...) l)
   (queue-get ((l_rest (v_rest ...) ) ...) l)]
  [(queue-get () l) ()])

(define-metafunction React-tRace
  queue-push : Q l v -> Q
  [(queue-push ((l (v_existing ...)) (l_rest (v_rest ...) ) ...) l v_new)
   ((l (v_existing ... v_new)) (l_rest (v_rest ...) ) ...)]
  [(queue-push ((l_other (v_other ...)) (l_rest (v_rest ...) ) ...) l v_new)
   ,(cons (term (l_other (v_other ...)))
          (term (queue-push ((l_rest (v_rest ...) ) ...) l v_new)))]
  [(queue-push () l v_new)
   ((l (v_new)))])

(define-metafunction React-tRace
  queue-clear : Q l -> Q
  [(queue-clear ((l (v ...)) (l_rest (v_rest ...) ) ...) l)
   ((l ()) (l_rest (v_rest ...) ) ...)]
  [(queue-clear ((l_other (v_other ...)) (l_rest (v_rest ...) ) ...) l)
   ,(cons (term (l_other (v_other ...)))
          (term (queue-clear ((l_rest (v_rest ...) ) ...) l)))]
  [(queue-clear () l) ()])

(define-metafunction React-tRace
  queue-nonempty-labels : Q -> (l ...)
  [(queue-nonempty-labels ()) ()]
  [(queue-nonempty-labels ((l ()) (l_rest (v_rest ...) ) ...))
   (queue-nonempty-labels ((l_rest (v_rest ...) ) ...))]
  [(queue-nonempty-labels ((l (v v_more ...)) (l_rest (v_rest ...) ) ...))
   ,(cons (term l) (term (queue-nonempty-labels ((l_rest (v_rest ...) ) ...))))])


;; Applying updaters
;; Each updater is a lambda; we apply them left-to-right to get the new value.

(define-metafunction React-tRace
  apply-updaters : v (v ...) -> v
  [(apply-updaters v_current ()) v_current]
  [(apply-updaters v_current (v_updater v_rest ...))
   (apply-updaters (apply-one v_current v_updater) (v_rest ...))])

(define-metafunction React-tRace
  apply-one : v v -> v
  [(apply-one v_current (λ (x) e))
   ,(eval-base (term (subst e x v_current)))])


;; Base reduction (ordinary call-by-value)

(define ->base
  (reduction-relation
   React-tRace

   [--> (+ n_1 n_2) ,(+ (term n_1) (term n_2)) "+"]
   [--> (- n_1 n_2) ,(- (term n_1) (term n_2)) "-"]
   [--> (= n_1 n_2)
        ,(if (= (term n_1) (term n_2)) (term true) (term false))
        "="]

   [--> (if true e_then e_else) e_then "if-true"]
   [--> (if false e_then e_else) e_else "if-false"]

   [--> (begin v e) e "begin"]

   [--> (let ([x v]) e) (subst e x v) "let"]

   [--> ((λ (x) e) v) (subst e x v) "β"]

   ;; print returns unit. The paper uses an output buffer; we simplify.
   [--> (print v) unit "print"]))

(define -->base
  (compatible-closure ->base React-tRace E))

(define (eval-base e)
  (define results (apply-reduction-relation* -->base e))
  (if (= (length results) 1)
      (first results)
      results))


;; React runtime reduction
;;
;; This models one component's render cycle:
;; - Init phase evaluates and stores Hook initializers
;; - Succ phase reads persistent state from the store
;; - Setter calls queue updaters (they don't mutate local variables)
;; - Check phase applies queued updates to the store
;;
;; This does NOT model the paper's full tree-memory/reconciliation/retry
;; semantics. It's enough to show how Hook state persists and setters queue.

(define -->react
  (reduction-relation
   React-tRace

   ;; Ordinary reduction within render
   [--> (render ϕ (in-hole E e) σ Q)
        (render ϕ (in-hole E e_new) σ Q)
        (where (e_new) ,(apply-reduction-relation ->base (term e)))
        "render-base"]

   ;; During Init, reduce e_init before processing the state form
   [--> (render Init (in-hole E-init (state l (x_state x_set) e_init e_body)) σ Q)
        (render Init (in-hole E-init (state l (x_state x_set) e_init_new e_body)) σ Q)
        (where (e_init_new) ,(apply-reduction-relation ->base (term e_init)))
        (side-condition (not (redex-match? React-tRace v (term e_init))))
        "state-init-step"]

   ;; Setter application: queue the updater, return unit immediately.
   ;; The queued function will be applied during check, not now.
   [--> (render ϕ (in-hole E ((setter l) v_updater)) σ Q)
        (render ϕ (in-hole E unit) σ (queue-push Q l v_updater))
        "setter-queue"]

   ;; Init: e_init is now a value; store it and bind variables
   [--> (render Init (in-hole E (state l (x_state x_set) v_init e_body)) σ Q)
        (render Init
                (in-hole E (subst (subst e_body x_state v_init) x_set (setter l)))
                (store-update σ l v_init)
                Q)
        "state-init"]

   ;; Succ: ignore e_init, read from store, bind variables
   [--> (render Succ (in-hole E (state l (x_state x_set) e_init e_body)) σ Q)
        (render Succ
                (in-hole E (subst (subst e_body x_state v_stored) x_set (setter l)))
                σ
                Q)
        (where v_stored (store-lookup σ l))
        (side-condition (term v_stored))
        "state-succ"]

   ;; Render done
   [--> (render ϕ v σ Q)
        (done v σ Q)
        "render-done"]

   ;; Check: apply queued updates one label at a time
   [--> (check σ Q)
        (check (store-update σ l v_new) (queue-clear Q l))
        (where (l l_rest ...) (queue-nonempty-labels Q))
        (where v_old (store-lookup σ l))
        (where (v_updater ...) (queue-get Q l))
        (where v_new (apply-updaters v_old (v_updater ...)))
        "check-apply"]

   ;; Check done: no more pending updates
   [--> (check σ Q)
        (done unit σ Q)
        (where () (queue-nonempty-labels Q))
        "check-done"]))


;; Convenience functions

(define (render-init e [σ '()] [Q '()])
  (apply-reduction-relation* -->react (term (render Init ,e ,σ ,Q))))

(define (render-succ e σ [Q '()])
  (apply-reduction-relation* -->react (term (render Succ ,e ,σ ,Q))))

(define (run-check σ Q)
  (apply-reduction-relation* -->react (term (check ,σ ,Q))))

(define (done-value config)
  (match config
    [`(done ,v ,σ ,Q) v]
    [_ config]))

(define (done-store config)
  (match config
    [`(done ,v ,σ ,Q) σ]
    [_ config]))

(define (done-queue config)
  (match config
    [`(done ,v ,σ ,Q) Q]
    [_ config]))


;; Tests

(module+ test
  (require rackunit)

  ;; Base language
  (check-equal? (eval-base (term (+ 1 2))) (term 3))
  (check-equal? (eval-base (term (- 5 2))) (term 3))
  (check-equal? (eval-base (term (= 2 2))) (term true))
  (check-equal? (eval-base (term (= 2 3))) (term false))

  (check-equal? (eval-base (term (if true 1 2))) (term 1))

  (check-equal? (eval-base (term (if false 1 2))) (term 2))
  (check-equal? (eval-base (term (begin 1 2))) (term 2))

  (check-equal? (eval-base (term ((λ (x) (+ x 1)) 4))) (term 5))
  (check-equal? (eval-base (term (let ([x 3]) (+ x 2)))) (term 5))
  (check-equal? (eval-base (term ((λ (x) ((λ (x) x) 2)) 1))) (term 2))

  ;; Store helpers
  (check-equal? (term (store-lookup ((0 5) (1 10)) 0)) (term 5))
  (check-equal? (term (store-lookup ((0 5) (1 10)) 1)) (term 10))
  (check-equal? (term (store-lookup () 0)) (term #f))
  (check-equal? (term (store-update ((0 5)) 0 99)) (term ((0 99))))
  (check-equal? (term (store-update ((0 5)) 1 10)) (term ((0 5) (1 10))))



  ;; Queue helpers
  (check-equal? (term (queue-get ((0 ((λ (x) x)))) 0)) (term ((λ (x) x))))
  (check-equal? (term (queue-get () 0)) (term ()))
  (check-equal? (term (queue-push () 0 (λ (x) x))) (term ((0 ((λ (x) x))))))
  (check-equal? (term (queue-nonempty-labels ((0 ()) (1 ((λ (x) x)))))) (term (1)))



  ;; Updater application
  (check-equal? (term (apply-updaters 5 ())) (term 5))
  (check-equal? (term (apply-updaters 5 ((λ (x) (+ x 1))))) (term 6))
  (check-equal? (term (apply-updaters 5 ((λ (x) (+ x 1)) (λ (x) (+ x 1))))) (term 7))

  ;; useState runtime

  ;; Init stores the initial value

  (let ([result (first (render-init (term (state 0 (count setCount) 0 count))))])
    (check-equal? (done-value result) (term 0))
    (check-equal? (done-store result) (term ((0 0)))))

  

  ;; Init evaluates e_init (not just accepts values)
  (let ([result (first (render-init (term (state 0 (count setCount) (+ 1 2) count))))])
    (check-equal? (done-value result) (term 3))
    (check-equal? (done-store result) (term ((0 3)))))


  



  ;; Succ reads from store, ignores e_init
  (let ([result (first (render-succ
                        (term (state 0 (count setCount) 0 count))
                        (term ((0 5)))))])
    (check-equal? (done-value result) (term 5))

    (check-equal? (done-store result) (term ((0 5)))))

  ;; Setter queues an update; this render still sees the old value
  (let ([result (first (render-init
                        (term (state 0 (count setCount) 0
                                (begin (setCount (λ (x) (+ x 1))) count)))))])
    
    (check-equal? (done-value result) (term 0))

    (check-equal? (done-store result) (term ((0 0))))
    (check-equal? (length (term (queue-get ,(done-queue result) 0))) 1))


  
  ;; Check applies queued update

  (let ([result (first (run-check
                        (term ((0 0)))
                        (term ((0 ((λ (x) (+ x 1))))))))])
    (check-equal? (done-store result) (term ((0 1)))))

  

  ;; Multiple queued updates compose left-to-right
  (let ([result (first (run-check
                        (term ((0 0)))
                        (term ((0 ((λ (x) (+ x 1)) (λ (x) (+ x 1))))))))])
    (check-equal? (done-store result) (term ((0 2)))))

  




  ;; Full cycle: init -> queue update -> check -> re-render sees new value
  (let* ([r1 (first (render-init
                     (term (state 0 (count setCount) 0
                             (begin (setCount (λ (x) (+ x 1))) count)))))]
         [r2 (first (run-check (done-store r1) (done-queue r1)))]
         [r3 (first (render-succ
                     (term (state 0 (count setCount) 0 count))
                     (done-store r2)))])
    (check-equal? (done-value r1) (term 0))
    (check-equal? (done-store r2) (term ((0 1))))
    (check-equal? (done-value r3) (term 1)))

  


  ;; Multiple hooks in one component body
  (let ([result (first (render-init
                        (term (state 0 (a setA) 10
                                (state 1 (b setB) 20
                                  (+ a b))))))])
    (check-equal? (done-value result) (term 30))
    (check-equal? (term (store-lookup ,(done-store result) 0)) (term 10))
    (check-equal? (term (store-lookup ,(done-store result) 1)) (term 20)))

  

)


(provide React-tRace
         subst
         store-lookup store-update
         queue-get queue-push queue-clear queue-nonempty-labels
         apply-updaters
         ->base -->base eval-base
         -->react
         render-init render-succ run-check
         done-value done-store done-queue
         (all-from-out redex))
