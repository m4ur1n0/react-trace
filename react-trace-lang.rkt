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
     (let (x e) e) ;; probably not necessary

     ;; useState: (state l (x_state x_set) e_init e_body)
     ;; In Init phase, e_init is evaluated and stored at label l.
     ;; In Succ phase, e_init is ignored; we read from the store.
     ;; x_state and x_set are bound in e_body only.
         ;; paper equivalent: < let (x, xset) = useState^l e_1 in e_2 >
     (state l (x_state x_set) e_init e_body)

     ;; Setter value (appears at runtime after state is processed)
     (setter l p))

  (op + - * / < <= = > >= !=)

  ;; Values
  (v ::=
     k
     cl
     C
     cs
     (s ...)
     (setter l p)) ;;need to be using a particular setter

  (k ::= n true false ())

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

  (π ::= (view cs (dec ...) ρ q t))
  (dec ::= Check Effect (dec ...))

  ;; ρ = a store of state vars within a view
  (ρ ::= ((l v q) ...))  
  (q ::= (cl ...)) ;; the setter also stored

  
  (Σ ::= m π)
  (m ::= ((p π) ...) mt)
  (t ::= k cl p (t ...))

  ;; Runtime configurations for the one-component model

  (ϕ ::= Init Succ Normal) ;; Change phase to phi, or ϕ, to better follow paper 

  ;; Store: maps Hook labels to their persistent values
  (σ ::= ((x v) ...)) ;; ordinary var environment, not hook store

  ;; Queue: maps Hook labels to lists of pending updater functions
  (Q ::= ((l (v ...)) ...))

  (μ ::= rendered ⟲ • (μ ...)) ;; "rendered" corresponds to neuron-looking thing

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
  (config (CONFIG t m ω δ μ))

  ;; Allow hook to take in either input, allowing initialization
  (hook-input ::= (e δ) (t m ω δ μ)))


(define-judgment-form React-tRace
  #:mode (hook I O)
  #:contract (hook hook-input (t m ω δ μ))

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
  [(where (_ ... cl_handler _ ...) (handlers m_1 t))
   (where (λ x_arg e_body σ_cl) cl_handler)
   (eval m_1 (store-update σ_cl x_arg ()) e_body Normal - v m_2 ω_2)
   ----------------------------------- "StepEvent"
   (hook (t m_1 ω_1 δ •)
         (t m_2 (append-ω ω_1 ω_2) δ ⟲))]
  )


;; The append -|-|- helper function, extend output buffer
(define-metafunction React-tRace
  append-ω : ω ω -> ω
  [(append-ω () ω) ω]
  [(append-ω (ω_1 (fun x -> e)) ω_2)
   ((append-ω ω_1 ω_2) (fun x -> e))])


;;
;; ------------------------------ HANDLERS
;; 
(define-metafunction React-tRace
  handlers : m t -> (cl ...)
  ;; if t = k (constant)
  [(handlers m k)
   ()]
  ;; if t = cl (closure)
  [(handlers m cl)
   (cl)]
  ;; if t = [t_i]^n (array)
  [(handlers m (t_i ...))
   ,(apply append (map (λ (t_i) (term (handlers m ,t_i))) (term (t_i ...))))]
  ;; if t = p (path), look up view and recurse on child
  [(handlers m p)
   (handlers m (π-child (m-lookup m p)))])


;;
;; ------------------------------ INIT
;;

(define-judgment-form React-tRace
  #:mode (init I I I O O O)
  #:contract (init m_1 δ s t m_2 ω)
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

  ;; InitArray-Nil
  [-------- "InitArray-Nil"
   (init m δ () () m ())]
  
  ;; InitArray-Cons
  [(init m_0 δ s_1 t_1 m_1 ω_1)
   (init m_1 δ (s_rest ...) (t_rest ...) m_2 ω_2)
   -------- "InitArray-Cons"
   (init m_0 δ (s_1 s_rest ...)
         (t_1 t_rest ...)
         m_2
         (append-ω ω_1 ω_2))])


;;
;; ------------------------------ APPLY UPDATES
;;


(define-judgment-form React-tRace
  #:mode (apply-updaters I I I I I O O O)
  #:contract (apply-updaters π q ϕ p v v π ω)

  ;; no queued updates = final val is starting val
  [--------------------------------------"ApplyUpdatersDone"
   (apply-updaters π () ϕ p v v π ())]

  ;; apply first updater closure, hten keep going
  [(eval π
         (env-extend σ_cl x_arg v_in)
         e_updater
         ϕ p v_next π_1 ω_1)

   (apply-updaters π_1 (cl_rest ...) ϕ p v_next v_out π_2 ω_2)
   ----------------------------------------------------------"ApplyUpdatersStep"
   (apply-updaters π
                   (((λ (x_arg) e_updater) σ_cl) cl_rest ...)
                   ϕ p v_in v_out π_2 (append-ω ω_1 ω_2))])
  


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
   (eval Σ σ (e_1 e_2) ϕ p v Σ_3 (append-ω (append-ω ω_1 ω_2) ω_3))]

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

   ;; get the hook store proper actually
   (where ρ_2 (π-ρ π_2))
   (where ρ_3 (ρ-enqueue ρ_2 l cl))
   (where π_2+ (π-set-ρ π_2 ρ_3))
   (where π_3 (update-dec π_2 Check))
   --------------------------------- "AppSetComp"
   (eval π σ (e_1 e_2) ϕ p ;; removed (app ...), our language says application is (e e) not (app e e)?
         () π_3 (append-ω ω_1 ω_2))]

  ;; AppSetNormal
  [(eval m σ e_1 Normal - (l p) m_1 ω_1)
   (eval m_1 σ e_2 Normal - cl m_2 ω_2)
   ;; (where - TODO: will check big bracket on bottom... eventually
   -------- "AppSetNormal"
   (eval m σ (e_1 e_2) Normal - ;; removed (app ...), our language says application is (e e) not (app e e)?
         () m_2 (append-ω ω_1 ω_2))]

  ;; SttBind
    ;; EVALUATING A STATE BINDING DURING INITIAL RENDER
    ;; π_1 will now have { π_1.sttst = [ l --> { val: v_1 , sttq : [] } }
    ;; σ will now have [ x |-> v_1 , x_set |-> (l p) ]
    ;; and e_2 will evaluae under this new context

  ;; first eval the initializer,
  ;; then store that val in teh view's hook store,
  ;; then bind state var and setter var,
  ;; then eval body
  
  [(eval π σ e_init Init p v_init π_1 ω_1)

   ;; big bracket section for sttbind in fig 5
   (where ρ_1 (π-ρ π_1))
   (where ρ_2 (ρ-init ρ_1 l v_init))
   (where π_1+ (π-set-ρ π_1 ρ_2))

   (where σ+ (env-extend
              (env-extend σ x_state v_init)
              x_set
              (setter l p)))

   ;; then we can evaluate e_2 under these conditions
   (eval π_1+ σ+ e_body Init p v_body π_2 ω_2)
   -------------- "SttBind"

   (eval π σ
         (state l (x_state x_set) e_init e_body)
         Init p
         v_body
         π_2
         (append-ω ω_1 ω_2))
   ]


  ;; SttReBind
  ;; if we use a useState binding after initial render (pretty much the whole ballgame)
  ;; read the old hook state from rho, apply the updaters, clear the q, bind state var and setter then exec body

  ;;start by getting the pieces we need
  
  [ (where ρ_0 (π-ρ π_0))
    (where v_old (ρ-val ρ_0 l))
    (where q_old (ρ-queue ρ_0 l))

    ;; if the label is missing then dis-apply this rule
    (side-condition (not (equal? (term v_old) #f)))
    (side-condition (not (equal? (term q_old) #f)))

    ;; apply the queued updaters with the helper i jus wrote
    (apply-updaters π_0 q_old Succ p v_old v_new π_n ω_updates)

    ;; store the real final state val, then clear the q cause we applied everything
    (where ρ_n (π-ρ π_n))
    (where ρ_done (ρ-set-clear ρ_n l v_new))
    (where π_n+ (π-set-ρ π_n ρ_done))

    ;; bind x_state and x_set proper
    (where σ+ (env-extend
               (env-extend σ x_state v_new)
               x_set
               (setter l p)))

    ;; finally eval
    (eval π_n+ σ+ e_body Succ p v_body π_final ω_body)
    
   -------------- "SttReBind"
   (eval π_0 σ
         (state l (x_state x_set) e_init e_body)
         Succ p v_body π_final
         (append-ω ω_updates ω_body))
   ]
  )


;; Metafunction to update view's state store





;; Metafunction to update view's decision
(define-metafunction React-tRace
  update-dec : π dec -> π
  [(update-dec (view cs (dec_1 ...) ρ q t) dec_2) (view cs (union-dec (dec_1 ...) dec_2) ρ q t)])

;; Add d to a list of decisions only if not already present
(define-metafunction React-tRace
  union-dec : (dec ...) dec -> (dec ...)
  [(union-dec (dec_1 ... dec dec_2 ...) dec) (dec_1 ... dec dec_2 ...)] ;; already present, just return same list
  [(union-dec (dec_1 ...) dec) (dec_1 ... dec)]) ;; not present, append




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
  ;; Check each element left-to-right, threading memory through.
  ;; Base Case: empty array
  [-------- "CheckArray-Nil"
   (check m δ () () m ())]

  ;; Inductive Step: Check head, then tail with updated memory
  [(check m_0 δ t_1 μ_1 m_1 ω_1)
   (check m_1 δ (t_rest ...)
          (μ_rest ...) m_2 ω_2)
   ------------------------------ "CheckArray-Cons"
   (check m_0 δ
          (t_1 t_rest ...)
          (μ_1 μ_rest ...)
          m_2
          (append-ω ω_1 ω_2))]

  ;; CheckIdle
  [(where π (m-lookup m_1 p))
   (side-condition (not (eq? (term π) #f)))
   (side-condition (not (member 'Check (term (π-dec π)))))
   (check m_1 δ (π-child π) μ m_2 ω)
   ------------------------------- "CheckIdle"
   (check m_1 δ p μ m_2 ω)])


;; Metafunction to find a view given a path
(define-metafunction React-tRace
  m-lookup : m p -> any
  [(m-lookup ((p_0 π_0) (p_rest π_rest) ...) p) π_0
   (side-condition (equal? (term p_0) (term p)))]
  [(m-lookup ((p_0 π_0) (p_rest π_rest) ...) p)
   (m-lookup ((p_rest π_rest) ...) p)
   (side-condition (not (equal? (term p_0) (term p))))]
  [(m-lookup mt p) #f]
  [(m-lookup () p) #f])

;; Metafunction to get a view's child
(define-metafunction React-tRace
  π-child : π -> t
  [(π-child (view cs (dec ...) ρ q t)) t])

;; Metafunction to get a view's decision
(define-metafunction React-tRace
  π-dec : π -> (dec ...)
  [(π-dec (view cs (dec ...) ρ q t)) (dec ...)])

  
;; Store operations

;; pull the hook state store out of a view
(define-metafunction React-tRace
  π-ρ : π -> ρ
  [(π-ρ (view cs (dec ...) ρ q t))
   ρ])


;; replace the whole hook state store of a view
(define-metafunction React-tRace
  π-set-ρ : π ρ -> π
  [(π-set-ρ (view cs (dec ...) ρ_old q t) ρ_new)
   (view cs (dec ...) ρ_new q t)])

;; initialize or replace the state entry for hook label l
;; in the pdf this is the part of the reduction relation that is like ρ[l |-> { val : v, sttq : [] }]
(define-metafunction React-tRace
  ρ-init : ρ l v -> ρ

  ;; if l is already there, replace the val with v then clear queue
  [(ρ-init ((l_before v_before q_before) ... (l v_old q_old) (l_after v_after q_after) ...) ;; maybe delete the l_after requirement? we want it to work if it's the last entry?
           l
           v_new)
   ((l_before v_before q_before) ... (l v_new ()) (l_after v_after q_after) ...)]


  ;; if l isn't in the store yet
  [(ρ-init ((l_old v_old q_old) ...) l_new v_new)
   ((l_old v_old q_old) ... (l_new v_new ()))
   (side-condition
    (not (member (term l_new) (term (l_old ...)))))])


;; extend the actual environment and allow shadowing
(define-metafunction React-tRace
  env-extend : σ x v -> σ
  [(env-extend ((x_old v_old) ...) x v)
   ((x v) (x_old v_old) ...)])


; lookup val from hook l (not calling it lookup because that might make more sense for something that also return sthe setter
(define-metafunction React-tRace
  ρ-val : ρ l -> v ;;any?
  [(ρ-val ((l v q) (l_rest v_rest q_rest) ...) l) ;; recursively search, so l if we find it will be first
   v]

  [(ρ-val ((l_other v_other q_other) (l_rest v_rest q_rest) ...) l) ;; if we don't see it yet, keep checking
   (ρ-val ((l_rest v_rest q_rest) ...) l)
   (side-condition (not (equal? (term l_other) (term l))))] ;; make sure l really doesn't match

  [(ρ-val () l) ;; base case, fail
   #f] ;; should we error? should we trust caller to error?
  )



;; Get queueued updatedr closures stored @ l
(define-metafunction React-tRace
  ρ-queue : ρ l -> q ;; any?

  [(ρ-queue ((l v q) (l_rest v_rest q_rest) ...) l) ;;recursive like lookup v
   q]

  [(ρ-queue ((l_other v_other q_other) (l_rest v_rest q_rest) ...) l) ;; if we don't see it yet, keep checking
   (ρ-queue ((l_rest v_rest q_rest) ...) l)
   (side-condition (not (equal? (term l_other) (term l))))]

  [(ρ-queue () l) ;; base
   #f])


;; replace a hook @ label l with a new val and q
(define-metafunction React-tRace
  ρ-set : ρ l v q -> ρ

  [(ρ-set ((l_before v_before q_before) ... (l v_old q_old) (l_after v_after q_after) ...)
          l
          v_new
          q_new)
   ((l_before v_before q_before) ... (l v_new q_new) (l_after v_after q_after) ...)]

  [(ρ-set ((l_old v_old q_old) ...) l_new v_new q_new)
   ((l_old v_old q_old) ... (l_new v_new q_new))
   (side-condition
    (not (member (term l_new) (term (l_old ...)))))])


(define-metafunction React-tRace ;; helper to write new value and empty queue
  ρ-set-clear : ρ l v -> ρ
  [(ρ-set-clear ρ l v)
   (ρ-set ρ l v ())])

  
;; put updates in state queue
(define-metafunction React-tRace
  ρ-enqueue : ρ l cl -> ρ

  [(ρ-enqueue ((l_before v_before q_before) ...
               (l v_old (cl_old ...))
               (l_after v_after q_after) ...)
              l
              cl_new)
   ((l_before v_before q_before) ...
    (l v_old (cl_old ... cl_new))
    (l_after v_after q_after) ...)])




  

(define-metafunction React-tRace ;; should be like env-lookup or something? either way this symbol is wrong
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


   





;;
;; ------------------------------ TESTS
;;
;; ---- InitConst ----
#;(redex-match React-tRace δ (term ()))

#;(redex-match React-tRace ω (term ()))

#;(redex-match React-tRace s (term ((λ (x_1) x_1) ())))

(test-equal
  (judgment-holds (init mt () 42 t m_2 ω) (t m_2 ω))
  '((42 mt ())))

(test-equal
  (judgment-holds (init mt () true t m_2 ω) (t m_2 ω))
  '((true mt ())))

(test-equal
  (judgment-holds (init mt () () t m_2 ω) (t m_2 ω))
  '((() mt ())))

;; ---- InitClos ----
(test-equal
  (judgment-holds (init mt () ((λ (x_1) x_1) ()) t m_2 ω) (t m_2 ω))
  '((((λ (x_1) x_1) ()) mt ())))

(test-equal
  (judgment-holds (init mt () ((λ (x_1) x_1) ((0 42))) t m_2 ω) (t m_2 ω))
  '((((λ (x_1) x_1) ((0 42))) mt ())))

(test-equal
  (judgment-holds (init mt () ((λ (x_1) (x_1 x_1)) ()) t m_2 ω) (t m_2 ω))
  '((((λ (x_1) (x_1 x_1)) ()) mt ())))

(test-equal
  (judgment-holds (init mt () ((λ (x_1) x_1) ((0 42) (1 true))) t m_2 ω) (t m_2 ω))
  '((((λ (x_1) x_1) ((0 42) (1 true))) mt ())))

(test-equal
  (judgment-holds (init mt () ((λ (x_1) 42) ()) t m_2 ω) (t m_2 ω))
  '((((λ (x_1) 42) ()) mt ())))

;; Memory is non-empty but unchanged — closures don't modify memory
(test-equal
  (judgment-holds
    (init ((0 (view (C 42) () () () 42))) ()
          ((λ (x_1) x_1) ())
          t m_2 ω)
    (t m_2 ω))
  '((((λ (x_1) x_1) ()) ((0 (view (C 42) () () () 42))) ())))


;; ---- InitArray ----

;; ---- InitArray-Nil ----
(test-equal
  (judgment-holds (init mt () () t m_2 ω) (t m_2 ω))
  '((() mt ())))

;; ---- InitArray-Cons ----
(test-equal
  (judgment-holds (init mt () (42) t m_2 ω) (t m_2 ω))
  '(((42) mt ())))

(test-equal
  (judgment-holds (init mt () (1 2 3) t m_2 ω) (t m_2 ω))
  '(((1 2 3) mt ())))

(test-equal
  (judgment-holds
    (init mt ()
          (42 ((λ (x_1) x_1) ()) true)
          t m_2 ω)
    (t m_2 ω))
  '(((42 ((λ (x_1) x_1) ()) true) mt ())))

(test-equal
  (judgment-holds
    (init mt ()
          ((1 2) (3 4))
          t m_2 ω)
    (t m_2 ω))
  '((((1 2) (3 4)) mt ())))

;; ---- CheckConst ----
;; Memory doesn't matter for constants, but provide non-empty m to be safe
(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () 42))) () 42 μ m_2 ω)
    (μ m_2 ω))
  '((• ((0 (view (C 42) () () () 42))) ())))

(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () 42))) () true μ m_2 ω)
    (μ m_2 ω))
  '((• ((0 (view (C 42) () () () 42))) ())))

;; ---- CheckClos ----
(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () 42))) ()
           ((λ (x_1) x_1) ())
           μ m_2 ω)
    (μ m_2 ω))
  '((• ((0 (view (C 42) () () () 42))) ())))

;; ---- CheckArray-Nil ----
(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () 42))) () (42) μ m_2 ω)
    (μ m_2 ω))
  '(((•) ((0 (view (C 42) () () () 42))) ())))

;; ---- CheckArray-Cons ----
(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () 42))) () (42) μ m_2 ω)
    (μ m_2 ω))
  '(((•) ((0 (view (C 42) () () () 42))) ())))

(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () 42))) () (1 2 3) μ m_2 ω)
    (μ m_2 ω))
  '(((• • •) ((0 (view (C 42) () () () 42))) ())))

(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () 42))) ()
           (42 ((λ (x_1) x_1) ()))
           μ m_2 ω)
    (μ m_2 ω))
  '(((• •) ((0 (view (C 42) () () () 42))) ())))

;; ---- CheckIdle ----
(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () 42))) ()
           0 μ m_2 ω)
    (μ m_2 ω))
  '((• ((0 (view (C 42) () () () 42))) ())))

(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () ((λ (x_1) x_1) ())))) ()
           0 μ m_2 ω)
    (μ m_2 ω))
  '((• ((0 (view (C 42) () () () ((λ (x_1) x_1) ())))) ())))

(test-equal
  (judgment-holds
    (check ((0 (view (C 42) () () () 1))
            (1 (view (C 43) () () () 42))) ()
           0 μ m_2 ω)
    (μ m_2 ω))
  '((• ((0 (view (C 42) () () () 1))
        (1 (view (C 43) () () () 42))) ())))

;; ---- Handlers ----
(test-equal (term (handlers ((0 (view (C 42) () () () 42))) 42)) '())

(test-equal
  (term (handlers ((0 (view (C 42) () () () 42))) ((λ (x_1) x_1) ())))
  '(((λ (x_1) x_1) ())))

(test-equal
  (term (handlers ((0 (view (C 42) () () () 42)))
                  (42 ((λ (x_1) x_1) ()))))
  '(((λ (x_1) x_1) ())))