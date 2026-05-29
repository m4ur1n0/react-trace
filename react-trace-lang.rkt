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

  (π ::= (view cs (dec ...) ρ q t))
  (dec ::= Check Effect (dec ...))
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

  (μ ::= rendered ⟲ •) ;; "rendered" corresponds to neuron-looking thing

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
  #;[ ;; TODO
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
   (where π_3 (update-dec π_2 check))
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
   (check m δ μ (view ()) m ())]

  ;; Inductive Step: Check head, then tail with updated memory
  [(check m_0 δ s_1 μ_1 m_1 ω_1)
   (check m_1 δ (view (s_rest ...))
          (μ_rest ...) m_2 ω_2)
   ------------------------------ "CheckArray-Cons"
   (check m_0 δ (view (s_1 s_rest ...))
          (view (μ_1 μ_rest ...))
               m_2
               (append-ω ω_1 ω_2))]

  ;; CheckIdle
  [(where π (m-lookup m_1 p))
   (check m_1 δ (π-child π) μ m_2 ω)
   (side-condition (not (member 'check (term (π-dec π)))))
   ------------------------------- "CheckIdle"
   (check m_1 δ p μ m_2 ω)])


;; Metafunction to find a view given a path
(define-metafunction React-tRace
  m-lookup : m p -> π
  [(m-lookup ((p_0 π_0) (p_rest π_rest) ...) p) π_0
   (side-condition (equal? (term p_0) (term p)))]
  [(m-lookup ((p_0 π_0) (p_rest π_rest) ...) p)
   (m-lookup ((p_rest π_rest) ...) p)
   (side-condition (not (equal? (term p_0) (term p))))])

;; Metafunction to get a view's child
(define-metafunction React-tRace
  π-child : π -> t
  [(π-child (view cs (dec ...) ρ q t)) t])

;; Metafunction to get a view's decision
(define-metafunction React-tRace
  π-dec : π -> (dec ...)
  [(π-dec (view cs (dec ...) ρ q t)) (dec ...)])

  
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