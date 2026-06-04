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
  (P ::= (program (D ...) e))
  (D ::= (let C x = e))

  ;; Expressions
  (e ::= ()
     true
     false
     n
     x
     (e op e)
     (print e)
     (if e e e)
     (begin e e)
     (λ (x) e)
     (app e e)
     (let (x e) e) ;; probably not necessary
     (e ...)

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
 
  (x C y ::= (variable-except app eval init check hook apply-updaters state begin let if print setter view store rendered path))
  (l ::= natural)
  (n ::= integer)
  (p ::= (path natural) -)

  (View ::= (view cs (dec ...) Smap q t))
  (dec ::= Check Effect)

  ;; Smap = a store of state vars within a view
  (Smap ::= (store (l v q) ...))  
  (q ::= (cl ...)) ;; the setter also stored

  
  (Σ ::= m View)
  (m ::= ((p View) ...) mt)
  (t ::= k cl p (t ...))

  ;; Runtime configurations for the one-component model

  (ϕ ::= Init Succ Normal) ;; Change phase to phi, or ϕ, to better follow paper 

  ;; Store: maps Hook labels to their persistent values
  (σ ::= ((x v) ...)) ;; ordinary var environment, not hook store

  ;; Queue: maps Hook labels to lists of pending updater functions
  (Q ::= ((l (v ...)) ...))

  (μ ::= rendered ↺ • (μ ...)) ;; "rendered" corresponds to neuron-looking thing


                 
  (Outbuf ::= (v ...))

  ;; Render result outcome
  (outcome Normal Throw)

  ;; Stable marker
  (status Stable Rerendering)

  ;; External event queue (renamed from δ to avoid conflict with paper's δ)
  (evq ::= () (evq event))
  (event ::= (click ι) (change ι v))

  ;; Component definition table: maps component names to their body lambdas
  (δ ::= ((C (λ (x) e)) ...))

  ;; Top-level machine configurations
  (hook-input ::= (e evq δ) (t m Outbuf evq δ μ)))

(define-judgment-form React-tRace
  #:mode (hook I O)

  ;; "StepInit" — replaced by react-step; this version kept for reference
  [
   (where View_root (view (Root ()) () (store) () ()))
   (eval-view View_root () e Init (path 0) s View_after Outbuf)
   (init (((path 0) View_after)) δ s t m Outbuf_prime)
   ----------------------------------- "StepInit"
   (hook (e evq δ)
         (t m (append-Outbuf Outbuf Outbuf_prime) evq δ rendered))]

  ;; "StepCheck"
  [
   (check m_1 δ t μ m_2 Outbuf_2)
   ----------------------------------- "StepCheck"
   (hook (t m_1 Outbuf_1 evq δ ↺)
         (t m_2 (append-Outbuf Outbuf_1 Outbuf_2) evq δ μ))]

  ;; "StepEvent"
  [(where (_ ... cl_handler _ ...) (handlers m_1 t))
   (where ((λ (x_arg) e_body) σ_cl) cl_handler)
   (eval-mem m_1 (env-extend σ_cl x_arg ()) e_body v m_2 Outbuf_2)
   ----------------------------------- "StepEvent"
   (hook (t m_1 Outbuf_1 evq δ •)
         (t m_2 (append-Outbuf Outbuf_1 Outbuf_2) evq δ ↺))]
  )


;; The append -|-|- helper function, extend output buffer
(define-metafunction React-tRace
  append-Outbuf : Outbuf Outbuf -> Outbuf
  [(append-Outbuf () Outbuf) Outbuf]
  [(append-Outbuf (v_1 v_rest ...) Outbuf_2)
   (v_1 v_flat ...)
   (where (v_flat ...) (append-Outbuf (v_rest ...) Outbuf_2))])

;; pull the hook state store out of a view
(define-metafunction React-tRace
  View-Smap : View -> Smap
  [(View-Smap (view cs (dec ...) Smap q t))
   Smap])

;; Store operations

;; replace the whole hook state store of a view
(define-metafunction React-tRace
  View-set-Smap : View Smap -> View
  [(View-set-Smap (view cs (dec ...) Smap_old q t) Smap_new)
   (view cs (dec ...) Smap_new q t)])

;; initialize or replace the state entry for hook label l
;; in the pdf this is the part of the reduction relation that is like Smap[l |-> { val : v, sttq : [] }]
(define-metafunction React-tRace
  Smap-init : Smap l v -> Smap

  ;; if l is already there, replace the val with v then clear queue
  [(Smap-init (store (l_before v_before q_before) ... (l v_old q_old) (l_after v_after q_after) ...) ;; maybe delete the l_after requirement? we want it to work if it's the last entry?
           l
           v_new)
   (store (l_before v_before q_before) ... (l v_new ()) (l_after v_after q_after) ...)]


  ;; if l isn't in the store yet
  [(Smap-init (store (l_old v_old q_old) ...) l_new v_new)
   (store (l_old v_old q_old) ... (l_new v_new ()))
   (side-condition
    (not (member (term l_new) (term (l_old ...)))))])


;; extend the actual environment and allow shadowing
(define-metafunction React-tRace
  env-extend : σ any v -> σ
  [(env-extend ((x_old v_old) ...) x_new v)
   ((x_new v) (x_old v_old) ...)])


; lookup val from hook l (not calling it lookup because that might make more sense for something that also return sthe setter
(define-metafunction React-tRace
  Smap-val : Smap l -> any ;; v?
  [(Smap-val (store (l v q) (l_rest v_rest q_rest) ...) l) ;; recursively search, so l if we find it will be first
   v]

  [(Smap-val (store (l_other v_other q_other) (l_rest v_rest q_rest) ...) l) ;; if we don't see it yet, keep checking
   (Smap-val (store (l_rest v_rest q_rest) ...) l)
   (side-condition (not (equal? (term l_other) (term l))))] ;; make sure l really doesn't match

  [(Smap-val () l) ;; base case, fail
   #f] ;; should we error? should we trust caller to error?
  )

; store lookup, using variable bindings
(define-metafunction React-tRace
  store-lookup : σ x -> any
  [(store-lookup ((x_0 v_0) (x_rest v_rest) ...) x)
   v_0
   (side-condition (equal? (term x_0) (term x)))]
  [(store-lookup ((x_0 v_0) (x_rest v_rest) ...) x)
   (store-lookup ((x_rest v_rest) ...) x)
   (side-condition (not (equal? (term x_0) (term x))))]
  [(store-lookup () x) #f])



;; Get queueued updatedr closures stored @ l
(define-metafunction React-tRace
  Smap-queue : Smap l -> any ;; q?

  [(Smap-queue (store (l v q) (l_rest v_rest q_rest) ...) l) ;;recursive like lookup v
   q]

  [(Smap-queue (store (l_other v_other q_other) (l_rest v_rest q_rest) ...) l) ;; if we don't see it yet, keep checking
   (Smap-queue (store (l_rest v_rest q_rest) ...) l)
   (side-condition (not (equal? (term l_other) (term l))))]

  [(Smap-queue () l) ;; base
   #f])


;; replace a hook @ label l with a new val and q
(define-metafunction React-tRace
  Smap-set : Smap l v q -> Smap

  [(Smap-set (store (l_before v_before q_before) ... (l v_old q_old) (l_after v_after q_after) ...)
          l
          v_new
          q_new)
   (store (l_before v_before q_before) ... (l v_new q_new) (l_after v_after q_after) ...)]

  [(Smap-set (store (l_old v_old q_old) ...) l_new v_new q_new)
   (store (l_old v_old q_old) ... (l_new v_new q_new))
   (side-condition
    (not (member (term l_new) (term (l_old ...)))))])


(define-metafunction React-tRace ;; helper to write new value and empty queue
  Smap-set-clear : Smap l v -> Smap
  [(Smap-set-clear Smap l v)
   (Smap-set Smap l v ())])

  
;; put updates in state queue
(define-metafunction React-tRace
  Smap-enqueue : Smap l cl -> Smap

  [(Smap-enqueue (store (l_before v_before q_before) ...
               (l v_old (cl_old ...))
               (l_after v_after q_after) ...)
              l
              cl_new)
   (store (l_before v_before q_before) ...
    (l v_old (cl_old ... cl_new))
    (l_after v_after q_after) ...)])


(define-metafunction React-tRace
  mu-join : μ μ -> μ
  [(mu-join rendered _)  rendered]
  [(mu-join _ rendered)  rendered]
  [(mu-join ↺ _)         rendered]
  [(mu-join _ ↺)         rendered]
  [(mu-join • •)         •])

;; dec-has-check?: returns #t if Check appears in the dec list, #f otherwise.
;; Used to guard CheckIdle so it only fires when no Check is present.
(define-metafunction React-tRace
  dec-has-check? : (dec ...) -> any
  [(dec-has-check? (_ ... Check _ ...)) #t]
  [(dec-has-check? (dec ...))           #f])

;;
;; ------------------------------ δ-LOOKUP (component definition table)
;;
(define-metafunction React-tRace
  δ-lookup : δ C -> any
  [(δ-lookup ((C (λ (x) e)) (C_r (λ (x_r) e_r)) ...) C)
   (λ (x) e)]
  [(δ-lookup ((C_hd (λ (x_hd) e_hd)) (C_r (λ (x_r) e_r)) ...) C)
   (δ-lookup ((C_r (λ (x_r) e_r)) ...) C)
   (side-condition (not (equal? (term C_hd) (term C))))]
  [(δ-lookup () C)
   #f])

;;
;; ------------------------------ DELTA (primitive operations)
;;
(define-metafunction React-tRace
  delta : op n n -> v
  [(delta + n_1 n_2) ,(+ (term n_1) (term n_2))]
  [(delta - n_1 n_2) ,(- (term n_1) (term n_2))]
  [(delta * n_1 n_2) ,(* (term n_1) (term n_2))]
  [(delta / n_1 n_2) ,(quotient (term n_1) (term n_2))]
  [(delta < n_1 n_2)  ,(if (< (term n_1) (term n_2)) (term true) (term false))]
  [(delta <= n_1 n_2) ,(if (<= (term n_1) (term n_2)) (term true) (term false))]
  [(delta = n_1 n_2)  ,(if (= (term n_1) (term n_2)) (term true) (term false))]
  [(delta > n_1 n_2)  ,(if (> (term n_1) (term n_2)) (term true) (term false))]
  [(delta >= n_1 n_2) ,(if (>= (term n_1) (term n_2)) (term true) (term false))]
  [(delta != n_1 n_2) ,(if (not (= (term n_1) (term n_2))) (term true) (term false))])

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
   (handlers m (View-child (m-lookup m p)))])


;;
;; ------------------------------ INIT
;;

(define-judgment-form React-tRace
  #:mode (init I I I O O O)
  #:contract (init m_1 δ s t m_2 Outbuf)
  ;; init takes in a tree memory, a definition table, and a spec s
  ;; and renders into a tree t, modifies memory, and prints buffer Outbuf

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
  [(init m_0 δ s_1 t_1 m_1 Outbuf_1)
   (init m_1 δ (s_rest ...) (t_rest ...) m_2 Outbuf_2)
   -------- "InitArray-Cons"
   (init m_0 δ (s_1 s_rest ...)
         (t_1 t_rest ...)
         m_2
         (append-Outbuf Outbuf_1 Outbuf_2))])


;;
;; ------------------------------ APPLY UPDATES
;;


(define-judgment-form React-tRace
  #:mode (apply-updaters I I I I I O O O)

  ;; no queued updates = final val is starting val
  [--------------------------------------"ApplyUpdatersDone"
   (apply-updaters View () ϕ p v v View ())]

  ;; apply first updater closure, then keep going
  [(eval-view View
              (env-extend σ_cl x_arg v_in)
              e_updater
              ϕ p v_next View_1 Outbuf_1)

   (apply-updaters View_1 (cl_rest ...) ϕ p v_next v_out View_2 Outbuf_2)
   ----------------------------------------------------------"ApplyUpdatersStep"
   (apply-updaters View
                   (((λ (x_arg) e_updater) σ_cl) cl_rest ...)
                   ϕ p v_in v_out View_2 (append-Outbuf Outbuf_1 Outbuf_2))])


(define-metafunction React-tRace
  remove-dec : (dec ...) dec -> (dec ...)
  [(remove-dec () dec) ()]
  [(remove-dec (dec dec_rest ...) dec)
   (dec_rest ...)]
  [(remove-dec (dec_other dec_rest ...) dec)
   (dec_other dec_new ...)
   (where (dec_new ...) (remove-dec (dec_rest ...) dec))])

;; Metafunction to update view's decision
(define-metafunction React-tRace
  update-dec : View dec -> View
  [(update-dec (view cs (dec_1 ...) Smap q t) dec_2) (view cs (union-dec (dec_1 ...) dec_2) Smap q t)])

;; Add d to a list of decisions only if not already present
(define-metafunction React-tRace
  union-dec : (dec ...) dec -> (dec ...)
  [(union-dec (dec_1 ... dec dec_2 ...) dec) (dec_1 ... dec dec_2 ...)] ;; already present, just return same list
  [(union-dec (dec_1 ...) dec) (dec_1 ... dec)]) ;; not present, append

;; Metafunction to find a view given a path
(define-metafunction React-tRace
  m-lookup : m p -> any
  [(m-lookup ((p_0 View_0) (p_rest View_rest) ...) p) View_0
   (side-condition (equal? (term p_0) (term p)))]
  [(m-lookup ((p_0 View_0) (p_rest View_rest) ...) p)
   (m-lookup ((p_rest View_rest) ...) p)
   (side-condition (not (equal? (term p_0) (term p))))]
  [(m-lookup mt p) #f]
  [(m-lookup () p) #f])

;; Update (replace) a view at path p in memory m
(define-metafunction React-tRace
  m-update : m p View -> m
  [(m-update ((p_before View_before) ... (p View_old) (p_after View_after) ...) p View_new)
   ((p_before View_before) ... (p View_new) (p_after View_after) ...)]
  ;; If p is not present, insert it
  [(m-update ((p_old View_old) ...) p_new View_new)
   ((p_old View_old) ... (p_new View_new))
   (side-condition (not (member (term p_new) (term (p_old ...)))))])

;; Append a closure to an existing setter queue
(define-metafunction React-tRace
  queue-append : q cl -> q
  [(queue-append (cl_old ...) cl_new)
   (cl_old ... cl_new)])

;; Metafunction to get a view's child
(define-metafunction React-tRace
  View-child : View -> t
  [(View-child (view cs (dec ...) Smap q t)) t])

;; Replace a view's child tree, preserving all other fields (inc. dec from Succ eval)
(define-metafunction React-tRace
  View-set-child : View t -> View
  [(View-set-child (view cs (dec ...) Smap q t_old) t_new)
   (view cs (dec ...) Smap q t_new)])

;; Metafunction to get a view's decision
(define-metafunction React-tRace
  View-dec : View -> (dec ...)
  [(View-dec (view cs (dec ...) Smap q t)) (dec ...)])

;;
;; ------------------------------ EVAL HELPERS
;;
;; These helper judgments break `where`-chain dependencies that Redex's
;; mode-checker cannot trace across multiple eval-view premises.
;;

;; init-hook: initializes a hook label l with value v in the view's store.
(define-judgment-form React-tRace
  #:mode (init-hook I I I O)
  [(where Smap_in  (View-Smap View_in))
   (where Smap_out (Smap-init Smap_in l v))
   (where View_out (View-set-Smap View_in Smap_out))
   ----
   (init-hook View_in l v View_out)])

;; clear-hook: writes v_new to label l and clears the queue.
(define-judgment-form React-tRace
  #:mode (clear-hook I I I O)
  [(where Smap_in  (View-Smap View_in))
   (where Smap_out (Smap-set-clear Smap_in l v_new))
   (where View_out (View-set-Smap View_in Smap_out))
   ----
   (clear-hook View_in l v_new View_out)])

;; enqueue-hook: appends closure cl to the setter queue of label l, marks Check.
(define-judgment-form React-tRace
  #:mode (enqueue-hook I I I O)
  [(where Smap_in  (View-Smap View_in))
   (where Smap_out (Smap-enqueue Smap_in l cl))
   (where View_out (update-dec (View-set-Smap View_in Smap_out) Check))
   ----
   (enqueue-hook View_in l cl View_out)])

;; bind-state: extends environment with the state variable and its setter.
(define-judgment-form React-tRace
  #:mode (bind-state I I I I I I O)
  [(where σ_mid (env-extend σ x_state v_init))
   (where σ_out (env-extend σ_mid x_set (setter l p)))
   ----
   (bind-state σ x_state x_set l p v_init σ_out)])

;;
;; ------------------------------ EVAL
;;

;;
;; eval-view : evaluate an expression with a single view View as context.
;; Used during Init and Succ phases (rendering inside a component).
;;
(define-judgment-form React-tRace
  #:mode (eval-view I I I I I O O O)

  ;; AppFunc-view
  [(eval-view View σ e_1 ϕ p_cur ((λ (x) e_body) σ_cl) View_1 Outbuf_1)
   (eval-view View_1 σ e_2 ϕ p_cur v_arg View_2 Outbuf_2)
   (eval-view View_2 (env-extend σ_cl x v_arg) e_body ϕ p_cur v View_3 Outbuf_3)
   ---------------------------------------- "AppFunc-view"
   (eval-view View σ (app e_1 e_2) ϕ p_cur v View_3
              (append-Outbuf (append-Outbuf Outbuf_1 Outbuf_2) Outbuf_3))]

  ;; AppCom-view
  [(eval-view View σ e_1 ϕ p_cur C View_1 Outbuf_1)
   (eval-view View_1 σ e_2 ϕ p_cur v View_2 Outbuf_2)
   ------------------------------ "AppCom-view"
   (eval-view View σ (app e_1 e_2) ϕ p_cur (C v) View_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; AppSet-view: calling a setter during Init or Succ phase
  ;; The setter is (setter l p_cur), the argument is an updater closure.
  [(eval-view View σ e_1 ϕ p_cur (setter l p_cur) View_1 Outbuf_1)
   (eval-view View_1 σ e_2 ϕ p_cur cl View_2 Outbuf_2)
   (enqueue-hook View_2 l cl View_3)
   --------------------------------- "AppSet-view"
   (eval-view View σ (app e_1 e_2) ϕ p_cur () View_3 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; SttBind: first render — evaluate initializer, store in Smap, bind vars, eval body
  ;; Uses helper judgments to avoid Redex mode-checker issues with View chains.
  [(eval-view View σ e_init Init p_cur v_init View_a Outbuf_a)
                       
   (init-hook View_a l v_init View_b)
   (bind-state σ x_state x_set l p_cur v_init σ_ext)
   
   (eval-view View_b σ_ext e_body Init p_cur v_body View_c Outbuf_b)
   --------------------------------------------------------------------------- "SttBind"
   (eval-view View σ (state l (x_state x_set) e_init e_body) Init p_cur
              v_body View_c (append-Outbuf Outbuf_a Outbuf_b))]

  ;; SttReBind: subsequent render — apply queued updaters, clear queue, bind vars, eval body
  [(where Smap_0 (View-Smap View_0))
   (where v_old  (Smap-val Smap_0 l))
   (where q_old  (Smap-queue Smap_0 l))
   
   (side-condition (not (equal? (term v_old) #f)))
   (side-condition (not (equal? (term q_old) #f)))

   (apply-updaters View_0 q_old Succ p_cur v_old v_new View_n Outbuf_upd)
                       
   (clear-hook View_n l v_new View_nb)
   (bind-state σ x_state x_set l p_cur v_new σ_ext)

   (eval-view View_nb σ_ext e_body Succ p_cur v_body View_final Outbuf_body)
   -------------- "SttReBind"
   (eval-view View_0 σ (state l (x_state x_set) e_init e_body) Succ p_cur
              v_body View_final (append-Outbuf Outbuf_upd Outbuf_body))]

  ;; Const-view
  [(side-condition #t)
   ------------- "Const-view"
   (eval-view View σ k ϕ p k View ())]

  ;; Var-view
  [(where v (store-lookup σ x))
   (side-condition #t)
   ------------- "Var-view"
   (eval-view View σ x ϕ p v View ())]

  ;; Lam-view: close lambda over current environment
  [(side-condition #t)
   ------------- "Lam-view"
   (eval-view View σ (λ (x) e) ϕ p ((λ (x) e) σ) View ())]

  ;; Clos-view: a pre-formed closure passes through unchanged
  [(side-condition #t)
   ------------- "Clos-view"
   (eval-view View σ cl ϕ p cl View ())]

  ;; If-True-view
  [(eval-view View σ e_c ϕ p true View_1 Outbuf_1)
   (eval-view View_1 σ e_t ϕ p v View_2 Outbuf_2)
   ------------- "If-True-view"
   (eval-view View σ (if e_c e_t e_e) ϕ p v View_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; If-False-view
  [(eval-view View σ e_c ϕ p false View_1 Outbuf_1)
   (eval-view View_1 σ e_e ϕ p v View_2 Outbuf_2)
   ------------- "If-False-view"
   (eval-view View σ (if e_c e_t e_e) ϕ p v View_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; Begin-view
  [(eval-view View σ e_1 ϕ p v_1 View_1 Outbuf_1)
   (eval-view View_1 σ e_2 ϕ p v_2 View_2 Outbuf_2)
   ------------- "Begin-view"
   (eval-view View σ (begin e_1 e_2) ϕ p v_2 View_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; Let-view
  [(eval-view View σ e_r ϕ p v_r View_1 Outbuf_1)
   (eval-view View_1 (env-extend σ x v_r) e_b ϕ p v_b View_2 Outbuf_2)
   ------------- "Let-view"
   (eval-view View σ (let (x e_r) e_b) ϕ p v_b View_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; Print-view
  [(eval-view View σ e_1 ϕ p v View_1 Outbuf_1)
   ------------- "Print-view"
   (eval-view View σ (print e_1) ϕ p () View_1 (append-Outbuf Outbuf_1 (v)))]

  ;; Op-view
  [(eval-view View σ e_1 ϕ p n_1 View_1 Outbuf_1)
   (eval-view View_1 σ e_2 ϕ p n_2 View_2 Outbuf_2)
   (where v_r (delta op n_1 n_2))
   ------------- "Op-view"
   (eval-view View σ (e_1 op e_2) ϕ p v_r View_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; Array-Nil-view
  [(side-condition #t)
   ------------- "Array-Nil-view"
   (eval-view View σ () ϕ p () View ())]

  ;; Array-Cons-view
  [(eval-view View σ e_1 ϕ p v_1 View_1 Outbuf_1)
   (eval-view View_1 σ (e_r ...) ϕ p (v_r ...) View_2 Outbuf_2)
   ------------- "Array-Cons-view"
   (eval-view View σ (e_1 e_r ...) ϕ p (v_1 v_r ...) View_2 (append-Outbuf Outbuf_1 Outbuf_2))]
  )

;;
;; eval-mem : evaluate an expression with tree memory m as context.
;; Used during Normal phase (event handlers between renders).
;;
(define-judgment-form React-tRace
  #:mode (eval-mem I I I O O O)

  ;; AppFunc-mem
  [(eval-mem m σ e_1 ((λ (x) e_body) σ_cl) m_1 Outbuf_1)
   (eval-mem m_1 σ e_2 v_arg m_2 Outbuf_2)
   (eval-mem m_2 (env-extend σ_cl x v_arg) e_body v m_3 Outbuf_3)
   ---------------------------------------- "AppFunc-mem"
   (eval-mem m σ (app e_1 e_2) v m_3
             (append-Outbuf (append-Outbuf Outbuf_1 Outbuf_2) Outbuf_3))]

  ;; AppCom-mem
  [(eval-mem m σ e_1 C m_1 Outbuf_1)
   (eval-mem m_1 σ e_2 v m_2 Outbuf_2)
   ------------------------------ "AppCom-mem"
   (eval-mem m σ (app e_1 e_2) (C v) m_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; AppSet-mem: calling a setter during Normal phase (event handler)
  [(eval-mem m σ e_1 (setter l p) m_1 Outbuf_1)
   (eval-mem m_1 σ e_2 cl m_2 Outbuf_2)
   (where View    (m-lookup m_2 p))
   (side-condition (not (equal? (term View) #f)))
   (where Smap    (View-Smap View))
   (where q_new (queue-append (Smap-queue Smap l) cl))
   (where Smap_new (Smap-set Smap l (Smap-val Smap l) q_new))
   (where View_new (update-dec (View-set-Smap View Smap_new) Check))
   (where m_3   (m-update m_2 p View_new))
   -------- "AppSet-mem"
   (eval-mem m σ (app e_1 e_2) () m_3 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; Const-mem
  [(side-condition #t)
   ------------- "Const-mem"
   (eval-mem m σ k k m ())]

  ;; Var-mem
  [(where v (store-lookup σ x))
   (side-condition #t)
   ------------- "Var-mem"
   (eval-mem m σ x v m ())]

  ;; Lam-mem: close lambda over current environment
  [(side-condition #t)
   ------------- "Lam-mem"
   (eval-mem m σ (λ (x) e) ((λ (x) e) σ) m ())]

  ;; Clos-mem: pre-formed closure passes through
  [(side-condition #t)
   ------------- "Clos-mem"
   (eval-mem m σ cl cl m ())]

  ;; If-True-mem
  [(eval-mem m σ e_c true m_1 Outbuf_1)
   (eval-mem m_1 σ e_t v m_2 Outbuf_2)
   ------------- "If-True-mem"
   (eval-mem m σ (if e_c e_t e_e) v m_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; If-False-mem
  [(eval-mem m σ e_c false m_1 Outbuf_1)
   (eval-mem m_1 σ e_e v m_2 Outbuf_2)
   ------------- "If-False-mem"
   (eval-mem m σ (if e_c e_t e_e) v m_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; Begin-mem
  [(eval-mem m σ e_1 v_1 m_1 Outbuf_1)
   (eval-mem m_1 σ e_2 v_2 m_2 Outbuf_2)
   ------------- "Begin-mem"
   (eval-mem m σ (begin e_1 e_2) v_2 m_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; Let-mem
  [(eval-mem m σ e_r v_r m_1 Outbuf_1)
   (eval-mem m_1 (env-extend σ x v_r) e_b v_b m_2 Outbuf_2)
   ------------- "Let-mem"
   (eval-mem m σ (let (x e_r) e_b) v_b m_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; Print-mem
  [(eval-mem m σ e_1 v m_1 Outbuf_1)
   ------------- "Print-mem"
   (eval-mem m σ (print e_1) () m_1 (append-Outbuf Outbuf_1 (v)))]

  ;; Op-mem
  [(eval-mem m σ e_1 n_1 m_1 Outbuf_1)
   (eval-mem m_1 σ e_2 n_2 m_2 Outbuf_2)
   (where v_r (delta op n_1 n_2))
   ------------- "Op-mem"
   (eval-mem m σ (e_1 op e_2) v_r m_2 (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; Array-Nil-mem
  [(side-condition #t)
   ------------- "Array-Nil-mem"
   (eval-mem m σ () () m ())]

  ;; Array-Cons-mem
  [(eval-mem m σ e_1 v_1 m_1 Outbuf_1)
   (eval-mem m_1 σ (e_r ...) (v_r ...) m_2 Outbuf_2)
   ------------- "Array-Cons-mem"
   (eval-mem m σ (e_1 e_r ...) (v_1 v_r ...) m_2 (append-Outbuf Outbuf_1 Outbuf_2))]
  )


;;
;; ------------------------------ CHECK
;;

(define-judgment-form React-tRace
  #:mode (check I I I O O O)
  ;; check takes in tree memory m_1, a definition table δ, and a tree t,
  ;; then outputs modified tree memory m_2, updates the mode to rendered or • (event loop), and prints Outbuf
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
  [-------- "CheckArray-Nil"
   (check m δ () • m ())]

  [(check m_0 δ t_1 μ_1 m_1 Outbuf_1)
   (check m_1 δ (t_rest ...) μ_rest m_2 Outbuf_2)
   (where μ_joined (mu-join μ_1 μ_rest))
   ------------------------------ "CheckArray-Cons"
   (check m_0 δ
          (t_1 t_rest ...)
          μ_joined
          m_2
          (append-Outbuf Outbuf_1 Outbuf_2))]

  ;; CheckIdle: view has no Check decision — recurse on child
  [(where View (m-lookup m_1 p))
   (side-condition (not (eq? (term View) #f)))
   (where #f (dec-has-check? (View-dec View)))
   (check m_1 δ (View-child View) μ m_2 Outbuf)
   ------------------------------- "CheckIdle"
   (check m_1 δ p μ m_2 Outbuf)]

  ;; CheckActive: view has Check and component is in δ.
  ;; Re-evaluates the component body in Succ phase, which triggers SttReBind
  ;; to apply queued updater closures and clear the queue.
  [(where View (m-lookup m_1 p))
   (side-condition (not (equal? (term View) #f)))
   (where (view (C_cs v_arg) (dec_a ... Check dec_b ...) Smap_0 q_0 t_0) View)
   (where (λ (x_arg) e_body) (δ-lookup δ C_cs))
   (where View_cleared (view (C_cs v_arg) (dec_a ... dec_b ...) Smap_0 q_0 t_0))
   (eval-view View_cleared (env-extend () x_arg v_arg) e_body Succ p v_new View_after Outbuf_body)
   (where View_final (View-set-child View_after v_new))
   (where m_2 (m-update m_1 p View_final))
   (check m_2 δ v_new μ_child m_3 Outbuf_child)
   ------------------------------- "CheckActive"
   (check m_1 δ p rendered m_3 (append-Outbuf Outbuf_body Outbuf_child))]

  ;; CheckActive-NoLookup: view has Check but component not in δ — clear Check, recurse on old child.
  [(where View (m-lookup m_1 p))
   (side-condition (not (equal? (term View) #f)))
   (where (view (C_cs v_arg) (dec_a ... Check dec_b ...) Smap_0 q_0 t_0) View)
   (where #f (δ-lookup δ C_cs))
   (where View_cleared (view (C_cs v_arg) (dec_a ... dec_b ...) Smap_0 q_0 t_0))
   (where m_2 (m-update m_1 p View_cleared))
   (check m_2 δ t_0 μ_child m_3 Outbuf_child)
   ------------------------------- "CheckActive-NoLookup"
   (check m_1 δ p rendered m_3 Outbuf_child)])


;;
;; --------------- REACT-STEP
;;
(define react-step
  (reduction-relation React-tRace
   #:domain hook-input

   ;; StepInit: first render
   (--> (e evq δ)
        (t m_2 (append-Outbuf Outbuf Outbuf_2) evq δ ↺)
        (where View_root (view (Root ()) () (store) () ()))
        (where p_root (path 0))
        (judgment-holds (eval-view View_root () e Init p_root s View_after Outbuf))
        (judgment-holds (init ((p_root View_after)) δ s t m_2 Outbuf_2))
        "StepInit")

   ;; StepCheck: process queued state updates
   (--> (t m Outbuf evq δ ↺)
        (t m_2 (append-Outbuf Outbuf Outbuf_2) evq δ μ)
        (judgment-holds (check m δ t μ m_2 Outbuf_2))
        "StepCheck")

   ;; StepEvent: fire an event handler
   (--> (t m Outbuf evq δ •)
        (t m_2 (append-Outbuf Outbuf Outbuf_2) evq δ ↺)
        (where (_ ... ((λ (x_arg) e_body) σ_cl) _ ...) (handlers m t))
        (judgment-holds (eval-mem m (env-extend σ_cl x_arg ()) e_body v m_2 Outbuf_2))
        "StepEvent")))

(define (run-react e evq δ)
  (let ([results (apply-reduction-relation* react-step (term (,e ,evq ,δ)))])
    (cond
      [(empty? results) 'diverges]
      [(= (length results) 1) (first results)]
      [else (raise "BUG: non-deterministic!")])))

#;(traces react-step
  (term ((((λ (x_1) x_1) ()) 42) () ())))

;; These should work end-to-end  (evq=(), δ=() empty tables)
(apply-reduction-relation react-step (term (42 () ())))
(apply-reduction-relation react-step (term (true () ())))
(apply-reduction-relation react-step (term (((λ (x_1) x_1) ()) () ())))

;;
;; ------------------------------ TESTS
;;
;; ---- InitConst ----
#;(redex-match React-tRace δ (term ()))

#;(redex-match React-tRace Outbuf (term ()))

#;(redex-match React-tRace s (term ((λ (x_1) x_1) ())))

(test-equal
  (judgment-holds (init mt () 42 t m_2 Outbuf) (t m_2 Outbuf))
  '((42 mt ())))

(test-equal
  (judgment-holds (init mt () true t m_2 Outbuf) (t m_2 Outbuf))
  '((true mt ())))

(test-equal
  (judgment-holds (init mt () () t m_2 Outbuf) (t m_2 Outbuf))
  '((() mt ())))

;; ---- InitClos ----
(test-equal
  (judgment-holds (init mt () ((λ (x_1) x_1) ()) t m_2 Outbuf) (t m_2 Outbuf))
  '((((λ (x_1) x_1) ()) mt ())))

#;(redex-match React-tRace σ (term ((0 42)))) 
#;(redex-match React-tRace σ (term ((y_1 42))))

(test-equal
  (judgment-holds (init mt () ((λ (x_1) x_1) ((y_1 42))) t m_2 Outbuf) (t m_2 Outbuf))
  '((((λ (x_1) x_1) ((y_1 42))) mt ())))

(test-equal
  (judgment-holds (init mt () ((λ (x_1) (x_1 x_1)) ()) t m_2 Outbuf) (t m_2 Outbuf))
  '((((λ (x_1) (x_1 x_1)) ()) mt ())))

(test-equal
  (judgment-holds (init mt () ((λ (x_1) x_1) ((y_1 42) (y_2 true))) t m_2 Outbuf) (t m_2 Outbuf))
  '((((λ (x_1) x_1) ((y_1 42) (y_2 true))) mt ())))

(test-equal
  (judgment-holds (init mt () ((λ (x_1) 42) ()) t m_2 Outbuf) (t m_2 Outbuf))
  '((((λ (x_1) 42) ()) mt ())))

;; Memory is non-empty but unchanged — closures don't modify memory
(test-equal
  (judgment-holds
    (init (((path 0) (view (C 42) () (store) () 42))) ()
          ((λ (x_1) x_1) ())
          t m_2 Outbuf)
    (t m_2 Outbuf))
  '((((λ (x_1) x_1) ()) (((path 0) (view (C 42) () (store) () 42))) ())))


;; ---- InitArray ----

;; ---- InitArray-Nil ----
(test-equal
  (judgment-holds (init mt () () t m_2 Outbuf) (t m_2 Outbuf))
  '((() mt ())))

;; ---- InitArray-Cons ----
(test-equal
  (judgment-holds (init mt () (42) t m_2 Outbuf) (t m_2 Outbuf))
  '(((42) mt ())))

(test-equal
  (judgment-holds (init mt () (1 2 3) t m_2 Outbuf) (t m_2 Outbuf))
  '(((1 2 3) mt ())))

(test-equal
  (judgment-holds
    (init mt ()
          (42 ((λ (x_1) x_1) ()) true)
          t m_2 Outbuf)
    (t m_2 Outbuf))
  '(((42 ((λ (x_1) x_1) ()) true) mt ())))

(test-equal
  (judgment-holds
    (init mt ()
          ((1 2) (3 4))
          t m_2 Outbuf)
    (t m_2 Outbuf))
  '((((1 2) (3 4)) mt ())))

;; ---- CheckConst ----
;; Memory doesn't matter for constants, but provide non-empty m to be safe
(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) () 42 μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) () true μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

;; ---- CheckClos ----
(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) ()
           ((λ (x_1) x_1) ())
           μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

;; ---- CheckArray-Nil ----
(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) () (42) μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

;; ---- CheckArray-Cons ----
(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) () (42) μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) () (1 2 3) μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) ()
           (42 ((λ (x_1) x_1) ()))
           μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

;; ---- CheckIdle ----
(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) ()
           (path 0) μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () ((λ (x_1) x_1) ())))) ()
           (path 0) μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () ((λ (x_1) x_1) ())))) ())))

(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 1))
            ((path 1) (view (C 43) () (store) () 42))) ()
           (path 0) μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 1))
        ((path 1) (view (C 43) () (store) () 42))) ())))

;; ---- Handlers ----
(test-equal (term (handlers (((path 0) (view (C 42) () (store) () 42))) 42)) '())

(test-equal
  (term (handlers (((path 0) (view (C 42) () (store) () 42))) ((λ (x_1) x_1) ())))
  '(((λ (x_1) x_1) ())))

(test-equal
  (term (handlers (((path 0) (view (C 42) () (store) () 42)))
                  (42 ((λ (x_1) x_1) ()))))
  '(((λ (x_1) x_1) ())))


;;
;; ============================================================
;; eval-view UNIT TESTS
;; ============================================================

(define-syntax-rule (check-ev expr expected-v expected-out)
  (test-equal
    (judgment-holds
      (eval-view (view (Root ()) () (store) () ()) ()
                 expr Init (path 0)
                 v_1 View_1 Outbuf_1)
      (v_1 Outbuf_1))
    (list (list expected-v expected-out))))

;; Leaf forms
(check-ev 42    42    '())
(check-ev true  'true  '())
(check-ev false 'false '())

;; Arithmetic
(check-ev (3 + 4)   7   '())
(check-ev (10 - 3)  7   '())
(check-ev (2 * 5)   10  '())
(check-ev (3 < 5)   (quote true)  '())
(check-ev (5 < 3)   (quote false) '())
(check-ev (3 = 3)   (quote true)  '())
(check-ev (3 != 4)  (quote true)  '())

;; If
(check-ev (if true 1 2)    1 '())
(check-ev (if false 1 2)   2 '())
(check-ev (if (3 < 5) 99 0) 99 '())

;; Begin
(check-ev (begin 1 2)    2 '())
(check-ev (begin true 7) 7 '())

;; Let
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (let (myvar 7) (myvar + 1)) Init (path 0)
               v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((8 ())))

;; Lambda (creates closure over env)
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (λ (x1) x1) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((((λ (x1) x1) ()) ())))

;; Application: identity
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (app (λ (x1) x1) 42) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((42 ())))

;; Application: arithmetic
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (app (λ (x1) (x1 + 1)) 41) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((42 ())))

;; Print
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (print 99) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((() (99))))

;; Print sequence
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (begin (print 1) (print 2)) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((() (1 2))))

;;
;; ============================================================
;; useState UNIT TESTS (via eval-view)
;; ============================================================

;; SttBind: init stored, body result returned
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (state 0 (sv ss) 42 sv) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((42 ())))

;; SttBind: store correctly populated
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (state 0 (sv ss) 99 sv) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 (Smap-val (View-Smap View_1) 0)))
  '((99 99)))

;; SttBind: arithmetic on state
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (state 0 (sv ss) 10 (sv + 5)) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((15 ())))

;; SttBind: print in body
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (state 0 (sv ss) 5 (begin (print sv) sv)) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((5 (5))))

;; SttBind: if on state value
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (state 0 (bv bs) true (if bv 1 2)) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((1 ())))

;; SttBind: two useState hooks
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (state 0 (s1 set1) 10 (state 1 (s2 set2) 20 (s1 + s2)))
               Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((30 ())))

;; SttBind: body returns pair (array) — use a more explicit array expression
;; Note: (sv ss) is ambiguous in Redex (could be app or array).
;; Use the Array-Cons form with explicit nested arrays, or just test tree membership.
;; Here we verify the setter value is bound correctly in the env:
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (state 0 (sv ss) 7 ss) Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '(((setter 0 (path 0)) ())))

;; SttReBind: one queued updater s -> s+1
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store (0 5 (((λ (sv) (sv + 1)) ())))) () ())
               () (state 0 (sv ss) 0 sv) Succ (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((6 ())))

;; SttReBind: two queued updaters (+1 then +10 = 11)
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store
                                    (0 0 (((λ (sv) (sv + 1)) ())
                                          ((λ (sv) (sv + 10)) ())))) () ())
               () (state 0 (sv ss) 0 sv) Succ (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((11 ())))

;; SttReBind: queue is cleared after applying
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store (0 5 (((λ (sv) (sv + 1)) ())))) () ())
               () (state 0 (sv ss) 0 sv) Succ (path 0) v_1 View_1 Outbuf_1)
    ((Smap-queue (View-Smap View_1) 0)))
  '((())))

;; SttBind: setter callback queues update and returns ()
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (state 0 (sv ss) 0
                 (begin
                   (app ss (λ (old) (old + 1)))
                   sv))
               Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 (Smap-queue (View-Smap View_1) 0)))
  ;; sv = 0, setter enqueued (λ old old+1) which captures the current env
  '((0 (((λ (old) (old + 1)) ((ss (setter 0 (path 0))) (sv 0)))))))

;;
;; ============================================================
;; END-TO-END react-step EXAMPLES
;; ============================================================

(display "\n\n;;; === END-TO-END useState EXAMPLES ===\n\n")

(define (show label result)
  (display (string-append "--- " label " ---\n"))
  (if (null? result)
      (display "  (no steps fired)\n\n")
      (for ([r result])
        (match r
          [(list t m out δ μ)
           (display (format "  tree:   ~v\n" t))
           (display (format "  memory: ~v\n" m))
           (display (format "  output: ~v\n" out))
           (display (format "  phase:  ~v\n\n" μ))]
          [_ (display (format "  ~v\n\n" r))]))))


(define (print-deriv d [indent 0])
  (define pad (make-string indent #\space))
  (printf "~a~a\n" pad (or (derivation-name d) "<unnamed rule>"))
  (printf "~a  ~s\n" pad (derivation-term d))
  (for ([sub (derivation-subs d)])
    (print-deriv sub (+ indent 2))))

(define-syntax-rule (show-derivs label judgment)
  (begin
    (printf "\n--- ~a ---\n" label)
    (define ds (build-derivations judgment))
    (if (null? ds)
        (printf "No derivations.\n")
        (for ([d ds])
          (print-deriv d)))))


#;(show-derivs
 "SttBind derivation"
 (eval-view (view (Root ()) () (store) () ())
            ()
            (state 0 (s setS) 10 s)
            Init
            0
            v_out
            View_out
            Outbuf_out))

;; Ex1: simplest useState
#;(show "Ex1: useState^0 42 → s"C
  (apply-reduction-relation react-step
    (term ((state 0 (sv ss) 42 sv) ()))))

;;(traces react-step (term ((state 0 (sv ss) 42 sv) ())))

;; Ex2: zero initial value
#; (show "Ex2: useState^0 0 → s"
  (apply-reduction-relation react-step
    (term ((state 0 (sv ss) 0 sv) ()))))

;;(traces react-step (term ((state 0 (sv ss) 0 sv) ())))

;; Ex3: arithmetic in body
#; (show "Ex3: useState^0 3 → s+1"
  (apply-reduction-relation react-step
    (term ((state 0 (sv ss) 3 (sv + 1)) ()))))

#;(traces react-step (term ((state 0 (sv ss) 3 (sv + 1)) ())))

;; Ex4: print in body
#; (show "Ex4: useState^0 7, print s then return s"
  (apply-reduction-relation react-step
    (term ((state 0 (sv ss) 7 (begin (print sv) sv)) ()))))

;; Ex5: conditional on state
#; (show "Ex5: useState^0 true, if s then 1 else 2"
  (apply-reduction-relation react-step
    (term ((state 0 (bv bs) true (if bv 1 2)) ()))))

;; Ex6: two hooks
#;(show "Ex6: two useState hooks, s1+s2"
  (apply-reduction-relation react-step
    (term ((state 0 (s1 set1) 10
              (state 1 (s2 set2) 20
                (s1 + s2)))
           ()))))

#;(traces react-step (term ((state 0 (s1 set1) 10
              (state 1 (s2 set2) 20
                (s1 + s2)))
           ())))


#;(define d
  (build-derivations
   (eval-view
    (view (Root ()) () (store) () ())
    ()
    10
    Init
    0
    10
    (view (Root ()) () (store) () ())
    ())))

;; Ex7: counter — tree is [s, click-handler]
#; (show "Ex7: Counter [s, click-handler]"
  (apply-reduction-relation react-step
    (term ((state 0 (sv ss) 0
              (sv (λ (dummy) (app ss (λ (old) (old + 1))))))
           ()))))

#;(traces react-step (term ((state 0 (sv ss) 0
              (sv (λ (dummy) (app ss (λ (old) (old + 1))))))
           ())))

;; Ex8: run-react to fixpoint
(display "--- Ex8: run-react fixpoint ---\n")
(display (run-react (term (state 0 (sv ss) 42 sv)) (term ()) (term ())))
(newline)(newline)

;;
;; ============================================================
;; δ-lookup UNIT TESTS
;; ============================================================

;; found
(test-equal
  (term (δ-lookup ((Counter (λ (props) (state 0 (s setS) 0 s)))) Counter))
  '(λ (props) (state 0 (s setS) 0 s)))

;; missing component
(test-equal
  (term (δ-lookup ((Counter (λ (props) (state 0 (s setS) 0 s)))) Other))
  #f)

;; empty table
(test-equal
  (term (δ-lookup () Counter))
  #f)

;; two entries, look up second
(test-equal
  (term (δ-lookup ((Foo (λ (x) 1)) (Bar (λ (y) 2))) Bar))
  '(λ (y) 2))

;;
;; ============================================================
;; CheckActive (via δ) UNIT TESTS
;; ============================================================
;;
;; NOTE: paths (p ::= natural) overlap with integer constants (n ::= integer),
;; so check on a path like 0 can also fire CheckConst (treating 0 as k).
;; These tests use test-predicate to verify the desired (rendered ...) derivation
;; exists, without requiring it to be the only derivation.
;;

;; CheckActive: one queued updater +1, state goes from 5 to 6
;; δ has Counter mapped to a body using useState at label 0
(test-predicate
  (λ (results) (and (member '(rendered 6 ()) results) #t))
  (judgment-holds
    (check (((path 0) (view (Counter 0) (Check)
                            (store (0 5 (((λ (sv) (sv + 1)) ()))))
                            () 5)))
           ((Counter (λ (props) (state 0 (s setS) 0 s))))
           (path 0) μ m_2 Outbuf)
    (μ (Smap-val (View-Smap (m-lookup m_2 (path 0))) 0) Outbuf)))

;; CheckActive: queue is cleared after applying (the rendered derivation clears it)
(test-predicate
  (λ (results) (and (member '(()) results) #t))
  (judgment-holds
    (check (((path 0) (view (Counter 0) (Check)
                            (store (0 5 (((λ (sv) (sv + 1)) ()))))
                            () 5)))
           ((Counter (λ (props) (state 0 (s setS) 0 s))))
           (path 0) μ m_2 Outbuf)
    ((Smap-queue (View-Smap (m-lookup m_2 (path 0))) 0))))

;; CheckActive: two queued updaters (+1 then +10 = 16 from 5)
(test-predicate
  (λ (results) (and (member '(rendered 16 ()) results) #t))
  (judgment-holds
    (check (((path 0) (view (Counter 0) (Check)
                            (store (0 5 (((λ (sv) (sv + 1)) ())
                                         ((λ (sv) (sv + 10)) ()))))
                            () 5)))
           ((Counter (λ (props) (state 0 (s setS) 0 s))))
           (path 0) μ m_2 Outbuf)
    (μ (Smap-val (View-Smap (m-lookup m_2 (path 0))) 0) Outbuf)))

;; CheckActive-NoLookup: component not in δ — clears Check, returns rendered
(test-predicate
  (λ (results) (and (member '(rendered ()) results) #t))
  (judgment-holds
    (check (((path 0) (view (Unknown 0) (Check) (store (0 5 ())) () 5)))
           ()
           (path 0) μ m_2 Outbuf)
    (μ Outbuf)))

;; Two-hook component: CheckActive applies queued update to hook 0, hook 1 unchanged
;; Component body: (state 0 (s1 set1) 0 (state 1 (s2 set2) 0 (s1 + s2)))
;; Hook 0: state=3, queued (+10) → new state=13
;; Hook 1: state=4, no queue → unchanged
;; Body result = 13 + 4 = 17
(test-predicate
  (λ (results) (and (member '(rendered 13 4 ()) results) #t))
  (judgment-holds
    (check (((path 0) (view (TwoHook 0) (Check)
                            (store (0 3 (((λ (s) (s + 10)) ())))
                                   (1 4 ()))
                            () 7)))
           ((TwoHook (λ (props) (state 0 (s1 set1) 0 (state 1 (s2 set2) 0 (s1 + s2))))))
           (path 0) μ m_2 Outbuf)
    (μ (Smap-val (View-Smap (m-lookup m_2 (path 0))) 0)
       (Smap-val (View-Smap (m-lookup m_2 (path 0))) 1)
       Outbuf)))

;;
;; ============================================================
;; PATH / CONSTANT DISAMBIGUATION TEST
;; ============================================================
;; With p ::= (path natural), integer 0 is unambiguously a constant
;; and (path 0) is unambiguously a view reference.

;; Plain integer 0 is a constant: CheckConst fires, μ = •, memory unchanged.
(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) () 0 μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

;; Tagged (path 0) looks up the view: CheckIdle fires, μ = •, recurses on child 42.
(test-equal
  (judgment-holds
    (check (((path 0) (view (C 42) () (store) () 42))) () (path 0) μ m_2 Outbuf)
    (μ m_2 Outbuf))
  '((• (((path 0) (view (C 42) () (store) () 42))) ())))

;;
;; ============================================================
;; FINAL PRESENTATION DEMOS
;; ============================================================

;; ── Demo 1: Set-then-read ────────────────────────────────────────────────────
;; Expression: (state 0 (s setS) 0 (begin (app setS (λ (old) (old + 1))) s))
;; Phase: Init from empty view.
;; SttBind stores 0; AppSet-view enqueues the updater and marks dec=(Check);
;; body evaluates s=0 and returns it.  No output printed.
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (state 0 (s setS) 0
                 (begin (app setS (λ (old) (old + 1))) s))
               Init (path 0) v_1 View_1 Outbuf_1)
    (v_1
     (Smap-val   (View-Smap View_1) 0)
     (Smap-queue (View-Smap View_1) 0)
     (View-dec   View_1)
     Outbuf_1))
  '((0
     0
     (((λ (old) (old + 1)) ((setS (setter 0 (path 0))) (s 0))))
     (Check)
     ())))

;; ── Demo 2A: Counter — initial render (SttBind) ──────────────────────────────
;; Counter body evaluated with props=0, Init phase, empty Smap.
;; SttBind: count stored as 0, queue empty.
;; Body (count handler) returns array spec: current count + click-handler closure.
(test-equal
  
  (judgment-holds
    (eval-view (view (Counter 0) () (store) () ()) ((props 0))
               (state 0 (count setCount) 0
                 (count (λ (dummy) (app setCount (λ (old) (old + 1))))))
               Init (path 0) v_1 View_1 Outbuf_1)
    (v_1
     (Smap-val   (View-Smap View_1) 0)
     (Smap-queue (View-Smap View_1) 0)
     Outbuf_1))

  
  '(((0 ((λ (dummy) (app setCount (λ (old) (old + 1))))
         ((setCount (setter 0 (path 0))) (count 0) (props 0))))
     0 () ())))

;; ── Demo 2B: Counter — event handler enqueues updater (AppSet-mem) ───────────
;; m has Counter at (path 0) with count=0, empty queue.
;; Handler closure is called with dummy=(); body: (app setCount (λ old. old+1)).
;; AppSet-mem enqueues the updater, marks Check on the view; count value unchanged.
(test-equal


  (judgment-holds
    (eval-mem
      (((path 0) (view (Counter 0) () (store (0 0 ())) () 0)))
      ((dummy ()) (setCount (setter 0 (path 0))) (count 0) (props 0))
      (app setCount (λ (old) (old + 1)))
      v_1 m_1 Outbuf_1)
    (v_1
     (Smap-val   (View-Smap (m-lookup m_1 (path 0))) 0)
     (Smap-queue (View-Smap (m-lookup m_1 (path 0))) 0)
     (View-dec   (m-lookup m_1 (path 0)))
     Outbuf_1))
     
     
  '((() ; event itself returns void
     0 ; hook 0 val is STILL 0.
     (((λ (old) (old + 1)) 
       ((dummy ()) 
        (setCount (setter 0 (path 0))) 
        (count 0) 
        (props 0)))) ;; queue: updater enqueued
       (Check) ; dec: view scheduled for re-render
       ())))

;; ── Demo 2C: Counter — CheckActive applies updater, state advances 0 → 1 ─────
;; m has Counter at (path 0) with Check and one queued updater (λ old. old+1).
;; δ maps Counter to its component body.
;; CheckActive re-evaluates body in Succ; SttReBind applies updater: 0+1=1.
;; Queue cleared, new Smap-val=1, mode=rendered.

(test-equal
  (judgment-holds
    (check
      (((path 0) (view (Counter 0) (Check)
                       (store (0 0 (((λ (old) (old + 1))
                                     ((dummy ()) (setCount (setter 0 (path 0)))
                                      (count 0) (props 0))))))
                       () 0)))
      ((Counter (λ (props)
                  (state 0 (count setCount) 0
                    (count (λ (dummy) (app setCount (λ (old) (old + 1)))))))))
      (path 0)
      μ_1 m_1 Outbuf_1)
    
    (μ_1
     (Smap-val   (View-Smap (m-lookup m_1 (path 0))) 0)
     (Smap-queue (View-Smap (m-lookup m_1 (path 0))) 0)
     Outbuf_1))
  '((rendered 1 () ())))

;; ── Demo 3A: Local let in Init — purely lexical, does not touch Smap ─────────
;; (let (count 0) count) in Init with empty Smap.  v = 0.
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store) () ()) ()
               (let (count 0) count)
               Init (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((0 ())))


;; ── Demo 3B: Local let in Succ — ignores Smap, still gives 0 ─────────────────
;; (let (count 0) count) in Succ with (store (0 99 ())).  v = 0, not 99.
;; let is purely syntactic; it never reads the hook state store.
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store (0 99 ())) () ()) ()
               (let (count 0) count)
               Succ (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((0 ())))

;; ── Demo 3C: useState in Succ — SttReBind reads 99, ignores initializer 0 ────
;; (state 0 (count setCount) 0 count) in Succ with (store (0 99 ())).
;; SttReBind fires: queue is empty so v_new=99; clear-hook; bind count=99; eval count.
;; v = 99, demonstrating that useState ignores the initializer on re-render.
(test-equal
  (judgment-holds
    (eval-view (view (Root ()) () (store (0 99 ())) () ()) ()
               (state 0 (count setCount) 0 count)
               Succ (path 0) v_1 View_1 Outbuf_1)
    (v_1 Outbuf_1))
  '((99 ())))

(test-results)

;;
;; ============================================================
;; FINAL DEMO DERIVATION/TRACE OUTPUTS
;; ============================================================
;; Each show-derivs call is commented out with #; so the file
;; stays quiet during normal test runs.  Remove the #; prefix
;; to print full Redex derivation trees for that demo.
;;
;; Variable-name conventions (all legal Redex names):
;;   v_d1, View_d1, Outbuf_d1  — Demo 1
;;   v_d2a, View_d2a, ...       — Demo 2A
;;   v_d2b, m_d2b, Outbuf_d2b  — Demo 2B
;;   μ_d2c, m_d2c, Outbuf_d2c  — Demo 2C
;;   v_d3a, View_d3a, ...       — Demo 3 local let
;;   v_d3c, View_d3c, ...       — Demo 3 contrast (useState)
;; ============================================================

;; ── Demo 1: set-then-read ────────────────────────────────────────────────────
;; eval-view of (state 0 (s setS) 0 (begin (app setS (λ old. old+1)) s))
;; in Init phase from an empty view.
;; Expected: v=0, Smap-val(0)=0, queue=[updater], dec=(Check), Outbuf=()


(show-derivs
   "Demo 1: set state then read state (Init)"
   (eval-view (view (Root ()) () (store) () ())
              ()
              (state 0 (s setS) 0
                (begin (app setS (λ (old) (old + 1))) s))
              Init
              (path 0)
              v_d1
              View_d1
              Outbuf_d1))



;; ── Demo 2A: Counter initial render ─────────────────────────────────────────
;; eval-view of Counter body in Init phase.
;; Expected: v=(0 handler-cl), Smap-val(0)=0, queue=(), Outbuf=()
(show-derivs
   "Demo 2A: Counter initial render (Init / SttBind)"

  
   (eval-view (view (Counter 0) () (store) () ())
              ((props 0))
              (state 0 (count setCount) 0
                (count (λ (dummy) (app setCount (λ (old) (old + 1))))))
              Init
              (path 0)
              v_d2a
              View_d2a
              Outbuf_d2a))



;; ── Demo 2B: Click event enqueues updater ────────────────────────────────────
;; eval-mem of the handler body (app setCount (λ old. old+1)) in Normal phase.
;; Expected: v=(), Smap-val(0)=0, queue=[updater], dec=(Check), Outbuf=()
(show-derivs
   "Demo 2B: Counter event handler enqueues updater (AppSet-mem)"
   (eval-mem
     (((path 0) (view (Counter 0) () (store (0 0 ())) () 0)))
     ((dummy ()) (setCount (setter 0 (path 0))) (count 0) (props 0))
     (app setCount (λ (old) (old + 1)))
     v_d2b
     m_d2b
     Outbuf_d2b))

;; ── Demo 2C: CheckActive applies updater, count 0 → 1 ───────────────────────
;; check on (path 0) with δ providing Counter body.
;; Expected: μ=rendered, Smap-val(0)=1, queue=(), Outbuf=()
(show-derivs
   "Demo 2C: CheckActive applies queued updater (Succ / SttReBind)"
   (check
     (((path 0) (view (Counter 0) (Check)
                      (store (0 0 (((λ (old) (old + 1))
                                    ((dummy ()) (setCount (setter 0 (path 0)))
                                     (count 0) (props 0))))))
                      () 0)))
     ((Counter (λ (props)
                 (state 0 (count setCount) 0
                   (count (λ (dummy) (app setCount (λ (old) (old + 1)))))))))
     (path 0)
     μ_d2c
     m_d2c
     Outbuf_d2c))

;; ── Demo 3A: local let in Init — store untouched ─────────────────────────────
;; eval-view of (let (count 0) count) in Init with empty store.
;; Expected: v=0, store unchanged, Outbuf=()
(show-derivs
   "Demo 3A: local let in Init (Let-view / Const-view / Var-view)"
   (eval-view (view (Root ()) () (store) () ())
              ()
              (let (count 0) count)
              Init
              (path 0)
              v_d3a
              View_d3a
              Outbuf_d3a))

;; ── Demo 3B: local let in Succ — still ignores store ────────────────────────
;; eval-view of (let (count 0) count) in Succ with store (0 99 ()).
;; Expected: v=0 (not 99), store unchanged, Outbuf=()
(show-derivs
   "Demo 3B: local let in Succ — store has 99, let still returns 0"
   (eval-view (view (Root ()) () (store (0 99 ())) () ())
              ()
              (let (count 0) count)
              Succ
              (path 0)
              v_d3b
              View_d3b
              Outbuf_d3b))

;; ── Demo 3C: useState in Succ — reads persisted value 99 ────────────────────
;; eval-view of (state 0 (count setCount) 0 count) in Succ with store (0 99 ()).
;; SttReBind fires; apply-updaters base case (empty queue); bind count=99.
;; Expected: v=99, Outbuf=()
(show-derivs
   "Demo 3C: useState in Succ reads persisted value (SttReBind)"
   (eval-view (view (Root ()) () (store (0 99 ())) () ())
              ()
              (state 0 (count setCount) 0 count)
              Succ
              (path 0)
              v_d3c
              View_d3c
              Outbuf_d3c))

;;
;; ── react-step TRACES ────────────────────────────────────────────────────────
;; `traces` is complementary to `show-derivs`:
;;   show-derivs  = proof tree for ONE judgment (how a rule fires internally)
;;   traces       = graph of ALL machine states react-step visits to fixpoint
;;                  (what the whole reaction cycle looks like)
;;
;; All calls are commented out with #; — uncomment in DrRacket / interactive
;; session to open the Redex GUI trace visualizer.
;; Use apply-reduction-relation* variants below for non-GUI printable output.
;;
;; Initial term form: (e evq δ)
;;   e   = starting expression
;;   evq = event queue (empty here)
;;   δ   = component table (empty unless Counter needed)
;; ─────────────────────────────────────────────────────────────────────────────

;; Demo 1 — set-then-read: TWO steps (StepInit, then StepCheck).
;; StepInit fires: runs eval-view in Init, stores s=0, enqueues updater, marks Check.
;; StepCheck fires: CheckActive applies updater, s becomes 1, queue cleared.
;; traces shows this two-node reduction graph.
#;(traces react-step
   (term ((state 0 (s setS) 0
            (begin (app setS (λ (old) (old + 1))) s))
          ()
          ())))

;; Demo 3A — local let: ONE step only (StepInit).
;; (let (count 0) count) never calls a setter, so dec stays () and no
;; StepCheck follows.  traces shows a single-node graph after init.
#;(traces react-step
   (term ((let (count 0) count)
          ()
          ())))

;; Demo 3C — useState no-op init: ONE step (StepInit).
;; (state 0 (count setCount) 0 count) with an empty event queue never enqueues
;; an updater during the init render, so no Check is marked and StepCheck does
;; not fire.  traces graph has one node.
#;(traces react-step
   (term ((state 0 (count setCount) 0 count)
          ()
          ())))

;; Demo 2 initial render only (no event, no click): ONE step (StepInit).
;; Counter body evaluated with δ providing the component definition.
;; No setter is called during the init render itself; Check not marked.
#;(traces react-step
   (term ((state 0 (count setCount) 0
            (count (λ (dummy) (app setCount (λ (old) (old + 1))))))
          ()
          ((Counter (λ (props)
                      (state 0 (count setCount) 0
                        (count (λ (dummy)
                                 (app setCount (λ (old) (old + 1))))))))))))

;; ── Non-GUI alternatives (apply-reduction-relation*) ─────────────────────────
;; Same semantics as traces but returns a list of fixpoint configurations
;; rather than opening a GUI window.  Useful in terminal / CI contexts.

;; Demo 1 fixpoint — should reach (t m Outbuf evq δ •) with s=1 in Smap.
#;(for ([cfg (apply-reduction-relation* react-step
               (term ((state 0 (s setS) 0
                        (begin (app setS (λ (old) (old + 1))) s))
                      ()
                      ())))])
   (printf "Demo 1 fixpoint:\n  ~s\n\n" cfg))

;; Demo 3A fixpoint — local let, s read as 0.
#;(for ([cfg (apply-reduction-relation* react-step
               (term ((let (count 0) count) () ())))])
   (printf "Demo 3A fixpoint:\n  ~s\n\n" cfg))

;; Demo 3C fixpoint — useState init to 0.
#;(for ([cfg (apply-reduction-relation* react-step
               (term ((state 0 (count setCount) 0 count) () ())))])
   (printf "Demo 3C fixpoint:\n  ~s\n\n" cfg))



;; APPFUNC EXAMPLE
(traces react-step
  (term
   ((state 0 (s1 set1) 10
      (app (λ (x) x) 10))
    ()   
    ())))

(define d
  (build-derivations
   (eval-view
    (view (Root ()) () (store) () ())
    ()                      
    (app (λ (x) x) 10)
    Init
    (path 0)
    10
    (view (Root ()) () (store) () ())
    ())))

(show-derivations d)
