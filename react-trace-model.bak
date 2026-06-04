#lang racket

(require redex)

#|

██████╗ ██╗      █████╗ ███╗   ██╗███╗   ██╗██╗███╗   ██╗ ██████╗ 
██╔══██╗██║     ██╔══██╗████╗  ██║████╗  ██║██║████╗  ██║██╔════╝ 
██████╔╝██║     ███████║██╔██╗ ██║██╔██╗ ██║██║██╔██╗ ██║██║  ███╗
██╔═══╝ ██║     ██╔══██║██║╚██╗██║██║╚██╗██║██║██║╚██╗██║██║   ██║
██║     ███████╗██║  ██║██║ ╚████║██║ ╚████║██║██║ ╚████║╚██████╔╝
╚═╝     ╚══════╝╚═╝  ╚═╝╚═╝  ╚═══╝╚═╝  ╚═══╝╚═╝╚═╝  ╚═══╝ ╚═════╝ 
                                                                  
dissecting the parts related to figure 1

x ::== variable-not-otherwise-mentioned
C ::== component-name
n ::== integer
l ::== natural number hook label
ρ[l] ::== current state value
ρ (ro) ::== ((l value queue) ...)
Prog P ::== D e
    - a program P is a sequence of component definitions ( D ) followed by a main expression e

in redex terms the whole program is sort of (program defs e)


COMPONENT DEFINITIONS

ComDef D ::= let C(x) = e
    - component D has a parameter x and a body e
    - because components are just functions to react 

and the component definition table works like

δ[C] = λx.e

EXPRESSIONS

Exp e ::= ()
        | true
        | false
        | n
        | x                                         --> will look up variable within the environment
        | C
        | e ⊕ e                                     --> should be like ( + - * = < > ≤ ≥ ÷ ) --> not sure if we should imp all of em
        | [e]                                       --> since react components can return trees of children, tRace models as an array-like structure
        | print e
        | if e_1 then e_2 else e_3                  
        | e ; e
        | fun x                                     --> e
        | e e
        | let x = e_1 in e_2                        --> when evaluating e_2, let occurrences of 'x' refer to e_1
        | let (x, xset) = useState_l e_1 in e_2
            - we are at Hook label l
            - On initial render:
                - evaluate e_1
                - store this as hook's state
                - bind xset to a setter function
                - continue with e_2
            - on later render
                - ignore/reuse the already-stored state don't reinitialize
                - bind x to the current stored state
                - bind xset to the setter
                - continue with e_2
        | useEffect e                               --> <which we won't use>


the unit value is just (), essentially void / undefined

-- they use print to show calling order, which we could also do 




FURTHER SYMBOLS FROM FIG 3

ω                 --> output buffer, stores printed values
m                 --> tree memory, maps paths to views with m[p] = view at path p = π = { spec (which component and argument this came from), decision (like Check), state-store (hook state store), child tree }
δ                 --> component definition table mapping component names to bodies with δ[ComponentName] = λx.e
ϕ ∈ {Init, Succ}  --> a "phase" among [init, succ, normal]
    - init --> initialization phase where component is rendered/mounted for the first time and useStates create new state entries
    - succ --> component has already been mounted and is being re-redneredc, so state stuff is just retrieved and queued updates are applied (basically just later renders)

π, σ              --> π is a view, a mounted component instance
    - where m is the whole tree memory,
    - π is one view mounted within that tree
    - some operations (like setters from event handlers or updating across components) need the whole tree memory, though most will only need their own local view
σ                 --> ordinary variable environment, maps variables to values, e.g. σ[x] = 0, σ[s] = 3, σ[setS] = setter closure

ρ                 --> stores persistent hook states. so σ[x] is recreated on each render but ρ[l] persists



FOR NOW -- let's just implement the language and ignore hook semantics, just maintain hook syntax
|#

