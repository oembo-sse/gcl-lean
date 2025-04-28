import Gcl.Semantics
import Lean
import ProofWidgets.Component.GraphDisplay
import ProofWidgets.Component.HtmlDisplay

namespace GCL

inductive State where
| init
| final
| named : ℕ → State
deriving DecidableEq

structure Edge where
    source : State
    action : Act
    target : State
deriving DecidableEq
notation "q▹" => State.init
notation "q◂" => State.final
notation "q[" q "]" => State.named q

instance : Repr State where
  reprPrec s _ :=
    match s with
    | q▹ => "q▹"
    | q◂ => "q◂"
    | q[n] => s!"q[{n}]"

def State.safeStr (s : State) :=
    match s with
    | q▹ => "q_start"
    | q◂ => "q_end"
    | q[n] => s!"q[{n}]"

instance : Repr Edge where
  reprPrec e _ :=
    s!"({repr e.source}, {repr e.action}, {repr e.target})"

def Guarded.done : Guarded Command → BExpr
| gcluard { ~b → ~_ } => bexpr { ¬~b }
| gcluard { ~GC₁ [] ~GC₂ } =>
    bexpr { ~(GC₁.done) ∧ ~(GC₂.done) }

abbrev GraphBuilder T := StateM ℕ T

def fresh : GraphBuilder State := do
    let n ← get
    set (n + 1)
    pure $ q[n]

mutual

def Command.edges (q q' : State) : Command → GraphBuilder (DSet Edge)
| gcl { ~x := ~y } => pure {⟨q, act {~x := ~y}, q'⟩}
| gcl { skip } => pure {⟨q, act {skip}, q'⟩}
| gcl { ~C₁ ; ~C₂ } => do
    let q₁ ← fresh
    let E₁ ← C₁.edges q q₁
    let E₂ ← C₂.edges q₁ q'
    pure $ (E₁ ∪ E₂)
| gcl { if ~gc fi } => gc.edges q q'
| gcl { do ~gc od } => do
    let b := gc.done
    let E ← gc.edges q q
    pure $ E ∪ {⟨q, act {if ~b}, q'⟩}

def Guarded.edges (q q' : State) : Guarded Command → GraphBuilder (DSet Edge)
| gcluard { ~b → ~C } => do
    let q₁ ← fresh
    let E ← C.edges q₁ q'
    pure $ {⟨q, act {if ~b}, q₁⟩} ∪ E
| gcluard { ~GC₁ [] ~GC₂ } => do
    let E₁ ← GC₁.edges q q'
    let E₂ ← GC₂.edges q q'
    pure $ E₁ ∪ E₂

end

mutual

def Command.dedges (q q' : State) : Command → GraphBuilder (DSet Edge)
| gcl { ~x := ~y } => pure {⟨q, act {~x := ~y}, q'⟩}
| gcl { skip } => pure {⟨q, act {skip}, q'⟩}
| gcl { ~C₁ ; ~C₂ } => do
    let q₁ ← fresh
    let E₁ ← C₁.dedges q q₁
    let E₂ ← C₂.dedges q₁ q'
    pure $ (E₁ ∪ E₂)
| gcl { if ~gc fi } => do
  let ⟨E, _⟩ ← gc.dedges q q' false
  pure $ E
| gcl { do ~gc od } => do
    let ⟨E, d⟩ ← gc.dedges q q false
    pure $ E ∪ {⟨q, act {if ~d}, q'⟩}

def Guarded.dedges (q q' : State) (d : BExpr) : Guarded Command → GraphBuilder (DSet Edge × BExpr)
| gcluard { ~b → ~C } => do
    let q₁ ← fresh
    let E ← C.dedges q₁ q'
    pure $ ({⟨q, act {if ~b ∧ ¬~d}, q₁⟩} ∪ E, bexpr {~b ∨ ~d})
| gcluard { ~GC₁ [] ~GC₂ } => do
    let ⟨E₁, d₁⟩ ← GC₁.dedges q q' d
    let ⟨E₂, d₂⟩ ← GC₂.dedges q q' d₁
    pure $ ⟨E₁ ∪ E₂, d₂⟩

end

structure Graph where
    edges : DSet Edge
deriving Repr

instance {g : Graph} : Decidable (s ∈ g.edges) := DSet.instDecidableMem _

def Command.graph (c : Command) : Graph :=
    ⟨(c.edges q▹ q◂ 0).fst⟩

def Command.dgraph (c : Command) : Graph :=
    ⟨(c.dedges q▹ q◂ 0).fst⟩

/-- info: { edges := {(q▹, skip, q◂)} } -/
#guard_msgs in
#eval (gcl { skip }).graph

/-- info: { edges := {(q▹, skip, q[0]), (q[0], skip, q◂)} } -/
#guard_msgs in
#eval (gcl { skip; skip }).graph

#eval (gcl { skip ; if 1 = 2 -> skip fi }).graph
#eval (gcl { skip ; do 1 = 2 -> skip [] 3 = 4 → skip od }).graph
#eval (gcl { skip ; do 1 = 2 -> skip [] 3 = 4 → skip od }).dgraph

structure Configuration where
    state : State
    σ : Mem
deriving DecidableEq

instance : Repr Configuration where
  reprPrec c _ := s!"⟨{repr c.state},{repr c.σ}⟩"

def Transition (g : Graph) (c₁ c₂ : Configuration) (α : Act) : Prop :=
    ⟨c₁.state, α, c₂.state⟩ ∈ g.edges ∧ 𝒮 α c₁.σ = c₂.σ

notation c₁ " ⟹[" g "," α "] " c₂ => Transition g c₁ c₂ α

instance : Decidable (c₁ ⟹[g,α] c₂) :=
  if h : ⟨c₁.state, α, c₂.state⟩ ∈ g.edges ∧ 𝒮 α c₁.σ = c₂.σ then .isTrue (by simp_all [Transition])
  else .isFalse (by simp_all [Transition])

#eval
    let σ' := mem {x ↦ 0}
    let G := gcl { x := 12 }.graph
    (⟨q▹, σ'⟩ ⟹[G, act{x := 12}] ⟨q◂, σ'["x" ↦ 12]⟩)

def Graph.succs' (g : Graph) (c : Configuration) : Set Configuration :=
    { c' | ∃ α, c ⟹[g, α] c' }

def Graph.succs (g : Graph) (c : Configuration) : DSet Configuration :=
    g.edges.filterMap fun ⟨c₀, α, c₁⟩ ↦ do
        let σ' ← 𝒮 α c.σ
        if c.state = c₀ ∧ (c ⟹[g, α] ⟨c₁, σ'⟩) then some ⟨c₁, σ'⟩
        else none

def Graph.succs_act' (g : Graph) (c : Configuration) (α : Act) : Set Configuration :=
    { c' | c ⟹[g, α] c' }

def Graph.succs_act (g : Graph) (c : Configuration) (α : Act) : DSet Configuration :=
    g.edges.filterMap fun ⟨c₀, α', c₁⟩ ↦ do
        let σ' ← 𝒮 α c.σ
        if c.state = c₀ ∧ α' = α ∧ (c ⟹[g, α] ⟨c₁, σ'⟩) then some ⟨c₁, σ'⟩
        else none

theorem Graph.succs_eq (g : Graph) : c' ∈ g.succs c ↔ c' ∈ g.succs' c := by
  simp [succs, succs']
  constructor <;> simp_all [Option.bind]
  · intro e he h
    split at h <;> simp_all
    obtain ⟨⟨_, _⟩, _⟩ := h
    simp_all
    use e.action
  · intro α h
    use ⟨c.state, α, c'.state⟩
    split <;> simp_all [Transition]

theorem Graph.succs_act_eq (g : Graph) : c' ∈ g.succs_act c α ↔ c' ∈ g.succs_act' c α := by
  simp [succs_act, succs_act']
  constructor <;> simp_all [Option.bind]
  · intro e he h
    split at h <;> simp_all
    obtain ⟨⟨_, _⟩, _⟩ := h
    simp_all
  · intro h
    use ⟨c.state, α, c'.state⟩
    split <;> simp_all [Transition]

@[mk_iff, aesop safe [constructors, cases]]
inductive ωTransition (g : Graph) : Configuration → Configuration → List Act → Prop where
| refl : ωTransition g c₁ c₁ {}
| cons : Transition g c₁ c' α → ωTransition g c' c₂ ω → ωTransition g c₁ c₂ (α :: ω)

def ωTransition.decidable (g : Graph) (c₁ c₂ : Configuration) (ω : List Act) :
    Decidable (ωTransition g c₁ c₂ ω) :=
  match ω with
  | .nil => if h : c₁ = c₂ then .isTrue (by subst_eqs; exact .refl) else .isFalse (by aesop)
  | α :: ω =>
    if h : g.succs_act c₁ α |>.any (fun c' ↦ have := decidable g c' c₂ ω; ωTransition g c' c₂ ω)
    then .isTrue (by
      simp_all [Graph.succs_act_eq, Graph.succs_act']
      obtain ⟨c', h, h'⟩ := h
      apply ωTransition.cons h h')
    else .isFalse (by
      simp_all [Graph.succs_act_eq, Graph.succs_act']
      rintro ⟨_⟩
      rename_i c' h' h''
      exact h c' h' h'')

instance : Decidable (ωTransition g c₁ c₂ ω) := ωTransition.decidable g c₁ c₂ ω

def Graph.dot (g : Graph) : String :=
    let edges :=
        g.edges.image (fun e ↦ s!"{reprStr e.source} -> {reprStr e.target}[label=\"{reprStr e.action}\"]")
            |>.elements |> "  ".intercalate
    s!"dgraph \{{edges}}"

#eval gcl {
    skip; x := 1; if x < 10 -> x := 1 fi
}.graph

/-- info: "dgraph {q▹ -> q[0][label=\"skip\"]  q[0] -> q◂[label=\"\"a\" := 12\"]}" -/
#guard_msgs in
#eval gcl { skip; a := 12 }.graph.dot

open Lean Widget
open ProofWidgets Jsx

def Graph.states (g : Graph) : DSet State := g.edges.flatMap (fun e ↦ {e.source, e.target})

def Graph.widget (g : Graph) :=
    let vertices := g.states.elements.toArray.map ({id:=reprStr ·});
    let edges := g.edges.elements.toArray.map (fun e ↦
        {source:=reprStr e.source, target:=reprStr e.target, label?:=<g>
            <text>{Html.text (reprStr e.action)}</text>
        </g>});
    <GraphDisplay
        vertices={vertices}
        edges={edges}
        forces={#[
            .link {distance? := some 100}
        ]}
    />

#html gcl {x := 10; skip; do 0 < x -> x := x - 1; skip od}.graph.widget
