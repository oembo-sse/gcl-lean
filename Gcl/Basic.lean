import Gcl.Syntax
import Gcl.ProgramGraph
import Lean.PrettyPrinter.Parenthesizer
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Sort
import Mathlib.Data.PFun
import Mathlib.Data.Finite.Prod
import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.Powerset

instance : IsTotal String LE.le := by
  constructor
  intro a b
  exact String.le_total a b

instance : IsTrans String LE.le := by
  constructor
  intro a b c hab hbc
  exact String.le_trans hab hbc

def Function.Dom (f : α → Option β) : Set α := {a : α | (f a).isSome}

@[simp]
theorem Finset.union_biUnion (α β : Type*) [DecidableEq α] [DecidableEq β] (S₁ S₂ : Finset α)
    (f : α → Finset β) : (S₁ ∪ S₂).biUnion f = (S₁.biUnion f) ∪ (S₂.biUnion f) := by
  ext
  simp_all
  aesop

namespace Relation.ReflTransGen

variable [instFintype : Fintype α] [DecidableEq α]
variable (r : α → α → Prop) [DecidableRel r]

def with_next : Finset α →o Finset α :=
  ⟨fun S ↦ S ∪ S.biUnion (fun s ↦ instFintype.elems.filter (r s)), by
    intro a b h x hx
    simp_all [Fintype.complete]
    rcases hx with hx | ⟨y, hy, hxy⟩
    · left; exact h hx
    · right; use y, h hy, hxy⟩

def reachable_n (S : Finset α) : ℕ → Finset α
| 0 => S
| n + 1 => reachable_n (with_next r S) n

def reachable (S : Finset α) : Finset α :=
  let next : Finset α := with_next r S
  if _ : S = next then
    S
  else
    reachable next
termination_by instFintype.card - S.card
decreasing_by
  have h₁ : (with_next r S).card ≤ instFintype.card := by
    apply Finset.card_le_card; intro; simp [Fintype.complete]
  have h₂ : S.card ≤ instFintype.card := by
    apply Finset.card_le_card; intro; simp [Fintype.complete]
  have h₃ : S.card < (with_next r S).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ?_
    simp_all [next, with_next]
  omega

@[simp] theorem reachable_n_zero : reachable_n r S 0 = S := rfl
@[simp]
theorem reachable_n_union : reachable_n r (S₁ ∪ S₂) n = reachable_n r S₁ n ∪ reachable_n r S₂ n := by
  induction n generalizing S₁ S₂ with
  | zero => simp_all
  | succ n ih =>
    simp_all [reachable_n, with_next]
    ext x
    simp_all
    aesop
@[simp]
theorem reachable_union : reachable r (S₁ ∪ S₂) = reachable r S₁ ∪ reachable r S₂ := by
  ext s'
  simp_all
  induction S₂ using Finset.induction generalizing s' S₁ with
  | empty =>
    simp_all
    rw [reachable]
    simp [with_next]
  | insert =>
    simp_all
    -- simp [with_next]
    -- aesop
    sorry
  -- induction n generalizing S₁ S₂ with
  -- | zero => simp_all
  -- | succ n ih =>
  --   simp_all [reachable_n, with_next]
  --   ext x
  --   simp_all
  --   aesop

theorem reachable_eq_reachable_n' (s' : α) : s' ∈ reachable r S ↔ ∃ i, s' ∈ reachable_n r S i := by
  constructor
  · intro h
    use instFintype.card
    sorry
    -- induction S using reachable.induct r
    -- · rename_i S S' h'
    --   simp_all [with_next, S']
    -- · sorry
  · simp_all
    intro n h
    sorry
    -- induction S using reachable.induct r
    -- induction n generalizing S with
    -- | zero =>
    --   simp_all
    --   rw [reachable]
    --   simp_all [with_next]
    --   split_ifs with h' <;> simp_all

    --   obtain ⟨s₀, h₁, h₂⟩ := h'
    --   rw [@Finset.not_subset] at h₂
    --   simp_all [Fintype.complete]
    --   obtain ⟨s₁, h₂, h₃⟩ := h₂

    --   sorry
    -- | succ n ih =>
    --   sorry
theorem reachable_eq_reachable_n : reachable r S = ⨆ n, (reachable_n r S n).toSet := by
  ext s
  simp_all [reachable_eq_reachable_n']

def self_subset_reachable (S : Finset α) :
    S ⊆ reachable r S := by
  intro x h
  simp [reachable_eq_reachable_n']
  use 0
  simp [reachable_n, h]

def reachable_complete (S : Finset α) :
    s' ∈ reachable r S ↔ s' ∈ {s' | ∃ s ∈ S, Relation.ReflTransGen r s s'} := by
  simp_all
  simp_all [reachable_eq_reachable_n']
  constructor
  · simp_all
    intro n h
    induction n generalizing s' S with
    | zero => simp_all [reachable_n]; use s'
    | succ n ih =>
      simp_all [reachable_n, with_next]
      have := ih (s':=s') (with_next r S)
      clear ih
      simp_all [with_next]
      obtain ⟨s'', _ | ⟨s''', h, h'', h'''⟩, h'⟩ := this
      · use s''
      · use s''', h
        exact head h''' h'
  · simp_all
    intro s hs h
    induction h generalizing S hs with
    | refl => use 0; simp_all
    | tail h hr ih =>
      rename_i s'' s'''
      sorry
      -- obtain ih := ih (with_next r S)
      -- simp_all [with_next]
      -- obtain ⟨n, ih | ih⟩ := ih
      -- · use n + 1
      --   simp_all [reachable_n, with_next]
      --   right
      -- simp_all
      -- use n + 1
      -- simp [reachable_n, with_next]
      -- right
  -- constructor
  -- · intro h
  --   sorry
  -- · simp_all
  --   intro s h h'
  --   induction h' with
  --   | refl =>
  --     unfold reachable; simp_all
  --     split_ifs
  --     · assumption
  --     · simp_all
  --   | tail => sorry

instance : Decidable (s' ∈ reachable r {s}) := Finset.decidableMem s' (reachable r {s})

def asdjkasd : Relation.ReflTransGen r s s' ↔ s' ∈ reachable r {s} := by
  simp [reachable_complete]

def decidable [instFintype : Fintype α] [DecidableEq α] (r : α → α → Prop) [DecidableRel r] :
    Decidable (Relation.ReflTransGen r s₁ s₂) :=
  if h : s₂ ∈ reachable r {s₁} then
    .isTrue (by simp_all [asdjkasd])
  else
    .isFalse (by simp_all [asdjkasd])

  -- let all := { (s, s') | Relation.ReflTransGen r s s' }
  -- have : (instFintype.elems.toSet ×ˢ instFintype.elems.toSet).Finite :=
  --   Set.toFinite _
  -- have : all.Finite := by simp [all]; exact Set.toFinite _
  -- have : Fintype all := ⟨all, sorry⟩
  -- have : Decidable ((s₁, s₂) ∈ all) := by
  --   simp only [all]
  --   have := Finset.decidableMem (s₁, s₂) all.toFinset
  --   exact {x | Relation.ReflTransGen r x.1 x.2}.decidableMemOfFintype (s₁, s₂)
  -- if h : (s₁, s₂) ∈ all then
  --   .isTrue (by simp_all [all])
  -- else
  --   .isFalse (by simp_all [all])
  -- if h : s₁ ∈ reachable r {s₁} then
  --   .isTrue (by

  --     )
  -- else
  --   .isFalse sorry
  -- let next : Finset α := instFintype.elems.filter (r s₁)
  -- if s₂ ∈

end Relation.ReflTransGen

namespace GCL

def Graph.run (g : Graph) (c : Configuration) : ℕ → DSet Configuration
| 0 => {c}
| n + 1 =>
  let res := (g.succs c).flatMap fun c' ↦ g.run c' n
  -- let res := g.run c n |>.flatMap fun c' ↦ g.succs c'
  if res = {} then {c} else res

#eval
  let σ' : Mem := mem {x ↦ 0, y ↦ 0}
  let G := gcl { x := 12; x := x + 2 }.graph
  G.run ⟨q▹, σ'⟩ 10

def Graph.Deterministic (g : Graph) : Prop := ∀ (σ σ' σ'' : Mem) (ω' ω'' : List Act),
  ωTransition g ⟨q▹, σ⟩ ⟨q◂, σ'⟩ ω' → ωTransition g ⟨q▹, σ⟩ ⟨q◂, σ''⟩ ω'' → σ' = σ'' ∧ ω' = ω''

def Graph.of_deterministic (g : Graph)
  (h : ∀ e₁ ∈ g.edges, ∀ e₂ ∈ g.edges, (e₁.action, e₁.target) ≠ (e₂.action, e₂.target) →
    (𝒮 e₁.action).Dom ∩ (𝒮 e₂.action).Dom = ∅) : g.Deterministic := by
  simp [Deterministic]
  simp_all
  intro σ σ' σ'' ω' ω'' h' h''
  cases h'; cases h''
  simp_all
  rename_i h' _ _ _ _ h'' _
  simp_all [Transition]
  have := h _ h'.left _ h''.left
  simp_all [Function.Dom]
  contrapose this
  simp_all
  rw [@Set.eq_empty_iff_forall_not_mem]
  simp_all
  sorry

theorem Graph.dgraph_deterministic (p : Command) : p.dgraph.Deterministic := by
  apply p.dgraph.of_deterministic
  simp_all [Function.Dom, Set.eq_empty_iff_forall_not_mem, Option.isSome_iff_exists]
  intro e₁ h₁ e₂ h₂ h σ σ₁ h₁' σ₂ h₂'
  sorry



structure Mem' (α : Type*) where
  dom : List String
  sorted : dom.Sorted String.le
  dedup : dom.Nodup
  read : {v // v ∈ dom} → α
deriving DecidableEq

def Mem.map' (f : ℤ → α) (σ : Mem) : Mem' α where
  dom := σ.dom
  sorted := σ.sorted
  dedup := σ.dedup
  read := f ∘ σ.read

def Mem'.concrete (f : α → ℤ) (σ : Mem' α) : Mem where
  dom := σ.dom
  sorted := σ.sorted
  dedup := σ.dedup
  read := f ∘ σ.read

def Mem'.flatConcrete (f : α → DSet ℤ) (σ : Mem' α) : DSet Mem :=
  let x : List ({v // v ∈ σ.dom} × DSet ℤ) := σ.dom.attach.map (fun v ↦ (v, f (σ.read v)))
  x.foldl (fun acc ⟨v, S⟩ ↦
    let y : DSet (Mem × {v // v ∈ σ.dom} × ℤ) := acc ×ˢ ({v} ×ˢ S)
    y.image (fun ⟨acc, v, z⟩ ↦ acc[v ↦ z])
    ) ({σ.concrete (fun _ ↦ 0)})
  -- let x : List (DSet ({v // v ∈ σ.dom} × ℤ)) := σ.dom.attach.map (fun v ↦ {v} ×ˢ f (σ.read v))
  -- let y : DSet (DSet _) := DSet.ofList x

class Analysis (g : Graph) (α : Type*) where
  η : Mem → Mem' α
  A : State → Set (Mem' α)
  A_correct₁ :
    ∀ e ∈ g.edges, ∀ σ, η σ ∈ A e.source → ∃ σ' ∈ 𝒮 e.action σ, η σ' ∈ A e.target

inductive Sign where | minus | zero | plus
deriving DecidableEq

instance : Repr Sign where
  reprPrec s _ := match s with | .minus => "-" | .zero => "0" | .plus => "+"

instance [Repr α] : Repr (Mem' α) where
  reprPrec σ _ :=
    "mem' {" ++
      (σ.dom.attach.map (fun x ↦ x ++ " ↦ " ++ reprStr (σ.read x)) |>.intersperse ", " |> String.join)
    ++ "}"

def Sign.ofInt : ℤ → Sign
| 0 => .zero
| n => if n < 0 then .minus else .plus

def Sign.represent : Sign → DSet ℤ
| .minus => {-1, -2}
| .zero => {0}
| .plus => {1, 2}

#eval mem { x ↦ 12 }.map' Sign.ofInt
#eval mem { x ↦ 12 }.map' Sign.ofInt |>.flatConcrete Sign.represent

def 𝒜' : AExpr → Mem' Sign → Option (DSet Sign)
| .const n, _ => some {Sign.ofInt n}
| .var n, σ => if h : n ∈ σ.dom then some {σ.read ⟨n, h⟩} else none
| aexpr {~a + ~b}, σ => sorry
| _, _ => sorry

def 𝒜'' (a : AExpr) (σ : Mem' Sign) : DSet Sign :=
  σ.flatConcrete Sign.represent |>.image (𝒜 a) |>.filterMap (·) |>.image Sign.ofInt
  -- sorry

#eval 𝒜'' (aexpr { x - y }) (mem { x ↦ 1, y ↦ 1, z ↦ 3 }.map' Sign.ofInt)

theorem asdasd : ∀ z ∈ 𝒜 a σ, Sign.ofInt z ∈ 𝒜'' a (σ.map' Sign.ofInt) := by
  intro z h
  simp_all
  induction a generalizing σ z
  next n =>
    simp_all [𝒜]
    subst_eqs
    simp_all [𝒜'']
    use n
    simp_all [𝒜, Mem'.flatConcrete]

    sorry
  next v =>
    simp_all [𝒜]
    obtain ⟨h, h'⟩ := h
    subst_eqs
    simp_all [𝒜'']
    sorry
  next => sorry

instance (g : Graph) : Analysis g Sign where
  η σ := σ.map' Sign.ofInt
  A := sorry
  A_correct₁ := sorry



end GCL

#min_imports
