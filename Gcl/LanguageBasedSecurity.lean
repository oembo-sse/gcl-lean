import Gcl.Semantics
import Mathlib.Order.Closure

namespace Finset

variable {α : Type*} [DecidableEq α]

theorem subset_of_union_card_eq (S S' : Finset α) (h : (S ∪ S').card = S'.card) : S ⊆ S' := by
  rw [← @card_sdiff_add_card] at h
  simp at h
  exact h

end Finset

namespace DSet

variable {α : Type*} [BEq α] [LawfulBEq α]
variable {β : Type*} [BEq β] [LawfulBEq β]

def toFinset (S : DSet α) : Finset α := ⟨Multiset.ofList S.elements, by simp [S.nodup]⟩

instance : HasSubset (DSet α) where
  Subset S S' := ∀ s ∈ S, s ∈ S'

instance {S S' : DSet α} : Decidable (S ⊆ S') :=
  if h : S.all (· ∈ S') then .isTrue (by simp_all [instHasSubset])
  else .isFalse (by simp_all [instHasSubset])

instance : Preorder (DSet α) where
  le := instHasSubset.Subset
  le_refl := by simp_all [instHasSubset]
  le_trans := by simp_all [instHasSubset]

instance : IsTrans (DSet (α × α)) HasSubset.Subset := ⟨instPreorder.le_trans⟩

@[simp]
theorem le_iff_subset {S S' : DSet α} : S ≤ S' ↔ S ⊆ S' := by rfl

def relation_step (S : DSet (α × α)) : DSet (α × α) :=
  S.flatMap (fun ⟨a, b⟩ ↦ S.filterMap fun ⟨c, d⟩ ↦ if b = c then some (a, d) else none) ∪ S

def card (S : DSet α) : ℕ := S.elements.length

theorem toFinset_subset_iff_subset (S S' : DSet α) : S.toFinset ⊆ S'.toFinset ↔ S ⊆ S' := by
  simp [toFinset]; rfl

theorem toFinset_card_eq_card (S : DSet α) : S.toFinset.card = S.card := rfl
theorem sprod_toFinset (S S' : DSet α) : (S ×ˢ S').toFinset = S.toFinset ×ˢ S'.toFinset := by
  ext ⟨s, s'⟩; simp [toFinset]

theorem toFinset_union (S S' : DSet α) : (S ∪ S').toFinset = S.toFinset ∪ S'.toFinset := by
  ext s; simp [instUnion, toFinset, ofList]

theorem card_product (S S' : DSet α) : (S ×ˢ S').card = S.card * S'.card := by
  simp [← toFinset_card_eq_card, sprod_toFinset]

theorem card_le_card (S S' : DSet α) (h : S ⊆ S') : S.card ≤ S'.card := by
  simp_all [← toFinset_card_eq_card, ← toFinset_subset_iff_subset]
  exact Finset.card_le_card h

def upperbound (S : DSet (α × α)) : ℕ := (S.image (·.fst) |>.card) * (S.image (·.snd) |>.card)

theorem card_le_upperbound (S : DSet (α × α)) : S.card ≤ S.upperbound := by
  simp [upperbound]
  simp [← card_product]
  apply card_le_card
  intro ⟨s, s'⟩ h
  simp
  constructor
  · use s'
  · use s

theorem flatMap_mono (f : α → DSet β) : Monotone (DSet.flatMap (f:=f)) := by
  intro S S' h s
  simp_all [flatMap]
  intro s' h' h''; use s', h s' h', h''

@[simp]
theorem mem_flatMap (S : DSet α) (f : α → DSet β) : s ∈ S.flatMap f ↔ ∃ a ∈ S, s ∈ f a := by
  simp [flatMap]

theorem self_subset_relation_step (S : DSet (α × α)) : S ⊆ S.relation_step := by
  intro ⟨s, s'⟩ h; simp_all [relation_step]

theorem relation_step_mono : Monotone (relation_step (α:=α)) := by
  intro S S'
  simp_all [relation_step]
  intro h ⟨s, s'⟩ h'
  simp_all
  rcases h' with h' | h'
  · left; aesop
  · right; aesop

theorem card_le_card_relation_step (S : DSet (α × α)) : S.card ≤ S.relation_step.card :=
  S.card_le_card _ S.self_subset_relation_step

@[simp]
theorem relation_step_upperbound_eq_upperbound (S : DSet (α × α)) :
    S.relation_step.upperbound = S.upperbound := by
  simp [upperbound, ← card_product]
  apply le_antisymm
  · apply card_le_card
    intro ⟨s, s'⟩ h
    simp_all [relation_step]
    aesop
  · apply card_le_card
    intro ⟨s, s'⟩ h
    simp_all [relation_step]
    aesop

@[simp]
theorem union_card_eq_union {S S' : DSet α} (h : (S ∪ S').card = S'.card) : S ⊆ S' := by
  simp_all only [← toFinset_card_eq_card, toFinset_union, ← toFinset_subset_iff_subset,
    Finset.subset_of_union_card_eq]

@[simp]
theorem ofList_idem (S : DSet α) : ofList S.elements = S := by
  obtain ⟨elements, h⟩ := S
  simp_all [ofList, List.Nodup.dedup h]

@[simp]
theorem empty_union (S : DSet α) : ∅ ∪ S = S := by
  simp [instUnion, instEmptyCollection]

@[simp]
theorem union_idem (S : DSet α) : S ∪ S = S := by
  obtain ⟨elements, h⟩ := S
  simp [instUnion, ofList]
  simp [List.dedup_append, List.Nodup.dedup h, List.Subset.union_eq_right]

theorem asdasd (S S' : DSet α) : S ∪ S' = S' ↔ S ⊆ S' := by
  constructor
  · intro h s hs
    obtain ⟨S₁, h₁⟩ := S
    obtain ⟨S₂, h₂⟩ := S'
    simp_all [instUnion, ofList, instHasSubset]
    rw [instMembership] at hs ⊢
    simp_all
    simp_all [List.dedup_append, List.Nodup.dedup]
    rw [← h]
    exact List.mem_union_left hs S₂
  · intro h
    obtain ⟨S₁, h₁⟩ := S
    obtain ⟨S₂, h₂⟩ := S'
    simp_all [instUnion, ofList, instHasSubset]
    rw [instMembership] at h
    simp at h
    simp [List.dedup_append]
    rw [List.Nodup.dedup h₂]
    exact List.Subset.union_eq_right h


theorem ashjdas (S : DSet (α × α)) (h : S.relation_step.card ≤ S.card) : S.relation_step = S := by
  have : S.relation_step.card = S.card :=
    le_antisymm h <| S.card_le_card _ S.self_subset_relation_step
  simp_all
  simp_all [relation_step]
  simp_all [asdasd]

def relation_fix (S : DSet (α × α)) : DSet (α × α) :=
  let S' := S.relation_step
  if S.card < S'.card then S'.relation_fix else S
termination_by S.upperbound - S.card
decreasing_by
  have h₂ := S.relation_step.card_le_upperbound
  simp_all [S']
  omega

theorem self_subset_relation_fix (S : DSet (α × α)) : S ⊆ S.relation_fix := by
  induction S using relation_fix.induct
  next S S' h₁ h₂ =>
    simp_all [S']; clear S'
    apply subset_trans S.self_subset_relation_step
    apply subset_trans h₂
    nth_rw 2 [relation_fix]
    simp_all
  next S S' h =>
    nth_rw 1 2 [relation_fix]
    simp_all [S', ashjdas]

theorem relation_fix_def' (S : DSet (α ×  α)) :
    S.relation_fix = if S.relation_step = S then S else S.relation_step.relation_fix := by
  nth_rw 1 [relation_fix]
  split_ifs <;> simp_all [ashjdas]


theorem relation_fix_idem (S : DSet (α × α)) : S.relation_fix.relation_fix = S.relation_fix := by
  induction S using relation_fix.induct
  next S S' h₁ h₂ =>
    simp_all [S']; clear S'
    nth_rw 3 [relation_fix]
    simp [h₁]
    nth_rw 2 [relation_fix]
    simp [h₁]
    exact h₂
  next S S' h =>
    simp_all [S']; clear S'
    have := S.ashjdas h
    simp_all
    nth_rw 3 2 [relation_fix]
    simp_all
    nth_rw 1 [relation_fix]
    simp_all

def relation_closure : ClosureOperator (DSet (α × α)) where
  toFun := relation_fix
  monotone' := by
    intro S S' h
    simp_all
    induction S using relation_fix.induct generalizing S'
    next S S'' h₁ h₂ =>
      simp_all [S'']; clear S''
      rw [relation_fix]
      simp_all
      nth_rw 2 [relation_fix]
      split_ifs with h'
      · apply h₂
        exact S.relation_step_mono h
      · simp_all
        have h₃ := S'.ashjdas h'
        simp_all
        have : S'.relation_fix = S' := by
          rw [relation_fix]
          simp_all
        rw [← this]
        apply h₂
        rw [← h₃]
        apply relation_step_mono h
    next S S'' h' =>
      simp_all [S'']; clear S''
      have := S.ashjdas h'
      simp_all
      rw [relation_fix]
      simp_all
      apply subset_trans h
      exact S'.self_subset_relation_fix
  le_closure' := self_subset_relation_fix
  idempotent' := relation_fix_idem

theorem relation_closure_refl {S : DSet (α × α)} : (s, s) ∈ S.relation_closure := by
  sorry

theorem relation_closure_head {S : DSet (α × α)} : (s₁, s₂) ∈ S → (s₂, s₃) ∈ S.relation_closure → (s₁, s₃) ∈ S.relation_closure := by
  sorry

@[simp]
theorem ashjdsahdjash (S : DSet (α × α)) (h : S.relation_step = S) :
    S.relation_fix = S := by
  rw [relation_fix]; simp_all
@[simp]
theorem ashjdsahdjash' (S : DSet (α × α)) (h : S.relation_step = S) :
    S.relation_closure = S := by
  simp_all [relation_closure, DFunLike.coe]

theorem ahsjdjahsd (S : DSet (α × α)) : (a, b) ∈ S.relation_closure ↔
    a = b ∨ ∃ c, (a, c) ∈ S.relation_closure ∧ (c, b) ∈ S := by
  constructor
  · intro h
    simp [relation_closure, DFunLike.coe] at h
    rw [relation_fix_def'] at h
    split_ifs at h
    · simp_all
      right
      use b
      simp_all
      sorry
    ·
      sorry
  · sorry


theorem relation_closure_induction_on {b : α} {S : DSet (α × α)}
  {P : (a : α) → (a, b) ∈ S.relation_closure → Prop} {a : α} (h : (a, b) ∈ S.relation_closure) (refl : P b relation_closure_refl)
  (head : ∀ {a c : α} (h' : (a, c) ∈ S) (h : (c, b) ∈ S.relation_closure), P c h → P a (relation_closure_head h' h)) : P a h := by
  if a = b then
    simp_all
  else
    rw [relation_closure] at h
    simp [DFunLike.coe] at h
    rw [relation_fix_def'] at h
    split_ifs at h with h'
    · simp_all
      simp_all
      apply head h _ refl
      sorry
    ·
      sorry

theorem aasdasd (S : DSet (α × α)) :
    Relation.ReflTransGen (fun a b ↦ (a, b) ∈ S) a b ↔ (a, b) ∈ S.relation_closure := by
  constructor
  · intro h
    induction h
    · rw [ahsjdjahsd]; left; rfl
    · rename_i c₁ c₂ _ _ _
      rw [ahsjdjahsd]; right; use c₁
  · intro h
    apply S.relation_closure_induction_on (a:=a) (b:=b) (P:=fun a h ↦ Relation.ReflTransGen (fun a b ↦ (a, b) ∈ S) a b)
    · exact h
    · exact Relation.ReflTransGen.refl
    · exact fun {a c} h' h a_1 ↦ Relation.ReflTransGen.head h' a_1

theorem mem_relation_fix (S : DSet (α × α)) : (s, s') ∈ S.relation_fix ↔ (s, s') ∈ S ∨ (s, s') ∈ S.relation_step.relation_fix := by
  nth_rw 1 [relation_fix]
  split_ifs
  · sorry
  · simp_all
    have : S.relation_step = S := sorry
    simp_all

-- theorem relation_fix_idem_relation_step (S : DSet (α × α)) : S.relation_fix.relation_step = S.relation_fix := by
-- theorem relation_fix_idem (S : DSet (α × α)) : S.relation_fix.relation_fix = S.relation_fix := by
--   nth_rw 1 [relation_fix]
--   simp_all

#eval ("a", "d") ∈ (DSet.ofList [("a", "b"), ("b", "c"), ("c", "d")] |>.relation_step)
#eval ("a", "d") ∈ (DSet.ofList [("a", "b"), ("b", "c"), ("c", "d")] |>.relation_fix)

end DSet

namespace GCL

class Flowr (α : Type*) [BEq α] [LawfulBEq α] where
  allowedSet : DSet (α × α)

variable {α : Type*} [BEq α] [LawfulBEq α]

def Flowr.allowed [instFlowr : Flowr α] (a b : α) : Prop := (a, b) ∈ instFlowr.allowedSet
def Flowr.allowed_decidable [instFlowr : Flowr α] (a b : α) : Decidable (instFlowr.allowed a b) :=
  if h : (a, b) ∈ instFlowr.allowedSet then .isTrue h else .isFalse h

def Flow {α : Type*} [BEq α] [LawfulBEq α] [instFlowr : Flowr α] : α → α → Prop :=
  Relation.ReflTransGen instFlowr.allowed

def Flowr.ofDSet {α : Type*} [BEq α] [LawfulBEq α] (allowed : DSet (α × α)) : Flowr α where
  allowedSet := allowed

infix:50 " ⟶ " => Flow

def Flows {α : Type*} [BEq α] [LawfulBEq α] [instFlowr : Flowr α] : DSet α → DSet α → Prop :=
  fun S₁ S₂ ↦ ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, (s₁ ⟶ s₂)

infix:50 " ⇒ " => Flows
notation S₁ " ⇒[" i "] " S₂ => Flows (instFlowr:=i) S₁ S₂

variable [instFlowr : Flowr α]

instance {a b : α} : Decidable (a ⟶ b) :=
  if h : (a, b) ∈ instFlowr.allowedSet.relation_fix then .isTrue (by sorry)
  else .isFalse (by sorry)



variable [instFlowr : Flowr String] [instFlowrDecidable : ∀ s₁ s₂, Decidable (instFlowr.allowed s₁ s₂)]

-- instance [BEq α] [LawfulBEq α] [Flowr α] [Fintype α] (s₁ s₂ : α) : Decidable (s₁ ⟶ s₂) := by
--   simp [Flow]

instance [BEq α] [LawfulBEq α] [Flowr α] [∀ s₁ s₂ : α, Decidable (s₁ ⟶ s₂)] (S₁ S₂ : DSet α) : Decidable (S₁ ⇒ S₂) :=
  if h : S₁.all fun s₁ ↦ S₂.all fun s₂ ↦ decide (s₁ ⟶ s₂)
  then
    .isTrue (by simp_all [Flows])
  else
    .isFalse (by simp_all [Flows])

mutual

def Command.sec : Command → DSet String → Prop
| gcl {~x := ~a}, X => X ∪ a.fv ⇒ {x}
| gcl {skip}, _ => true
| gcl {~C₁ ; ~C₂}, X => C₁.sec X ∧ C₂.sec X
| gcl {if ~GC fi}, X => let (w, _) := GC.sec false X; w
| gcl {do ~GC od}, X => let (w, _) := GC.sec false X; w

def Guarded.sec (d : BExpr) (X : DSet String) : Guarded Command → Prop × BExpr
| gcluard {~b → ~C} =>
  let w := C.sec (X ∪ b.fv ∪ d.fv)
  (w, bexpr {~b ∨ ~d})
| gcluard {~GC₁ [] ~GC₂} =>
  let (w₁, d₁) := GC₁.sec d X
  let (w₂, d₂) := GC₂.sec d₁ X
  (w₁ ∧ w₂, d₂)

end

mutual

def Command.flows : Command → DSet String → DSet (String × String)
| gcl {~x := ~a}, X => (X ∪ a.fv) ×ˢ {x}
| gcl {skip}, _ => {}
| gcl {~C₁ ; ~C₂}, X => C₁.flows X ∪ C₂.flows X
| gcl {if ~GC fi}, X => let (w, _) := GC.flows false X; w
| gcl {do ~GC od}, X => let (w, _) := GC.flows false X; w

def Guarded.flows (d : BExpr) (X : DSet String) : Guarded Command → (DSet (String × String)) × BExpr
| gcluard {~b → ~C} =>
  let w := C.flows (X ∪ b.fv ∪ d.fv)
  (w, bexpr {~b ∨ ~d})
| gcluard {~GC₁ [] ~GC₂} =>
  let (w₁, d₁) := GC₁.flows d X
  let (w₂, d₂) := GC₂.flows d₁ X
  (w₁ ∪ w₂, d₂)

end

mutual

def Command.sec_iff_flows (C : Command) : C.sec X ↔ ∀ f ∈ C.flows X, f.fst ⟶ f.snd :=
  match C with
  | gcl {~x := ~e} => by simp_all [Command.sec, Command.flows, Flows]
  | gcl {skip} => by simp [Command.sec, Command.flows]
  | gcl {~C₁; ~C₂} => by
    simp_all [Command.sec, Command.flows, Command.sec_iff_flows]
    aesop
  | gcl {if ~GC fi} | gcl {do ~GC od} => by simp_all [Command.sec, Command.flows, GC.sec_eq_flows]

def Guarded.sec_eq_flows (GC : Guarded Command) :
    GC.sec d X = (∀ f ∈ (GC.flows d X).fst, f.fst ⟶ f.snd, (GC.flows d X).snd) :=
  match GC with
  | gcluard {~b → ~C} => by
    simp_all [Guarded.sec, Guarded.flows, Command.sec_iff_flows]
  | gcluard {~GC₁ [] ~GC₂} => by
    simp_all [Guarded.sec, Guarded.flows, GC₁.sec_eq_flows, GC₂.sec_eq_flows]
    aesop

end

instance [∀ s₁ s₂ : String, Decidable (s₁ ⟶ s₂)] (C : Command) : Decidable (C.sec X) :=
  if h : C.flows X |>.all fun ⟨x, y⟩ ↦ x ⟶ y then
    .isTrue (by simp_all [Command.sec_iff_flows])
  else
    .isFalse (by simp_all [Command.sec_iff_flows])

#eval! gcl { x := y; if x < 2 → z := 2 fi }.flows {}
#eval! gcl { y := x }.flows {}

end GCL
