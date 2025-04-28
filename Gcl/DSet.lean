import Mathlib.Data.List.Dedup

instance (α : Type*) [BEq α] [LawfulBEq α] : DecidableEq α := fun a b ↦
  if h : a == b then .isTrue (by simp_all) else .isFalse (by simp_all)

structure DSet (α : Type*) [BEq α] [LawfulBEq α]
  -- [instLE : LE α] [DecidableRel instLE.le] -- [IsTotal α instLE.le] [IsTrans α instLE.le]
where
  elements : List α
  nodup : elements.Nodup
  -- sorted : elements.Sorted instLE.le

namespace DSet

variable {α : Type*} [BEq α] [LawfulBEq α]
   -- [instLE : LE α] [DecidableRel instLE.le] -- [IsTotal α instLE.le] [IsTrans α instLE.le]
variable {β : Type*} [BEq β] [LawfulBEq β]
   -- [instLeβ : LE β] [DecidableRel instLeβ.le] -- [IsTotal β instLeβ.le] [IsTrans β instLeβ.le]
variable {s : α} (S : DSet α)

-- instance : DecidableEq α := fun a b ↦
--   if h : a ≤ b ∧ b ≤ a then
--     .isTrue (by apply antisymm)
--   else
--     .isFalse (by simp_all)

def ofList (l : List α) : DSet α where
  elements := l.dedup
  nodup := by simp [List.nodup_dedup]
  -- sorted := by exact List.sorted_mergeSort' LE.le l.dedup

instance : BEq (DSet α) where
  beq a b := a.elements = b.elements

instance : LawfulBEq (DSet α) where
  eq_of_beq := by rintro ⟨_⟩ ⟨_⟩ _; simp_all [instBEq]
  rfl := by simp [instBEq]

instance : DecidableEq (DSet α) := fun a b ↦
  if h : a == b then .isTrue (by simp_all) else .isFalse (by simp_all)

instance : Membership α (DSet α) where
  mem S s := s ∈ S.elements

instance : Decidable (s ∈ S) := if h : s ∈ S.elements then .isTrue h else .isFalse h

instance : EmptyCollection (DSet α) where
  emptyCollection := ⟨{}, by simp⟩

instance : Singleton α (DSet α) where
  singleton s := ⟨{s}, List.dedup_eq_self.mp rfl⟩

instance : Insert α (DSet α) where
  insert s S := ofList (s :: S.elements)

instance : Union (DSet α) where
  union S₁ S₂ := ofList (S₁.elements ++ S₂.elements)

@[simp] theorem mem_empty : ¬s ∈ ({} : DSet α) := by simp [instMembership, instEmptyCollection]
@[simp] theorem mem_singleton : s ∈ ({s'} : DSet α) ↔ s = s' := by
  simp [instMembership, instSingleton, List.instSingletonList]

def all (f : α → Bool) : Bool := S.elements.all f

@[simp]
theorem all_eq_true : S.all f = true ↔ ∀ s ∈ S, f s = true := by simp [all]; rfl
theorem all_mem (h : S.all f) (h' : s ∈ S) : f s := by simp_all

def any (f : α → Bool) : Bool := S.elements.any f

@[simp]
theorem any_eq_true : S.any f = true ↔ ∃ s ∈ S, f s = true := by simp [any]; rfl
theorem any_mem (h : f s) (h' : s ∈ S) : S.any f := by simp_all; use s

def image (f : α → β) : DSet β :=
  ofList (S.elements.map f)

def toSet := {x | x ∈ S}

instance [Repr α] : Repr (DSet α) where
  reprPrec S _ := "{" ++ (S.elements.map (reprStr ·) |>.intersperse ", " |> String.join) ++ "}"

def fold (f : γ → α → γ) (init : γ) : γ := S.elements.foldl f init
def flatMap (f : α → DSet β) : DSet β := ofList (S.elements.flatMap (f · |>.elements))
def filterMap (f : α → Option β) : DSet β := ofList (S.elements.filterMap f)

@[simp]
theorem mem_ofList : s ∈ ofList L ↔ s ∈ L := by
  simp [ofList, instMembership]
@[simp]
theorem mem_elements : s ∈ S.elements ↔ s ∈ S := by simp [instMembership]
@[simp]
theorem mem_filterMap (f : α → Option β) : s' ∈ S.filterMap f ↔ ∃ s ∈ S, f s = some s' := by
  simp [filterMap]

def product (S₁ : DSet α) (S₂ : DSet β) : DSet (α × β) :=
  S₁.flatMap fun s₁ ↦ S₂.image fun s₂ ↦ (s₁, s₂)

instance instSProd : SProd (DSet α) (DSet β) (DSet (α × β)) where
  sprod := product

@[simp] theorem mem_image {f : α → β} : s' ∈ S.image f ↔ ∃ s ∈ S, f s = s' := by simp [image]

@[simp] theorem mem_sprod {S : DSet α} {S' : DSet β} : x ∈ S ×ˢ S' ↔ x.fst ∈ S ∧ x.snd ∈ S' := by
  obtain ⟨a, b⟩ := x; simp [instSProd, product, flatMap]

@[simp] theorem product_eq_sprod {S : DSet α} {S' : DSet β} : S.product S' = S ×ˢ S' := rfl

@[simp] theorem mem_union : s ∈ S ∪ S' ↔ s ∈ S ∨ s ∈ S' := by simp [instUnion]

end DSet
