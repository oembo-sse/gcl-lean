import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ENNReal.Lemmas

abbrev ERat := WithBot (WithTop Rat)

abbrev q_bound (p : ℕ) (emin emax : ℤ) (q : ℕ) : Prop := emin ≤ q + p - 1 ∧ q + p - 1 ≤ emax

/-- `IEEE754` Floating point numbers -/
inductive IEEE754 (b : ℕ) (p : ℕ) (emin emax : ℤ) where
| finite :
  (s : Bool) → (c : Fin (b ^ p)) → (q : ℕ) →
  (property : q_bound p emin emax q) → IEEE754 b p emin emax
| pos_infinity
| neg_infinity
| qNaN
| sNaN

namespace IEEE754

variable (n m : IEEE754 b p emin emax)

/-- General operations -/

def roundToIntegralTiesToEven : IEEE754 b p emin emax := sorry
-- ...

def roundToIntegralExact : IEEE754 b p emin emax := sorry

def nextUp : IEEE754 b p emin emax := sorry
def nextDown : IEEE754 b p emin emax := sorry

def remainder : IEEE754 b p emin emax := sorry

def set_q (q' : ℕ) (h : q_bound p emin emax q') : IEEE754 b p emin emax := match n with
| .finite s c q _ => .finite s c q' h
| _ => sorry

/-- The operation addition(x, y) computes x + y.
    The preferred exponent is min(Q(x), Q(y)). -/
def addition : IEEE754 b p emin emax :=
  match n, m with
  | .finite s₁ c₁ q₁ _, .finite s₂ c₂ q₂ _ => .finite (s₁ ∧ s₂) (c₁ + c₂) (min q₁ q₂) sorry
  | _, _ => sorry
def subtraction : IEEE754 b p emin emax := sorry
def multiplication : IEEE754 b p emin emax := sorry

def toERat : Option ERat :=
  match n with
  | .finite s c q _ => some <| (-1 : Rat)^s.toNat * c.val * b ^ q
  | .pos_infinity => some ⊤
  | .neg_infinity => some ⊥
  | .qNaN | .sNaN => none

example : (n.addition m).toERat = n.toERat.get sorry + m.toERat.get sorry := by
  simp [toERat]
  rcases n with ⟨s₁, c₁, q₁, _⟩ | _
  · rcases m with ⟨s₂, c₂, q₂, _⟩ | _
    · simp_all [addition]
      congr
      simp_all
      obtain ⟨c₁, hc₁⟩ := c₁
      obtain ⟨c₂, hc₂⟩ := c₂
      simp_all


      sorry
    · sorry
    · sorry
    · sorry
    · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  -- split <;> split <;> split
  -- · simp_all
  --   sorry
  -- all_goals sorry

end IEEE754

-- def IEEE754.toReal (n : IEEE754 b p emin emax) : Real :=
--   n.toRat

abbrev IEEE754.f32 := IEEE754 2 24 (-126) 127

structure Floaty (E : ℕ) (M : ℕ) where
  bytes : BitVec (1 + E + M)

abbrev Floaty32 := Floaty 8 23

def BitVec.slice (v : BitVec n) (a b : ℕ) : BitVec (b - a) := (v.sshiftRight a).truncate (b - a)

#eval (0b010100 : BitVec 6)
#eval (0b010100 : BitVec 6)[2]
#eval (0b010100 : BitVec 6).slice 2 5

namespace Floaty

variable (f : Floaty E M)

def sign : Bool := f.bytes[0]
def exponent : BitVec E := f.bytes.slice 1 (E + 1)
def mantissa : BitVec M := f.bytes.slice (1 + E) (M + (1 + E)) |>.cast (by omega)

abbrev bits (_f : Floaty E M) : ℕ := 1 + E + M

def toList : List Bool :=
  List.range f.bits |>.attach.map (fun (⟨i, _⟩ : {x // x ∈ List.range f.bits}) ↦ f.bytes[i]'(by simp_all))

def toBitString : String := f.toList.reverse.map (if · then "1" else "0") |> String.join

def toRat : Rat :=
  let v := sorry
  if f.sign then -v else v

end Floaty

/-- info: 32 -/
#guard_msgs in
#eval (⟨0⟩ : Floaty32).bits

#eval (⟨0b1⟩ : Floaty32).toBitString


-- def Float32.toRat (f : Float32) : ERat := f < 0

-- #eval (0.123123 : Float32).toRat
