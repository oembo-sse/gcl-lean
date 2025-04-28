import Gcl.Syntax

namespace GCL

def AExpr.fv : AExpr → DSet String
| .const _ => {}
| .var x => {x}
| aexpr {~a ~_ ~b} => a.fv ∪ b.fv

def BExpr.fv : BExpr → DSet String
| .const _ => {}
| bexpr {¬~a} => a.fv
| bexpr {~a = ~b} | bexpr {~a ≠ ~b}
| bexpr {~a < ~b} | bexpr {~a ≤ ~b}
| bexpr {~a ≥ ~b} | bexpr {~a > ~b}
| bexpr {~a ∧ ~b} | bexpr {~a ∨ ~b} =>
  a.fv ∪ b.fv

structure Mem where
  dom : List String
  sorted : dom.Sorted String.le
  dedup : dom.Nodup
  read : {v // v ∈ dom} → ℤ
deriving DecidableEq

instance : Repr Mem where
  reprPrec m _ :=
    "mem {" ++ (", ".intercalate <| m.dom.attach.map fun x ↦ s!"{x} ↦ {m.read x}") ++ "}"

def Mem.set (σ : Mem) (x : String) (a : ℤ) : Mem where
  dom := (x :: σ.dom).dedup.mergeSort
  sorted :=
    have : IsTrans String LE.le := ⟨fun _ _ _ ↦ String.le_trans⟩
    have : IsTotal String LE.le := ⟨String.le_total⟩
    List.sorted_mergeSort' _ _
  dedup := List.nodup_mergeSort.mpr (List.nodup_dedup (x :: σ.dom))
  read := fun y ↦ if h : x = y then a else σ.read ⟨y, by aesop⟩

notation σ "[" x " ↦ " a "]" => Mem.set σ x a

instance : Inhabited Mem where
  default := ⟨{}, by simp, by simp, fun _ ↦ 0⟩

instance : HAppend Mem Mem Mem where
  hAppend a b :=
    b.dom.attach.foldl (fun σ x ↦ σ[x.val ↦ b.read x]) a

inductive Act where
| assign : String → AExpr → Act
| condition : BExpr → Act
| skip
deriving DecidableEq

section Syntax

open Lean PrettyPrinter.Delaborator SubExpr PrettyPrinter.Parenthesizer

declare_syntax_cat act

syntax varname " := " aexp : act
syntax "skip" : act
syntax "if " bexp : act

syntax:min "act " "{" act "}" : term

macro_rules
  | `(act {$x:varname := $e}) => `(Act.assign (var {$x}) (aexpr {$e}))
  | `(act {skip}) => `(Act.skip)
  | `(act {if $b}) => `(Act.condition (bexpr {$b}))

declare_syntax_cat mem

syntax varname " ↦ " num : mem
syntax mem ", " mem : mem

syntax:min "mem " "{" mem "}" : term
syntax:min "mem " "{" "}" : term

macro_rules
  | `(mem { }) => `((default : Mem))
  | `(mem { $x:varname ↦ $y }) => `((mem {})[(var {$x}) ↦ $y])
  | `(mem { $m₁, $m₂ }) => `((mem {$m₁}) ++ (mem {$m₂}))

-- syntax:min "dom " "{" varname,* "}" : term

-- macro_rules
--   | `(dom { $d₁:varname,* }) => `(({ $[var { $d₁ }],* } : Set String))

-- #check dom { x, y, z }

instance : Repr Act where
  reprPrec α _ :=
    match α with
    | act {~x := ~e} => s!"{repr x} := {repr e}"
    | act {skip} => "skip"
    | act {if ~b} => s!"if {repr b}"

end Syntax

#eval mem {}
#eval mem { x ↦ 12 }
#eval mem { x ↦ 12, y ↦ 15 }

def 𝒜 : AExpr → Mem → Option ℤ
| .const n, _ => some n
| .var n, σ => if h : n ∈ σ.dom then σ.read ⟨n, h⟩ else none
| aexpr { ~a₁ + ~a₂ }, σ => return (← 𝒜 a₁ σ) + (← 𝒜 a₂ σ)
| aexpr { ~a₁ - ~a₂ }, σ => return (← 𝒜 a₁ σ) - (← 𝒜 a₂ σ)
| aexpr { ~a₁ * ~a₂ }, σ => return (← 𝒜 a₁ σ) * (← 𝒜 a₂ σ)
| aexpr { ~a₁ / ~a₂ }, σ => return (← 𝒜 a₁ σ) / (← 𝒜 a₂ σ)

def ℬ : BExpr → Mem → Option Bool
| .const t, _ => pure t
| bexpr { ¬~b }, σ => return ¬(← ℬ b σ)
| bexpr { ~a₁ = ~a₂ }, σ => return (← 𝒜 a₁ σ) = (← 𝒜 a₂ σ)
| bexpr { ~a₁ ≠ ~a₂ }, σ => return (← 𝒜 a₁ σ) ≠ (← 𝒜 a₂ σ)
| bexpr { ~a₁ < ~a₂ }, σ => return (← 𝒜 a₁ σ) < (← 𝒜 a₂ σ)
| bexpr { ~a₁ ≤ ~a₂ }, σ => return (← 𝒜 a₁ σ) ≤ (← 𝒜 a₂ σ)
| bexpr { ~a₁ > ~a₂ }, σ => return (← 𝒜 a₁ σ) > (← 𝒜 a₂ σ)
| bexpr { ~a₁ ≥ ~a₂ }, σ => return (← 𝒜 a₁ σ) ≥ (← 𝒜 a₂ σ)
| bexpr { ~a₁ ∧ ~a₂ }, σ => return (← ℬ a₁ σ) ∧ (← ℬ a₂ σ)
| bexpr { ~a₁ ∨ ~a₂ }, σ => return (← ℬ a₁ σ) ∨ (← ℬ a₂ σ)

def 𝒮 : Act → Mem → Option Mem
| act {~x := ~a}, σ => do some $ σ[x ↦ ← 𝒜 a σ]
| act {skip}, σ => some σ
| act {if ~b}, σ => do if ← ℬ b σ then some σ else none
