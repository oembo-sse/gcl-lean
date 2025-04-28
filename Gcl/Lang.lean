import Gcl.DSet

namespace GCL

inductive AOp where | add | sub | mul | div
deriving Repr, DecidableEq

inductive ROp where | lt | le | gt | ge | eq | ne
deriving Repr, DecidableEq

inductive LOp where | land | lor
deriving Repr, DecidableEq

inductive AExpr where
| const : ℤ → AExpr
| var : String → AExpr
| bin : AOp → AExpr → AExpr → AExpr
deriving DecidableEq

inductive BExpr where
| const : Bool → BExpr
| not : BExpr → BExpr
| rel : ROp → AExpr → AExpr → BExpr
| bin : LOp → BExpr → BExpr → BExpr
deriving DecidableEq

inductive Guarded (C : Type*) where
| condition : BExpr → C → Guarded C
| choice : Guarded C → Guarded C → Guarded C

inductive Command where
| assign : String → AExpr → Command
| skip
| seq : Command → Command → Command
| iffi : Guarded Command → Command
| dood : Guarded Command → Command

instance : Coe Bool BExpr where
  coe := .const

end GCL
