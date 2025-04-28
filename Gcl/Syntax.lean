import Gcl.Lang
import Gcl.DSet
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

namespace GCL

section Syntax

open Lean PrettyPrinter.Delaborator SubExpr PrettyPrinter.Parenthesizer

declare_syntax_cat varname

syntax ident : varname
syntax:max "~" term:max : varname

syntax "var " "{" varname "}" : term

open Lean in
macro_rules
    | `(var { $n:ident }) => `(term|$(quote n.getId.toString))
    | `(var { ~$stx }) => pure stx

declare_syntax_cat aop

syntax "*" : aop
syntax "/" : aop
syntax "+" : aop
syntax "-" : aop

syntax:min "aopr " "{" aop "}" : term

macro_rules
  | `(aopr {*}) => `(AOp.mul)
  | `(aopr {/}) => `(AOp.div)
  | `(aopr {+}) => `(AOp.add)
  | `(aopr {-}) => `(AOp.sub)

declare_syntax_cat aexp

syntax varname : aexp
syntax "var " varname : aexp
syntax "var " "~" term:max : aexp
syntax num : aexp
syntax "const " num : aexp
syntax "const " "~" term:max : aexp

syntax:75 "-" aexp:75 : aexp

syntax:70 aexp:70 " * " aexp:71 : aexp
syntax:70 aexp:70 " / " aexp:71 : aexp

syntax:65 aexp:65 " + " aexp:66 : aexp
syntax:65 aexp:65 " - " aexp:66 : aexp

syntax "(" aexp ")" : aexp
syntax:max "~" term:max : aexp

syntax:min aexp "~" term:max aexp : aexp
syntax:min "aexpr " "{" aexp "}" : term

declare_syntax_cat bexp

syntax "const " "~" term:max : bexp

syntax:75 "¬" bexp:75 : bexp

syntax:50 aexp:50 " < " aexp:51 : bexp
syntax:50 aexp:50 " ≤ " aexp:51 : bexp
syntax:50 aexp:50 " <= " aexp:51 : bexp
syntax:50 aexp:50 " >= " aexp:51 : bexp
syntax:50 aexp:50 " ≥ " aexp:51 : bexp
syntax:50 aexp:50 " > " aexp:51 : bexp
syntax:45 aexp:45 " = " aexp:46 : bexp
syntax:45 aexp:45 " != " aexp:46 : bexp
syntax:45 aexp:45 " ≠ " aexp:46 : bexp

syntax:35 bexp:35 " ∧ " bexp:36 : bexp
syntax:35 bexp:35 " ∨ " bexp:36 : bexp

syntax "(" bexp ")" : bexp
syntax:max "~" term:max : bexp

syntax:min "bexpr " "{" bexp "}" : term

declare_syntax_cat cmd
declare_syntax_cat gcmd

syntax varname " := " aexp : cmd
syntax "skip" : cmd
syntax:40 cmd:40 " ; " cmd:41 : cmd
syntax "if " gcmd " fi" : cmd
syntax "do " gcmd " od" : cmd

syntax:max "~" term:max : cmd

syntax:min "gcl " "{" cmd "}" : term

syntax bexp " → " cmd : gcmd
syntax bexp " -> " cmd : gcmd
syntax gcmd " [] " gcmd : gcmd

syntax:max "~" term:max : gcmd

syntax:min "gcluard " "{" gcmd "}" : term

open Lean in
macro_rules
    | `(aexpr {$n:num}) => `(AExpr.const $(quote n.getNat))
    | `(aexpr {const $n:num}) => `(AExpr.const $(quote n.getNat))
    | `(aexpr {const ~$n}) => `(AExpr.const $n)
    | `(aexpr {$n:varname}) => `(AExpr.var (var {$n}))
    | `(aexpr {var $n:varname}) => `(AExpr.var (var {$n}))
    | `(aexpr {var ~$n}) => `(AExpr.var $n)
    | `(aexpr {$e1:aexp * $e2:aexp}) => `(AExpr.bin .mul (aexpr {$e1}) (aexpr {$e2}))
    | `(aexpr {$e1:aexp / $e2:aexp}) => `(AExpr.bin .div (aexpr {$e1}) (aexpr {$e2}))
    | `(aexpr {$e1:aexp + $e2:aexp}) => `(AExpr.bin .add (aexpr {$e1}) (aexpr {$e2}))
    | `(aexpr {$e1:aexp - $e2:aexp}) => `(AExpr.bin .sub (aexpr {$e1}) (aexpr {$e2}))
    | `(aexpr {$e1:aexp ~$op:term $e2:aexp}) => `(AExpr.bin $op (aexpr {$e1}) (aexpr {$e2}))
    | `(aexpr {($e)}) => `(aexpr{$e})
    | `(aexpr {~$stx}) => pure stx

open Lean in
macro_rules
    | `(bexpr {const ~$e}) => `(BExpr.const $e)
    | `(bexpr {¬$e:bexp}) => `(BExpr.not (bexpr {$e}))
    | `(bexpr {$e1:aexp < $e2:aexp}) => `(BExpr.rel .lt (aexpr {$e1}) (aexpr {$e2}))
    | `(bexpr {$e1:aexp ≤ $e2:aexp}) => `(BExpr.rel .le (aexpr {$e1}) (aexpr {$e2}))
    | `(bexpr {$e1:aexp <= $e2:aexp}) => `(BExpr.rel .le (aexpr {$e1}) (aexpr {$e2}))
    | `(bexpr {$e1:aexp >= $e2:aexp}) => `(BExpr.rel .ge (aexpr {$e1}) (aexpr {$e2}))
    | `(bexpr {$e1:aexp ≥ $e2:aexp}) => `(BExpr.rel .ge (aexpr {$e1}) (aexpr {$e2}))
    | `(bexpr {$e1:aexp > $e2:aexp}) => `(BExpr.rel .gt (aexpr {$e1}) (aexpr {$e2}))
    | `(bexpr {$e1:aexp = $e2:aexp}) => `(BExpr.rel .eq (aexpr {$e1}) (aexpr {$e2}))
    | `(bexpr {$e1:aexp != $e2:aexp}) => `(BExpr.rel .ne (aexpr {$e1}) (aexpr {$e2}))
    | `(bexpr {$e1:aexp ≠ $e2:aexp}) => `(BExpr.rel .ne (aexpr {$e1}) (aexpr {$e2}))
    | `(bexpr {$e1:bexp ∧ $e2:bexp}) => `(BExpr.bin .land (bexpr {$e1}) (bexpr {$e2}))
    | `(bexpr {$e1:bexp ∨ $e2:bexp}) => `(BExpr.bin .lor (bexpr {$e1}) (bexpr {$e2}))
    | `(bexpr {($e)}) => `(bexpr{$e})
    | `(bexpr {~$stx}) => pure stx

open Lean in
macro_rules
    | `(gcl {$n:varname := $e:aexp}) => `(Command.assign (var {$n}) (aexpr {$e}))
    | `(gcl {skip}) => `(Command.skip)
    | `(gcl {$c1 ; $c2}) => `(Command.seq (gcl {$c1}) (gcl {$c2}))
    | `(gcl {if $g fi}) => `(Command.iffi (gcluard {$g}))
    | `(gcl {do $g od}) => `(Command.dood (gcluard {$g}))
    | `(gcl {~$stx}) => pure stx

open Lean in
macro_rules
    | `(gcluard {$b:bexp → $c:cmd}) => `(Guarded.condition (bexpr {$b}) (gcl {$c}))
    | `(gcluard {$b:bexp -> $c:cmd}) => `(Guarded.condition (bexpr {$b}) (gcl {$c}))
    | `(gcluard {$c1:gcmd [] $c2:gcmd}) => `(Guarded.choice (gcluard {$c1}) (gcluard {$c2}))
    | `(gcluard {~$stx}) => pure stx

@[category_parenthesizer aexp]
def aexp.parenthesizer : Lean.PrettyPrinter.CategoryParenthesizer | prec => do
  maybeParenthesize `aexp true wrapParens prec $
    parenthesizeCategoryCore `aexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

@[category_parenthesizer aexp]
def bexp.parenthesizer : Lean.PrettyPrinter.CategoryParenthesizer | prec => do
  maybeParenthesize `bexp true wrapParens prec $
    parenthesizeCategoryCore `bexp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

def delabNameInner : DelabM (TSyntax `varname) := do
  let e ← getExpr
  match e with
  | .lit (.strVal s) =>
    let x := mkIdent <| .mkSimple s
    pure <| ⟨x.raw⟩
  | _ => `(varname|~($(← delab))) >>= annAsTerm

partial def delabAExprInner : DelabM (TSyntax `aexp) := do
    let e ← getExpr
    let stx ←
        match_expr e with
        | AExpr.const x =>
            match_expr x with
            | OfNat.ofNat _ n _ =>
                if let some n' := n.nat? then
                    pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
                else if let .lit (.natVal n') := n then
                    pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
                else withAppArg `(aexp| ~$(← delab))
            | _ =>
                `(aexp| ~(AExpr.const $(← withAppArg delab)))
        | AExpr.bin op _ _ =>
            let s1 ← withAppFn <| withAppArg delabAExprInner
            let s2 ← withAppArg delabAExprInner
            match_expr op with
            | AOp.add => `(aexp| $s1 + $s2)
            | AOp.mul => `(aexp| $s1 * $s2)
            | _ => `(aexp|~(AExpr.bin $(← withAppFn <| withAppFn <| withAppArg delab) $(← withAppFn <| withAppArg delab) $(← withAppArg delab)))
        | _ =>
            `(aexp| ~$(← delab))
    annAsTerm stx

@[delab app.GCL.AExpr.const, delab app.GCL.AExpr.bin]
partial def delabAExpr : Delab := do
    guard <| match_expr ← getExpr with
        | AExpr.const _ => true
        | AExpr.bin _ _ _ => true
        | _ => false
    match ← delabAExprInner with
    | `(aexp|~$e) => pure e
    | e => `(term|aexpr {$(⟨e⟩)})

partial def delabBExprInner : DelabM (TSyntax `bexp) := do
    let e ← getExpr
    let stx ←
        match_expr e with
        | BExpr.const x =>
            match_expr x with
            -- | OfNat.ofNat _ n _ =>
            --     if let some n' := n.nat? then
            --         pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
            --     else if let .lit (.natVal n') := n then
            --         pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
            --     else withAppArg `(aexp| ~$(← delab))
            | _ =>
                `(bexp| ~(BExpr.const $(← withAppArg delab)))
        | BExpr.rel op _ _ =>
            let s1 ← withAppFn <| withAppArg delabAExprInner
            let s2 ← withAppArg delabAExprInner
            match_expr op with
            | ROp.eq => `(bexp| $s1:aexp = $s2)
            | ROp.lt => `(bexp| $s1:aexp < $s2)
            | ROp.lt => `(bexp| $s1:aexp < $s2)
            | ROp.le => `(bexp| $s1:aexp ≤ $s2)
            | ROp.ge => `(bexp| $s1:aexp ≥ $s2)
            | ROp.gt => `(bexp| $s1:aexp > $s2)
            | ROp.eq => `(bexp| $s1:aexp = $s2)
            | ROp.ne => `(bexp| $s1:aexp ≠ $s2)
            | _ => `(bexp|~(BExpr.rel $(← withAppFn <| withAppFn <| withAppArg delab) $(← withAppFn <| withAppArg delab) $(← withAppArg delab)))
        | _ =>
            `(bexp| ~$(← delab))
    annAsTerm stx

@[delab app.GCL.BExpr.const, delab app.GCL.BExpr.rel]
partial def delabBExpr : Delab := do
    guard <| match_expr ← getExpr with
        | BExpr.const _ => true
        | BExpr.rel _ _ _ => true
        | _ => false
    match ← delabBExprInner with
    | `(bexp|~$e) => pure e
    | e => `(term|bexpr {$(⟨e⟩)})

mutual

partial def delabCommandInner : DelabM (TSyntax `cmd) := do
    let e ← getExpr
    let stx ←
        match_expr e with
        | Command.skip =>
            `(cmd| skip)
        | Command.assign _ _ =>
            let s1 ← withAppFn <| withAppArg delabNameInner
            let s2 ← withAppArg delabAExprInner
            `(cmd| $s1:varname := $s2)
        | Command.seq _ _ =>
            let s1 ← withAppFn <| withAppArg delabCommandInner
            let s2 ← withAppArg delabCommandInner
            `(cmd| $s1:cmd ; $s2)
        | Command.iffi _ =>
            let s1 ← withAppArg delabGuardedInner
            `(cmd| if $s1 fi)
        | Command.dood _ =>
            let s1 ← withAppArg delabGuardedInner
            `(cmd| do $s1 od)
        | _ =>
            `(cmd| ~$(← delab))
    annAsTerm stx

partial def delabGuardedInner : DelabM (TSyntax `gcmd) := do
    let e ← getExpr
    let stx ←
        match_expr e with
        | Guarded.condition _ _ _ =>
            let s1 ← withAppFn <| withAppArg delabBExprInner
            let s2 ← withAppArg delabCommandInner
            `(gcmd| $s1:bexp → $s2)
        | Guarded.choice _ _ _ =>
            let s1 ← withAppFn <| withAppArg delabGuardedInner
            let s2 ← withAppArg delabGuardedInner
            `(gcmd| $s1 [] $s2)
        | _ =>
            `(gcmd| ~$(← delab))
    annAsTerm stx

end

@[delab app.GCL.Command.skip, delab app.GCL.Command.assign, delab app.GCL.Command.seq]
partial def delabCommand : Delab := do
    guard <| match_expr ← getExpr with
        | Command.skip => true
        | Command.assign _ _ => true
        | Command.seq _ _ => true
        | _ => false
    match ← delabCommandInner with
    | `(cmd|~$e) => pure e
    | e => `(term|gcl {$(⟨e⟩)})

@[delab app.GCL.Guarded.choice, delab app.GCL.Guarded.condition]
partial def delabGuarded : Delab := do
    guard <| match_expr ← getExpr with
        | Guarded.choice _ _ _ => true
        | Guarded.condition _ _ _ => true
        | _ => false
    match ← delabGuardedInner with
    | `(gcmd|~$e) => pure e
    | e => `(term|gcluard {$(⟨e⟩)})

set_option pp.rawOnError true

#check aexpr { 12 }
#check aexpr { 12 + 15 * 16 + 3 }
#check bexpr { 12 + 15 * 16 + 3 <= 2 }
#check gcl { skip }
#check gcl { x := 12 ; if 3 > 2 → skip fi ; do 3 > 2 → skip od }

def AExpr.repr : AExpr → String
| .const n => s!"{n}"
| .var n => s!"{n}"
| aexpr {~e1 * ~e2} => s!"({repr e1} * {repr e2})"
| aexpr {~e1 / ~e2} => s!"({repr e1} / {repr e2})"
| aexpr {~e1 + ~e2} => s!"({repr e1} + {repr e2})"
| aexpr {~e1 - ~e2} => s!"({repr e1} - {repr e2})"

def BExpr.repr : BExpr → String
| .const b => s!"{b}"
| bexpr {¬~e} => s!"¬{e.repr}"
| bexpr {~e1 < ~e2} => s!"{e1.repr} < {e2.repr}"
| bexpr {~e1 ≤ ~e2} => s!"{e1.repr} ≤ {e2.repr}"
| bexpr {~e1 ≥ ~e2} => s!"{e1.repr} ≥ {e2.repr}"
| bexpr {~e1 > ~e2} => s!"{e1.repr} > {e2.repr}"
| bexpr {~e1 = ~e2} => s!"{e1.repr} = {e2.repr}"
| bexpr {~e1 ≠ ~e2} => s!"{e1.repr} ≠ {e2.repr}"
| bexpr {~e1 ∧ ~e2} => s!"{e1.repr} ∧ {e2.repr}"
| bexpr {~e1 ∨ ~e2} => s!"{e1.repr} ∨ {e2.repr}"

instance : Repr AExpr where reprPrec e _ := e.repr
instance : Repr BExpr where reprPrec e _ := e.repr

end Syntax

end GCL
