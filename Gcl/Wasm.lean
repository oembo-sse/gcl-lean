import Init.System.IO
import Std.Data.HashMap.Basic

namespace Wasm

def WId := String

def Label := String
deriving Repr, BEq, Hashable

def LabelIdx := String
deriving Repr, BEq, Hashable

def LocalIdx := String
deriving Repr, BEq, Hashable

structure GlobalIdx where
deriving Repr, BEq, Hashable

structure FuncIdx where
deriving Repr, BEq, Hashable

structure HeapType where
deriving Repr, BEq, Hashable

structure Offset where
deriving Repr, BEq, Hashable

structure Align (n : ℕ) where
deriving Repr, BEq, Hashable

structure Memarg (n : ℕ) where
  offset : Offset
  align : Align n
deriving Repr, BEq, Hashable

structure Float64 where
deriving Repr, BEq, Hashable

instance : Repr Int32 where
  reprPrec x _ := s!"{x}"

inductive PlainInstr where
  -- Control Instructions
  | unreachable
  | nop
  | br : LabelIdx → PlainInstr
  | br_if : LabelIdx → PlainInstr
  | return
  | call
  | call_indirect
  -- Reference Instructions
  | ref_null : HeapType → PlainInstr
  | ref_is_null : PlainInstr
  | ref_func : FuncIdx → PlainInstr
  -- Parametric Instructions
  | drop
  | select -- TODO: (result*)?
  -- Variable Instructions
  | local.get : LocalIdx → PlainInstr
  | local.set : LocalIdx → PlainInstr
  | local.tee : LocalIdx → PlainInstr
  | global.get : GlobalIdx → PlainInstr
  | global.set : GlobalIdx → PlainInstr
  -- Table Instructions
  -- Memory Instructions
  | i32.load : (Memarg 4) → PlainInstr
  | i64.load : (Memarg 8) → PlainInstr
  | f32.load : (Memarg 4) → PlainInstr
  | f64.load : (Memarg 8) → PlainInstr
  -- TODO: load*
  | i32.store : (Memarg 4) → PlainInstr
  | i64.store : (Memarg 8) → PlainInstr
  | f32.store : (Memarg 4) → PlainInstr
  | f64.store : (Memarg 8) → PlainInstr
  -- TODO: store*
  | memory_size
  | memory_grow
  | memory_fill
  | memory_copy
  -- TODO: memory init & data drop
  -- Numeric Instructions
  | i32.const : Int32 → PlainInstr
  | i64.const : Int64 → PlainInstr
  | f32.const : Float32 → PlainInstr
  | f64.const : Float64 → PlainInstr

  | i32.clz
  | i32.ctz
  | i32.popcnt
  | i32.add
  | i32.sub
  | i32.mul
  | i32.div_s
  | i32.div_u
  | i32.rem_s
  | i32.rem_u
  | i32.and
  | i32.or
  | i32.xor
  | i32.shl
  | i32.shr_s
  | i32.shr_u
  | i32.rotl
  | i32.rotr

  | i64.clz
  | i64.ctz
  | i64.popcnt
  | i64.add
  | i64.sub
  | i64.mul
  | i64.div_s
  | i64.div_u
  | i64.rem_s
  | i64.rem_u
  | i64.and
  | i64.or
  | i64.xor
  | i64.shl
  | i64.shr_s
  | i64.shr_u
  | i64.rotl
  | i64.rotr

  | f32.abs
  | f32.neg
  | f32.ceil
  | f32.floor
  | f32.trunc
  | f32.nearest
  | f32.sqrt
  | f32.add
  | f32.sub
  | f32.mul
  | f32.div
  | f32.min
  | f32.max
  | f32.copysign

  | f64.abs
  | f64.neg
  | f64.ceil
  | f64.floor
  | f64.trunc
  | f64.nearest
  | f64.sqrt
  | f64.add
  | f64.sub
  | f64.mul
  | f64.div
  | f64.min
  | f64.max
  | f64.copysign

  | i32.eqz
  | i32.eq
  | i32.ne
  | i32.lt_s
  | i32.lt_u
  | i32.gt_s
  | i32.gt_u
  | i32.le_s
  | i32.le_u
  | i32.ge_s
  | i32.ge_u

  | i64.eqz
  | i64.eq
  | i64.ne
  | i64.lt_s
  | i64.lt_u
  | i64.gt_s
  | i64.gt_u
  | i64.le_s
  | i64.le_u
  | i64.ge_s
  | i64.ge_u

  | f32.eq
  | f32.ne
  | f32.lt
  | f32.gt
  | f32.le
  | f32.ge

  | f64.eq
  | f64.ne
  | f64.lt
  | f64.gt
  | f64.le
  | f64.ge

  | i32.wrap_i64
  | i32.trunc_f32_s
  | i32.trunc_f32_u
  | i32.trunc_f64_s
  | i32.trunc_f64_u
  | i32.trunc_sat_f32_s
  | i32.trunc_sat_f32_u
  | i32.trunc_sat_f64_s
  | i32.trunc_sat_f64_u
  | i64.extend_i32_s
  | i64.extend_i32_u
  | i64.trunc_f32_s
  | i64.trunc_f32_u
  | i64.trunc_f64_s
  | i64.trunc_f64_u
  | i64.trunc_sat_f32_s
  | i64.trunc_sat_f32_u
  | i64.trunc_sat_f64_s
  | i64.trunc_sat_f64_u
  | f32.convert_i32_s
  | f32.convert_i32_u
  | f32.convert_i64_s
  | f32.convert_i64_u
  | f32.demote_f64
  | f64.convert_i32_s
  | f64.convert_i32_u
  | f64.convert_i64_s
  | f64.convert_i64_u
  | f64.promote_f32
  | i32.reinterpret_f32
  | i64.reinterpret_f64
  | f32.reinterpret_i32
  | f64.reinterpret_i64

  | i32.extend8_s
  | i32.extend16_s
  | i64.extend8_s
  | i64.extend16_s
  | i64.extend32_s

  -- Vector Instructions
deriving Repr, BEq

mutual

inductive BlockInstr where
  | ite : List Instr → List Instr → BlockInstr
  | block : Label → List Instr → BlockInstr
  | loop : Label → List Instr → BlockInstr
deriving BEq

inductive Instr where
  | plain : PlainInstr → Instr
  | block : BlockInstr → Instr
  | marker : LabelIdx → List Instr → Instr
deriving BEq

end

structure Expr where
  instructions : List Instr
deriving Inhabited

inductive NumType where
  | i32
  | i64
  | f32
  | f64

inductive ValType where
  | numtype : NumType → ValType
  | vectype
  | reftype

structure Local where
  id : WId
  type : ValType

structure Func where
  id : WId
  locals : List Local
  instructions : List Instr

inductive ModuleField where
  | func : Func → ModuleField

structure Module where
  fields : List ModuleField

instance : ToString WId where
  toString x := x

instance : Repr WId where
  reprPrec x _ := toString x

instance : ToString Label where
  toString x := x

instance : Repr Label where
  reprPrec x _ := toString x

instance : ToString LocalIdx where
  toString x := x

instance : Repr LocalIdx where
  reprPrec x _ := toString x

def indent (s : String) : String := s.split (· = '\n') |>.map ("  " ++ ·) |> "\n".intercalate

def PlainInstr.toString : PlainInstr → String
| .return => "return"
| .i32.lt_u => "i32.lt_u"
| .i32.ge_u => "i32.ge_u"
| .i32.eqz => "i32.eqz"
| .i32.eq => "i32.eq"
| .i32.ne => "i32.ne"
| .i32.lt_s => "i32.lt_s"
| .i32.le_s => "i32.le_s"
| .i32.gt_s => "i32.gt_s"
| .i32.ge_s => "i32.ge_s"
| .i32.and => "i32.and"
| .i32.or => "i32.or"
| .i32.rem_u => "i32.rem_u"
| .i32.add => "i32.add"
| .i32.sub => "i32.sub"
| .i32.mul => "i32.mul"
| .i32.div_s => "i32.div_s"
| .i32.const n => s!"(i32.const {n})"
| .local.get n => s!"(local.get {n})"
| .local.set n => s!"(local.set {n})"
| .br label => s!"br {reprStr label}"
| .br_if label => s!"br_if {reprStr label}"
| i => s!"\{TODO: {reprStr i}}"

instance : Repr PlainInstr := ⟨fun p _ ↦ p.toString⟩

mutual

def Instr.toString : Instr → String
| .plain pinst => reprStr pinst
| .block binst => binst.toString
| .marker label rest => s!"#marker {reprStr label} (rest {rest.map Instr.toString |> "\n".intercalate |> indent})"

def BlockInstr.toString : BlockInstr → String
  | .ite thens [] =>
    s!"if\n{
      thens.map Instr.toString |> "\n".intercalate |> indent
    }\nend"
  | .ite thens elses =>
    s!"if\n{
      thens.map Instr.toString |> "\n".intercalate |> indent
    }\nelse\n{
      elses.map Instr.toString |> "\n".intercalate |> indent
    }\nend"
  | .block label body =>
    s!"(block {reprStr label}\n{
      body.map Instr.toString |> "\n".intercalate |> indent
    }\n)"
  | .loop label body =>
    s!"(loop {reprStr label}\n{
      body.map Instr.toString |> "\n".intercalate |> indent
    }\n)"

end

instance : Repr Instr := ⟨fun i _ ↦ i.toString⟩
instance : Repr BlockInstr := ⟨fun b _ ↦ b.toString⟩

instance : Repr NumType where
  reprPrec n _ := match n with
    | .i32 => "i32"
    | .i64 => "i64"
    | .f32 => "f32"
    | .f64 => "f64"

instance : Repr ValType where
  reprPrec v _ := match v with
    | .numtype n => repr n
    | _ => "??"


instance : Repr Local where
  reprPrec l _ := s!"(local {reprStr l.id} {reprStr l.type})"

instance : Repr Func where
  reprPrec f _ :=
    s!"(func {reprStr f.id} ({f.locals.map reprStr |> " ".intercalate})\n{
      f.instructions.map reprStr |> "\n".intercalate |> indent}\n)"

instance : Repr ModuleField where
  reprPrec f _ := match f with
    | .func func => reprStr func

instance : Repr Module where
  reprPrec m _ := s!"(module\n{m.fields.map reprStr |> "\n".intercalate |> indent}\n)"

-- declare_syntax_cat wasm_ident
-- syntax "$" ident : wasm_ident
-- syntax "wasm_ident " "{" wasm_ident "}" : term
-- open Lean
-- macro_rules | `(wasm_ident { $id }) => do `(term|$(quote s!"${id.raw.getArg 2 |>.getId.toString}"))

declare_syntax_cat wasm_spec

syntax "|" ident ident num "/" num : wasm_spec

syntax "declare_wasm_spec " "{" wasm_spec* "}" : command

syntax "wasm_spec_ident " "{" wasm_spec "}" : term

open Lean in
macro_rules
  -- | `()
  | `(declare_wasm_spec { $things* }) =>
    -- let this := things.map (fun x ↦ x)
    `(
      def x := $(quote (reprStr things))

      #eval x
    )

    -- let things' : TSyntaxArray `ident  := {}
    -- `(
    --     inductive Thing where
    --     $[| wasm_spec_ident { $things' }]*
    --   )

declare_wasm_spec {
  | local.get localidx 0/1
  | local.set localidx 1/0
}

declare_syntax_cat wasm_module

declare_syntax_cat wasm_local

declare_syntax_cat wasm_local_idx

declare_syntax_cat wasm_instr

declare_syntax_cat wasm_instrs

declare_syntax_cat wasm_instr_folded

declare_syntax_cat wasm_field

declare_syntax_cat wasm_num

declare_syntax_cat wasm_id

declare_syntax_cat wasm_label

declare_syntax_cat wasm_label_idx

declare_syntax_cat wasm_type

syntax ident : wasm_id

syntax ident : wasm_local_idx
syntax:max "~" term:max : wasm_local_idx

syntax ident : wasm_label
syntax:max "~" term:max : wasm_label

syntax ident : wasm_label_idx
syntax:max "~" term:max : wasm_label_idx

syntax "i32" : wasm_type

syntax num : wasm_num
syntax:max "~" term:max : wasm_num

syntax "if" ppLine wasm_instrs ppDedent(ppLine "else") ppLine wasm_instrs ppDedent(ppLine "end") : wasm_instr
syntax "if" ppLine wasm_instrs ppDedent(ppLine "end") : wasm_instr
syntax "block " wasm_label ppLine wasm_instrs ppDedent(ppLine "end") : wasm_instr
syntax "(" "block " wasm_label ppLine wasm_instrs ppDedent(ppLine ")") : wasm_instr
syntax "loop " wasm_label ppLine wasm_instrs ppDedent(ppLine "end") : wasm_instr
syntax "(" "loop " wasm_label ppLine wasm_instrs ppDedent(ppLine ")") : wasm_instr
syntax "unreachable" : wasm_instr
syntax "nop" : wasm_instr
syntax "br" wasm_label_idx : wasm_instr
syntax "br_if" wasm_label_idx : wasm_instr
syntax "return" : wasm_instr

syntax:max "~" term:max : wasm_instr

syntax "local.get" wasm_local_idx : wasm_instr
syntax "local.set" wasm_local_idx : wasm_instr
syntax "i32.const" wasm_num : wasm_instr
syntax "i32.ge_u" : wasm_instr
syntax "i32.lt_u" : wasm_instr
syntax "i32.eqz" : wasm_instr
syntax "i32.eq" : wasm_instr
syntax "i32.ne" : wasm_instr
syntax "i32.lt_s" : wasm_instr
syntax "i32.le_s" : wasm_instr
syntax "i32.gt_s" : wasm_instr
syntax "i32.ge_s" : wasm_instr
syntax "i32.and" : wasm_instr
syntax "i32.or" : wasm_instr
syntax "i32.rem_u" : wasm_instr
syntax "i32.add" : wasm_instr
syntax "i32.sub" : wasm_instr
syntax "i32.mul" : wasm_instr
syntax "i32.div_s" : wasm_instr
syntax "i32.div_u" : wasm_instr
-- syntax "(" wasm_instr ")" : wasm_instr
syntax "(" wasm_instr ppSpace wasm_instr_folded ")" : wasm_instr
syntax "(" wasm_instr ")" : wasm_instr

syntax wasm_instr : wasm_instr_folded
syntax wasm_instr ppSpace wasm_instr_folded : wasm_instr_folded

syntax wasm_instr : wasm_instrs
syntax wasm_instr wasm_instrs : wasm_instrs

syntax "(" "local " wasm_id ppSpace wasm_type ")" : wasm_local

syntax "(" "func " wasm_id ppSpace ppLine "(" wasm_local* ")" ppLine wasm_instrs ppDedent(ppLine ")") : wasm_field

syntax "(" "module " ppLine wasm_field* ppDedent(ppLine ")") : wasm_module

syntax "wasm " "{" ppLine wasm_module ppDedent(ppLine "}") : term
syntax "wasm_num " "{" wasm_num "}" : term
syntax "wasm_type " "{" wasm_type "}" : term
syntax "wasm_local_idx " "{" wasm_local_idx "}" : term
syntax "wasm_field " "{" ppLine wasm_field ppDedent(ppLine "}") : term
syntax "wasm_local " "{" ppLine wasm_local ppDedent(ppLine "}") : term
syntax "wasm_label " "{" wasm_label "}" : term
syntax "wasm_label_idx " "{" wasm_label_idx "}" : term
syntax "wasm_instr_folded " "{" wasm_instr_folded "}" : term
syntax "wasm_instr " "{" wasm_instr "}" : term
syntax "wasm_instrs " "{" wasm_instrs "}" : term
syntax "wasm_id " "{" wasm_id "}" : term

open Lean in
macro_rules
  | `(wasm_id { $id:ident }) =>
    `(term|($(quote id.getId.toString) : WId))
  | `(wasm_local_idx { $id:ident }) =>
    `(term|($(quote id.getId.toString) : LocalIdx))
  | `(wasm_local_idx { ~$id }) => `($id)
  | `(wasm_label { $id:ident }) =>
    `(term|($(quote id.getId.toString) : Label))
  | `(wasm_label { ~$id }) => `($id)
  | `(wasm_label_idx { $id:ident }) =>
    `(term|($(quote id.getId.toString) : LabelIdx))
  | `(wasm_label_idx { ~$id }) => `($id)

  | `(wasm_num { $n:num }) => `($n)
  | `(wasm_num { ~$n }) => `($n)

  | `(wasm_instr { block $label:wasm_label $body end }) =>
    `([Instr.block (.block (wasm_label {$label}) (wasm_instrs {$body}))])
  | `(wasm_instr { (block $label:wasm_label $body) }) =>
    `([Instr.block (.block (wasm_label {$label}) (wasm_instrs {$body}))])
  | `(wasm_instr { loop $label:wasm_label $body end }) =>
    `([Instr.block (.loop (wasm_label {$label}) (wasm_instrs {$body}))])
  | `(wasm_instr { (loop $label:wasm_label $body) }) =>
    `([Instr.block (.loop (wasm_label {$label}) (wasm_instrs {$body}))])
  | `(wasm_instr { if $thens else $elses end }) =>
    `([Instr.block (.ite (wasm_instrs {$thens}) (wasm_instrs {$elses}))])
  | `(wasm_instr { if $thens end }) =>
    `([Instr.block (.ite (wasm_instrs {$thens}) [])])

  | `(wasm_instr { br $label }) => `([Instr.plain (.br (wasm_label_idx {$label}))])
  | `(wasm_instr { br_if $label }) => `([Instr.plain (.br_if (wasm_label_idx {$label}))])
  | `(wasm_instr { return }) => `([Instr.plain .return])

  | `(wasm_instr { local.get $idx }) => `([Instr.plain (.local.get (wasm_local_idx {$idx}))])
  | `(wasm_instr { local.set $idx }) => `([Instr.plain (.local.set (wasm_local_idx {$idx}))])
  | `(wasm_instr { i32.const $n }) => `([Instr.plain (.i32.const (wasm_num {$n} : Int32))])
  | `(wasm_instr { i32.eqz }) => `([Instr.plain .i32.eq])
  | `(wasm_instr { i32.eq }) => `([Instr.plain .i32.eq])
  | `(wasm_instr { i32.ne }) => `([Instr.plain .i32.ne])
  | `(wasm_instr { i32.lt_s }) => `([Instr.plain .i32.lt_s])
  | `(wasm_instr { i32.lt_u }) => `([Instr.plain .i32.lt_u])
  | `(wasm_instr { i32.le_s }) => `([Instr.plain .i32.le_s])
  | `(wasm_instr { i32.gt_s }) => `([Instr.plain .i32.gt_s])
  | `(wasm_instr { i32.ge_s }) => `([Instr.plain .i32.ge_s])
  | `(wasm_instr { i32.ge_u }) => `([Instr.plain .i32.ge_u])
  | `(wasm_instr { i32.and }) => `([Instr.plain .i32.and])
  | `(wasm_instr { i32.or }) => `([Instr.plain .i32.or])
  | `(wasm_instr { i32.rem_u }) => `([Instr.plain .i32.rem_u])
  | `(wasm_instr { i32.add }) => `([Instr.plain .i32.add])
  | `(wasm_instr { i32.sub }) => `([Instr.plain .i32.sub])
  | `(wasm_instr { i32.mul }) => `([Instr.plain .i32.mul])
  | `(wasm_instr { i32.div_s }) => `([Instr.plain .i32.div_s])
  | `(wasm_instr { i32.div_u }) => `([Instr.plain .i32.div_u])

  | `(wasm_instr { ($a:wasm_instr) }) => `(wasm_instr {$a})
  | `(wasm_instrs { $a:wasm_instr }) => `(wasm_instr {$a})
  | `(wasm_instrs { $a:wasm_instr $b }) => `(wasm_instr {$a} ++ wasm_instrs {$b})
  | `(wasm_instr { ($a:wasm_instr $b:wasm_instr_folded) }) =>
    `(wasm_instr_folded {$b} ++ wasm_instr {$a})
  | `(wasm_instr_folded { $a:wasm_instr $b:wasm_instr_folded }) =>
    `(wasm_instr_folded {$b} ++ wasm_instr {$a})
  | `(wasm_instr_folded { $a:wasm_instr }) =>
    `(wasm_instr {$a})

  | `(wasm_instr { ~$a }) => `($a)

  | `(wasm_type { i32 }) => `(ValType.numtype .i32)
  | `(wasm_local { (local $id $type) }) =>
    `(Local.mk (wasm_id {$id}) (wasm_type {$type}))
  | `(wasm_field { (func $id ($locals*) $instr) }) =>
    `((ModuleField.func (Func.mk
      (wasm_id { $id })
      [$[wasm_local { $locals }],*]
      (wasm_instrs { $instr }))))
  | `(wasm { (module $fields*) }) =>
    `((Module.mk
      [$[wasm_field { $fields }],*]
    ))

#eval wasm_field { (func pi () i32.lt_u) }
#eval wasm {
    (module
      (func is_prime
        ((local i i32))

        (i32.const 2)
        (local.get n)
        i32.lt_u
      )
    )
  }
#eval wasm {
    (module
      (func is_prime
        ((local i i32))

        (i32.lt_u (local.get n) (i32.const 2))
      )
    )
  }
#eval wasm {
    (module
      (func is_prime
        ((local i i32))

        (i32.lt_u (local.get n) (i32.const 2))
        if
          i32.const 0
          return
        end

        (i32.eq (local.get n) (i32.const 2))

        (i32.eq (i32.rem_u (local.get n) (i32.const 2)) (i32.const 0))
        if
          i32.const 0
          return
        end

        (local.set i (i32.const 3))

        i32.const 1
      )
    )
  }

abbrev Value := Int32

structure Ctx where
  mod : Module
  locals : Std.HashMap LocalIdx Value
  stack : List Value
  frame : Expr

instance : Repr Ctx where
  reprPrec ctx _ :=
    s!"ctx \{ locals := \{{
      ctx.locals.toList.map (fun (k, v) ↦ s!"{k} ↦ {v}") |> ", ".intercalate
    }}\n      stack := {ctx.stack}, frame := {ctx.frame.instructions.map reprStr |> " ; ".intercalate} }"

def Ctx.ofModule (mod : Module) : Ctx where
  mod := mod
  locals := default
  stack := default
  frame := mod.fields.head? |>.map (fun f ↦
    match f with
    | .func f => Expr.mk f.instructions)
    |>.get!

def Ctx.push (ctx : Ctx) (v : Value) : Ctx :=
  {ctx with stack := v :: ctx.stack}
def Ctx.pop (ctx : Ctx) : Option (Value × Ctx) :=
  match ctx.stack with
  | top :: s => (top, {ctx with stack := s})
  | [] => panic! "no values on the stack"
def Ctx.pop2 (ctx : Ctx) : Option (Value × Value × Ctx) :=
  match ctx.stack with
  | a :: b :: s => (a, b, {ctx with stack := s})
  | _ => panic! "not enough (2) values on the stack"

def Ctx.pop_frame (ctx : Ctx) : Ctx :=
  {ctx with frame := ⟨ctx.frame.instructions.tail⟩}

def Ctx.local_get (ctx : Ctx) (n : LocalIdx) : Option Value :=
  ctx.locals.get? n
def Ctx.local_set (ctx : Ctx) (n : LocalIdx) (v : Value) : Ctx :=
  {ctx with locals := ctx.locals.insert n v}

def Ctx.binop_pop_frame (ctx : Ctx) (f : Value → Value → Option Value) : Option Ctx := do
  -- NOTE: reverse order
  let (r, l, ctx) ← ctx.pop2
  (ctx.push (← f l r)).pop_frame

def Instr.isMarker (inst : Instr) (label : LabelIdx) : Bool :=
  match inst with
  | .marker label' _ => label == label'
  | _ => false

def Ctx.step (ctx : Ctx) : Option Ctx :=
  match ctx.frame.instructions with
  | instr :: _ =>
    match instr with
    | .plain (.i32.const n) => ctx.push n |>.pop_frame
    | .plain .i32.add => ctx.binop_pop_frame (· + ·)
    | .plain .i32.sub => ctx.binop_pop_frame (· - ·)
    | .plain .i32.mul => ctx.binop_pop_frame (· * ·)
    | .plain .i32.div_s => ctx.binop_pop_frame (· / ·)
    | .plain .i32.rem_u => ctx.binop_pop_frame (· % ·)
    | .plain .i32.ge_u => ctx.binop_pop_frame (some <| if · ≥ · then 1 else 0)
    | .plain .i32.lt_u => ctx.binop_pop_frame (some <| if · < · then 1 else 0)
    | .plain .i32.lt_s => ctx.binop_pop_frame (some <| if · < · then 1 else 0)
    | .plain .i32.eq => ctx.binop_pop_frame (some <| if · = · then 1 else 0)
    | .plain .return => some {ctx with frame := ⟨{}⟩}
    | .plain (.local.set n) => do
      let (v, ctx) ← ctx.pop
      ctx.local_set n v |>.pop_frame
    | .plain (.local.get n) => do
      let v ← ctx.local_get n
      ctx.push v |>.pop_frame

    | .plain (.br label) =>
      let frame := ctx.frame.instructions.dropWhile (!·.isMarker label)
      match frame with
      | .marker _ rest :: tail => some {ctx with frame := ⟨rest ++ tail⟩}
      | _ => panic! "marker not found"
    | .plain (.br_if label) => do
      let (v, ctx) ← ctx.pop
      if v ≠ 0 then
        some {ctx with frame := ⟨.plain (.br label) :: ctx.frame.instructions.tail⟩}
      else
        ctx.pop_frame
    | .block (.ite thens elses) => do
      let (v, ctx) ← ctx.pop
      if v ≠ 0 then
        pure {ctx with frame := ⟨thens ++ ctx.frame.instructions.tail⟩ }
      else
        pure {ctx with frame := ⟨elses ++ ctx.frame.instructions.tail⟩ }
    | .block (.block label body) => do
      pure {ctx with frame := ⟨body ++ [.marker label []] ++ ctx.frame.instructions.tail⟩ }
    | .block (.loop label body) => do
      pure {ctx with frame := ⟨body ++ [.marker label [(.block (.loop label body))]] ++ ctx.frame.instructions.tail⟩ }

    | .marker _ _ => ctx.pop_frame

    | _ => panic! (s!"unhanded instr: {reprStr instr}")
  | [] => none

def Ctx.step_n (ctx : Ctx) : Nat → Option Ctx
| 0 => some ctx
| n+1 => match ctx.step with | some ctx' => ctx'.step_n n | none => none

partial def Ctx.run (ctx : Ctx) : Ctx :=
  match ctx.step with
  | some ctx => ctx.run
  | none => ctx

/--
info: ctx { locals := {i ↦ 3}
      stack := [10], frame :=  }
-/
#guard_msgs in
#eval
  let mod := wasm {
    (module
      (func hello
        ((local i i32))
        (i32.add (i32.const 1) (i32.const 2))
        (local.set i)
        (i32.sub (local.get i) (local.get i))
        if
          i32.const 5
        else
          i32.const 10
        end
      )
    )
  }
  Ctx.ofModule mod |>.run

#eval
  let mod := wasm {
    (module
      (func is_prime
        ((local i i32))

        (i32.lt_u (local.get n) (i32.const 2))
        if
          i32.const 0
          return
        end

        (i32.eq (local.get n) (i32.const 2))

        (i32.eq (i32.rem_u (local.get n) (i32.const 2)) (i32.const 0))
        if
          i32.const 0
          return
        end

        (local.set i (i32.const 3))
        (loop testprime (block breaktestprime
          (i32.ge_u (local.get i) (local.get n))
          br_if breaktestprime

          (i32.eq (i32.rem_u (local.get n) (local.get i)) (i32.const 0))
          if
            i32.const 0
            return
          end

          (local.set i (i32.add (local.get i) (i32.const 2)))
          br testprime
        ))

        i32.const 1
      )
    )
  }

  let ctx := Ctx.ofModule mod |>.local_set "n" 5

  ctx.run

end Wasm
