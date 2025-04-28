import Gcl.Wasm
import Gcl.Semantics

namespace GCL

mutual

def Guarded.fv : Guarded Command → DSet String
| gcluard { ~b → ~C } => b.fv ∪ C.fv
| gcluard { ~GC₁ [] ~GC₂ } => GC₁.fv ∪ GC₂.fv

def Command.fv : Command → DSet String
| gcl { skip } => {}
| gcl { ~C₁ ; ~C₂ } => C₁.fv ∪ C₂.fv
| gcl { ~x := ~e } => {x} ∪ e.fv
| gcl { if ~GC fi } | gcl { do ~GC od } => GC.fv

end

def AOp.wasm : AOp → List Wasm.Instr
| .add => wasm_instr { i32.add }
| .sub => wasm_instr { i32.sub }
| .mul => wasm_instr { i32.mul }
| .div => wasm_instr { i32.div_s }

def AExpr.wasm : AExpr → List Wasm.Instr
| aexpr {const ~n} => wasm_instr { i32.const ~(.ofInt n) }
| aexpr {var ~x} => wasm_instr { local.get ~x }
| aexpr { ~a₁ ~op ~a₂ } => a₁.wasm ++ a₂.wasm ++ op.wasm

def BExpr.wasm : BExpr → List Wasm.Instr
| bexpr {const ~b} => if b then wasm_instr { i32.const 1 } else wasm_instr { i32.const 0 }
| bexpr { ¬~b } => b.wasm ++ wasm_instr { i32.eqz }
| bexpr { ~a₁ = ~a₂ } => a₁.wasm ++ a₂.wasm ++ wasm_instr { i32.eq }
| bexpr { ~a₁ ≠ ~a₂ } => a₁.wasm ++ a₂.wasm ++ wasm_instr { i32.ne }
| bexpr { ~a₁ < ~a₂ } => a₁.wasm ++ a₂.wasm ++ wasm_instr { i32.lt_s }
| bexpr { ~a₁ ≤ ~a₂ } => a₁.wasm ++ a₂.wasm ++ wasm_instr { i32.le_s }
| bexpr { ~a₁ > ~a₂ } => a₁.wasm ++ a₂.wasm ++ wasm_instr { i32.gt_s }
| bexpr { ~a₁ ≥ ~a₂ } => a₁.wasm ++ a₂.wasm ++ wasm_instr { i32.ge_s }
| bexpr { ~a₁ ∧ ~a₂ } => a₁.wasm ++ a₂.wasm ++ wasm_instr { i32.and }
| bexpr { ~a₁ ∨ ~a₂ } => a₁.wasm ++ a₂.wasm ++ wasm_instr { i32.or }

mutual

partial def Guarded.wasm_ite (oth : Option (Guarded Command)) : Guarded Command → List Wasm.Instr
| gcluard { ~b → ~C } =>
  b.wasm ++
    match oth with
    | some oth' =>
      wasm_instr { if ~C.wasm else ~(oth'.wasm_ite none) end }
    | none =>
      wasm_instr { if ~C.wasm end }
| gcluard { ~GC₁ [] ~GC₂ } => GC₁.wasm_ite (some <| (oth.map (gcluard {~GC₂ [] ~·})).getD GC₂)

partial def Guarded.wasm_loop (label : Wasm.LabelIdx) (oth : Option (Guarded Command)) : Guarded Command → List Wasm.Instr
| gcluard { ~b → ~C } =>
  b.wasm ++
    match oth with
    | some oth' =>
      wasm_instr { if ~C.wasm (br ~label) else ~(oth'.wasm_loop label none) end }
    | none =>
      wasm_instr { if ~C.wasm (br ~label) end }
| gcluard { ~GC₁ [] ~GC₂ } => GC₁.wasm_loop label (some <| (oth.map (gcluard {~GC₂ [] ~·})).getD GC₂)

partial def Command.wasm : Command → List Wasm.Instr
| gcl { skip } => {}
| gcl { ~C₁ ; ~C₂ } => C₁.wasm ++ C₂.wasm
| gcl { ~x := ~e } => e.wasm ++ wasm_instr { local.set ~x }
| gcl { if ~GC fi } => GC.wasm_ite none
| gcl { do ~GC od } =>
  let label : Wasm.LabelIdx := "loop_head"
  let body := GC.wasm_loop label none
  wasm_instr { (loop ~label ~body) }

end

partial def Command.wasm_module (C : Command) : Wasm.Module :=
  let locals := C.fv.elements.map (Wasm.Local.mk · (.numtype .i32))
  let instructions := C.wasm
  {fields := [.func (Wasm.Func.mk "main" locals instructions)]}

partial def Command.wasm_step_n (C : Command) (n : ℕ) :=
  C.wasm_module |> Wasm.Ctx.ofModule |>.step_n n

partial def Command.wasm_run (C : Command) :=
  C.wasm_module |> Wasm.Ctx.ofModule |>.run

-- #eval gcl { x := 1 + 2 * 3 / y } |>.wasm_module
-- #eval gcl { a := 2 ; b := a + y } |>.wasm_module |> Wasm.Ctx.ofModule |>.local_set "y" 1 |>.run
-- #eval gcl { if 1 = 2 → x := 1 [] 2 = 2 → x := 2 fi } |>.wasm_module
#eval gcl { if 1 = 2 → x := 1 [] 2 = 2 → x := 2 fi } |>.wasm_module
#eval gcl { if 1 = 2 → x := 1 [] 2 = 2 → x := 2 fi } |>.wasm_module |> Wasm.Ctx.ofModule |>.run
#eval gcl { x := 0 ; do x < 10 → x := x + 1 od  } |>.wasm_module
#eval gcl { x := 0 ; do x < 10 → x := x + 1 od  } |>.wasm_run

end GCL
