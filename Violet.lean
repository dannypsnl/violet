import Lean.Elab.Command
import Violet.Ast.Surface
import Violet.Parser
import Violet.Core.Elaboration
open Lean Meta Elab Command

namespace Violet.Core
open Violet.Ast
open Violet.Ast.Surface (Program)

abbrev ElabM := StateT MetaCtx (ExceptT String IO)
abbrev ProgramM := StateT ElabContext (StateT MetaCtx (ExceptT String IO))

def fieldsToSigma (fields : List (String × Surface.Typ)) (f : Surface.Typ → Surface.Typ) : Surface.Typ :=
  match fields with
  | [] => .var "Unit"
  | [(_, ty)] => f ty
  | (name, ty) :: fields =>
    let cur := λ ty2 => f <| Surface.Tm.sigma name ty ty2
    fieldsToSigma fields cur

def reduceCheck (tm : Surface.Tm) (vty : VTy) : ProgramM Val := do
  let ctx ← get
  let tm ← ctx.check tm vty (m := ElabM)
  return ← ctx.env.eval tm (m := ElabM)

def checkDefinitions (p : Program) : ProgramM Unit := do
  for d in p.definitions do
    match d with
    | .def startPos endPos name tele ret_ty body =>
      let ty : Surface.Typ := tele.foldr (λ (x, mode, a) b => .pi mode x a b) ret_ty
      let ty ← reduceCheck (.src startPos endPos ty) .type
      let ctx := (← get).define name (.recur name (← get).lvl) ty
      let val := tele.foldr (λ (x, mode, _) body => .lam mode x body) body
      let val ← ctx.check (.src startPos endPos val) ty (m := ElabM)
      let val ← ctx.env.eval val (m := ElabM)
      set <| (← get).define name val ty
    | .data startPos endPos dataName constructors =>
      -- A data type definition bind its name as type in context is an axiom,
      -- which means we cannot check it but just insert it. Thus, the example
      -- `data A ...` makes judgement:
      --
      -- -----------------
      --    Γ, A : Type
      --
      -- TODO: for indexed data type, it will not be like current simple `Nat : Type`
      --       so we will need to change this line
      let ctx ← get
      let dataTypeLvl := ctx.lvl
      set <| ctx.bind dataName .type
      for (name, tys) in constructors do
        let ty := tys.foldr (λ ty b => .pi .explicit "_" ty b) (.var dataName)
        let ty ← reduceCheck (.src startPos endPos ty) .type
        -- A constructor is just a rigid binding in the environment
        --
        -- e.g. `true` will have value `.rigid true`
        --
        -- so we use `coe` here for constructor name too
        let ctx ← get
        -- record constructors into ElabContext, maps data type to constructors
        let ctorLvl := ctx.lvl
        set <| (ctx.bind name ty).addConstructor dataTypeLvl ctorLvl
    | .record startPos endPos name fields =>
      let ctx ← get
      let v := fieldsToSigma fields.toList (λ ty => ty)
      let v ← reduceCheck (.src startPos endPos v) .type
      set <| ctx.define name v .type

end Violet.Core

namespace Violet.Ast.Surface
open Violet.Core
open Violet.Parser

partial def repl : ProgramM Unit := do
  let ctx ← get
  let stdin ← IO.getStdin
  IO.print "> "
  let expression ← stdin.getLine
  match term.run expression with
  | .ok v =>
    let (v, vty) ← ctx.infer v (m := ElabM)
    let v ← ctx.env.eval v (m := ElabM)
    IO.println s!"{← ctx.showVal v (m := ElabM)} : {← ctx.showVal vty (m := ElabM)}"
    repl
  | .error ε => IO.eprintln s!"{ε}"

def Program.checkAux (opts : Options) (p : Program) (src : System.FilePath) : IO (Except String (ElabContext × MetaCtx)) := do
  let verbose? := opts.getBool `violet.verbose
  -- TODO: let checkDefinition use this information to change log level
  IO.println s!"checking {src} ..."
  match ← (((checkDefinitions p).run ElabContext.empty).run default).run with
    | Except.ok ((_, elabCtx), metaCtx) => return Except.ok (elabCtx, metaCtx)
    | Except.error ε => return Except.error ε

def Program.check (opts : Options) (p : Program) (src : System.FilePath) : IO Unit := do
  match ←p.checkAux opts src with
  | Except.ok .. => IO.println s!"{src} ok"
  | Except.error ε => IO.eprintln s!"{src}:{ε}"
def Program.load (opts : Options) (p : Program) (src : System.FilePath) : IO Unit := do
  match ←p.checkAux opts src with
  | Except.ok (elabCtx, metaCtx) =>
    IO.println s!"{src} checked successfully"
    let _ ← ((repl.run elabCtx).run metaCtx).run
  | Except.error ε => IO.eprintln s!"{src}:{ε}"

end Violet.Ast.Surface
