import Violet.Core.Eval
import Violet.Core.DBI
import Lean.Data.HashSet

namespace Violet.Core
open Violet.Ast.Core

@[reducible]
abbrev TypCtx := List (String × VTy)

structure ElabContext where
  env : Env
  typCtx : TypCtx
  mctx : MetaCtx
  dataTypeCtx : Lean.HashMap Lvl (Lean.HashSet Lvl)
  lvl : Lvl

def ElabContext.empty : ElabContext := {
    env := default
    typCtx := []
    mctx := default
    dataTypeCtx := default
    lvl := .lvl 0
  }
instance : Inhabited ElabContext where
  default := ElabContext.empty

def ElabContext.bind (ctx : ElabContext) (name : String) (ty : VTy)
  : ElabContext :=
  let (.lvl curLvl) := ctx.lvl
  { ctx with
    lvl := .lvl <| curLvl + 1
    env := ctx.env.extend (vvar name ctx.lvl)
    typCtx := (name, ty) :: ctx.typCtx
  }
def ElabContext.define (ctx : ElabContext) (name : String) (val : Val) (ty : VTy)
  : ElabContext :=
  let (.lvl curLvl) := ctx.lvl
  { ctx with
    lvl := .lvl <| curLvl + 1
    env := ctx.env.extend val
    typCtx := (name, ty) :: ctx.typCtx
  }
def ElabContext.addConstructor (ctx : ElabContext) (dataType ctor : Lvl) : ElabContext :=
  let ctors := ctx.dataTypeCtx.findD dataType Lean.HashSet.empty
  { ctx with
    dataTypeCtx := ctx.dataTypeCtx.insert dataType (ctors.insert ctor)
  }

-- misc: pretty print
partial def ElabContext.showPat (ctx : ElabContext) (pat : Pattern) : String :=
  let (name, _) := ctx.typCtx.get! <| lvl2Ix ctx.lvl pat.ctor
  name ++ " " ++ toString pat.vars

partial def ElabContext.showTm (ctx : ElabContext) : Tm → String
  | .sigma x a b => s!"({x} : {ctx.showTm a}) × {ctx.showTm b}"
  | .pair fst snd => s!"({ctx.showTm fst}, {ctx.showTm snd})"
  | .fst t => s!"{ctx.showTm t}.0"
  | .snd t => s!"{ctx.showTm t}.1"
  | .lam p .implicit body => "λ " ++ "{" ++ p ++ "}" ++ s!" => {ctx.showTm body}"
  | .lam p .explicit body => s!"λ {p} => {ctx.showTm body}"
  | .pi p .implicit ty body =>
    "{" ++ p ++ " : " ++ ctx.showTm ty ++ "} → " ++ ctx.showTm body
  | .pi p .explicit ty body =>
    "(" ++ p ++ " : " ++ ctx.showTm ty ++ ") → " ++ ctx.showTm body
  | .app t u => s!"{ctx.showTm t} {ctx.showTm u}"
  | .var name .. => name
  | .meta m => s!"?{m}"
  | .let p ty val body =>
    s!"let {p} : {ctx.showTm ty} := {ctx.showTm val} in {ctx.showTm body}"
  | .match t cases => Id.run do
    let mut s := s!"match {ctx.showTm t}"
    for (p, body) in cases do
      s := s ++ s!"| {ctx.showPat p} => {ctx.showTm body}"
    return s
  | .type => "Type"

def ElabContext.showVal
  [Monad m] [MonadState MetaCtx m] [MonadExcept String m]
  (ctx : ElabContext) (val : Val) : m String := do
  let tm ← quote ctx.lvl val
  return ctx.showTm tm

end Violet.Core
