import Lean.Data.HashMap
import Violet.Ast.Core

namespace Violet.Core
open Violet.Ast.Core
open Violet.Ast

mutual

inductive Closure
  | mk (env : List Val) (arg : Tm)
  deriving Repr, Inhabited, BEq

/-- Val

`flex` and `rigid` are both stands for neutral terms,

1. but `flex` has a meta head
2. and `rigid` has a bound variable head

Let's say we have usual `Nat` definition, then `suc n` is `rigid`, but `a n` is flex where `{a : Nat → Nat}`
-/
inductive Val
  | flex (head : MetaVar) (spine : Array Val)
  | rigid (head : Lvl) (spine : Array Val)
  | pair (fst snd : Val)
  | sigma (name : String) (ty : Val) (clos : Closure)
  | lam (name : String) (mode : Surface.Mode) (clos : Closure)
  | pi (name : String) (mode : Surface.Mode) (ty : Val) (clos : Closure)
  | type
  deriving Repr, Inhabited, BEq

end

instance : Coe Nat Val where
  coe x := Val.rigid (.lvl x) #[]

@[reducible]
abbrev VTy := Val

inductive MetaEntry
  | solved (v : Val)
  | unsolved

structure MetaCtx where
  mapping : Lean.HashMap Nat MetaEntry
  currentMeta : MetaVar
  deriving Inhabited

def lookupMeta [Monad m] [MonadState MetaCtx m] [MonadExcept String m]
  (v : MetaVar) : m MetaEntry := do
  let ctx ← get
  match ctx.mapping.find? v with
  | .some e => pure e
  | _ => throw "violet internal bug in meta context"

@[reducible]
abbrev Env := List Val
def Env.extend (v : Val) (vs : Env) : Env := v :: vs

@[reducible]
abbrev Spine := Array Val
def Spine.extend (v : Val) (vs : Spine) : Spine := vs.push v

end Violet.Core
