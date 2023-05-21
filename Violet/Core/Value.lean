import Violet.Ast.Core

namespace Violet.Core
open Violet.Ast.Core
open Violet.Ast

mutual

inductive Env
  | mk (mapping : List (String × Val))
deriving Repr, Inhabited, BEq

inductive Spine
  | mk : Array Val → Spine
deriving Repr, Inhabited, BEq

inductive Closure
  | mk (name : String) : Env → Tm → Closure
deriving Repr, Inhabited, BEq

/-- Val

`flex` and `rigid` are both stands for neutral terms,

1. but `flex` has a meta head
2. and `rigid` has a bound variable head

Let's say we have usual `Nat` definition, then `suc n` is `rigid`, but `a n` is flex where `{a : Nat → Nat}`
-/
inductive Val
  | flex (head : MetaVar) (body : Spine)
  | rigid (head : String) (body : Spine)
  | lam : String → Closure → Val
  | pi : String → Surface.Mode → Val → Closure → Val
  | type : Val
deriving Repr, Inhabited, BEq

end

@[reducible]
abbrev VTy := Val

inductive MetaEntry
  | solved (v : Val)
  | unsolved
def MetaCtx := Array MetaEntry

def lookupMeta [Monad m] [MonadState MetaCtx m] [MonadExcept String m]
  (v : MetaVar) : m MetaEntry := do
  let ctx ← get
  match ctx.get? v with
  | .some e => pure e
  | _ => throw "violet internal bug in meta context"

def Env.extend (e : Env) (name : String) (v : Val) : Env :=
  match e with
  | .mk vs => .mk <| (name, v) :: vs

instance : Coe (Array Val) Spine := ⟨.mk⟩

def Spine.extend (sp : Spine) (v : Val) : Spine :=
  match sp with
  | .mk vs => vs.push v

end Violet.Core
