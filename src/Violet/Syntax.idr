module Violet.Syntax

import Data.String
import Text.Parser.Core
import public Violet.Core.Term

public export
data PatRaw
  = RPVar Name
  -- weak-head pattern
  | RPCons Name (List Name)

mutual
  ||| The Raw expression of violet
  public export
  data Raw
    = RSrcPos (WithBounds Raw)
    | RVar Name               -- x
    | RLam Name Raw           -- λ x => t
    | RApp Raw Raw            -- t u
    | RU                      -- U
    | RPi Name RTy RTy        -- (x : a) → b
    | RLet Name RTy Raw Raw   -- let x : a = t; u
    -- elim n
    -- | zero => u1
    -- | suc n => u2
    --
    -- elim trichotomy a b
    -- | greater _ => u1
    -- | less p | equals p => f p
    | RElim Raw (List (PatRaw, Raw))

  public export
  RTy : Type
  RTy = Raw

||| The Raw top-level definition of violet
public export
data TopLevelRaw
  = TLet Name RTy Raw       -- let x : a = t
  | TPostulate Name RTy     -- posulate x : a
  -- inductive type
  -- data Nat
  -- | zero : Nat
  -- | suc : Nat -> Nat
  | TData Name (List (Name, RTy))

public export
data ModuleImportStmt = MkModuleImportStat Name -- imported module name

public export
record ModuleInfoRaw where
  constructor MkModuleInfoRaw
  name : string
  imports : List ModuleImportStmt


public export
data ModuleRaw = MkModuleRaw ModuleInfoRaw (List TopLevelRaw)

export
Cast PatRaw Pat where
  cast (RPVar n) = PVar n
  cast (RPCons h vs) = PCons h vs

export
Cast Raw Tm where
  cast (RSrcPos raw) = SrcPos $ MkBounded (cast raw.val) True raw.bounds
  cast (RVar x) = Var x
  cast (RLam x t) = Lam x (cast t)
  cast (RApp t u) = Apply (cast t) (cast u)
  cast RU = U
  cast (RPi x a b) = Pi x (cast a) (cast b)
  cast (RLet x a t u) = Let x (cast a) (cast t) (cast u)
  cast (RElim r cases) = Elim (cast r) $ map (bimap cast cast) cases

toTTm : List TopLevelRaw -> Tm
toTTm [] = U
toTTm (TLet x a t :: xs) = Let x (cast a) (cast t) (toTTm xs)
toTTm (TPostulate x a :: xs) = Postulate x (cast a) (toTTm xs)
toTTm (TData x caseLst :: xs) = foldl
  (\a, (x, t) => \u => a (Postulate x (cast t) u))
  (\u => Postulate x U u)
  caseLst
  $ toTTm xs

export
Cast (List TopLevelRaw) Tm where
  cast = toTTm
