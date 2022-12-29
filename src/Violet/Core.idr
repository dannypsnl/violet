module Violet.Core

import System
import Data.List
import Data.String
import Text.Parser.Core

import Violet.Core.Term
import public Violet.Core.Val
import public Violet.Error.Check

public export
checkM : Type -> Type
checkM a = Either CheckError a

addPos : Ctx -> Bounds -> checkM a -> checkM a
addPos ctx bounds (Left ce) = case ce.bounds of
  Nothing => Left $ {bounds := Just bounds} ce
  Just _ => Left ce
addPos ctx _ ma = ma

report : Ctx -> CheckErrorKind -> checkM a
report ctx err = Left (MkCheckError ctx.filename ctx.source Nothing err)

eval : Env -> Tm -> Val
eval env tm = case tm of
  SrcPos tm => eval env tm.val
  Var x => case lookup x env of
    Just a => a
    _ => ?unreachable
  App t u => case (eval env t, eval env u) of
    (VLam _ t, u) => t u
    (VConstructor x vs, u) => VConstructor x (vs ++ [u])
    (t, u) => VApp t u
  U => VU
  Lam x t => VLam x (\u => eval (extend env x u) t)
  Pi x a b => VPi x (eval env a) (\u => eval (extend env x u) b)
  Let x a t u => eval (extend env x (eval env t)) u
  Postulate x a u => eval (extend env x (VVar x)) u
  Elim t cases => ?todo1
  Sum x cases => VSum x $ map (\(x, ts) => (x, map (eval env) ts)) cases
  Intro x u => eval (extend env x (VConstructor x [])) u

export
quote : Env -> Val -> Tm
quote env v = case v of
  VVar x => Var x
  VApp t u => App (quote env t) (quote env u)
  VLam x t =>
    let x = fresh env x
    in Lam x (quote (extend env x (VVar x)) (t (VVar x)))
  VPi x a b =>
    let x = fresh env x
    in Pi x (quote env a) (quote (extend env x (VVar x)) (b (VVar x)))
  VU => U
  VSum x cases => Sum x $ map (\(x, ts) => (x, map (quote env) ts)) cases
  VConstructor x vs => foldl App (Var x) $ map (quote env) vs

nf : Env -> Tm -> Tm
nf env tm = quote env (eval env tm)

export
nf0 : Tm -> Tm
nf0 = nf emptyEnv

mutual
  infer : Env -> Ctx -> Tm -> checkM VTy
  infer env ctx tm = do
    (ty, _) <- infer' env ctx tm
    pure ty

  emptyEnvAndCtx : (Env, Ctx)
  emptyEnvAndCtx = (emptyEnv, emptyCtx)

  -- infer but with new introduced env and ctx (only top level)
  export
  infer' : Env -> Ctx -> Tm -> checkM (VTy, (Env, Ctx))
  infer' env ctx tm = case tm of
    SrcPos t => addPos ctx t.bounds (infer' env ctx t.val)
    Var x => case lookupCtx ctx x of
      Nothing => report ctx (NoVar x)
      Just a => pure (a, emptyEnvAndCtx)
    U => pure (VU, emptyEnvAndCtx)
    App t u => do
      VPi _ a b <- infer env ctx t
        | t' => report ctx (BadApp (quote env t'))
      check env ctx u a
      pure (b (eval env u), emptyEnvAndCtx)
    Lam {} => report ctx (InferLam tm)
    Pi x a b => do
      check env ctx a VU
      let newEnv = extend emptyEnv x (VVar x)
          newCtx = extendCtx emptyCtx x (eval env a)
      check (newEnv <+> env) (newCtx <+> ctx) b VU
      pure (VU, (newEnv, newCtx))
    Postulate x a u => do
      check env ctx a VU
      let a' = eval env a
      let newEnv = extend emptyEnv x (VVar x)
          newCtx = extendCtx emptyCtx x a'
      (ty, restEnvAndCtx) <- infer' (newEnv <+> env) (newCtx <+> ctx) u
      pure (ty, (newEnv, newCtx) <+> restEnvAndCtx)
    Let x a t u => do
      check env ctx a VU
      let a' = eval env a
      check env ctx t a'
      let newEnv = extend emptyEnv x (eval env t)
          newCtx = extendCtx emptyCtx x a'
      (ty, restEnvAndCtx) <- infer' (newEnv <+> env) (newCtx <+> ctx) u
      pure (ty, (newEnv, newCtx) <+> restEnvAndCtx)
    Elim t cases => ?todo2
    Intro x u => do
      let newEnv = extend env x (VConstructor x [])
      (ty, restEnvAndCtx) <- infer' (newEnv <+> env) ctx u
      pure (ty, (newEnv, ctx) <+> restEnvAndCtx)
    Sum {} => pure (VU, emptyEnvAndCtx)

  check : Env -> Ctx -> Tm -> VTy -> checkM ()
  check env ctx t a = case (t, a) of
    (SrcPos t, a) => addPos ctx t.bounds (check env ctx t.val a)
    (Lam x t, VPi x' a b) =>
      let x' = fresh env x'
      in check (extend env x (VVar x)) (extendCtx ctx x a) t (b (VVar x'))
    (Let x a t u, _) => do
      check env ctx a VU
      let a' = eval env a
      check env ctx t a'
      check (extend env x (eval env t)) (extendCtx ctx x a') u a'
    (t, VSum x cases) => case eval env t of
      VConstructor x vs => case lookup x cases of
        Just (vty :: toCheck) => check env ctx t vty
        Just _ => report ctx (NoConstructor x)
        Nothing => report ctx (NoConstructor x)
      _ => report ctx (NotExpectedType x)
    _ => do
      tty <- infer env ctx t
      if (conv env tty a)
        then pure ()
        else report ctx $ TypeMismatch (quote env a) (quote env tty)

  conv : Env -> Val -> Val -> Bool
  conv env t u = case (t, u) of
    (VU, VU) => True
    (VPi x a b, VPi _ a' b') =>
      let x = fresh env x
      in conv env a a' && conv (extend env x (VVar x)) (b (VVar x)) (b' (VVar x))
    (VLam x t, VLam _ t') =>
      let x = fresh env x
      in conv (extend env x (VVar x)) (t (VVar x)) (t' (VVar x))
    -- checking eta conversion for Lam
    (VLam x t, u) =>
      let x = fresh env x
      in conv (extend env x (VVar x)) (t (VVar x)) (VApp u (VVar x))
    (u, VLam x t) =>
      let x = fresh env x
      in conv (extend env x (VVar x)) (VApp u (VVar x)) (t (VVar x))
    (VVar x, VVar x') => x == x'
    (VApp t u, VApp t' u') => conv env t t' && conv env u u'
    _ => False
