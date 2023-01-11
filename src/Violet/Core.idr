module Violet.Core

import System
import Control.App
import Control.App.Console
import Data.List
import Data.String
import Text.Bounded
import Violet.Core.Term
import public Violet.Core.Val
import public Violet.Error.Check

CtorSet : Type
CtorSet = List (Name, List VTy)

public export
record CheckState where
	constructor MkCheckState
	topCtx : Ctx
	topEnv : GlobalEnv
	dataDefs : List (Name, CtorSet)

export
checkState : Ctx -> CheckState
checkState ctx = MkCheckState ctx [] []

export
interface Has [Exception CheckError, State CheckState CheckState] e => Check e where
	getState : App e CheckState
	putState : CheckState -> App e ()

	updateEnv : Name -> Val -> App e ()
	updateCtx : Name -> VTy -> App e ()

	-- add inductive data type
	addIndType : Name -> CtorSet -> App e ()
	-- find constructor set for data type
	findCtorSet : Name -> App e CtorSet

	report : CheckErrorKind -> App e a
	addPos : Bounds -> App e a -> App e a
export
Has [Exception CheckError, State CheckState CheckState] e => Check e where
	getState = get CheckState
	putState = put CheckState

	updateEnv x v = do
		state <- getState
		putState $ { topEnv := (x, v) :: state.topEnv } state
	updateCtx x vty = do
		state <- getState
		putState $ { topCtx := extendCtx state.topCtx x vty } state

	addIndType dataName cs = do
		state <- getState
		putState $ { dataDefs := (dataName, cs) :: state.dataDefs } state
	findCtorSet dataName = do
		state <- getState
		Just cs <- pure $ lookup dataName state.dataDefs
			| Nothing => report $ NotADataType dataName
		pure cs

	report err = do
		state <- get CheckState
		let ctx = state.topCtx
		throw $ MkCheckError ctx.filename ctx.source Nothing err
	addPos bounds app = catch app
		(\ce => case ce.bounds of
			Nothing => let err : CheckError = {bounds := Just bounds} ce in throw err
			Just _ => throw ce)

export
runEval : Check es => (e -> a -> Either EvalError b) -> e -> a -> App es b
runEval f env a = do
	Right b <- pure $ f env a
		| Left e => report $ cast e
	pure b

mutual
	export
	checkModule : Check e => List Definition -> App e CheckState
	checkModule [] = getState
	checkModule (d :: ds) = go d *> checkModule ds
		where
			handleDataCase : Tm -> DataCase -> App e (Name, List VTy)
			handleDataCase returned_ty (C x tys) = do
				state <- getState
				let env = MkEnv state.topEnv []
				tys' <- for tys (runEval eval env)
				t' <- runEval eval env (foldr (\t, s => (Pi "_" t s)) returned_ty tys)
				updateCtx x t'
				updateEnv x (VCtor x)
				pure (x, tys')

			go : Definition -> App e ()
			go (DSrcPos def) = addPos def.bounds (go def.val)
			go (Data dataName cases) = do
				updateCtx dataName VU
				updateEnv dataName (VVar dataName)
				addIndType dataName !(for cases $ handleDataCase (Var dataName))
			go (Def x a t) = do
				state <- getState
				let env = MkEnv state.topEnv []
				check env state.topCtx a VU
				a' <- runEval eval env a

				check (MkEnv state.topEnv [(x, (VVar x))]) (extendCtx state.topCtx x a') t a'
				t' <- runEval eval env t
				updateEnv x t'
				updateCtx x a'

	export
	infer' : Check e => Tm -> App e VTy
	infer' tm = do
		state <- getState
		infer (MkEnv state.topEnv []) state.topCtx tm

	infer : Check e => Env -> Ctx -> Tm -> App e VTy
	infer env ctx tm = go tm
		where
			go : Tm -> App e VTy
			go (SrcPos t) = addPos t.bounds (go t.val)
			go (Var x) = case lookupCtx ctx x of
				Nothing => report (NoVar x)
				Just a => pure a
			go U = pure VU
			go (Apply t u) = case !(infer env ctx t) of
				VPi _ a b => do
					check env ctx u a
					u' <- runEval eval env u
					Right b' <- pure $ b u'
						| Left e => report $ cast e
					pure b'
				t' => report $ BadApp !(runEval quote env t')
			go (Lam {}) = report (InferLam tm)
			go (Pi x a b) = do
				check env ctx a VU
				check (extendEnv env x (VVar x)) (extendCtx ctx x !(runEval eval env a)) b VU
				pure VU
			go (Let x a t u) = do
				check env ctx a VU
				a' <- runEval eval env a
				check env ctx t a'
				t' <- runEval eval env t
				ty <- infer (extendEnv env x t') (extendCtx ctx x a') u
				pure ty
			go (Elim t cases) = do
				ty <- infer env ctx t
				-- TODO: to enable indexed data type, we will need to extend `findCtorSet` in the future
				[VVar x] <- runEval toSpine env ty
					| ts => report $ BadElimType !(for ts (runEval quote env))
				-- find a constructor set from definition context
				cs <- findCtorSet x
				-- if we can do so, then we use this set to check every case of elimination
				Just rhs_ty <- goCase env ctx cs Nothing cases
					| Nothing => report $ ElimInfer (Elim t cases)
				pure $ rhs_ty
				where
					maybeConv : Env -> Maybe VTy -> VTy -> App e (Maybe VTy)
					maybeConv env Nothing t = pure $ Just t
					maybeConv env (Just t) t' = do
						Right covertable <- pure $ conv env t t'
							| Left err => report $ cast err
						if covertable
							then pure $ Just t
							else report $ TypeMismatch !(runEval quote env t) !(runEval quote env t')

					getTelescope : CtorSet -> Name -> App e (List VTy)
					getTelescope cs x = do
						Just tys <- pure $ lookup x cs
							| Nothing => report $ BadConstructor x
						pure tys

					-- start with a rhs type & a list of case
					goCase : Env -> Ctx -> CtorSet -> Maybe VTy -> List (Pat, Tm) -> App e (Maybe VTy)
					goCase env ctx cs rhs_ty ((PVar x, rhs) :: cases) = do
						_ <- getTelescope cs x
						new_rhs_ty <- infer env ctx rhs
						goCase env ctx cs !(maybeConv env rhs_ty new_rhs_ty) cases
					goCase env ctx cs rhs_ty ((PCons head vars, rhs) :: cases) = do
						tys <- getTelescope cs head
						let patternEnv = vars `zip` (map VVar vars)
						let env' = { local := patternEnv ++ env.local } env
						let ctx' = extendCtxWithBinds ctx (vars `zip` tys)
						new_rhs_ty <- infer env' ctx' rhs
						goCase env ctx cs !(maybeConv env rhs_ty new_rhs_ty) cases
					goCase env ctx cs rhs_ty [] = pure rhs_ty

	check : Check e => Env -> Ctx -> Tm -> VTy -> App e ()
	check env ctx t a = go t a
		where
			go : Tm -> VTy -> App e ()
			go (SrcPos t) a = addPos t.bounds (go t.val a)
			go (Lam x t) (VPi x' a b) = do
				let x' = fresh env x'
				case b (VVar x') of
					Right u => check (extendEnv env x (VVar x)) (extendCtx ctx x a) t u
					Left err => report $ cast err
			go (Let x a t u) _ = do
				check env ctx a VU
				a' <- runEval eval env a
				check env ctx t a'
				let env' = (extendEnv env x !(runEval eval env t))
				let ctx' = (extendCtx ctx x a')
				check env' ctx' u a'
			go _ _ = do
				tty <- infer env ctx t
				Right convertable <- pure $ conv env tty a
					| Left err => report $ cast err
				if convertable
					then pure ()
					else report $ TypeMismatch !(runEval quote env a) !(runEval quote env tty)

	conv : Env -> Val -> Val -> Either EvalError Bool
	conv env t u = go t u
		where
			go : Val -> Val -> Either EvalError Bool
			go VU VU = pure True
			go (VPi x a b) (VPi _ a' b') = do
				let x' = fresh env x
				pure $ !(conv env a a') && !(conv (extendEnv env x' (VVar x')) !(b (VVar x')) !(b' (VVar x')))
			go (VLam x t) (VLam _ t') = do
				let x = fresh env x
				conv (extendEnv env x (VVar x)) !(t env.global (VVar x)) !(t' env.global (VVar x))
			-- checking eta conversion for Lam
			go (VLam x t) u = do
				let x = fresh env x
				conv (extendEnv env x (VVar x)) !(t env.global (VVar x)) (VApp u (VVar x))
			go u (VLam x t) = do
				let x = fresh env x
				conv (extendEnv env x (VVar x)) (VApp u (VVar x)) !(t env.global (VVar x))
			go (VVar x) (VVar x') = pure $ x == x'
			go (VApp t u) (VApp t' u') = pure $ !(conv env t t') && !(conv env u u')
			go _ _ = pure False
