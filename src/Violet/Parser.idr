module Violet.Parser

import Data.List
import Text.Parser.Core
import Text.Parser
import Text.Parser.Expression

import Violet.Lexer
import Violet.Syntax
import public Violet.Error.Parsing

-- `Grammar state tok consumes ty`
-- * `state` can be defined, but didn't be used here
-- * `tok` is the token type of the language
-- * `consumes` flag is True if the language is guaranteed to consume some input on success
-- * `ty` is the returned type of parser
public export
Rule : (ty : Type) -> Type
Rule = Grammar () VToken True

tmU : Rule Raw
tmU = match VTUniverse $> RU

tmVar : Rule Raw
tmVar = RVar <$> match VTIdentifier

parens : Rule a -> Rule a
parens p = match VTOpenP *> p <* match VTCloseP

mutual
  atom : Rule Raw
  atom = tmU <|> tmVar <|> (parens tm)

  spine : Rule Raw
  spine = foldl1 RApp <$> some atom

  expr : Rule Raw
  expr = buildExpressionParser [
    -- dollar sign can use to avoid parentheses
    -- the following expressions are same
    -- `a $ b c d` <=> `a (b c d)`
    -- except the arrow symbol, it's the lowest
    -- since it's about to reorganize the code
    [ Infix (RApp <$ match VTDollar) AssocRight ],
    -- To be convience, thus, arrow is the lowsest symbol
    -- For example, user might write `List a -> List b`, here `List a` is an application
    [ Infix (RPi "_" <$ match VTArrow) AssocRight ]
  ] (spine <|> atom)

  tm : Rule Raw
  tm = do
    r <- bounds (tmLet <|> tmElim <|> tmLam <|> tmPi <|> expr)
    pure $ RSrcPos r

  -- λ A x => x
  tmLam : Rule Raw
  tmLam = do
    match VTLambda
    names <- some $ match VTIdentifier
    match VTLambdaArrow
    body <- tm
    pure $ foldr RLam body names

  -- (A : U) -> A -> A
  tmPi : Rule Raw
  tmPi = do
    match VTOpenP
    name <- match VTIdentifier
    match VTColon
    a <- tm
    match VTCloseP
    match VTArrow
    RPi name a <$> tm

  -- let x : a = t; u
  tmLet : Rule Raw
  tmLet = do
    match VTLet
    name <- match VTIdentifier
    match VTColon
    a <- tm
    match VTAssign
    t <- tm
    match VTSemicolon
    u <- tm
    pure $ RLet name a t u

  -- elim n
  -- | C x => x
  -- | z => z
  tmElim : Rule Raw
  tmElim = do
    match VTElim
    pure $ RElim !tm !(many vcase)
    where
      pat : Rule PatRaw
      pat = pure $
            let (h ::: vs) = !(some (match VTIdentifier))
            in if isNil vs then RPVar h else RPCons h vs
      vcase : Rule (PatRaw, Raw)
      vcase = do
        match VTVerticalLine
        p <- pat
        match VTLambdaArrow
        (p,) <$> tm

ttmData : Rule TopLevelRaw
ttmData = do
  match VTData
  name <- match VTIdentifier
  caseList <- many pCase
  match VTSemicolon
  pure $ TData name caseList
  where
    pCase : Rule (Name, RTy)
    pCase = do
      match VTVerticalLine
      name <- match VTIdentifier
      match VTColon
      a <- tm
      pure (name, a)

ttmPostulate : Rule TopLevelRaw
ttmPostulate = do
  match VTPostulate
  name <- match VTIdentifier
  match VTColon
  a <- tm
  match VTSemicolon
  pure $ TPostulate name a

-- let x : a = t
ttmLet : Rule TopLevelRaw
ttmLet = do
  match VTLet
  name <- match VTIdentifier
  match VTColon
  a <- tm
  match VTAssign
  t <- tm
  match VTSemicolon
  pure $ TLet name a t

ttm : Rule TopLevelRaw
ttm = ttmData <|> ttmPostulate <|> ttmLet

export
ruleTm : Rule Raw
ruleTm = tm

ruleModuleImport : Rule ModuleImportStmt
ruleModuleImport = do
  match VTImport
  name <- match VTIdentifier
  pure $ MkModuleImportStat name

export
ruleModule : Rule ModuleRaw
ruleModule = do
  match VTModule
  name <- match VTIdentifier
  imports <- many ruleModuleImport
  bindings <- many ttm
  pure $ MkModuleRaw (MkModuleInfoRaw name imports) bindings

export
parseViolet : Rule a -> String -> Either PError a
parseViolet rule source =
  case lexViolet source of
    Just toks => parseTokens toks source
    Nothing => Left LexFail
  where
    parseTokens : List (WithBounds VToken) -> (source : String) -> Either PError a
    parseTokens toks source =
      let toks' = filter (not . ignored) toks
      in case parse rule toks' of
        Right (l, []) => Right l
        Right (_, leftTokens) => Left $ TokensLeave source leftTokens
        Left es => Left $ CollectPError $ map (\(Error msg bounds) => SinglePError source bounds msg) $ forget es
      where
        ignored : WithBounds VToken -> Bool
        ignored (MkBounded (Tok VTIgnore _) _ _) = True
        ignored _ = False
