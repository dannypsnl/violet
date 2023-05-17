import Lean.Data.Parsec
import Lean.Data.Position
import Violet.Ast.Surface

namespace Lean.Parsec
open Parsec.ParseResult

def getSourcePos : Parsec String.Pos := fun it : String.Iterator =>
  success it it.pos

-- The roll back is done by using old `it`
def tryP (p : Parsec a) : Parsec (Option a) := λ it =>
  match p it with
  | .success rem a => .success rem a
  | .error _ _ => .success it .none

def between (before : Parsec Unit) (p : Parsec a) (after : Parsec Unit) := do
  before; let r ← p; after; return r

def parens (p : Parsec a) : Parsec a := between (skipChar '(') p (skipChar ')')
def braces (p : Parsec a) : Parsec a := between (skipChar '{') p (skipChar '}')

def run' (p : Parsec α) (filepath : System.FilePath) (s : String) : Except String α :=
  match p s.mkIterator with
  | .success _ res => Except.ok res
  | .error it err  =>
    let f := it.s.toFileMap.toPosition it.pos
    Except.error s!"{filepath}:{f}: {err}"

end Lean.Parsec

namespace Violet.Parser
open Lean
open Lean.Parsec
open Violet.Ast.Surface

def keyword (s : String) := do
  (skipString s).orElse (fun _ => fail s!"expected: keyword `{s}`")
  ws
def identifier := do
  let r ← many1Chars <| satisfy valid?
  if keyword? r then
    fail s!"expected: identifier, got keyword `{r}`"
  ws; return r
  where
    valid? : Char → Bool
    | '-' | '_' | '?' | '!' => true
    | c => c.isAlphanum
    keyword? : String → Bool
    | "module" | "def" | "data" | "Type" => true
    | _ => false

mutual
  partial def atom : Parsec Tm := do
    parseLet <|> parseMatch
    <|> kwTyp <|> var
    <|> (parens term <* ws)
    where
      var : Parsec Tm := identifier
      kwTyp := do keyword "Type"; return Tm.type

  partial def spine : Parsec Tm := do
    let a ← atom
    let as ← many atom
    return as.foldl Tm.app a

  partial def parseMatch : Parsec Tm := do
    keyword "match"
    let target ← term
    let cs ← many clause
    return .«match» target cs
    where
      pattern : Parsec Pattern := do
        let ctor ← identifier
        let vars ← many identifier
        return ⟨ ctor, vars ⟩
      clause : Parsec $ Pattern × Tm := do
        keyword "|"
        let pat ← pattern
        keyword "=>"
        return ⟨ pat, ← term ⟩

  -- `let <name> : <ty> = <val>; <body>`
  partial def parseLet : Parsec Tm := do
    keyword "let"
    let name ← identifier
    keyword ":"
    let ty ← term
    keyword "="
    let val ← term
    keyword ";"
    let body ← term
    return .«let» name ty val body

  partial def binary (opList : List $ Parsec (Tm → Tm → Tm)) (tm : Parsec Tm)
    : Parsec Tm := do
    let l ← tm
    let es ← many opRhs
    return es.foldl (fun lhs e => (e.1 lhs e.2)) l
    where
      opRhs : Parsec $ (Tm → Tm → Tm) × Tm := do
        let mut op := .none
        for findOp in opList do
          op ← tryP findOp
          if op.isSome then break
        return (op.get!, ← tm)
  partial def term : Parsec Tm :=
    atom
    |> binary [keyword "->" *> return .pi .explicit "_",
               keyword "→" *> return .pi .explicit "_"]
    |> binary [keyword "$" *> return .app]
end

abbrev typ := term

def telescope : Parsec Telescope := do
  let grps ← many $
    bindGroup .explicit <* ws
    <|> bindGroup .implicit <* ws
  return grps.toList.join |> List.toArray
  where
    bindGroup (mode : Mode) :=
      let wrapper := match mode with
        | .implicit => braces
        | .explicit => parens
      wrapper $ do
        let names ← many1 identifier
        keyword ":"
        let ty ← typ
        return Array.toList <| names.map fun name => (name, mode, ty)
def parseDef : Parsec Definition := do
  keyword "def"
  let name ← identifier
  let tele ← telescope
  keyword ":"
  let ret_ty ← typ
  -- TODO: or pattern matching clauses
  let body ← singleBody
  return .«def» name tele ret_ty body
  where
    singleBody : Parsec Tm := do keyword "=>"; term

def parseData : Parsec Definition := do
  keyword "data"
  let name ← identifier
  let ctors ← many constructor
  return .data name ctors
  where
    constructor : Parsec Constructor := do
      keyword "|"
      let name ← identifier
      let mut tys : Array Typ := #[]
      let mut ty ← tryP typ
      while ty.isSome do
        tys := tys.push ty.get!
        ty ← tryP typ
      return ⟨ name, tys ⟩

def parseFile : Parsec Program := do
  keyword "module"
  let name ← identifier
  let defs ← many $ parseDef <|> parseData
  eof
  return { name := name, definitions := defs }

end Violet.Parser
