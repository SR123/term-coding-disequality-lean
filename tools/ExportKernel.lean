import Lean

open Lean

/- Documentation exporter. Reads checked declarations; it is not imported by any proof.
   Expressions are a lossless DAG (apart from non-semantic metadata payloads), including
   implicit arguments, universe levels, recursor reduction rules and all dependencies. -/
structure Graph where
  ids : Std.HashMap Expr Nat := {}
  nodes : Array Json := #[]
  deps : Std.HashSet Name := {}

partial def levelJson : Level → Json
  | .zero => toJson #[toJson "zero"]
  | .succ u => toJson #[toJson "succ",levelJson u]
  | .max u v => toJson #[toJson "max",levelJson u,levelJson v]
  | .imax u v => toJson #[toJson "imax",levelJson u,levelJson v]
  | .param n => toJson #[toJson "param",toJson n.toString]
  | .mvar n => toJson #[toJson "mvar",toJson n.name.toString]

def binderJson (b : BinderInfo) : Json := toJson <| match b with
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instance"

partial def exprJson (e : Expr) : StateM Graph Nat := do
  if let some id := (← get).ids[e]? then return id
  let node ← match e with
    | .bvar i => pure #[toJson "bound",toJson i]
    | .fvar i => pure #[toJson "free",toJson i.name.toString]
    | .mvar i => pure #[toJson "metavariable",toJson i.name.toString]
    | .sort u => pure #[toJson "sort",levelJson u]
    | .const n us =>
      modify fun s => {s with deps := s.deps.insert n}
      pure #[toJson "constant",toJson n.toString,toJson (us.map levelJson)]
    | .app f a => returnNode "apply" #[toJson (← exprJson f),toJson (← exprJson a)]
    | .lam n t b bi => returnNode "lambda" #[toJson n.toString,toJson (← exprJson t),toJson (← exprJson b),binderJson bi]
    | .forallE n t b bi => returnNode "forall" #[toJson n.toString,toJson (← exprJson t),toJson (← exprJson b),binderJson bi]
    | .letE n t v b nondep => returnNode "let" #[toJson n.toString,toJson (← exprJson t),toJson (← exprJson v),toJson (← exprJson b),toJson nondep]
    | .lit (.natVal n) => pure #[toJson "natural",toJson (toString n)]
    | .lit (.strVal s) => pure #[toJson "string",toJson s]
    | .mdata _ b => returnNode "metadata" #[toJson (← exprJson b)]
    | .proj n i b =>
      modify fun s => {s with deps := s.deps.insert n}
      returnNode "projection" #[toJson n.toString,toJson i,toJson (← exprJson b)]
  let id := (← get).nodes.size
  modify fun s => {s with nodes := s.nodes.push (.arr node), ids := s.ids.insert e id}
  return id
where
  returnNode (name : String) (xs : Array Json) : StateM Graph (Array Json) := pure (#[toJson name] ++ xs)

def kind (c : ConstantInfo) : String := match c with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive family"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some i => (env.header.modules[i]?.map (·.module)).getD Name.anonymous
  | none => env.mainModule

def rangeJson (r : DeclarationRange) : Json := Json.mkObj [
  ("line",toJson r.pos.line),("column",toJson r.pos.column),
  ("endLine",toJson r.endPos.line),("endColumn",toJson r.endPos.column)]

def exportDeclaration (env : Environment) (c : ConstantInfo) (project : Bool) : IO (Json × List Name) := do
  let action : StateM Graph (Nat × Option Nat × Json) := do
    let ty ← exprJson c.type
    let value ← if c.isUnsafe then pure none else c.value? true |>.mapM exprJson
    let extra ← match c with
      | .inductInfo v =>
        for n in v.ctors do modify fun s => {s with deps := s.deps.insert n}
        pure <| Json.mkObj [("constructors",toJson (v.ctors.map Name.toString)),("parameters",toJson v.numParams),("indices",toJson v.numIndices)]
      | .ctorInfo v =>
        modify fun s => {s with deps := s.deps.insert v.induct}
        pure <| Json.mkObj [("family",toJson v.induct.toString),("fields",toJson v.numFields),("parameters",toJson v.numParams)]
      | .recInfo v =>
        let rules ← v.rules.mapM fun r => do
          let rhs ← exprJson r.rhs
          modify fun s => {s with deps := s.deps.insert r.ctor}
          pure <| Json.mkObj [("constructor",toJson r.ctor.toString),("fields",toJson r.nfields),("rhs",toJson rhs)]
        pure <| Json.mkObj [("rules",toJson rules),("parameters",toJson v.numParams),("indices",toJson v.numIndices),("motives",toJson v.numMotives),("minorPremises",toJson v.numMinors)]
      | _ => pure Json.null
    return (ty,value,extra)
  let ((ty,value,extra),graph) := action.run {}
  let opts := ({} : Options).setNat `pp.width 100 |>.setBool `pp.fullNames true |>.setNat `pp.maxSteps 1000000 |>.setBool `pp.universes true |>.setNat `maxRecDepth 100000 |>.setNat `maxHeartbeats 0
  let ctx : Core.Context := {fileName := "<kernel export>",fileMap := default,options := opts}
  let state : Core.State := {env}
  let ((typeText,range),_) ← (do
    let txt ← Meta.MetaM.run' (return (← Meta.ppExpr c.type).pretty)
    let range ← findDeclarationRanges? c.name
    return (txt,range)
    : CoreM (String × Option DeclarationRanges)).toIO ctx state
  let doc ← findDocString? env c.name
  return (Json.mkObj [("name",toJson c.name.toString),("module",toJson (moduleOf env c.name).toString),
    ("kind",toJson (kind c)),("project",toJson project),("unsafe",toJson c.isUnsafe),
    ("typeText",toJson typeText),("type",toJson ty),("value",toJson value),
    ("levels",toJson (c.levelParams.map Name.toString)),("nodes",.arr graph.nodes),
    ("dependencies",toJson (graph.deps.toList.map Name.toString)),("extra",extra),
    ("range",range.map (rangeJson ·.range) |>.getD Json.null),("doc",toJson doc)],graph.deps.toList)

unsafe def main (args : List String) : IO UInt32 := do
  let out :: referenceFile :: cachedFile :: mods := args | throw (IO.userError "usage: ExportKernel out-directory reference-names.txt cached-names.txt module...")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let names := mods.map String.toName
  let imports := names.toArray.map fun n => ({module := n} : Import)
  let env ← importModules (loadExts := true) (level := .private) imports {} 0
  let out := System.FilePath.mk out
  IO.FS.createDirAll (out / "declarations")
  let constants := env.constants.toList
  let roots := constants.filterMap fun (n,c) => if names.contains (moduleOf env n) then some c else none
  let referenceStrings := (← IO.FS.readFile referenceFile).splitOn "\n" |>.filter (· != "")
  let wanted := referenceStrings.foldl (fun (s : Std.HashSet String) n => s.insert n) {}
  -- Recover actual Names from the environment, rather than reparsing private
  -- or generated names containing numeric components from their display text.
  let referenceNames := constants.filterMap fun (n,_) => if wanted.contains n.toString then some n else none
  let found := referenceNames.foldl (fun (s : Std.HashSet String) n => s.insert n.toString) {}
  let cached := (← IO.FS.readFile cachedFile).splitOn "\n" |>.foldl (fun (s : Std.HashSet String) n => s.insert n) {}
  let mut queue := roots.map ConstantInfo.name ++ referenceNames
  let mut visited : Std.HashSet Name := {}
  let mut index := #[]
  let mut missing := (referenceStrings.filter fun n => !found.contains n).toArray
  while !queue.isEmpty do
    let n := queue.head!
    queue := queue.tail!
    if visited.contains n then continue
    visited := visited.insert n
    if cached.contains n.toString then continue
    let some c := env.find? n | missing := missing.push n.toString; continue
    let isProject := names.contains (moduleOf env n)
    let (j,deps) ← exportDeclaration env c isProject
    let key := toString n.hash
    IO.FS.writeFile (out / "declarations" / s!"{key}.json") j.compress
    index := index.push <| Json.mkObj [("name",toJson n.toString),("key",toJson key),
      ("module",toJson (moduleOf env n).toString),("kind",toJson (kind c)),("project",toJson isProject)]
    queue := deps ++ queue
    if visited.size % 500 == 0 then
      IO.println s!"Exported {visited.size} declarations"
      (← IO.getStdout).flush
  IO.FS.writeFile (out / "index.json") (Json.compress <| Json.mkObj [("declarations",.arr index),("missing",toJson missing),("rootModules",toJson mods)])
  IO.println s!"COMPLETE: {index.size} declarations; {missing.size} missing dependencies"
  return if missing.isEmpty then 0 else 1
