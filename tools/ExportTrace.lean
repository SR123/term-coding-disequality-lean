import Lean

open Lean Lean.Elab

/- Export information produced by Lean itself while elaborating the unchanged source.
   This is documentation tooling, not a proof or a new trusted axiom. -/

def positionJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [("byte", toJson p.byteIdx), ("line", toJson pos.line), ("column", toJson pos.column)]

def syntaxRange (fm : FileMap) (stx : Syntax) : Json :=
  Json.mkObj [("start", positionJson fm (stx.getPos?.getD 0)),
    ("end", positionJson fm (stx.getTailPos?.getD 0))]

/- The cache is documentation-only. Keys use identity of immutable snapshots;
   entries retain those snapshots, so addresses cannot be recycled. For a goal whose type, local types, let values and local instances contain no
   expression or universe metavariables, ppGoal sees only its unchanged declaration;
   unrelated assignments elsewhere in the metavariable context are immaterial.
   Otherwise the key retains the complete metavariable snapshot. The complete
   command context includes all settings used by ContextInfo.runMetaM. -/
structure GoalKey where
  command : USize
  mctx : USize
  closed : Bool
  goal : Name
  deriving BEq, Hashable

def closedGoal (d : MetavarDecl) : Bool :=
  !d.type.hasMVar && d.localInstances.all (fun i => !i.fvar.hasMVar) &&
    d.lctx.foldl (init := true) (fun ok entry =>
      ok && !entry.type.hasMVar && !(entry.value?.any Expr.hasMVar))

abbrev GoalCache := Std.HashMap GoalKey (ContextInfo × MetavarContext × Json)

unsafe def goalsJson (cache : IO.Ref GoalCache) (ctx : ContextInfo) (mc : MetavarContext) (goals : List MVarId) : IO Json := do
  let strings ← goals.toArray.mapM fun g => do
    let (snapshot, closed) := match mc.findDecl? g with
      | some d => if closedGoal d then (ptrAddrUnsafe d, true) else (ptrAddrUnsafe mc, false)
      | none => (ptrAddrUnsafe mc, false)
    let key := GoalKey.mk (ptrAddrUnsafe ctx.toCommandContextInfo) snapshot closed g.name
    if let some (_,_,j) := (← cache.get)[key]? then return j
    let j ← {ctx with mctx := mc, options := ctx.options.setBool `pp.fullNames true}.runMetaM {} do
      let fmt ← Meta.ppGoal g
      return Json.mkObj [("id", toJson g.name.toString), ("text", toJson fmt.pretty)]
    cache.modify (·.insert key (ctx,mc,j))
    return j
  return .arr strings

unsafe def collectTrace (cache : IO.Ref GoalCache) (ctx? : Option ContextInfo) (tree : InfoTree)
    (rows : IO.Ref (Array Json)) (parent : Nat := 0) : IO Unit := do
  match tree with
  | .context partialCtx child => collectTrace cache (partialCtx.mergeIntoOuter? ctx?) child rows parent
  | .hole id => rows.modify (·.push (Json.mkObj [("kind", toJson "unresolvedInfo"), ("id", toJson id.name.toString)]))
  | .node info children =>
    let ctx? := info.updateContext? ctx?
    let mut nextParent := parent
    if let some ctx := ctx? then
      match info with
      | .ofTacticInfo ti =>
        if ti.stx.getPos?.isSome && ti.stx.getTailPos?.isSome then
          let id := (← rows.get).size + 1
          let before ← goalsJson cache ctx ti.mctxBefore ti.goalsBefore
          let after ← goalsJson cache ctx ti.mctxAfter ti.goalsAfter
          rows.modify (·.push (Json.mkObj [("kind", toJson "tactic"), ("id", toJson id),
            ("parent", toJson parent), ("declaration", toJson (ctx.parentDecl?.map Name.toString)),
            ("range", syntaxRange ctx.fileMap ti.stx), ("syntax", toJson ti.stx.getKind.toString),
            ("elaborator", toJson ti.elaborator.toString), ("before", before), ("after", after)]))
          nextParent := id
      | .ofTermInfo ti =>
        if ti.stx.getPos?.isSome && ti.stx.getTailPos?.isSome then
          let e ← ti.runMetaM ctx (instantiateMVars ti.expr)
          if let .const name _ := e.getAppFn then
            rows.modify (·.push (Json.mkObj [("kind", toJson "reference"), ("name", toJson name.toString),
              ("declaration", toJson (ctx.parentDecl?.map Name.toString)),
              ("range", syntaxRange ctx.fileMap ti.stx)]))
      | _ => pure ()
    for child in children do collectTrace cache ctx? child rows nextParent

unsafe def main (args : List String) : IO UInt32 := do
  let [file, output, olean] := args | throw (IO.userError "usage: ExportTrace file.lean trace.json module.olean")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let moduleName := (System.FilePath.mk file).fileStem.getD "Unknown" |>.toName
  let opts := ({} : Options).setBool `Elab.async true |>.setNat `maxRecDepth 100000 |>.setNat `maxHeartbeats 0
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx (mainModule := moduleName)
  let st ← IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  for message in st.commandState.messages.toList do
    IO.println (← message.toString)
  if st.commandState.messages.hasErrors then return 1
  IO.println s!"ELABORATED {moduleName}; exporting proof states"
  (← IO.getStdout).flush
  let rows ← IO.mkRef #[]
  let cache ← IO.mkRef ({} : GoalCache)
  for tree in st.commandState.infoState.substituteLazy.get.trees do collectTrace cache none tree rows
  IO.FS.writeFile output (Json.compress (Json.mkObj [("module", toJson moduleName.toString),
    ("rows", .arr (← rows.get))]))
  -- Module-export metadata uses a fresh default heartbeat context. Reset the
  -- thread counter after proof checking and tracing, as a separate export phase.
  IO.setNumHeartbeats 0
  writeModule st.commandState.env olean
  IO.println s!"EXPORTED {moduleName}: {(← rows.get).size} info records"
  return 0
