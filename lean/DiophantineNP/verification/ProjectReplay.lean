import Lean4Checker.Replay
import Lean.Util.Path

open Lean

/-- Read the project’s compiled declarations and submit them to the pinned checker's
kernel replay function. Run from the directory containing the project's lakefile. -/
unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let root := `DiophantineNP
  let projectOLean := fun m => modToFilePath ".lake/build/lib/lean" m "olean"
  let (umbrella, r) ← readModuleData (projectOLean root)
  let targets := #[root] ++ umbrella.imports.map (·.module) |>.filter root.isPrefixOf
  let mut sources := #[root]
  for path in ← System.FilePath.walkDir "DiophantineNP" do
    if path.extension == some "lean" then
      sources := sources.push (← moduleNameOfFileName path none)
  unless targets.size == sources.size && sources.all targets.contains do
    throw <| IO.userError "Umbrella imports disagree with the project source files"
  let mut external : Array Import := #[]
  let mut decls : Std.HashMap Name ConstantInfo := {}
  let mut regions := #[r]
  let mut theorems := 0
  for m in targets do
    let (mod, rg) ← readModuleData (projectOLean m)
    regions := regions.push rg
    if mod.isModule then throw <| IO.userError s!"Module {m} uses split serialized declarations"
    for imp in mod.imports do
      if root.isPrefixOf imp.module then
        unless targets.contains imp.module do throw <| IO.userError s!"Missing project import {imp.module}"
      else
        unless external.contains imp do external := external.push imp
    for n in mod.constNames, ci in mod.constants do
      if let some prev := decls[n]? then
        match prev, ci with
        | .thmInfo a, .thmInfo b =>
          if a == b then continue
          else throw <| IO.userError s!"Different versions of duplicated theorem {n}"
        | _, _ => throw <| IO.userError s!"Duplicated non-theorem {n}"
      decls := decls.insert n ci
      if ci matches .thmInfo _ then theorems := theorems + 1
  IO.println s!"Read {targets.size} project modules, holding {decls.size} distinct declarations and {theorems} theorems before accounting for identical dependency declarations."
  withImportModules external {} fun base => do
    let names := base.header.moduleNames
    for m in names do
      if root.isPrefixOf m then throw <| IO.userError s!"Project module in base: {m}"
    let mut toReplay := decls
    let mut keptTheorems := theorems
    for (n, ci) in decls do
      if let some prior := base.find? n then
        match prior, ci with
        | .thmInfo a, .thmInfo b =>
          unless a == b do throw <| IO.userError s!"Different theorem versions across dependency boundary: {n}"
          IO.println s!"Identical imported theorem also serialized by project: {n}"
          toReplay := toReplay.erase n
          keptTheorems := keptTheorems - 1
        | _, _ => throw <| IO.userError s!"Unexpected dependency overlap at {n}"
    for headline in [`DiophantineNP.classEquality, `DiophantineNP.nativeVerifier,
        `DiophantineNP.HAB.corollary63, `DiophantineNP.Curve37.rank_one] do
      unless toReplay[headline]? matches some (.thmInfo _) do
        throw <| IO.userError s!"Missing project theorem {headline}"
    IO.println s!"Selected {toReplay.size} project declarations and {keptTheorems} theorems."
    IO.println s!"External base loaded from {external.size} direct imports; its closure contains {names.size} modules and zero project declarations."
    let checked ← base.replay' toReplay
    let mut checkedCount := 0
    let mut checkedTheorems := 0
    for (n, ci) in toReplay do
      if !ci.isPartial && !ci.isUnsafe then
        unless (checked.toKernelEnv.find? n).isSome do
          throw <| IO.userError s!"Missing replayed declaration {n}"
        checkedCount := checkedCount + 1
        if ci matches .thmInfo _ then checkedTheorems := checkedTheorems + 1
    unless checkedTheorems == keptTheorems do
      throw <| IO.userError "Some project theorems were skipped"
    IO.println s!"Kernel replay passed for {checkedCount} safe, total project declarations, including all {checkedTheorems} theorems. Upstream excludes {toReplay.size - checkedCount} unsafe or partial declarations."
  for reg in regions do reg.free
