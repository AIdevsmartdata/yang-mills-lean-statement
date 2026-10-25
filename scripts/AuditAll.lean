/-
Automatic axiom audit of every declaration in the `ClayYM` namespace.

For each non-internal constant whose name starts with `ClayYM`, the axioms it depends on are
collected with `Lean.collectAxioms`. The script prints one summary line and lists every constant
that depends on an axiom outside {propext, Classical.choice, Quot.sound}, every `axiom`
declaration in the namespace, and the kind of the three statements (they must be definitions).
v1.1: it also lists every theorem whose statement mentions the named hypothesis (OS reconstruction).
-/
import ClayYM
import ClayYM.Audit

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.fold (init := #[]) fun acc nm _ =>
    if (`ClayYM).isPrefixOf nm && !nm.isInternal then acc.push nm else acc
  let mut bad : Array (Name × Array Name) := #[]
  let mut axDecls : Array Name := #[]
  let mut nThm : Nat := 0
  for nm in names do
    match env.find? nm with
    | some (.axiomInfo _) => axDecls := axDecls.push nm
    | some (.thmInfo _) => nThm := nThm + 1
    | _ => pure ()
    let axs ← collectAxioms nm
    let extra := axs.filter (fun a => !std.contains a)
    if !extra.isEmpty then bad := bad.push (nm, extra)
  logInfo m!"AUDIT ClayYM: {names.size} constants, {nThm} theorems, {axDecls.size} axiom declarations, {bad.size} constants with non-standard axioms"
  for (nm, extra) in bad do
    logInfo m!"NON-STANDARD: {nm} depends on {extra}"
  for nm in axDecls do
    logInfo m!"AXIOM DECLARATION: {nm}"
  for nm in [``ClayYM.ClayYM_A, ``ClayYM.ClayYM_B, ``ClayYM.ClayYM_AB] do
    match env.find? nm with
    | some (.defnInfo _) => logInfo m!"STATEMENT {nm}: definition (Prop), OK"
    | some _ => logInfo m!"STATEMENT {nm}: NOT a definition"
    | none => logInfo m!"STATEMENT {nm}: MISSING"

-- v1.1: NAMED HYPOTHESES. The Osterwalder–Schrader reconstruction is never an axiom: it is the structure
-- `ClayYM.Transfer.Recon` (Clay level: `ClayYM.OSReconstruction`), passed as an explicit argument.
-- List every theorem of the namespace whose STATEMENT mentions it.
#eval show CommandElabM Unit from do
  let env ← getEnv
  let named : List Name := [``ClayYM.OSReconstruction, ``ClayYM.Transfer.Recon]
  let names := env.constants.fold (init := #[]) fun acc nm _ =>
    if (`ClayYM).isPrefixOf nm && !nm.isInternal then acc.push nm else acc
  let mut users : Array Name := #[]
  for nm in names do
    match env.find? nm with
    | some (.thmInfo info) =>
      if info.type.getUsedConstants.any (fun c => named.contains c) then users := users.push nm
    | _ => pure ()
  let sorted := users.qsort (fun a b => a.toString < b.toString)
  logInfo m!"NAMED HYPOTHESIS (OSReconstruction / Transfer.Recon) in the statement of {users.size} theorems"
  for nm in sorted do
    logInfo m!"NAMED HYPOTHESIS USED BY: {nm}"
