import Lean

/-!
# Executable axiom audit

`#print axioms` only prints a diagnostic: a build succeeds whatever it reports.  This module adds a
command that turns the audit into a *check*:

    #assert_standard_axioms foo bar baz

elaborates to nothing when every listed declaration depends (transitively) only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`, and raises an **error** — failing
`lake build` — as soon as one of them depends on anything else (e.g. `sorryAx`, a project-specific
`axiom`, or `Lean.ofReduceBool` introduced by `native_decide`).  On success it logs the actual
axiom list of each declaration, so the build log doubles as the audit record.
-/

open Lean Elab Command

namespace ObserverEquivariance.AxiomAudit

/-- The axioms a declaration of this development is allowed to depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_standard_axioms d₁ d₂ …` fails unless every `dᵢ` depends only on
`propext`, `Classical.choice` and `Quot.sound`. -/
syntax (name := assertStandardAxioms) "#assert_standard_axioms" (ppSpace ident)+ : command

/-- The transitive axioms of `declName` that are not in `allowedAxioms`, together with all of its
transitive axioms. -/
def disallowedAxioms (declName : Name) : CommandElabM (Array Name × Array Name) := do
  let axs ← liftCoreM <| Lean.collectAxioms declName
  return (axs.filter fun a => !allowedAxioms.contains a, axs)

@[command_elab assertStandardAxioms]
def elabAssertStandardAxioms : CommandElab
  | `(#assert_standard_axioms $ids*) => do
    for id in ids do
      let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      let (bad, axs) ← disallowedAxioms declName
      if bad.isEmpty then
        logInfo m!"'{declName}' depends only on standard axioms: {axs.toList}"
      else
        throwErrorAt id "'{declName}' depends on non-standard axioms {bad.toList} (all: {axs.toList})"
  | _ => throwUnsupportedSyntax

/-- `#assert_standard_axioms_in_modules Pre` checks EVERY declaration (including auxiliary
ones such as `_proof_n`) of every imported module whose name has `Pre` as a prefix, and fails
if any of them depends on an axiom outside `propext`, `Classical.choice`, `Quot.sound`.
It reports how many declarations and modules were checked. -/
syntax (name := assertModuleAxioms) "#assert_standard_axioms_in_modules " ident : command

@[command_elab assertModuleAxioms]
def elabAssertModuleAxioms : CommandElab
  | `(#assert_standard_axioms_in_modules $pre:ident) => do
    let env ← getEnv
    let pfx := pre.getId
    let mods := env.header.moduleNames
    let names : Array Name := env.constants.map₁.fold (init := #[]) fun acc n _ =>
      match env.getModuleIdxFor? n with
      | some idx => if pfx.isPrefixOf (mods[idx.toNat]!) then acc.push n else acc
      | none => acc
    let checkedMods := mods.filter (pfx.isPrefixOf ·)
    if names.isEmpty then
      throwErrorAt pre "no imported declarations found in modules with prefix '{pfx}'"
    let mut bad : Array MessageData := #[]
    for n in names do
      let (b, _) ← disallowedAxioms n
      unless b.isEmpty do
        bad := bad.push m!"'{n}' depends on {b.toList}"
    if bad.isEmpty then
      logInfo m!"all {names.size} declarations in {checkedMods.size} modules with prefix \
        '{pfx}' depend only on standard axioms ({checkedMods.toList})"
    else
      throwErrorAt pre "{bad.size} declarations depend on non-standard axioms:\n\
        {MessageData.joinSep bad.toList "\n"}"
  | _ => throwUnsupportedSyntax

end ObserverEquivariance.AxiomAudit
