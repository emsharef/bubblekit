import Lean
import Upstream
import Novel
import Standalone

/-! Axiom audit. For every declaration in our own modules (Upstream, Novel, Standalone),
    the axioms it depends on must be within Lean's standard set, and none of our modules
    may declare an axiom. Built by `lake build Audit`; Lake caches it when nothing changed. Canonical copy: ops/ci/AxiomCheck.lean -/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def ourPrefixes : List Name := [`Upstream, `Novel, `Standalone]

def isOurs (m : Name) : Bool := ourPrefixes.any fun p => p.isPrefixOf m

elab "#audit_axioms" : command => do
  let env ← getEnv
  let mut bad : Array String := #[]
  let mut n : Nat := 0
  -- Walk only our own modules' declaration lists, not the whole Mathlib environment.
  for h : i in [0:env.header.moduleNames.size] do
    let mname := env.header.moduleNames[i]
    unless isOurs mname do continue
    for c in env.header.moduleData[i]!.constNames do
      if c.isInternal then continue
      let some ci := env.find? c | continue
      n := n + 1
      if let .axiomInfo _ := ci then
        bad := bad.push s!"{mname}: global axiom declared: {c}"
      let axs ← liftCoreM (collectAxioms c)
      for a in axs do
        unless allowedAxioms.contains a do
          bad := bad.push s!"{mname}: {c} uses non-standard axiom {a}"
  if bad.isEmpty then
    logInfo m!"axiom audit ok: {n} declarations checked"
  else
    for b in bad do logError m!"{b}"
    throwError "axiom audit failed"

#audit_axioms
