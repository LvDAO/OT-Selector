import OTSelector
import Lean.Util.CollectAxioms

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut unexpected : Nat := 0
  let mut allAxioms : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if (`OTSelector).isPrefixOf moduleName || (`LeanPool).isPrefixOf moduleName then
        checked := checked + 1
        for axiomName in (← collectAxioms name) do
          if !allAxioms.contains axiomName then
            allAxioms := allAxioms.push axiomName
          if !([`propext, `Classical.choice, `Quot.sound].contains axiomName) then
            logError m!"Unexpected axiom {axiomName} in {name}"
            unexpected := unexpected + 1
  logInfo m!"Audited {checked} declarations from OTSelector and vendored LeanPool modules"
  logInfo m!"Transitive axiom union: {allAxioms.qsort Name.lt}"
  if unexpected > 0 then
    throwError m!"{unexpected} unexpected axiom dependencies"

#check OTSelector.main_selector
#print axioms OTSelector.main_selector
