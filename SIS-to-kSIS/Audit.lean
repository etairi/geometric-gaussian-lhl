import «SIS-to-kSIS».UniformSimulation
import «SIS-to-kSIS».SolutionExtraction
import «SIS-to-kSIS».GeometricHints
import «SIS-to-kSIS».Parameters
import «SIS-to-kSIS».GaussianWidths
import «SIS-to-kSIS».CanonicalExtraction
import «SIS-to-kSIS».ReverseSampling
import «SIS-to-kSIS».GaussianConditioning
import «SIS-to-kSIS».GaussianFactorization
import «SIS-to-kSIS».SpectralHints
import «SIS-to-kSIS».ResidueMass
import «SIS-to-kSIS».HintIndependence
import «SIS-to-kSIS».FiniteResidueGames
import «SIS-to-kSIS».ModularReverseSampling
import «SIS-to-kSIS».ModularDuality
import «SIS-to-kSIS».GaussianRegularity
import «SIS-to-kSIS».CosetAveraging
import «SIS-to-kSIS».ModularRegularity
import «SIS-to-kSIS».FiniteSampling
import Lean.Util.CollectAxioms

/-! Every public declaration in the reduction namespace is checked recursively.
This checks proof dependencies; it does not certify unproved analytical premises. -/

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`SISToKSIS).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"SIS-to-kSIS: checked {checked} declarations; only propext, Classical.choice, and Quot.sound are allowed."
