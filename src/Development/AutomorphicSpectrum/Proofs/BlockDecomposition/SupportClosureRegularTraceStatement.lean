import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportClosureRegularTrace
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRegularDenseStatement
import BuildAid.ForwardExisting

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_closure_regular_trace : ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 → ∀ w : Pl F, ∀ a ∈ SuppAt d β {w},
  a ∈ closure {a' | a' ∈ SuppAt d β {w} ∧ (qmap (proj w) a').re ^ 2 ≠ 1} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.PlaneSA.RegClosure.reg_closure
