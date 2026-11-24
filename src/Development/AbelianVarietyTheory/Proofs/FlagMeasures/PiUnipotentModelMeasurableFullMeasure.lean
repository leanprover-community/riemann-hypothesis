module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinatesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem nset_closed (k r : ℕ) : IsClosed {y : Mt k r | Matrix.of y ∈ Nset k r} := by
  simp only [Nset, UH, Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · have hc : Continuous fun y : Mt k r => (Matrix.of y)ᴴ * Hpk k r * Matrix.of y := by
      have h0 : Continuous fun y : Mt k r => (Matrix.of y : Matrix _ _ ℂ) := continuous_id
      exact (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  · refine isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const
  · refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const

theorem pi_nset_full : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  intro ι _ k r
  have hS : MeasurableSet {y : Mt k r | Matrix.of y ∈ Nset k r} := (nset_closed k r).measurableSet
  have hH := (GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hset : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} =
      ⋂ w, Function.eval w ⁻¹' {y : Mt k r | Matrix.of y ∈ Nset k r} := by
    ext x; simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact MeasurableSet.iInter fun w => measurable_pi_apply w hS
  · rw [hset, Set.compl_iInter]
    refine measure_iUnion_null fun w => ?_
    rw [← Set.preimage_compl]
    exact Measure.pi_eval_preimage_null _ (by simpa [Set.compl_setOf] using hH.2.2.1)

end GlobalTheory.SnMass.VolN
