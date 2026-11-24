module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal TensorProduct

theorem volTProdU_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (g r : ℕ)
    [SFinite (sdE (E := E) ψ v (UIdx r))]
    (hM : MeasurableSet (VolTUSet (E := E) v g r)) (hMO : MeasurableSet (VolTO (E := E) v (UIdx r)))
    (hA : VolTAff (E := E) ψ v g (UIdx r)) (hO : VolTOne (E := E) ψ v (UIdx r)) :
    VolTProdU (E := E) ψ v g r := by
  unfold VolTProdU
  rw [Measure.prod_apply hM]
  have hsec : ∀ x : UIdx r → Fv F v ⊗[F] E,
      sdE (E := E) ψ v (UIdx r) (Prod.mk x ⁻¹' VolTUSet (E := E) v g r) =
        (VolTO (E := E) v (UIdx r)).indicator (fun _ => ((g : ℝ≥0∞) ^ (2 * Fintype.card (UIdx r)))⁻¹) x := by
    intro x
    by_cases hx : x ∈ VolTO (E := E) v (UIdx r)
    · rw [Set.indicator_of_mem hx]
      have hpre : Prod.mk x ⁻¹' VolTUSet (E := E) v g r =
          {w | (fun i => (w i - x i) * sc (E := E) v (g : Fv F v)⁻¹) ∈ VolTO (E := E) v (UIdx r)} := by
        ext y
        simp only [Set.mem_preimage, VolTUSet, VolTO, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [hpre, hA, hO, mul_one]
    · rw [Set.indicator_of_notMem hx]
      have hpre : Prod.mk x ⁻¹' VolTUSet (E := E) v g r = ∅ := by
        ext y
        simp only [Set.mem_preimage, VolTUSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hx h.1
      rw [hpre, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator_const hMO, mul_comm]

end Formalism.L2.SG.Pf.NcVal
