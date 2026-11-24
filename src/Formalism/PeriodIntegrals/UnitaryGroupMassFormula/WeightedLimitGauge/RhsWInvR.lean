module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem inv_fix {b : Mat k r} (hb : IsUnit b.det) {v : Fin (2 * r + k + 1) → ℂ} (h : b *ᵥ v = v) :
    b⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]

theorem uwset_inv {b : Mat k r} (hb : b ∈ UWset k r z') : b⁻¹ ∈ UWset k r z' := by
  obtain ⟨hU, hfix, hz⟩ := hb
  have hu := HU.isUnit_of_uh hU
  exact ⟨HU.uh_inv hU, fun a => ⟨inv_fix hu (hfix a).1, inv_fix hu (hfix a).2⟩, inv_fix hu hz⟩

theorem inner_r (hW : IsHaarOn (UWset k r z') μW') (M : Mat k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ)
    (b : Mat k r) (hb : b ∈ UWset k r z') :
    ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹ * b) i j) ∂μW' =
      ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by
  have hbi : b⁻¹ ∈ UWset k r z' := uwset_inv hb
  have hu : IsUnit (b⁻¹).det := HU.isUnit_of_uh hbi.1
  have hbu : IsUnit b.det := HU.isUnit_of_uh hb.1
  have hmap : μW'.map (lmulM b⁻¹) = μW' := hW.2.2.2 _ hbi
  have key : ∀ h' : Mt k r, M * (Matrix.of h')⁻¹ * b = M * (Matrix.of (lmulE b⁻¹ hu h'))⁻¹ := by
    intro h'
    change M * (Matrix.of h')⁻¹ * b = M * (b⁻¹ * Matrix.of h')⁻¹
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hbu, mul_assoc]
  calc ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹ * b) i j) ∂μW'
      = ∫⁻ h', (fun y : Mt k r => φ (fun i j => (M * (Matrix.of y)⁻¹) i j)) (lmulE b⁻¹ hu h') ∂μW' := by
        refine lintegral_congr fun h' => ?_
        simp only [key h']
    _ = ∫⁻ y, φ (fun i j => (M * (Matrix.of y)⁻¹) i j) ∂(μW'.map (lmulE b⁻¹ hu)) :=
        by rw [lintegral_map_equiv]
    _ = ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by
        rw [show ⇑(lmulE b⁻¹ hu) = lmulM b⁻¹ from rfl, hmap]

theorem rhsW_rmul (hd : WbData k r z z' μW μW' a a' μsec) (b : Mat k r) (hb : b ∈ UWset k r z')
    (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    rhsW k r z z' μW μW' μsec (fun x => φ (rmulM b x)) = rhsW k r z z' μW μW' μsec φ := by
  unfold rhsW
  refine lintegral_congr fun ζ => ?_
  congr 1
  refine lintegral_congr fun h => ?_
  exact inner_r hd.haarW' _ φ hφ b hb

theorem rInvNu : RInvNu := by
  intro k r z z' μW μW' a a' μsec hd b hb
  have hm : Measurable (rmulM b : Mt k r → Mt k r) := (rmulM_cont b).measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  have hi : Measurable (s.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hs
  have e1 := ZetaZeros.repr hd (s.indicator 1) hi
  have e2 := ZetaZeros.repr hd (fun x => s.indicator 1 (rmulM b x)) (hi.comp hm)
  have e3 := rhsW_rmul hd b hb (s.indicator 1) hi
  rw [lintegral_indicator_one hs] at e1
  have e4 : ∫⁻ x, s.indicator 1 (rmulM b x) ∂(nuR k r z z' μW μW' μsec) =
      nuR k r z z' μW μW' μsec (rmulM b ⁻¹' s) := by
    rw [← lintegral_indicator_one (hm hs)]
    refine lintegral_congr fun x => ?_
    simp only [Set.indicator, Pi.one_apply]
    rfl
  rw [← e4, ← e2, e3, e1]

end PI.RhsWLim.W.RI
