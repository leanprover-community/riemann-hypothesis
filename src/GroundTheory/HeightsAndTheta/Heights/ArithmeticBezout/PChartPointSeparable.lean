module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartPointSeparable
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfFreeParAlgIndep
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecPointSeparable
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

open Vertical.SecPointSeparable in
theorem ChartPointSeparable.proof (h : ChartFreeParAlgIndep.Statement) : ChartPointSeparable.Statement := by
  intro F _ _ n e K L _ _ _ _ _ _ u t η hu hK hη hrel hT htr
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, η j₀ ≠ 0 := by
    by_contra! h0
    simp [h0] at hT
  set z : Fin n → L := fun m => η m * (η j₀)⁻¹ with hz
  obtain ⟨hind, halg⟩ := h F n e K L u t η hu hK hη hrel hT j₀ hj₀ (htr j₀ hj₀)
  obtain ⟨r, hre, b, hb⟩ := Vertical.DerivSpanTrdeg.full F L (Fin n) z e (htr j₀ hj₀)
  have hfin : Module.Finite K L := by
    have h1 : FiniteDimensional K (IntermediateField.adjoin K (Set.range η)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [hη] at h1
    exact Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv
  have hadj : Algebra.adjoin K (Set.range η) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hη, IntermediateField.top_toSubalgebra]
  apply isSeparable_of_derivation_eq_zero
  intro D
  obtain ⟨c, hc⟩ := hb (D.restrictScalars F)
  have hc' : ∀ j, D (z j) = ∑ m, c m * (b m j : L) := hc
  have hlin : ∀ (a : K) (y : L), D (algebraMap K L a * y) = algebraMap K L a * D y := by
    intro a y
    rw [D.leibniz, D.map_algebraMap, smul_zero, add_zero, smul_eq_mul]
  have hDz₀ : D (z j₀) = 0 := by
    simp only [z, mul_inv_cancel₀ hj₀, Derivation.map_one_eq_zero]
  have hUDz : ∀ i : Fin e, ∑ j, algebraMap K L (u (i, j)) * D (z j) = 0 := by
    intro i
    have h0 : ∑ j, algebraMap K L (u (i, j)) * z j = 0 := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hrel i, zero_mul]
    have := congrArg D h0

    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => (hlin _ _).symm
  have hDz : ∀ j, D (z j) = 0 := by
    have key := Vertical.GenericFormsKer.full (IntermediateField.adjoin F (Set.range z)) L
      {j : Fin n // j ≠ j₀} e r hre (fun p => algebraMap K L (u (p.1, p.2.1))) hind
      (fun m j => b m j.1) c (fun i => ?_)
    · intro j
      by_cases hj : j = j₀
      · rw [hj, hDz₀]
      · rw [hc' j]
        exact key ⟨j, hj⟩
    · have := hUDz i
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, hDz₀, mul_zero, zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc' j.1]
      rfl
  have hη₀ : D (η j₀) = 0 := by
    have hs : ∑ m, algebraMap F L (t m) * z m = (η j₀)⁻¹ := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
    have h1 := congrArg D hs

    rw [map_sum, Finset.sum_eq_zero fun m _ => by
      rw [IsScalarTower.algebraMap_apply F K L, hlin, hDz, mul_zero],
    Derivation.leibniz_inv, eq_comm, smul_eq_mul, neg_mul, neg_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (inv_ne_zero hj₀))
  have hηj : ∀ j, D (η j) = 0 := by
    intro j
    have hηz : η j = z j * η j₀ := by simp only [z, mul_assoc, inv_mul_cancel₀ hj₀, mul_one]
    rw [hηz, D.leibniz, hη₀, hDz, smul_zero, smul_zero, add_zero]
  exact Derivation.ext_of_adjoin_eq_top (Set.range η) hadj (by rintro _ ⟨j, rfl⟩; simpa using hηj j)

end

end GroundTheory.Heights₂.Heights
