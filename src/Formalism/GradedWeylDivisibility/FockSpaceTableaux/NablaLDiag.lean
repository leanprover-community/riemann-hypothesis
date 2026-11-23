module

public import Formalism.GradedWeylDivisibility.StatementD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem nablaLDiag_of (h1 : RowActMul) (h2 : RowActDiagWeight) (h3 : NablaLBasis) : NablaLDiag := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g t hg ht
  have hD : IsUnit (Matrix.diagonal t).det := by
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => ht a)
  have hgD : IsUnit (g * Matrix.diagonal t).det := by
    rw [Matrix.det_mul]
    exact hg.mul hD
  have hDinv : (Matrix.diagonal t)⁻¹ = Matrix.diagonal (fun a => (t a)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with a
    exact inv_mul_cancel₀ (ht a)
  have hfam : (fun i => rowAct K (g * Matrix.diagonal t)⁻¹ (map (algebraMap R K) (b i))) =
      fun i => (∏ a, t a ^ μ i a)⁻¹ • rowAct K g⁻¹ (map (algebraMap R K) (b i)) := by
    funext i
    rw [Matrix.mul_inv_rev, ← h1 K k n g⁻¹ (Matrix.diagonal t)⁻¹, AlgHom.comp_apply, hDinv,
      h2 K k n _ (μ i) _ (ldlat_isWH_map _ (hb.2.2 i)), map_smul]
    congr 1
    rw [← Finset.prod_inv_distrib]
    simp [inv_pow]
  obtain ⟨hl, hs⟩ := h3 R K hinj k n ν b μ hb (g * Matrix.diagonal t) hgD
  rw [hfam] at hl hs
  exact ⟨hl, hs⟩

end Formalism.GradedWeylDivisibility
