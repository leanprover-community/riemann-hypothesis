module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem prod_pow_blockWeight {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {M : Type*}
    [CommMonoid M] (w : K → M) (e : (Σ k, ι k) →₀ ℕ) :
    ∏ k, w k ^ (Finsupp.weight (blockWeight ι) e k) = e.prod fun v n => w v.1 ^ n := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_eq_single v.1]
  · simp [blockWeight]
  · intro k _ hk
    simp [blockWeight, Pi.single_eq_of_ne hk]
  · simp

theorem MChartDehomog.proof : MChartDehomog.Statement := by
  intro F _ K _ _ ι P _ u hu f b hf
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  let w : K → L := fun k => φ (X ⟨k, u k⟩)
  have hw : ∀ k, w k ≠ 0 := fun k => by
    simp only [w, φ, RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  have hD : φ (chartMonomial u b) = ∏ k, w k ^ b k := by
    simp [chartMonomial, w, map_prod, map_pow]
  have hC : ∀ c : F, φ (C c) = algebraMap F L c := fun c => by
    simp only [φ, RingHom.comp_apply]
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk F, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hmono : ∀ e ∈ f.support, chartMap P u (monomial e (AddMonoidAlgebra.coeff f e)) * ∏ k, w k ^ b k =
      φ (monomial e (AddMonoidAlgebra.coeff f e)) := by
    intro e he
    have hwe : Finsupp.weight (blockWeight ι) e = b := hf (mem_support_iff.mp he)
    rw [← hwe, prod_pow_blockWeight, chartMap, aeval_monomial, mul_assoc, ← Finsupp.prod_mul,
      monomial_eq, map_mul, hC, Finsupp.prod, Finsupp.prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    change (φ (X v) / w v.1) ^ e v * w v.1 ^ e v = φ (X v ^ e v)
    rw [← mul_pow, div_mul_cancel₀ _ (hw v.1), map_pow]
  change chartMap P u f = φ f / φ (chartMonomial u b)
  rw [hD, eq_div_iff (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k))]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl hmono

end

end GroundTheory.Heights₂.Heights.FieldNumbers
