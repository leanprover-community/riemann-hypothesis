module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousNonvanishing

open GroundTheory.Heights₂.Heights.NumbersDVR

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem exists_component_ne (z : (Σ k, ι k) → ℂ) (q : MvPolynomial (Σ k, ι k) ℤ)
    (hq : eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0) :
    ∃ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (weightedHomogeneousComponent (blockWeight ι) a q)) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hq
  have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight ι) q
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) q]
  have key := map_finsum ((eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))) hfin
  simp only [RingHom.coe_comp, Function.comp_apply] at key
  rw [key]
  simp [h]

theorem exists_form_ne (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (d : K → ℕ) :
    ∃ m : MvPolynomial (Σ k, ι k) ℤ, IsWeightedHomogeneous (blockWeight ι) m d ∧
      eval z (MvPolynomial.map (Int.castRingHom ℂ) m) ≠ 0 := by
  choose i hi using hz
  refine ⟨∏ k, X ⟨k, i k⟩ ^ d k, ?_, ?_⟩
  · have h := IsWeightedHomogeneous.prod Finset.univ
      (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, i k⟩)
      (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, i k⟩).pow (d k))
    convert h using 1
    conv_lhs => rw [← Finset.univ_sum_single d]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ext j
    simp [blockWeight, Pi.single_apply]
  · simp [Finset.prod_ne_zero_iff, hi]

end PositivityTheory.Xgn.MultihomogeneousNonvanishing

theorem PositivityTheory.Xgn.multihomogeneous_nonvanishing_off : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (bf bg : K → ℕ) (z : ((Σ k, ι k) → ℂ)) (q : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → q ∈ P → eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u ∈ P ∧ v ∈ P ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
  intro K _ _ ι _ P bf bg z q hP hz hqP hq
  obtain ⟨a, ha⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_component_ne z q hq
  obtain ⟨m1, hm1, hm1z⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_form_ne z hz bg
  obtain ⟨m2, hm2, hm2z⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_form_ne z hz bf
  have hcP : weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a q ∈ P :=
    hP q hqP a
  have hch := weightedHomogeneousComponent_isWeightedHomogeneous
    (w := GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a q
  refine ⟨a + bg, a + bf, _ * m1, _ * m2, hch.mul hm1, hch.mul hm2, by abel,
    P.mul_mem_right _ hcP, P.mul_mem_right _ hcP, ?_, ?_⟩
  · simpa using mul_ne_zero ha hm1z
  · simpa using mul_ne_zero ha hm2z
