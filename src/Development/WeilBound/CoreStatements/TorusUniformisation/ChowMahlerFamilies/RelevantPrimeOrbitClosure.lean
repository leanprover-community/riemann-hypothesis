module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousOrbit

open GroundTheory.Heights₂.Heights.NumbersDVR

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

noncomputable def orb (z : (Σ k, ι k) → ℂ) : MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K ℂ :=
  eval₂Hom (Int.castRingHom _) (fun v => C (z v) * X v.1)

lemma prod_weight (d : (Σ k, ι k) →₀ ℕ) :
    (d.prod fun v n => (X v.1 : MvPolynomial K ℂ) ^ n) =
      ∏ k, (X k : MvPolynomial K ℂ) ^ (Finsupp.weight (blockWeight ι) d k) := by
  refine Finsupp.induction d ?_ ?_
  · simp
  · intro v b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    have h1 : ((Finsupp.single v b).prod fun x n => (X x.1 : MvPolynomial K ℂ) ^ n) = X v.1 ^ b :=
      Finsupp.prod_single_index (pow_zero _)
    rw [h1, ih, map_add (f := _)]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    simp [blockWeight, Pi.single_apply, Finsupp.weight_apply]

lemma orb_homog (z : (Σ k, ι k) → ℂ) (a : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℤ)
    (hs : s.IsWeightedHomogeneous (blockWeight ι) a) :
    orb z s = C (eval z (MvPolynomial.map (Int.castRingHom ℂ) s)) *
      ∏ k, (X k : MvPolynomial K ℂ) ^ a k := by
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum]

  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hw : Finsupp.weight (blockWeight ι) d = a := hs (mem_support_iff.mp hd)
  simp only [orb, coe_eval₂Hom, eval₂_monomial, map_monomial, eval_monomial, mul_pow,
    Finsupp.prod_mul]
  rw [prod_weight, hw]
  simp [map_finsuppProd, mul_assoc]

lemma orb_eq_zero (z : (Σ k, ι k) → ℂ) (s : MvPolynomial (Σ k, ι k) ℤ)
    (h : ∀ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (weightedHomogeneousComponent (blockWeight ι) a s)) = 0) : orb z s = 0 := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) s,
    map_finsum (orb z) (weightedHomogeneousComponent_finsupp s)]
  have h0 : ∀ a, orb z (weightedHomogeneousComponent (blockWeight ι) a s) = 0 := fun a => by
    rw [orb_homog z a _ (weightedHomogeneousComponent_isWeightedHomogeneous a s), h a, map_zero,
      zero_mul]
  simp [h0]

end PositivityTheory.Xgn.MultihomogeneousOrbit

theorem PositivityTheory.Xgn.relevant_prime_orbit_closure : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → z ∈ ReciprocityTheory.ChartRestriction.G.Geo.mcPts P → ∃ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime ∧ P ≤ W ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W ∧ (∀ p : Nat.Primes, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) ∧ ∀ s : MvPolynomial (Σ k, ι k) ℤ, s ∉ W → ∃ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ) (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a s)) ≠ 0 := by
  intro K _ _ ι _ P z hP hz
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨RingHom.ker (PositivityTheory.Xgn.MultihomogeneousOrbit.orb z), RingHom.ker_isPrime _, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [RingHom.mem_ker]
    exact PositivityTheory.Xgn.MultihomogeneousOrbit.orb_eq_zero z q (fun a => hz2 _ (hP q hq a))
  · intro k
    obtain ⟨i, hi⟩ := hz1 k
    refine ⟨i, ?_⟩
    rw [RingHom.mem_ker]
    simp [PositivityTheory.Xgn.MultihomogeneousOrbit.orb, hi, X_ne_zero]
  · intro p
    rw [RingHom.mem_ker]
    simp [PositivityTheory.Xgn.MultihomogeneousOrbit.orb, p.prop.ne_zero]
  · intro s hs
    by_contra hne
    push_neg at hne
    exact hs (RingHom.mem_ker.mpr (PositivityTheory.Xgn.MultihomogeneousOrbit.orb_eq_zero z s hne))
