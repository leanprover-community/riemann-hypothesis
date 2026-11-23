module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsProjIdealFormValue
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ProjIdealFormValue

theorem weight_blockWeight_apply {K : Type*} [DecidableEq K] {ι : K → Type*} (m : (Σ k, ι k) →₀ ℕ)
    (k : K) : Finsupp.weight (blockWeight ι) m k = Finsupp.mapDomain Sigma.fst m k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain, Finsupp.sum, Finsupp.sum, Finset.sum_apply,
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : v.1 = k
  · simp [blockWeight, h]
  · simp [blockWeight, Ne.symm h]

theorem eval₂_monomial_cone {F Φ : Type*} [CommRing F] [CommRing Φ] (α : F →+* Φ) {K : Type*}
    {ι : K → Type*} (z : (Σ k, ι k) → Φ) (m : (Σ k, ι k) →₀ ℕ) (c : F) :
    eval₂ (C.comp α) (fun p => C (z p) * X p.1) (monomial m c) =
      C (eval₂ α z (monomial m c)) * monomial (Finsupp.mapDomain Sigma.fst m) (1 : Φ) := by
  rw [eval₂_monomial, eval₂_monomial, monomial_eq, C_1, one_mul,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [mul_pow, Finsupp.prod_mul, map_mul, RingHom.coe_comp, Function.comp_apply,
    map_finsuppProd, map_pow, mul_assoc]

theorem proof : ProjIdealFormValue.Statement := by
  intro F _ Ω _ _ K _ ι y N E _ _ w M φ Φ _ _ t d x hx
  have hx' : IsWeightedHomogeneous (blockWeight (bundleIdx ι M)) x d := hx
  rw [projIdeal, RingHom.mem_ker, coe_eval₂Hom]
  by_cases hx0 : x = 0
  · subst hx0
    simp
  obtain ⟨m₀, hm₀⟩ : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hx0
  have hD : ∀ m ∈ x.support, Finsupp.mapDomain Sigma.fst m = Finsupp.mapDomain Sigma.fst m₀ := by
    intro m hm
    ext o
    rw [← weight_blockWeight_apply, ← weight_blockWeight_apply, hx' (mem_support_iff.mp hm),
      hx' (mem_support_iff.mp hm₀)]
  have key : eval₂ (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
      (fun p => C (projCoord y w φ t p) * X p.1) x =
      C (eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) x) *
        monomial (Finsupp.mapDomain Sigma.fst m₀) 1 := by
    conv_lhs => rw [x.as_sum]
    conv_rhs => rw [x.as_sum]

    rw [eval₂_sum, eval₂_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [eval₂_monomial_cone, hD m hm]
  rw [key, mul_eq_zero, C_eq_zero, monomial_eq_zero]
  simp

end ProjIdealFormValue

end

end GroundTheory.Heights₂.Heights.NumbersDVR
