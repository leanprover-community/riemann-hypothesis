module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Sub.Prod
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
import Mathlib.Tactic.Linter.Style
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

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]


omit [DecidableEq K] in
theorem chartMonomial_add (u : ∀ k, ι k) (a c : K → ℕ) :
    (chartMonomial u (a + c) : MRing ι F) = chartMonomial u a * chartMonomial u c := by
  simp only [chartMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (c : K → ℕ) :
    IsMultiHomog (chartMonomial u c : MRing ι F) c := by
  show IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, u k⟩ : MRing ι F) ^ c k) c
  have h := IsWeightedHomogeneous.prod (R := F) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ c k) (fun k => c k • blockWeight ι ⟨k, u k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (c k))
  convert h using 1
  funext j
  simp [blockWeight, Finset.sum_apply, Pi.single_apply]

theorem finsuppProd_chartVar (u : ∀ k, ι k) (e : (Σ k, ι k) →₀ ℕ) :
    (e.prod fun v n => (X ⟨v.1, u v.1⟩ : MRing ι F) ^ n) =
      chartMonomial u (Finsupp.weight (blockWeight ι) e) := by
  induction e using Finsupp.induction_linear with
  | zero => simp [chartMonomial]
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add (f := _),
      chartMonomial_add]
  | single v n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.weight_single]
    simp only [chartMonomial]
    rw [Finset.prod_eq_single v.1]
    · simp [blockWeight]
    · intro k _ hk
      simp [blockWeight, hk]
    · simp

theorem chartMap_monomial_mul (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) (e : (Σ k, ι k) →₀ ℕ) (c : F) :
    chartMap P u (monomial e c) *
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
          (Ideal.Quotient.mk P (chartMonomial u (Finsupp.weight (blockWeight ι) e))) =
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (monomial e c)) := by
  have hy : ∀ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ≠ 0 := fun k => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  rw [← finsuppProd_chartVar, chartMap, aeval_monomial, monomial_eq]
  simp only [map_mul, map_finsuppProd, map_pow]
  rw [mul_assoc, ← Finsupp.prod_mul]
  congr 1
  refine Finsupp.prod_congr fun v _ => ?_
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hy v.1))]

theorem MChartHomog.proof : MChartHomog.Statement.{u} := by
  intro F _ K _ _ ι u p
  classical
  obtain ⟨b, hle⟩ : ∃ b : K → ℕ, ∀ e ∈ p.support, Finsupp.weight (blockWeight ι) e ≤ b :=
    ⟨fun k => p.support.sup fun e => Finsupp.weight (blockWeight ι) e k, fun e he k =>
      Finset.le_sup (f := fun e => Finsupp.weight (blockWeight ι) e k) he⟩
  refine ⟨b, ∑ e ∈ p.support,
    monomial e (AddMonoidAlgebra.coeff p e) * chartMonomial u (b - Finsupp.weight (blockWeight ι) e), ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
    have := (isWeightedHomogeneous_monomial (blockWeight ι) e (AddMonoidAlgebra.coeff p e) rfl).mul
      (chartMonomial_isMultiHomog (F := F) u (b - Finsupp.weight (blockWeight ι) e))
    rwa [add_tsub_cancel_of_le (hle e he)] at this
  · intro P _ hu
    have hY : ∀ c, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u c)) ≠ 0 := fun c => by
      simp only [chartMonomial, map_prod, map_pow]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    rw [eq_div_iff (hY b)]
    conv_lhs => rw [p.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have key : (chartMonomial u b : MRing ι F) = chartMonomial u (Finsupp.weight (blockWeight ι) e) *
        chartMonomial u (b - Finsupp.weight (blockWeight ι) e) := by
      rw [← chartMonomial_add, add_tsub_cancel_of_le (hle e he)]
    rw [key, map_mul, map_mul, map_mul, map_mul, ← mul_assoc, chartMap_monomial_mul P u hu]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
