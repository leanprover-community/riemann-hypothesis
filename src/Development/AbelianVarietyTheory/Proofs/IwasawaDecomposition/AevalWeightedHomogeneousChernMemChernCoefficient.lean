module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffCharpolyRevMemTracePowerProductRealSpanStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpanStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerProductRealSpanMulMemStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem one_mem_trSpan_zero {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    (1 : Mat m S → S) ∈ TrSpan m 0 S := by
  unfold TrSpan
  exact Submodule.subset_span ⟨[], by simp, by simp, by funext A; simp [trProd]⟩

theorem pow_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w : ℕ)
    (f : Mat m S → S) (hf : f ∈ TrSpan m w S) (e : ℕ) : f ^ e ∈ TrSpan m (e * w) S := by
  induction e with
  | zero => simpa using one_mem_trSpan_zero m S
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S (k * w) w _ _ ih hf

theorem prod_mem_trSpan {ι κ : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (s : Finset κ)
    (w : κ → ℕ) (f : κ → Mat m S → S) (hf : ∀ x ∈ s, f x ∈ TrSpan m (w x) S) :
    ∏ x ∈ s, f x ∈ TrSpan m (∑ x ∈ s, w x) S := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using one_mem_trSpan_zero m S
  · intro a t ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S _ _ _ _ (hf a (Finset.mem_insert_self a t))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

theorem trSpan_le_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    TrSpan m n S ≤ Reach m n S := by
  unfold TrSpan
  rw [Submodule.span_le]
  rintro f ⟨l, hl, hs, rfl⟩
  exact GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan m n S l hl hs

theorem aeval_chern_mem_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (R : MvPolynomial (ι × ℕ) ℝ) (hR : R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n) :
    (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  refine trSpan_le_reach m n S ?_

  have key : ∀ d ∈ R.support, (fun A : Mat m S =>
      aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)))
        ∈ TrSpan m n S := by
    intro d hd
    have hdeg : Finsupp.weight Prod.snd d = n := hR (mem_support_iff.mp hd)
    have hprod := prod_mem_trSpan m S d.support (fun x => d x * x.2)
      (fun x (A : Mat m S) => (Matrix.charpolyRev (-(A x.1))).coeff x.2 ^ d x)
      (fun x _ => pow_mem_trSpan m S x.2 _ (GlobalTheory.T.coeff_charpolyRev_mem_tracePowerProductRealSpan m S x.1 x.2) (d x))
    have hw : ∑ x ∈ d.support, d x * x.2 = n := by
      rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
      simp [smul_eq_mul]
    rw [hw] at hprod
    convert Submodule.smul_mem _ (R.coeff d) hprod using 1
    funext A
    simp [aeval_monomial, Finsupp.prod, Finset.prod_apply, Algebra.smul_def]
  have hsum : (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) =
      ∑ d ∈ R.support, fun A : Mat m S =>
        aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)) := by
    funext A
    conv_lhs => rw [R.as_sum]

    simp only [map_sum, Finset.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ key

end GlobalTheory.GoodMetric.ChernSpan
