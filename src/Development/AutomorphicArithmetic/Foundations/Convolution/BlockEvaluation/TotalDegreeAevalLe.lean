module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Classical

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Reduction UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

private theorem totalDegree_aeval_le {σ : Type*} (q : MvPolynomial σ ℂ) (hq : q.totalDegree ≤ 1) (p : Polynomial ℂ) :
    (Polynomial.aeval q p).totalDegree ≤ p.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine totalDegree_finsetSum_le fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine (totalDegree_smul_le _ _).trans ((totalDegree_pow _ _).trans ?_)
  calc
    i * q.totalDegree ≤ i * 1 := Nat.mul_le_mul_left _ hq
    _ ≤ p.natDegree := by simpa using hi'

private theorem exists_fin_map (n : ℕ) (s : Multiset ℂ) (hs : s.card = n) :
    ∃ f : Fin n → ℂ, (Finset.univ : Finset (Fin n)).val.map f = s := by
  subst hs
  induction s using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩
    rw [Fin.univ_val_map]
    refine congrArg _ ?_
    apply List.ext_get <;> simp

theorem UpperTheory.ConvolutionTheory.Ci.bdLem :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (κ κ' : Finset (Pl K)) (D D' d d' : ℕ) (R R' : PR K n),
      (Bd κ D d R → Bd κ' D' d' R' → Bd (κ ∪ κ') (D + D') (d + d') (R * R')) ∧ (∀ η m, Bd κ 0 m (chebP η m : PR K n)) ∧
      (κ ⊆ κ' → D ≤ D' → d ≤ d' → Bd κ D d R → Bd κ' D' d' R) ∧
      ∀ Λ : (K →+* ℂ) → Multiset ℂ, (∀ τ, (Λ τ).card = n) → ∃ L : Ix K n → ℂ, msOf L = Λ := by
  intro K _ _ n κ κ' D D' d d' R R'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨?_, (totalDegree_mul _ _).trans (Nat.add_le_add h2 h2'), ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp (vars_mul R R' hx) with h | h
      · exact Finset.mem_union_left _ (h1 x h)
      · exact Finset.mem_union_right _ (h1' x h)
    · intro β
      rw [coeff_mul]
      exact totalDegree_finsetSum_le fun _ _ =>
        (totalDegree_mul _ _).trans (Nat.add_le_add (h3 _) (h3' _))
  · intro η m
    have hq : (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ).totalDegree ≤ 1 := by
      refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
      refine (totalDegree_mul _ _).trans ?_
      simp [totalDegree_X]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp [chebP, vars_C] at hx
    · simp [chebP]
    · intro β
      unfold chebP
      rw [coeff_C]
      split_ifs
      · refine (totalDegree_aeval_le _ hq _).trans ?_
        simp [Polynomial.Chebyshev.natDegree_T]
      · simp
  · rintro hκ hD hd ⟨h1, h2, h3⟩
    exact ⟨fun x hx => hκ (h1 x hx), h2.trans hD, fun β => (h3 β).trans hd⟩
  · intro Λ hΛ
    choose f hf using fun τ => exists_fin_map n (Λ τ) (hΛ τ)
    refine ⟨fun y => f y.1 y.2, ?_⟩
    funext τ
    exact hf τ
