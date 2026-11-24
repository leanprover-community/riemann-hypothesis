module

public import Formalism.PeriodIntegrals.UpqRep
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.DominantRootSums

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
private lemma sum_index_mul_root_eq_sub' {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * _root_.PI.UpqRep.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [_root_.PI.UpqRep.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.DominantRootSums.not_cDom_add_root : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (a b : Fin n), a < b →
    ¬ _root_.PI.UpqRep.CDom ε (Λ + _root_.PI.UpqRep.root a b) Λ := by
  intro n ε Λ a b hab hdom
  unfold _root_.PI.UpqRep.CDom at hdom
  obtain ⟨c, hc, hsum⟩ := hdom
  rw [show Λ - (Λ + _root_.PI.UpqRep.root a b) = -_root_.PI.UpqRep.root a b by abel] at hsum
  have h1 := congrArg (fun v : Fin n → ℝ => ∑ i : Fin n, ((i : ℕ) : ℝ) * v i) hsum
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sum_index_mul_root_eq_sub'] at h1
  have hR : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a', ∑ b', (c a' b' : ℝ) • _root_.PI.UpqRep.root a' b') i
      = ∑ a', ∑ b', (c a' b' : ℝ) * (((a' : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [← sum_index_mul_root_eq_sub', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR] at h1
  have hle : ∑ a', ∑ b', (c a' b' : ℝ) * (((a' : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun a' _ => Finset.sum_nonpos fun b' _ => ?_
    by_cases h0 : c a' b' = 0
    · simp [h0]
    · have hlt : ((a' : ℕ) : ℝ) < ((b' : ℕ) : ℝ) := by exact_mod_cast (hc a' b' h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

end GlobalTheory.DominantRootSums
