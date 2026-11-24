module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TorsionTranslate

theorem ee_mem_Qbar (x : ℝ) (n : ℕ) (hn : 0 < n) (k : ℤ) (h₀ : (n : ℝ) * x = k) : ee x ∈ Qbar := by
  have h : (n : ℂ) * x = k := by exact_mod_cast h₀
  have h1 : ee x ^ n = 1 := by
    unfold ee
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k, ← h]
    congr 1
    ring
  refine (mem_algebraicClosure_iff).2 ?_
  refine IsAlgebraic.of_pow hn ?_
  rw [h1]
  exact isAlgebraic_one

theorem Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (m m' : ℕ) (x y : VC D N N') :
    Hf D T (m • x) (m' • y) = (m * m' : ℕ) * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left, Hf_conj D T (m' • y) x, ← Nat.cast_smul_eq_nsmul ℂ,
    Hf_smul_left, Hf_conj D T y x]
  simp [mul_assoc]

theorem translate_mem : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, ∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → U D (tor0 D cc δ) t F ∈ Tr D (tor0 D cc δ) b := by
  intro D cc δ hC N N' r b hb F hF t m hm ht
  have hint := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N'
    (LaB D (tor0 D cc δ) b) (Or.inl ⟨r, b, hb, rfl⟩)).2.2.1
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨s, ⟨m', hm', hs⟩, rfl⟩ := hG
    obtain ⟨k, hk⟩ := hint _ ht _ hs
    rw [Hf_nsmul] at hk
    have hk' : ((m * m' : ℕ) : ℝ) * (Hf D (tor0 D cc δ) t s).im = k := by
      rw [← hk]; simp
    have hq : ee (-(Hf D (tor0 D cc δ) t s).im / 2) ∈ Qbar := by
      refine ee_mem_Qbar _ (2 * (m * m')) (by positivity) (-k) ?_
      push_cast at hk' ⊢
      linear_combination -hk'
    have : U D (tor0 D cc δ) t (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂))) =
        (⟨_, hq⟩ : Qbar) • U D (tor0 D cc δ) (t + s) (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂)) := by
      funext z
      rw [U_U]
      rfl
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨t + s, ⟨m * m', by positivity, ?_⟩, rfl⟩)
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_nsmul]; exact AddSubgroup.nsmul_mem _ ht _
    · rw [mul_nsmul']; exact AddSubgroup.nsmul_mem _ hs _
  | zero =>
    have : U D (tor0 D cc δ) t (0 : VC D N N' → ℂ) = 0 := by
      funext z; simp [U]
    rw [this]; exact zero_mem _
  | add G G' _ _ h h' =>
    have : U D (tor0 D cc δ) t (G + G') = U D (tor0 D cc δ) t G + U D (tor0 D cc δ) t G' := by
      funext z; simp [U, add_mul]
    rw [this]; exact add_mem h h'
  | smul a G _ h =>
    have : U D (tor0 D cc δ) t (a • G) = a • U D (tor0 D cc δ) t G := by
      funext z
      change U D (tor0 D cc δ) t (fun z => (a : ℂ) * G z) z = (a : ℂ) * U D (tor0 D cc δ) t G z
      simp only [U]; ring
    rw [this]; exact Submodule.smul_mem _ _ h

end GlobalTheory.TorsionTranslate
