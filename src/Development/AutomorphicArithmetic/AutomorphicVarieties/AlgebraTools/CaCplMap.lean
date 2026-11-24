module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Nakayama

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B → ∀ n : ℕ, (p ^ n).map (algebraMap R B) = maximalIdeal B ^ n := by
  intro R _ p B _ _ _ h n
  have hnoeth := h.noeth
  have hle : p.map (algebraMap R B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, h.comap_eq]
  have heq : p.map (algebraMap R B) = maximalIdeal B := by
    refine le_antisymm hle ?_
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
    intro b hb
    obtain ⟨a, s, hs, hsa⟩ := h.dense 2 b
    have hsu : IsUnit (algebraMap R B s) := by
      by_contra hn
      apply hs
      rw [← h.comap_eq, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hm2 : maximalIdeal B ^ 2 ≤ maximalIdeal B := Ideal.pow_le_self two_ne_zero
    have ha : a ∈ p := by
      rw [← h.comap_eq, Ideal.mem_comap]
      have : algebraMap R B a = algebraMap R B s * b - (algebraMap R B s * b - algebraMap R B a) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ hb) (hm2 hsa)
    obtain ⟨u, hu⟩ := hsu
    have hb' : b = (↑u⁻¹ : B) * (algebraMap R B a + (algebraMap R B s * b - algebraMap R B a)) := by
      rw [← hu]
      simp
    rw [hb', smul_eq_mul, ← pow_two]
    apply Ideal.mul_mem_left
    exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)) (Ideal.mem_sup_right hsa)
  rw [Ideal.map_pow, heq]
