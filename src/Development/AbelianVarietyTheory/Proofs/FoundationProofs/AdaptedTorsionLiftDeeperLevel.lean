module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem adapted_lift_deeper : ∀ (D : D7), galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, FixK D ⊤ σ → ∀ (c c' : ℂ) (n₀ n : ℕ), 0 < n₀ → 0 < n → InRationalLattice (lamOf D cc δ) c → Adp1 ⊤ σ (lamOf D cc δ) n₀ c c' → ∃ ω ∈ lamOf D cc δ, Adp1 ⊤ σ (lamOf D cc δ) (n₀ * n) (c + (n₀ : ℂ) * ω) c' := by
  intro D hS cc δ hC σ hσ c c' n₀ n h₀ hn hc hA
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := hS cc δ hC ⊤ σ hσ IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨k, hk, hkc⟩ := hc
  have e₀ : (n₀ : ℂ) ≠ 0 := by exact_mod_cast h₀.ne'
  have e₁ : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold Adp1 at hA ⊢
  have a1 : ((k * n₀ : ℕ) : ℂ) * (c / (n₀ : ℂ)) ∈ lamOf D cc δ := by
    have : ((k * n₀ : ℕ) : ℂ) * (c / (n₀ : ℂ)) = (k : ℂ) * c := by
      push_cast; field_simp
    rw [this]; exact hkc
  have a2 := (h6 _ _ _ hA).1 a1
  have a3 : ((k * n₀ * n : ℕ) : ℂ) * (c' / ((n₀ * n : ℕ) : ℂ)) ∈ lamConj ⊤ σ (lamOf D cc δ) := by
    have : ((k * n₀ * n : ℕ) : ℂ) * (c' / ((n₀ * n : ℕ) : ℂ)) = ((k * n₀ : ℕ) : ℂ) * (c' / (n₀ : ℂ)) := by
      push_cast; field_simp
    rw [this]; exact a2
  obtain ⟨u, -, hu⟩ := h7 (k * n₀ * n) (by positivity)
    (fun _ _ _ => ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩) _ a3
  have b1 := h5 (n : 𝓞 D.host.K) _ _ hu
  have b2 := h5 (-1 : 𝓞 D.host.K) _ _ hA
  have c1 : D.host.φ₀ ((((n : 𝓞 D.host.K) : D.host.K) : D.host.E)) = (n : ℂ) := by simp
  have c2 : D.host.φ₀ ((((-1 : 𝓞 D.host.K) : D.host.K) : D.host.E)) = (-1 : ℂ) := by simp
  rw [c1] at b1
  rw [c2] at b2
  have b3 := h4 _ _ _ _ b1 b2
  have z : (n : ℂ) * (c' / ((n₀ * n : ℕ) : ℂ)) + -1 * (c' / (n₀ : ℂ)) = 0 := by
    push_cast; field_simp; ring
  rw [z] at b3
  have b4 := (h6 1 _ _ b3).2 (by simp)
  rw [Nat.cast_one, one_mul] at b4
  refine ⟨_, b4, ?_⟩
  have : (c + (n₀ : ℂ) * ((n : ℂ) * u + -1 * (c / (n₀ : ℂ)))) / ((n₀ * n : ℕ) : ℂ) = u := by
    push_cast; field_simp; ring
  rw [this]; exact hu

end GlobalTheory.GalTheta
