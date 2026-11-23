module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem emb_mul_bigZ {E : Type} [Field E] [NumberField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ}
    (σ : Ψ → (𝓞 E →+* ℂ)) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (a : 𝓞 E) (i k : Ix Ψ j j') :
    emb σ i a * bigZ q t i k = bigZ q t i k * star (emb σ k a) := by
  obtain ⟨i1, τ⟩ := i
  obtain ⟨k1, τ'⟩ := k
  by_cases h : τ = τ'
  · subst h
    rcases i1 with i1 | i1 <;> rcases k1 with k1 | k1 <;>
      simp [bigZ, emb, blockDiagonal_apply, mul_comm]
  · simp [bigZ, blockDiagonal_apply_ne _ _ _ h]

theorem tz_bigZe_comm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ a x, tz (bigZe e q t) (B a x) = B a (tz (bigZe e q t) x) := by
  intro E _ _ _ Ψ _ _ j j' n g σ e q t B _ hB a x
  funext i
  have hsub : B a (tz (bigZe e q t) x) i
      = B a x i - B a (bigZe e q t *ᵥ star x) i := by
    simp only [tz, map_sub, Pi.sub_apply]
  rw [hsub]
  simp only [tz, Pi.sub_apply]
  congr 1
  rw [hB a (bigZe e q t *ᵥ star x) i]
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := emb_mul_bigZ σ q t a (e.symm i) (e.symm k)
  have hx : star (B a x) k = star (emb σ (e.symm k) a) * star (x k) := by
    simp [hB, mul_comm]
  rw [hx, ← mul_assoc, ← mul_assoc]
  simp only [bigZe, submatrix_apply, Pi.star_apply]
  rw [hk]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
