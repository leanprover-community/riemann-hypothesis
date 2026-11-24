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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem exists_bigZe_eq {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : Matrix (Fin g) (Fin g) ℂ) (hs : Zᵀ = Z)
    (hZ : ∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) :
    ∃ t, bigZe e q t = Z := by
  have hz : ∀ i k, ¬ ((e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) → Z i k = 0 :=
    fun i k h => by_contra fun h0 => h (hZ i k h0)
  have hsym : ∀ i k, Z i k = Z k i := fun i k => by
    have := congrFun (congrFun hs k) i
    simpa [Matrix.transpose_apply] using this
  let t : Fin n → ℂ := fun m => Z (e (Sum.inr (q.symm m).2.1, (q.symm m).1)) (e (Sum.inl (q.symm m).2.2, (q.symm m).1))
  have hb : ∀ τ a b, ballMat q t τ a b = Z (e (Sum.inr a, τ)) (e (Sum.inl b, τ)) := by
    intro τ a b
    simp [ballMat, t]
  refine ⟨t, ?_⟩
  ext i k
  obtain ⟨⟨x, τ⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨y, τ'⟩, rfl⟩ := e.surjective k
  simp only [bigZe, bigZ, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  by_cases hτ : τ = τ'
  · subst hτ
    rw [Matrix.blockDiagonal_apply_eq]
    rcases x with a | a <;> rcases y with b | b
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
      exact (hz _ _ (by simp)).symm
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.transpose_apply, hb, hsym]
    · rw [Matrix.fromBlocks_apply₂₁, hb]
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      exact (hz _ _ (by simp)).symm
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ hτ]
    exact (hz _ _ (by simp [hτ])).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
