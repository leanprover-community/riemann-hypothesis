module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXb
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt

theorem exists_rows_det_ne_zero {Ω : Type} [Field Ω] {n m : ℕ} (M : Matrix (Fin n) (Fin m) Ω)
    (B : Matrix (Fin m) (Fin n) Ω) (h : B * M = 1) :
    ∃ J : Fin m → Fin n, (M.submatrix J id).det ≠ 0 := by
  have hspan : Submodule.span Ω (Set.range fun j => M j) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hw : w = (w ᵥ* B) ᵥ* M := by rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
    rw [hw, Matrix.vecMul_eq_sum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨f, hf, -, hl⟩ := Submodule.exists_fun_fin_finrank_span_eq Ω (Set.range fun j => M j)
  have e : Module.finrank Ω (Submodule.span Ω (Set.range fun j => M j)) = m := by
    rw [hspan, finrank_top, Module.finrank_fin_fun]
  choose J hJ using fun i : Fin m => hf (Fin.cast e.symm i)
  refine ⟨J, ?_⟩
  have hl' : LinearIndependent Ω (M.submatrix J id).row := by
    have : (M.submatrix J id).row = f ∘ Fin.cast e.symm := by
      funext i
      exact hJ i
    rw [this]
    exact hl.comp _ (Fin.cast_injective _)
  exact ((Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.linearIndependent_rows_iff_isUnit.1 hl')).ne_zero

theorem exists_rows_castLE_det_ne_zero {Ω : Type} [Field Ω] {n m a : ℕ} (M : Matrix (Fin n) (Fin m) Ω)
    (B : Matrix (Fin m) (Fin n) Ω) (h : B * M = 1) (ha : a + 1 ≤ m) (hm : a + 1 = m) :
    ∃ J : Fin (a + 1) → Fin n, (M.submatrix J (Fin.castLE ha)).det ≠ 0 := by
  subst hm
  obtain ⟨J, hJ⟩ := exists_rows_det_ne_zero M B h
  exact ⟨J, hJ⟩

theorem step_full {Ψ : Type} {p q : ℕ} (K₀ : Type) (t : StepIx Ψ p q)
    (h : ∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r ≠ some (.inr t)) :
    (t.2 : ℕ) + 1 = rk Ψ p q t.1 := by
  apply GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.full_of_noBlock <;> assumption

theorem xb_block_ne : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type)
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), (∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0) →
    (∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * A s = 1) →
    ∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0 := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ hx hB k
  obtain ⟨k, hk⟩ := k
  rcases k with k | t
  · exact hx k
  · obtain ⟨B, hB⟩ := hB t.1
    exact exists_rows_castLE_det_ne_zero (A t.1) B hB t.2.2 (step_full K₀ t hk)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt
