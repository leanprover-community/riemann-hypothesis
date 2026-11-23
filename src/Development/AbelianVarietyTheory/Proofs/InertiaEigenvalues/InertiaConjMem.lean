module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

namespace GlobalTheory.InertiaConj

theorem norm_aut_eq {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

theorem inertia_conj_mem : ∀ (l : ℕ) [Fact l.Prime] (g τ : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) →
    τ⁻¹ * g * τ ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  intro l _ g τ hg
  have hS : ∀ σ : Gl l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1) →
      ∀ x : Om l, ‖x‖ ≤ 1 → ‖((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x‖ < 1 := by
    intro σ hσ x hx
    have hτx : ‖(τ : GQ l) x‖ ≤ 1 := by rw [norm_aut_eq]; exact hx
    have h1 := hσ ((τ : GQ l) x) hτx
    have h2 : ((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x =
        ((τ : GQ l).symm) ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) := by
      simp [map_sub]
    rw [h2, norm_aut_eq]
    exact h1
  unfold IK at hg ⊢
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hS x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : τ⁻¹ * (x * y) * τ = (τ⁻¹ * x * τ) * (τ⁻¹ * y * τ) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : τ⁻¹ * x⁻¹ * τ = (τ⁻¹ * x * τ)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

end GlobalTheory.InertiaConj
