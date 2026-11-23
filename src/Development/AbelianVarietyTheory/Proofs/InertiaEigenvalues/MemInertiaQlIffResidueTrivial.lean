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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.IKRes

theorem norm_gal_ql {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv g x).symm

theorem mem_IK_ql_iff : ∀ (l : ℕ) [Fact l.Prime] (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖(g : GQ l) x - x‖ < 1 := by
  intro l _ g
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem σ hσ => exact hσ
    | one => intro x _; simp
    | mul σ τ _ _ hσ hτ =>
      intro x hx
      have h1 : ‖(σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x‖ < 1 :=
        hσ _ (by rwa [norm_gal_ql])
      have h2 := hτ x hx
      have he : ((σ * τ : Gl l) : GQ l) x - x =
          ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x) := by
        rw [Subgroup.coe_mul, AlgEquiv.mul_apply]; abel
      rw [he]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
    | inv σ _ hσ =>
      intro x hx
      have hy : ‖((σ : GQ l)⁻¹) x‖ ≤ 1 := by rwa [norm_gal_ql]
      have h := hσ _ hy
      have hx' : (σ : GQ l) (((σ : GQ l)⁻¹) x) = x := by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
      rw [hx', norm_sub_rev] at h
      simpa [Subgroup.coe_inv] using h
  · intro h
    exact Subgroup.subset_closure h

end GlobalTheory.IKRes
