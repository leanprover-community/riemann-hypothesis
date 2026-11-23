module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Formalism.SatakeDualWeyl.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.SmallIntegral

theorem eq_zero_of_isIntegral_mul_of_small :
    ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (y : E), 0 < d →
      IsIntegral ℤ ((d : E) * y) → ∀ ε : ℝ, (∀ φ : E →+* ℂ, ‖φ y‖ ≤ ε) →
      ((d : ℝ) * ε) ^ Module.finrank ℚ E < 1 → y = 0 := by
  intro E _ _ d y hd hint ε hε hlt
  by_contra hy
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have hz : (d : E) * y ≠ 0 := mul_ne_zero hd' hy

  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm ℚ hint : IsIntegral ℤ (Algebra.norm ℚ ((d : E) * y)))
  have hnorm0 : Algebra.norm ℚ ((d : E) * y) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hz
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hnorm0 (by simpa using hn.symm)
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0

  have hprod : ((Algebra.norm ℚ ((d : E) * y) : ℚ) : ℂ) = ∏ φ : E →+* ℂ, φ ((d : E) * y) := by
    have h := Algebra.norm_eq_prod_embeddings ℚ ℂ ((d : E) * y)
    have h2 : ∏ σ : E →ₐ[ℚ] ℂ, σ ((d : E) * y) = ∏ φ : E →+* ℂ, φ ((d : E) * y) :=
      Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
    rw [← h2, ← h]
    simp
  have hnC : ((n : ℂ)) = ∏ φ : E →+* ℂ, φ ((d : E) * y) := by
    rw [← hprod, ← hn]
    simp
  have habs : |(n : ℝ)| = ∏ φ : E →+* ℂ, ‖φ ((d : E) * y)‖ := by
    have := congrArg norm hnC
    rw [norm_prod] at this
    simpa using this
  have hbound : ∏ φ : E →+* ℂ, ‖φ ((d : E) * y)‖ ≤ ((d : ℝ) * ε) ^ Module.finrank ℚ E := by
    have hle : ∀ φ ∈ (Finset.univ : Finset (E →+* ℂ)), ‖φ ((d : E) * y)‖ ≤ (d : ℝ) * ε := by
      intro φ _
      rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hε φ) (Nat.cast_nonneg d)
    calc ∏ φ : E →+* ℂ, ‖φ ((d : E) * y)‖ ≤ ∏ _φ : E →+* ℂ, (d : ℝ) * ε :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hle
      _ = ((d : ℝ) * ε) ^ Module.finrank ℚ E := by
          rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card E ℂ]
  linarith

end GlobalTheory.CompanionTheory.SmallIntegral
