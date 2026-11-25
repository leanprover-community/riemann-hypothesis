module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

namespace GlobalTheory.CompanionTheory.DiagBd

theorem valued_eq_one_of_isCompact_closure_zpowers (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w)
    (s : Fin n → (w.adicCompletion E)ˣ) (hg : g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹)
    (hc : IsCompact (closure (Subgroup.zpowers g : Set H))) (i : Fin n) :
    Valued.v (s i : w.adicCompletion E) = 1 := by
  set φ : H → w.adicCompletion E :=
    fun x => ((p⁻¹ * x.1 * p : GLw n w) : Matrix (Fin n) (Fin n) _) i i with hφdef
  have hφ : Continuous φ := by
    have h1 : Continuous fun x : H => (p⁻¹ * x.1 * p : GLw n w) :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have h2 : Continuous fun x : H => ((p⁻¹ * x.1 * p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :=
      Units.continuous_val.comp h1
    exact (continuous_apply i).comp ((continuous_apply i).comp h2)
  have hpow : ∀ m : ℤ, φ (g ^ m) = ((s i ^ m : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    intro m
    have h1 : p⁻¹ * ((g ^ m : H) : GLw n w) * p = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) (s ^ m) := by
      rw [Subgroup.coe_zpow, hg, map_zpow]
      rw [show p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ =
        MulAut.conj p (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s) from rfl, ← map_zpow]
      simp [MulAut.conj_apply, mul_assoc]
    simp only [hφdef, h1, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq, Pi.pow_apply]
  obtain ⟨R, hR⟩ := (hc.image hφ).isBounded.exists_norm_le
  have hb : ∀ m : ℤ, ‖((s i ^ m : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ ≤ R := by
    intro m
    rw [← hpow m]
    exact hR _ ⟨g ^ m, subset_closure (Subgroup.zpow_mem_zpowers g m), rfl⟩
  have hne : (s i : w.adicCompletion E) ≠ 0 := (s i).ne_zero
  have hpos : 0 < ‖(s i : w.adicCompletion E)‖ := norm_pos_iff.mpr hne
  have hnorm : ‖(s i : w.adicCompletion E)‖ = 1 := by
    rcases lt_trichotomy ‖(s i : w.adicCompletion E)‖ 1 with h | h | h
    · exfalso
      have h' : 1 < ‖(s i : w.adicCompletion E)‖⁻¹ := (one_lt_inv₀ hpos).mpr h
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R h'
      have := hb (-(k : ℤ))
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, _root_.zpow_neg, zpow_natCast, ← inv_pow] at this
      linarith
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R h
      have := hb (k : ℤ)
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, zpow_natCast] at this
      linarith
  refine le_antisymm (Valued.toNormedField.norm_le_one_iff.1 hnorm.le) (not_lt.1 fun h => ?_)
  exact absurd (Valued.toNormedField.norm_lt_one_iff.2 h) (by rw [hnorm]; exact lt_irrefl _)

end GlobalTheory.CompanionTheory.DiagBd
