module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

theorem eq_of_isPrim_of_toReal_eq_smul : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] (x y : LinearMap.BilinForm ℤ X)
    (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X), IsPrim bar (⟨x, hx⟩ : balForms bar X) →
    IsPrim bar (⟨y, hy⟩ : balForms bar X) → ∀ b : ℝ, 0 < b → toReal x = b • toReal y → x = y := by
  intro O _ bar X _ _ x y hx hy px py b hb h
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact not_isPrim_zero (bar := bar) py
  obtain ⟨a, c, hac⟩ : ∃ a c, y a c ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy0 (LinearMap.ext₂ hc)
  have hR : ∀ u v, (x u v : ℝ) = b * (y u v : ℝ) := fun u v => by
    have := LinearMap.congr_fun₂ h u v
    simpa [toReal_apply] using this
  have hacR : (y a c : ℝ) ≠ 0 := by exact_mod_cast hac
  have hxac : x a c ≠ 0 := by
    have : (x a c : ℝ) ≠ 0 := by rw [hR]; exact mul_ne_zero hb.ne' hacR
    exact_mod_cast this
  have habs : |(x a c : ℝ)| = b * |(y a c : ℝ)| := by
    rw [hR, abs_mul, abs_of_pos hb]
  apply eq_of_isPrim hx hy px py (k := (y a c).natAbs) (n := (x a c).natAbs)
    (Int.natAbs_pos.2 hac) (Int.natAbs_pos.2 hxac)
  apply LinearMap.ext₂
  intro u v
  simp only [LinearMap.smul_apply, smul_eq_mul, Int.natCast_natAbs]
  have e : |(y a c : ℝ)| * (x u v : ℝ) = |(x a c : ℝ)| * (y u v : ℝ) := by
    rw [hR u v, habs]; ring
  exact_mod_cast e

end GlobalTheory.PolFan.SmoothEnd
