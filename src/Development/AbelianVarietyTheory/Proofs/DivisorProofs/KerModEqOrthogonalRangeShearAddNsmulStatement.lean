module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmul
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem _root_.GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | exact GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | (intros; apply GlobalTheory.LowFilt.ker_mod_eq_perp_range_add <;> assumption)
