module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryKernelCoisotropicMod
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_isometry_kernel_coisotropic_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.exists_isometry_kerIs | exact GlobalTheory.LowFilt.exists_isometry_kerIs | (intros; apply GlobalTheory.LowFilt.exists_isometry_kerIs <;> assumption)
