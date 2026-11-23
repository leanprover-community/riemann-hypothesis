module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicShearOfAdjoint
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

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem _root_.GlobalTheory.T.exists_isotropic_shear_of_adjoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    ∀ σ w : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') → (∀ b ∈ Z', σ b = b) → (∀ a, ∃ e, y (σ a) = y a + n • e) →
    (∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e) → (∀ a b, D.EF (w a) b = D.EF a (σ b)) →
    (∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e) →
    ∃ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) ∧ (∀ z z' : Z, D.EF (t z) (t z') = 0) ∧
      ∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a := by
  first | exact @GlobalTheory.LowFilt.exists_shear_of_adjoint | exact GlobalTheory.LowFilt.exists_shear_of_adjoint | (intros; apply GlobalTheory.LowFilt.exists_shear_of_adjoint <;> assumption)
