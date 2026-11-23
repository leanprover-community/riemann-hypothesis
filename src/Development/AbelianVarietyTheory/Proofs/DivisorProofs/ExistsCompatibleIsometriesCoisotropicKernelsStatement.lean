module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleIsometriesCoisotropicKernels
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

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_compatible_isometries_coisotropic_kernels : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : ℕ → D.La →ₗ[𝓞 E] X), (∀ n, 0 < n → Cois D (y n) n) →
    (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e) →
    Module.finrank (𝓞 E) X ≤ min D.p D.q → ∀ N, 0 < N →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X ∧
      ∃ g : ℕ → D.La ≃ₗ[𝓞 E] D.La, (∀ n a b, D.EF (g n a) (g n b) = D.EF a b) ∧
        (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) ∧ (∀ n a, ∃ e, g n a = a + N • e) ∧
        ∀ n, 0 < n → ∀ a, (∃ e, y n (g n a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.exists_compatible_isometries | exact GlobalTheory.LowFilt.exists_compatible_isometries | (intros; apply GlobalTheory.LowFilt.exists_compatible_isometries <;> assumption)
