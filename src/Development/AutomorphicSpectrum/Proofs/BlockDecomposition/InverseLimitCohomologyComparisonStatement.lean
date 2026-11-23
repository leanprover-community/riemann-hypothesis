module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseLimitCohomologyComparison
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.inverse_limit_cohomology_comparison : ∀ {R : Type} [CommRing R] {K : Cx.{1} R} (Kn : ℕ → Cx.{1} R) (c : R) (red : ∀ n, Cx.Hom K (Kn n) (RingHom.id R))
    (tr : ∀ n, Cx.Hom (Kn (n + 1)) (Kn n) (RingHom.id R)), (∀ n j x, (tr n).f j ((red (n + 1)).f j x) = (red n).f j x) →
    (∀ n j, Function.Surjective ((red n).f j)) → (∀ n j x, (red n).f j x = 0 ↔ ∃ y, x = c ^ n • y) → (∀ j (x : K.X j), c • x = 0 → x = 0) →
    ∀ j k : ℕ, (∀ (x : K.H (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) → (∀ x : K.H j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) →
    (∀ x : ℕ → K.H j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : K.H j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) →
    (∀ x : ∀ n, (Kn n).H j, (∀ n, (tr n).mapH j (x (n + 1)) = x n) → ∃ z : K.H j, ∀ n, (red n).mapH j z = c ^ (2 * k) • x n) ∧
    ∀ z : K.H j, (∀ n, (red n).mapH j z = 0) → c ^ k • z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LimLift.lim_lift | exact GlobalTheory.CompanionTheory.LimLift.lim_lift | (intros; apply GlobalTheory.CompanionTheory.LimLift.lim_lift <;> assumption)
