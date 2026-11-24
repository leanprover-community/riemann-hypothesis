module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
public import Mathlib.Algebra.Exact.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingShortExact
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.cohomology_vanishing_short_exact : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂)
    (β : F₂ ⟶ F₃), (∀ T, Function.Injective (α.app T).hom) → (∀ T, Function.Exact (α.app T).hom (β.app T).hom) →
    (∀ T, Function.Surjective (β.app T).hom) → (∀ n, Subsingleton (CH.H F₂ n)) → (∀ n, Subsingleton (CH.H F₃ n)) →
    ∀ n, Subsingleton (CH.H F₁ n) := by
  first | exact @GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | exact GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | (intros; apply GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses <;> assumption)
