module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentative
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

@[expose] public section


theorem _root_.GlobalTheory.T.unique_reduced_orbit_representative : ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) → Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by
  first | exact @GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | exact GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate | (intros; apply GlobalTheory.CompanionTheory.SiegelKlingen.exists_unique_minimal_translate <;> assumption)
