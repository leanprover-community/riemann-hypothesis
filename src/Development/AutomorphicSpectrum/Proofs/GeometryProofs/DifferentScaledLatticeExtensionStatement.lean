module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentScaledLatticeExtension
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.different_scaled_lattice_extension : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (R : Subring Ω) (R' : Subring Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (W : Submodule Ω V) (W' : Submodule Ω' V') (O : Type) [CommRing O] (σ : O →+* Ω) (𝔡 : Ideal O) (d₀ : O) (D : Submodule R V) (D' : Submodule R' V'), IsExtOver i j → (∀ a ∈ R, i a ∈ R') → W' = Submodule.span Ω' (j '' (W : Set V)) → d₀ ∈ 𝔡 → σ d₀ ≠ 0 → (∀ d ∈ 𝔡, σ d / σ d₀ ∈ R) → (∀ e ∈ D, e ∈ W) → D' = Submodule.span R' (j '' (D : Set V)) → Submodule.span R' {e | e ∈ W' ∧ ∀ d ∈ 𝔡, (i.comp σ) d • e ∈ D'} = Submodule.span R' (j '' (Submodule.span R {e | e ∈ W ∧ ∀ d ∈ 𝔡, σ d • e ∈ D} : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.scale_pull_ext | exact GlobalTheory.CompanionTheory.Ar.scale_pull_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.scale_pull_ext <;> assumption)
