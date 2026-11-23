module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenFieldExtension
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

theorem _root_.GlobalTheory.T.lattice_eigen_field_extension : ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω) (R : Subring Ω) (R' : Subring Ω') (L : Submodule R V), IsExtOver i j → (∀ a e, ρ' a (j e) = j (ρ a e)) → (∀ a ∈ R, i a ∈ R') → (∀ a, ∀ e ∈ L, ρ a e ∈ L) → (∀ a, σ a ∈ R) → ((NumberField.discr F : ℤ) : Ω)⁻¹ ∈ R → Submodule.span R' (j '' (L : Set V)) ⊓ (eigSp ρ' (i.comp σ)).restrictScalars R' = Submodule.span R' (j '' ((L ⊓ (eigSp ρ σ).restrictScalars R : Submodule R V) : Set V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp | exact GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp <;> assumption)
