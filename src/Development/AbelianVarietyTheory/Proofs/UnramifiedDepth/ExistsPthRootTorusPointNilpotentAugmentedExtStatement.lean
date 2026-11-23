module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPthRootTorusPointNilpotentAugmentedExt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Formalism.LocalToGlobal.CharacterGerms.GeNatCast
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.DualLattices.FormalChartAtZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_pth_root_torus_point_nilpotent_augmented_ext : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ χ : Multiplicative X →* Aˣ, (∀ x, π (χ x).val = 1) → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω) (χ' : Multiplicative X →* A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧ (∀ x, π' (χ' x).val = 1) ∧ χ' ^ p = (Units.map (f : A →* A')).comp χ := by
  first | exact @GlobalTheory.TorusRoot.exists_root_character | exact GlobalTheory.TorusRoot.exists_root_character | (intros; apply GlobalTheory.TorusRoot.exists_root_character <;> assumption)
