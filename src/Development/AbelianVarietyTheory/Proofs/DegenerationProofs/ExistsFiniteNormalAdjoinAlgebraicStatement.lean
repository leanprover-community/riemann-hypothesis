module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalAdjoinAlgebraic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT


theorem _root_.GlobalTheory.T.exists_integrally_closed_extension_of_adjoin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (s : AlgebraicClosure (FractionRing R)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂) (h' : FractionRing R →+* FractionRing R₂) (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧ (∃ s₂, e s₂ = s) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F), ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by
  first | exact @GlobalTheory.exists_finite_normal_adjoin_algebraic | exact GlobalTheory.exists_finite_normal_adjoin_algebraic | (intros; apply GlobalTheory.exists_finite_normal_adjoin_algebraic <;> assumption)
