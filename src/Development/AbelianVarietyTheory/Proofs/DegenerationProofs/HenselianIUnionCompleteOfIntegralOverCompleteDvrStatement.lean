module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HenselianIUnionCompleteOfIntegralOverCompleteDvr
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr : ∀ (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra W R], Function.Injective (algebraMap W R) → Algebra.IsIntegral W R → IsLocalHom (algebraMap W R) ∧ HenselianLocalRing R ∧ ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'), (↑s : Set R) ⊆ W' ∧ IsAdicComplete (IsLocalRing.maximalIdeal W') W' ∧ Module.Finite W W' ∧ IsLocalHom W'.val.toRingHom := by
  first | exact @GlobalTheory.henselian_and_union_of_isIntegral_complete | exact GlobalTheory.henselian_and_union_of_isIntegral_complete | (intros; apply GlobalTheory.henselian_and_union_of_isIntegral_complete <;> assumption)
