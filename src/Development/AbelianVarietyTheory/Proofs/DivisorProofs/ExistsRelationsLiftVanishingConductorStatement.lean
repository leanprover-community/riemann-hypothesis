module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelationsLiftVanishingConductor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_relations_lift_vanishing_conductor : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  first | exact @GlobalTheory.Pinch.relations_lift_vanishing | exact GlobalTheory.Pinch.relations_lift_vanishing | (intros; apply GlobalTheory.Pinch.relations_lift_vanishing <;> assumption)
