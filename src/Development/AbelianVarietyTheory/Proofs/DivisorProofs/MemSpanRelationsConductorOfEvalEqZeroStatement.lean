module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanRelationsConductorOfEvalEqZero
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

theorem _root_.GlobalTheory.T.mem_span_relations_conductor_of_eval_eq_zero : ∀ (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E] (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D) (F : σ → MvPolynomial ν R), Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) → RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) → IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ) → ∀ G : MvPolynomial ν R', MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0 → G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔ (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  first | exact @GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | exact GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | (intros; apply GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero <;> assumption)
