module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteExtGeomIntegralLocalization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_finite_ext_geom_integral_localization : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (p : R →ₐ[K] ℂ), ∃ (k : IntermediateField K ℂ) (e : k ⊗[K] R), FiniteDimensional K k ∧ IsIdempotentElem e ∧ Algebra.TensorProduct.lift k.val p (fun _ _ => Commute.all _ _) e = 1 ∧ GeomInt k (Localization.Away e) := by
  first | exact @GlobalTheory.GeomComp.exists_geomInt_component | exact GlobalTheory.GeomComp.exists_geomInt_component | (intros; apply GlobalTheory.GeomComp.exists_geomInt_component <;> assumption)
