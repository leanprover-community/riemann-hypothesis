module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponent
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

theorem _root_.GlobalTheory.T.lift_idempotent_eq_of_sameComplexComponent : ∀ (K : Type) [Field K] [Algebra K ℂ] (X : Scheme.{0}) (s : X ⟶ Sp K) (R : Type) [CommRing R] [Algebra K R] (i : Sp R ⟶ X) (p q : R →ₐ[K] ℂ), Smooth s → IsOpenImmersion i → i ≫ s = spMap (algebraMap K R) → SameComp s (algebraMap K ℂ) (spMap p.toRingHom ≫ i) (spMap q.toRingHom ≫ i) → ∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e := by
  first | exact @GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | exact GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem | (intros; apply GlobalTheory.KeyFam.lift_eq_of_sameComp_of_isIdempotentElem <;> assumption)
