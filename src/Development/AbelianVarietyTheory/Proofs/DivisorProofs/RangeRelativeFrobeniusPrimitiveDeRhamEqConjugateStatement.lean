module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRelativeFrobeniusPrimitiveDeRhamEqConjugate
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.range_relativeFrobenius_primitiveDeRham_eq_conjugate : GlobalTheory.Published.AbelianDeRham.BaseChange → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left) (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) (F : A ⟶ A₁) [IsMonHom F] (hF : F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A)) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LinearMap.range (primPull (dp0 R) (𝟙 _) F) = conjDR p R hR A ∧ PrimitiveSubmodule A₁ ≤ LinearMap.ker (primPull (dp0 R) (𝟙 _) F) := by
  first | exact @GlobalTheory.ConjSeq.range_primPull_relFrob | exact GlobalTheory.ConjSeq.range_primPull_relFrob | (intros; apply GlobalTheory.ConjSeq.range_primPull_relFrob <;> assumption)
