module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralDerivativeCurveHomGoodReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.isIntegral_derivative_curve_hom_good_reduction : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.PolBaseChangeSt → ∀ (M : Type) [Field M] [NumberField M] (P Q : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (t : epsR (𝓞 M) ⟶ Q.A) (a : M), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) Q Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) → IsIntegral ℤ a := by
  first | exact @GlobalTheory.isIntegral_of_hom_derivative | exact GlobalTheory.isIntegral_of_hom_derivative | (intros; apply GlobalTheory.isIntegral_of_hom_derivative <;> assumption)
