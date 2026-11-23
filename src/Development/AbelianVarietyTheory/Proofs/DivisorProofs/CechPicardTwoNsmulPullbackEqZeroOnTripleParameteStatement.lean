module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardTwoNsmulPullbackEqZeroOnTripleParamete
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
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechPicard_two_nsmul_pullback_eq_zero_on_tripleParameterScheme : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → A.hom ⁻¹ᵁ U ≤ W → W ≤ A.hom ⁻¹ᵁ U ⊔ V → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), p ≫ V.ι = v.left → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) → GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) → e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ → GlobalTheory.CechPic.pull (x.left ∣_ W) (2 • c) = 0 := by
  first | exact @GlobalTheory.pull_two_nsmul_eq_zero_of_triples | exact GlobalTheory.pull_two_nsmul_eq_zero_of_triples | (intros; apply GlobalTheory.pull_two_nsmul_eq_zero_of_triples <;> assumption)
