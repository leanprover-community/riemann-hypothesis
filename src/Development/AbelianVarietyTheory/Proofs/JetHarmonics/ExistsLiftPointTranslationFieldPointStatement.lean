module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExpF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLiftPointTranslationFieldPoint
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_lift_point_translation_fieldPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (T : Over (Spec (CommRingCat.of R))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ G), g.left = e ≫ x.left ≫ pullback.fst G.hom (jK R) → ∃ ρ : T.left ⟶ (UnifPre.GF (G := G) F).left, ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ ρ ≫ UnifPre.gFK (G := G) F = r.left ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ UnifPre.gFK (G := G) F = (r * g).left := by
  first | exact @GlobalTheory.exists_lift_translT | exact GlobalTheory.exists_lift_translT | (intros; apply GlobalTheory.exists_lift_translT <;> assumption)
