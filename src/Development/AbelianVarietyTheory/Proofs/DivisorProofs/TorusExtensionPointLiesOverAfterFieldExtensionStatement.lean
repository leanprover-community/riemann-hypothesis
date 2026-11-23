module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointLiesOverAfterFieldExtension
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.torusExtension_point_liesOver_after_field_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre (FractionRing R)) (w : Frm D.toPre (FractionRing R) 1 g.b) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x), w.IsGen → fr.IsGen → GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ g w x fr → ∀ (x' : TFK (R := R) F ⟶ A.A), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → ∃ (w' : Frm D.toPre F 1 (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b) (fr' : FrAt x'), w'.IsGen ∧ fr'.IsGen ∧ GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' x' fr' := by
  first | exact @GlobalTheory.Poinc.Tors.LiesOverExt.liesOver_ext | exact GlobalTheory.Poinc.Tors.LiesOverExt.liesOver_ext | (intros; apply GlobalTheory.Poinc.Tors.LiesOverExt.liesOver_ext <;> assumption)
