module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataSymmAndOfOAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThickenedGroupEndomorphismTorusCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomThickenedGroupEndomorphismTorusCoordinatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTorusViaCharactersStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTransitionCompatStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem q_comm_of_coordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) (h' : D.X →+ D.X)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (F : thickObj R I e G ⟶ thickObj R I e G) (hF : IsCoordEnd g a a' h' u F) :
    F ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map a := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    have h2 : ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst D.P.A.hom (thick R I e) =
        pullback.fst D.P.A.hom (thick R I e) ≫ a.left := by
      simp
    rw [h2]
    exact hF.1
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    have w1 : g.q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w g.q
    have w2 : ((Over.pullback (thick R I e)).map a).left ≫ pullback.snd D.P.A.hom (thick R I e) =
        pullback.snd D.P.A.hom (thick R I e) := Over.w ((Over.pullback (thick R I e)).map a)
    have w3 : F.left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w F
    rw [w2, w1]
    exact w3

theorem formalEnd_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ b, FormalEnd U.toUnifPre a h' b := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hE
  obtain ⟨ha, ha', hr, -, hc, -⟩ := hE
  have hr' := GlobalTheory.Mum.RosatiSymmetry.rosatiAdj_symm D.toPre.P.A D.toPre.P.L D.toPre.P.isLB a a' hr
  obtain ⟨u, hu, h₀⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB a' a hr'
  choose F hF using fun e => GlobalTheory.T.exists_thickenedGroup_endomorphism_torusCoordinates (U.gt e) a a' h' hc u hu h₀
  exact ⟨F, fun e => GlobalTheory.T.isMonHom_thickenedGroup_endomorphism_torusCoordinates (U.gt e) a a' h' hc u hu h₀ (F e) (hF e),
    fun e => GlobalTheory.T.thickenedGroup_endomorphism_transition_compat U.toUnifPre e a a' h' u (F e) (F (e + 1)) (hF e) (hF (e + 1)),
    fun e => q_comm_of_coordEnd (U.gt e) a a' h' u (F e) (hF e),
    fun e => GlobalTheory.T.thickenedGroup_endomorphism_torus_via_characters (U.gt e) a a' h' u hu h₀ (F e) (hF e)⟩

end GlobalTheory.Mum.EndThick
end
