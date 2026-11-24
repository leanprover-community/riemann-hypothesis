module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointPicardClassEqTranslateOfTrivialLambdaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricRigidTranslateLineBundleOfSquareDefectStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
noncomputable section
namespace GlobalTheory.RiemannExists

theorem exists_sym_translate : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L → ∃ (L' : LB B.left) (hL' : L'.IsLB), Out.Rigidified B L' ∧ Out.Sym B L' ∧ Out.RelAmple B L' ∧ Out.KTriv B L' ∧ lam (cls L' hL') (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) := by
  intro K _ _ B _ hB L hL ha hk
  have := hB.comm
  obtain ⟨c, hc⟩ := exists_gen_theta_of_isAbelianScheme K B hB L hL
  have hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen := ⟨c, hc⟩
  obtain ⟨O, hO, eO⟩ := CechPic.cls_surj (CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL)
  have hlam : lam (cls O hO) (fst B B) (snd B B) = 0 := by
    rw [eO, PrimitiveOverField.lam_sub, CechPic.lam_pull, ← Hom.inv_def, ← Hom.inv_def,
      FormPoly.lam_inv_left hL hΘ, FormPoly.lam_inv_right hL hΘ, neg_neg, sub_self]
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_point_picardClass_eq_translate_of_trivial_lambda K B hB L hL hk O hO hlam
  obtain ⟨a, hab⟩ := SS.SemiDivisible.pow_surj_abelian K B hB (n := 2) (by norm_num) b
  have hL' : (RigidTranslate.rigTransl L a).IsLB := DVR.linComb_isLB _ hL _ _
  refine ⟨_, hL', RigidTranslate.rigidified_rigTransl hL, GlobalTheory.T.symmetric_rigidTranslateLineBundle_of_square_defect K B L hL hΘ a (by rw [← eO, hb, hab]),
    GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint K B hB L hL a ha, GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle _ B L hL a hk, ?_⟩
  have e := (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2
    (RigidTranslate.lam_rigTransl (t := a) hL c hc)
  rw [CechPic.cls_pull (LB.isLB_linComb hL _ _), CechPic.pull_id] at e
  exact (CechPic.cls_cube_two hL' _ _ _).symm.trans (e.trans (CechPic.cls_cube_two hL _ _ _))

end GlobalTheory.RiemannExists
