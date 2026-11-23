module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicLamdiff
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicPic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicQuot
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicTransl
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicWeight
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PquoFibre
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PquoSplit
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

open Out

namespace PositivityTheory.HtPt.Ppic

private theorem isMonHom_comp_comp {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {A B D F : C} [MonObj A] [MonObj B] [MonObj D] [MonObj F]
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ F) (ha : IsMonHom a.hom) (hb : IsMonHom b.hom)
    (hc : IsMonHom c.hom) : IsMonHom (a.hom ≫ b.hom ≫ c.hom) := by
  infer_instance


open GlobalTheory.CechPic in
theorem isPrincipal_tB_of (hU : GlobalTheory.LN.UDvrSt) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), GlobalTheory.LN.CDvr V → Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → GlobalTheory.LN.PolAt tV (Out.jK V) → ∀ P : AbPart tV (spMap r), IsPrincipal P.tB := by
  intro E _ _ _ H V _ _ _ r tV hC hr hker hpol P
  obtain ⟨Pu, -⟩ := hU E H V hC tV hpol (PositivityTheory.HtPt.Pquo.split E H V r tV hr hker P)
  obtain ⟨Q, X, _, _, _, T, β, hβ, hL⟩ := PositivityTheory.HtPt.Pquo.fibre E H V r tV hr hker Pu P
  obtain ⟨e', he', hq⟩ := PositivityTheory.HtPt.Ppic.quot P.tK.G P.τ X T
  letI := P.τ.grpB
  let g : Q.A ≅ P.tB.G := Iso.trans β.symm (Iso.trans e'.symm P.e)
  haveI : IsMonHom g.hom :=
    isMonHom_comp_comp β.symm e'.symm P.e (by show IsMonHom β.inv; infer_instance)
      (by show IsMonHom e'.inv; infer_instance) P.e_hom
  have hLB := P.tB.PP.isLB
  have hQL := Q.isLB
  have hKL := P.tK.PP.isLB
  have hMLB : (P.tB.PP.L.pull g.hom.left).IsLB := LB.isLB_pull hLB _
  have hrefl : LBIso (P.tB.PP.L.pull g.hom.left) (P.tB.PP.L.pull g.hom.left) :=
    (cls_eq_iff hMLB hMLB).1 rfl
  have hcomp : (T.q ≫ β.hom).left ≫ g.hom.left = (P.τ.q ≫ P.e.hom).left := by
    rw [← Over.comp_left]
    congr 1
    simp only [g, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← hq, Category.assoc, Iso.hom_inv_id_assoc]
  have h1 : LBIso ((P.tB.PP.L.pull g.hom.left).pull (T.q ≫ β.hom).left)
      (P.tB.PP.L.pull (P.τ.q ≫ P.e.hom).left) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso hrefl _ hcomp.symm
  have h2 : LBIso ((P.tB.PP.L.pull g.hom.left).pull (T.q ≫ β.hom).left)
      (Q.L.pull (T.q ≫ β.hom).left) :=
    LBIso.trans (LB.isLB_pull hMLB _) (LB.isLB_pull hLB _) (LB.isLB_pull hQL _) h1
      (LBIso.trans (LB.isLB_pull hLB _) hKL (LB.isLB_pull hQL _) P.pp.symm hL)
  obtain ⟨u, hu⟩ := PositivityTheory.HtPt.Ppic.lamdiff PositivityTheory.HtPt.Ppic.weight Q X P.tK.G T β hβ _ hMLB h2
  obtain ⟨x, hx⟩ := PositivityTheory.HtPt.Ppic.pic Q _ hMLB ⟨u, hu⟩
  obtain ⟨hA, hK⟩ := PositivityTheory.HtPt.Ppic.transl Q _ hMLB x hx
  haveI := P.tB.semi.smooth
  haveI := P.tB.semi.separated
  haveI := P.tB.semi.quasiCompact
  haveI : IsProper Q.A.hom := Q.isAb.proper
  have hpb : IsGrpPullback Q.A P.tB.G (specOf (RingHom.id ℂ)) g.hom.left :=
    (isGrpPullback_of_iso g).congr (specOf_id ℂ).symm rfl
  exact GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension ℂ ℂ (RingHom.id ℂ) P.tB.G Q.A
    g.hom.left hpb P.tB.PP.L _ hLB hMLB hrefl inferInstance hA hK

theorem dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), GlobalTheory.LN.CDvr V → Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → GlobalTheory.LN.PolAt tV (Out.jK V) → ∀ P : AbPart tV (spMap r), IsPrincipal P.tB :=
  isPrincipal_tB_of GlobalTheory.LN.uDvrSt_holds

end PositivityTheory.HtPt.Ppic
