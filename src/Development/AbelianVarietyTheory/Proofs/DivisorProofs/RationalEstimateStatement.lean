import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRationalOfOneMapOverL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverFieldOfContainsRayField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTieCoordBase

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OntoChain
set_option autoImplicit false
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistedRatBase

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem exists_base_lift (hU : R.LUnif) (hB : GlobalTheory.BigOn.BaseLinks R F)
    (hRk : Formalism.L2.Indef.Tree.RankRows ((R.toCx F).data F.cr false)) (i : Fin D.R.m) :
    ∃ (x₀ : A.fam.amb.FL i A.μ0) (y : Fin (R.nW i) → D.what₂.LL),
      (R.FW i).j (sg0 D A) y = R.thG i A.μ0 (R.jV i A.μ0 x₀) ∧ (R.FW i).j (sg0 D A) y ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have hd : 0 < Module.finrank D.what₂.LL (R.WL F false i) := hRk.1.trans_eq (hRk.2 i).symm
  obtain ⟨y, hy⟩ : ∃ y, (GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y = fun _ => 1 :=
    ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false) (RealDat.ewNorm false) (RealDat.nP_pos false) hB.1
      hB.2.1 i A.μ0).2 _
  have h1 := GlobalTheory.BigOnBase.j_thetaMat_base hB i A.μ0 y
  refine hn ⟨(A.fam.L i A.μ0).toF (GlobalTheory.OntoChain.liftLvl F) (GlobalTheory.OntoChain.liftSub R F i A.μ0) y,
    GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y), h1, fun h0 => ?_⟩
  have h2 : GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y) = 0 :=
    (injective_iff_map_eq_zero _).1 (j_injective hU i) _ h0
  have h3 := (injective_iff_map_eq_zero _).1 (GlobalTheory.OntoChain.coordMap_injective (R := R) (F := F) i) _ h2
  exact one_ne_zero (congrFun (hy.symm.trans h3) ⟨0, hd⟩)

theorem baseLiftNeZero (hU : R.LUnif) (hB : GlobalTheory.BigOn.BaseLinks R F)
    (hRk : Formalism.L2.Indef.Tree.RankRows ((R.toCx F).data F.cr false)) :
    ∀ i, ∃ x₀ : A.fam.amb.FL i A.μ0, R.thG i A.μ0 (R.jV i A.μ0 x₀) ≠ 0 := fun i =>
  (exists_base_lift hU hB hRk i).imp fun _ h => h.elim fun _ h => h.1.symm.trans_ne h.2

theorem twistedRational_of_rayField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), R.Char F → IoExt R → R.LUnif → (∀ i, OMPins J R κ v₀ O i) → QGuard R → (∀ i, OneMapRowR J R κ v₀ O (fun _ => 1) i) → BaseLinks R F → RankRows ((R.toCx F).data F.cr false) → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → TwistedRational R F (fun _ => 1) := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw O hC hio hU hO hQ hrow hB hRk hray
  exact GlobalTheory.TwistedClassSum.twistedRational hC fw hio hU hO hQ hrow
    (GlobalTheory.TwistField.coverField_of_containsRayField D G Pl0 T0 A J R fw.laws hC.lev hQ hray) (baseLiftNeZero hU hB hRk)

end GlobalTheory.TwistedRatBase
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OntoChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedClassSums_rational_of_rayClassFields : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), R.Char F → IoExt R → R.LUnif → (∀ i, OMPins J R κ v₀ O i) → QGuard R → (∀ i, OneMapRowR J R κ v₀ O (fun _ => 1) i) → BaseLinks R F → RankRows ((R.toCx F).data F.cr false) → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → TwistedRational R F (fun _ => 1) := by
  atlas_forward_decl GlobalTheory.TwistedRatBase.twistedRational_of_rayField
end

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 1000000 in

theorem oneMapRowR_charOf (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) (ph : Fin D.R.m → ℂ)
    (i : Fin D.R.m) (h : OneMapRowR J R κ v₀ O ph i) :
    OneMapRowR J (charOf R F) κ v₀ (fun k => reOM (O k) F) ph i := by
  refine ⟨?_, fun hq => ?_⟩
  · obtain ⟨cc, ph', h0⟩ := h.1
    exact ⟨cc, ph', h0⟩
  · obtain ⟨O', h1, h2, h3⟩ := h.2 hq
    refine ⟨{ O' with }, h1, ⟨⟨h2.lift.field, h2.lift.std, h2.lift.v0, h2.lift.c0, h2.lift.lev⟩,
      fun t => ⟨(h2.tuple t).reps, (h2.tuple t).B, (h2.tuple t).xi, (h2.tuple t).phi, (h2.tuple t).half⟩,
      h2.act, h2.bad, h2.reps, h2.ep, h2.io, h2.w, h2.cov, h2.cxi, h2.model₂⟩, h3⟩

end Gen

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem phEff_eq_one : phEff p.R = fun _ => 1 := by
  funext i
  simp [phEff, p.phsOne i]

theorem extremal_vectors_split_part (h : p.Rows) : IoExt (R2 p) := h.ioExt

theorem splitPartRealisation_satisfies_qGuard : QGuard (R2 p) := p.qGuard

theorem one_map_split_part (h : p.Rows) (i : Fin D.R.m) : OneMapRowR p.T (R2 p) p.κ p.v₀ (om2 p) (fun _ => 1) i := by
  have := oneMapRowR_charOf (κ := p.κ) (v₀ := p.v₀) p.O (F2 p) (phEff p.R) i (h.oneMap i)
  rw [phEff_eq_one] at this
  exact this

theorem twistedRational_at (h : p.Rows) (hm : More p) : GlobalTheory.RealIndexBound.TwistedRational (R2 p) (F2 p) fun _ => 1 := by
  have hL : Links2 p := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p h hm.1
  exact GlobalTheory.T.twistedClassSums_rational_of_rayClassFields D _ _ _ _ p.T (R2 p) (F2 p) p.κ p.v₀ (fw2 p) (om2 p) hL.1 (extremal_vectors_split_part p h) hL.2.2.1
    hL.2.2.2.2.2.2.1 (splitPartRealisation_satisfies_qGuard p) (one_map_split_part p h) hL.2.2.2.1 hL.2.2.2.2.1 hm.2.2.rayQ

end Point

theorem ratSt : RatSt :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p h hm => twistedRational_at p h hm⟩⟩⟩

end GlobalTheory.BigOn

end
end
