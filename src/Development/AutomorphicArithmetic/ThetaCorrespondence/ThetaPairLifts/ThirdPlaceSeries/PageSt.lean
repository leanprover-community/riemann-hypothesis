import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PageEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafLevelSquareBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafLevelSquareBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BigOn
theorem levelSq_yBound_atRec_alt :
    _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    ⟨0, fun c _ _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ r O hO => ?_⟩⟩⟩
  obtain ⟨st, td⟩ := hO.1.depth
  letI := hostAlg (Fm.D x i)
  have g1 : O.g1 = (Fm.D x i).host.g 0 := td.jets_eq_fact
  have g2 : O.g2 = (Fm.D x i).host.g 1 := td.g2_eq
  have f1 : O.f = ((Fm.D x i).R.f : ℝ) := td.f_eq
  have k1 : O.k = ((Fm.D x i).R.k : ℝ) := td.k_eq
  have hrec : (R2 p).grp_record := by
    obtain ⟨plg, iso, -, h2, h3, h4⟩ := p.grpRecPin
    exact ⟨p.R.eG.trans p.cG, plg, iso, h2, h3, h4⟩
  have yb : ∀ {large₂ : SizeData₂ (Fm.D x i)} {Pm : ParameterChoice' (Fm.D x i) large₂}, ParamsT (Fm.D x i) large₂ Pm →
      LeafYBound (onOf (R2 p) (F2 p) c (supArgs (R2 p))) := fun {_ Pm} _ =>
    leafYBound (F := F2 p) c (supArgs (R2 p)) Pm
  refine ⟨?_, ?_⟩
  · have := leafLevelSq (F := F2 p) c (supArgs (R2 p)) hrec
    unfold LeafLevelSq
    rw [g1, g2]
    exact this
  · have := yb (Fm.parT x hx i)
    unfold LeafYBound OnObj.y
    rw [g1, g2, f1, k1]
    exact this
end GlobalTheory.BigOn
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafLevelSq_and_leafYBound : _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.BigOn.PageNumbers
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}
end GlobalTheory.BigOn.PageNumbers
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem pageSt_alt : _root_.GlobalTheory.BigOn.PageStatement := by
  refine (GlobalTheory.T.indexBoundParameterRequirements_eventually_family.and _root_.GlobalTheory.T.leafLevelSq_and_leafYBound).imp fun Fm CH _ H => ?_
  obtain ⟨⟨xs, hxs⟩, ⟨c1, hc1⟩⟩ := H
  refine ⟨max c1 1, fun c hc hB => ?_⟩
  obtain ⟨x2, hx2⟩ := hc1 c ((le_max_left _ _).trans hc) hB
  refine ⟨max (max xs x2) (3 * c.C), fun x hx hle i p hp hm r O hr => ?_⟩
  have hxs' : xs ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have hx2' : x2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have hxC : 3 * c.C ≤ x := (le_max_right _ _).trans hle
  have hR := hxs x hx hxs' i
  obtain ⟨hSq, hY⟩ := hx2 x hx hx2' i p hp hm r O hr
  have hE : ∀ C CH', ErrorConstantMatchesDefinition ((R2 p).num (F2 p) C CH') O C := fun C CH' => (GlobalTheory.BigOn.Check.twoRunDatum_boundUnit_at_indefinitePoint p (Fm.parT x hx i) r O hr C CH').1
  have hb : O.b = (Fm.L x i).sc.b := (GlobalTheory.BigOn.Check.twoRunDatum_boundUnit_at_indefinitePoint p (Fm.parT x hx i) r O hr 0 0).2
  obtain ⟨st, hd⟩ := hr.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  have hd' : GlobalTheory.RunDepth.RunTie p.T.toCore (Fm.ex x hx i).errX (Fm.parT x hx i) (Fm.ex x hx i).kap_def ({ O with de2 := (Fm.L x i).de2 } : Obj p c)
      (fun j : Fin (Fm.D x i).R.m => (j : ℕ) + 1) := { hd with }
  have hN : GlobalTheory.IndexAssembly.NumTie (Fm.parT x hx i) (Fm.ex x hx i).kap_def ({ O with de2 := (Fm.L x i).de2 } : Obj p c) :=
    ⟨hr.1.rr_eq, hr.1.realisedChain_torus_eq, hr.1.Nc_eq,
      hr.1.DF_eq.trans (congrArg (fun n : ℕ => (n : ℝ)) (PageNumbers.sup_fin_eq_topDeg _ _)), rfl, hr.1.pde_eq⟩
  have hx3 : 3 * c.C ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx]; exact hxC
  have hC : Formalism.L2.Indef.Tree.OnPage.ConstC c := (le_max_right _ _).trans hc
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.IndexAssembly.numericLeaves hd' hN hR hC hB hx3
  refine ⟨h1, h2, h3, h4, hSq, hY, hb, ?_, hE⟩
  have hx0 : 0 < (Fm.L x i).sc.x := by linarith [(Fm.L x i).sc.one_lt_alt]
  have e1 := Real.rpow_pos_of_pos hx0 (Fm.L x i).sc.eps
  have e2 := Real.rpow_pos_of_pos hx0 (-(Fm.L x i).sc.eps)
  change 0 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b *
    (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps + (Fm.L x i).Nc)
  have hb0 : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  positivity
end GlobalTheory.BigOn
end
end
end
