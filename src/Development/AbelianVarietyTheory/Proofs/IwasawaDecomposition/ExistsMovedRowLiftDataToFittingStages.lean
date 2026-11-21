import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStages

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Tr

theorem rowPsi_eq_of_psi {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl

theorem reps_parts_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → (∀ (Φ : Type) (rep : Φ → _), Reps y F rep → @Reps b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by exact rep))) ∧ (∀ bb π, HEq (@Hd.prtE b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb ((by exact π))) (y.prtE F bb π)) ∧ ∀ i π, HEq (@Hd.prtW b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) ((by exact i)) ((by exact π))) (y.prtW F i π) := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs
  letI := alg b iK
  have hY0 : (rowPsi a y'.PY).ψ = y.PY.ψ := (by with_unfolding_all exact ((eq_of_heq hs.PY) :))
  have hY : rowPsi a y'.PY = y.PY := rowPsi_eq_of_psi _ _ hY0
  have hW0 : (fun i => (rowPsi a (y'.PW i)).ψ) = (fun i => (y.PW i).ψ) := (by with_unfolding_all exact ((eq_of_heq hs.PW) :))
  have hW : ∀ i, rowPsi a (y'.PW i) = y.PW i := fun i => rowPsi_eq_of_psi _ _ (congrFun hW0 i)
  have hocc : HEq (y'.occ (face b F)) (y.occ F) := by
    unfold Hd.occ principalLevelFrame.OccRows principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.occ F)) :))
  have e : y'.occ (face b F) = y.occ F := (by with_unfolding_all exact ((eq_of_heq hocc) :))
  refine ⟨?_, ?_, ?_⟩
  · intro Φ rep h
    exact ⟨h.fin, fun π => by rw [e]; exact h.mem π, fun π π' hi => h.inj π π' hi, fun ρ hρ => h.all ρ (by rw [e] at hρ; exact hρ)⟩
  · intro bb π
    unfold Hd.prtE principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtE F bb π)) :))
  · intro i π
    unfold Hd.prtW
    rw [isotL_eq a b]
    delta isotLB
    rw [hW i]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtW F i π)) :))

end GlobalTheory.Mem.R3.Tr

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeRepresentativesParts_otherLaterStages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → (∀ (Φ : Type) (rep : Φ → _), Reps y F rep → @Reps b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by exact rep))) ∧ (∀ bb π, HEq (@Hd.prtE b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb ((by exact π))) (y.prtE F bb π)) ∧ ∀ i π, HEq (@Hd.prtW b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) ((by exact i)) ((by exact π))) (y.prtW F i π) := by
  first | exact @GlobalTheory.Mem.R3.Tr.reps_parts_tr | exact GlobalTheory.Mem.R3.Tr.reps_parts_tr | (intros; apply GlobalTheory.Mem.R3.Tr.reps_parts_tr <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 4000000 in

theorem chT_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (bb : Bool) (Φ : Type) (rep : Φ → _) (Top : C.Tup → Hs) (c : ChD C.Tup Φ B.R.m Top) jA (t : ChT y F bb rep (Top := Top) jA c) jA', HEq jA' jA → ∃ t' : @ChT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb Φ ((rep)) Top jA' c, letI := alg b iK; HEq t'.jE t.jE ∧ HEq t'.jM t.jM ∧ HEq t'.jX t.jX := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hS bb Φ rep Top c jA t jA' hjA
  have hP := (GlobalTheory.T.typeRepresentativesParts_otherLaterStages B C a b G Pl0 T Ks A R F y y' hS).2.1
  obtain ⟨htup, htupT, hPY, hPW⟩ := hS
  rcases y' with ⟨tup', tupT', tupT_tup', tup0', hm', hTop', hinj', PY', PW', ιW', isomFin', frameMatch', hF', stdPsi'⟩
  have e1 : tup' = (y.tup) := eq_of_heq ((htup))
  have e2 : tupT' = (y.tupT) := eq_of_heq ((htupT))
  subst e1 e2
  have e3 : jA' = (jA) := eq_of_heq ((hjA))
  subst e3
  have hCC := chain_CC b F y.tupT y.hm y.hTop
  have hCCX := chain_CCX b F y.tupT y.hm y.hTop
  have hCCP := chain_CCP b F y.tupT y.hm y.hTop
  have hCCXP := chain_CCXP b F y.tupT y.hm y.hTop
  have hEEc := chain_EEc b F y.tupT y.hm y.hTop
  letI := alg b iK
  refine ⟨{
    jE := (t.jE)
    jM := (t.jM)
    jX := (t.jX)
    jE_inj := (t.jE_inj)
    jE_range := by
      have e : LinearMap.range t.jE = _ := t.jE_range.trans (congrFun hEEc bb)
      exact (e)
    jE_ip := (t.jE_ip)
    jM_inj := (t.jM_inj)
    jM_range := fun μ hU j h1 h2 => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have h2a : j ≤ a.D.R.m - 1 := (h2)
      have e : LinearMap.range (t.jM μa j) = _ := (t.jM_range μa hUa j h1 h2a).trans (congrFun (congrFun (congrFun hCCP bb) μa) j)
      exact (e)
    jM_ip := (t.jM_ip)
    jX_inj := (t.jX_inj)
    jX_range := fun μ hU => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have e : LinearMap.range (t.jX μa) = _ := (t.jX_range μa hUa).trans (congrFun (congrFun hCCXP bb) μa)
      exact (e)
    jX_ip := (t.jX_ip)
    io0 := fun μ hU x v h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      let va : (c.Mult μa 1).T := (v)
      have e := congrFun (congrFun (congrFun hCC bb) μa) 1
      have h0 : t.jM μa 1 va ∈ (y.C F).CC bb μa 1 := cast (congrArg (t.jM μa 1 va ∈ ·) e.symm) ((h))
      have hv := chain_ioC b (R := R) (y.tupT μa) 0 (t.jM μa 1 va) ((h)) h0
      have e' := (t.io0 μa hUa x va h0).trans (congrArg (fun z => (y.C F).ipE bb (t.jE x) z) hv.symm)
      kexactB e'
    io := fun μ hU j h1 h2 x v h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have h2a : j + 1 ≤ a.D.R.m - 1 := (h2)
      let va : (c.Mult μa (j + 1)).T := (v)
      have e := congrFun (congrFun (congrFun hCC bb) μa) (j + 1)
      have h0 : t.jM μa (j + 1) va ∈ (y.C F).CC bb μa (j + 1) := cast (congrArg (t.jM μa (j + 1) va ∈ ·) e.symm) ((h))
      have hv := chain_ioC b (R := R) (y.tupT μa) j (t.jM μa (j + 1) va) ((h)) h0
      have e' := (t.io μa hUa j h1 h2a x va h0).trans (congrArg (fun z => (y.C F).ipP bb μa j (t.jM μa j x) z) hv.symm)
      kexactB e'
    ioTop := fun μ hU x v v' hvv h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      let va : (c.Mult μa a.D.R.m).T := (v)
      let va' : (c.Mult μa (a.D.R.m - 1 + 1)).T := (v')
      have hvva : HEq va' va := (hvv)
      have e := congrFun (congrFun hCCX bb) μa
      have h0 : t.jX μa (c.multTop μa va) ∈ (y.C F).CCX bb μa := cast (congrArg (t.jX μa (c.multTop μa va) ∈ ·) e.symm) ((h))
      have hv := chain_ioX b (R := R) y.hm y.hTop (y.tupT μa) (t.jX μa (c.multTop μa va)) ((topMult_tr b y.hTop)) ((h)) h0
      have e' := (t.ioTop μa hUa x va va' hvva h0).trans
        (congrArg (fun z => (y.C F).ipP bb μa (a.D.R.m - 1) (t.jM μa (a.D.R.m - 1) x) z) hv.symm)
      exact (e')
    junk := (t.junk)
    ft := fun π => by
      rw [eq_of_heq (hP bb (rep π))]
      exact (t.ft π)
    disj := fun π π' hne => by
      rw [eq_of_heq (hP bb (rep π)), eq_of_heq (hP bb (rep π'))]
      exact (t.disj π π' hne)
    top := (t.top) }, (HEq.refl t.jE), (HEq.refl t.jM), (HEq.refl t.jX)⟩

end GlobalTheory.Mem.R3.Rw
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainComparison_transfer_otherLaterStages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (bb : Bool) (Φ : Type) (rep : Φ → _) (Top : C.Tup → Hs) (c : ChD C.Tup Φ B.R.m Top) jA (t : ChT y F bb rep (Top := Top) jA c) jA', HEq jA' jA → ∃ t' : @ChT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb Φ ((rep)) Top jA' c, letI := alg b iK; HEq t'.jE t.jE ∧ HEq t'.jM t.jM ∧ HEq t'.jX t.jX := by
  first | exact @GlobalTheory.Mem.R3.Rw.chT_tr | exact GlobalTheory.Mem.R3.Rw.chT_tr | (intros; apply GlobalTheory.Mem.R3.Rw.chT_tr <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem hd_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (y : Hd R), ∃ y' : HdB b R, Same b y y' := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R y
  letI := alg b iK
  let y' : HdB b R :=
    { tup := (by with_unfolding_all exact (y.tup :))
      tupT := (by with_unfolding_all exact (y.tupT :))
      tupT_tup := (by with_unfolding_all exact (y.tupT_tup :))
      tup0 := (by with_unfolding_all exact (y.tup0 :))
      hm := (by with_unfolding_all exact (y.hm :))
      hTop := topMult_tr b y.hTop
      hinj := inj_tr b y.hinj
      PY := (by with_unfolding_all exact ((rowPsi b y.PY) :))
      PW := fun i => (by with_unfolding_all exact ((rowPsi b (y.PW i)) :))
      ιW := (by with_unfolding_all exact (y.ιW :))
      isomFin := fun i => ⟨(by with_unfolding_all exact ((y.isomFin i).bij :)), (by with_unfolding_all exact ((y.isomFin i).conj :)), (by with_unfolding_all exact ((y.isomFin i).lat :))⟩
      frameMatch := (by with_unfolding_all exact (y.frameMatch :))
      hF := (by with_unfolding_all exact (y.hF :))
      stdPsi := (by with_unfolding_all exact (y.stdPsi :)) }
  exact ⟨y', ⟨(by with_unfolding_all exact ((HEq.refl y.tup) :)), (by with_unfolding_all exact ((HEq.refl y.tupT) :)), (by with_unfolding_all exact ((HEq.refl y.PY.ψ) :)), (by with_unfolding_all exact ((HEq.refl fun i => (y.PW i).ψ) :))⟩⟩

end GlobalTheory.Mem.R3.Rw

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem frame_eq_of_map_eq {D : D7} {V : HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl

set_option maxHeartbeats 8000000 in

theorem lfT_of_same : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs Φ rep Mt l jL t jL' hj
  obtain ⟨tup', tupT', _, _, _, _, _, ⟨ψY, _, _, _⟩, PW', ιW', _, _, _, _⟩ := y'
  obtain ⟨h1, h2, h3, h4⟩ := hs
  obtain rfl : tup' = (by with_unfolding_all exact (y.tup :)) := eq_of_heq h1
  obtain rfl : tupT' = (by with_unfolding_all exact (y.tupT :)) := eq_of_heq h2
  obtain rfl : ψY = (by with_unfolding_all exact (y.PY.ψ :)) := eq_of_heq h3
  have e4 : (fun i => (PW' i).ψ) = (by with_unfolding_all exact ((fun i => (y.PW i).ψ) :)) := eq_of_heq h4
  obtain rfl : PW' = fun i => rowPsi b (y.PW i) :=
    funext fun i => frame_eq_of_map_eq _ _ ((by with_unfolding_all exact ((congrFun e4 i) :)))
  obtain rfl : jL' = (by with_unfolding_all exact (jL :)) := eq_of_heq hj
  letI := alg b iK
  refine ⟨{
    eW := (by with_unfolding_all exact (t.eW :))
    eW_range := fun i => (by with_unfolding_all exact (((t.eW_range i).trans (by rw [wat_eq b R])) :))
    eW_norm := (by with_unfolding_all exact (t.eW_norm :))
    eW_lat := (by with_unfolding_all exact (t.eW_lat :))
    jMj := (by with_unfolding_all exact (t.jMj :))
    jMj_read := (by with_unfolding_all exact (t.jMj_read :))
    jMj_inj := (by with_unfolding_all exact (t.jMj_inj :))
    jMj_range := fun i => (by with_unfolding_all exact (((t.jMj_range i).trans (congrFun (lift_Wc b F y.tupT y.hm y.hTop y.hinj) i)) :))
    jMj_ip := (by with_unfolding_all exact (t.jMj_ip :))
    jMt := (by with_unfolding_all exact (t.jMt :))
    jMt_inj := (by with_unfolding_all exact (t.jMt_inj :))
    jMt_range := (by with_unfolding_all exact (t.jMt_range :))
    jMt_ip := (by with_unfolding_all exact (t.jMt_ip :))
    theta := fun μ hμ i x h w hw1 he hw2 => by
      have hw1' : ((by with_unfolding_all exact (w :)) : (y.L F).AmbW i) ∈ (toLiftReal R F y.tupT y.hm y.hTop y.hinj).MultW i := by
        rw [lift_MultW b F y.tupT y.hm y.hTop y.hinj]; exact (by with_unfolding_all exact (hw1 :))
      have hw2' : (y.L F).eW i ∘ₗ ((by with_unfolding_all exact (w :)) : (y.L F).AmbW i) ∈ (toLiftReal R F y.tupT y.hm y.hTop y.hinj).Wc i := by
        rw [lift_Wc b F y.tupT y.hm y.hTop y.hinj]; exact (by with_unfolding_all exact (hw2 :))
      exact (by with_unfolding_all exact ((t.theta ((μ)) ((hμ)) ((i)) ((x)) ((h)) ((w)) hw1' ((he)) hw2') : _))
    junk := (by with_unfolding_all exact (t.junk :))
    out := (by with_unfolding_all exact (t.out :))
    isot := fun i π v => by
      unfold Hd.prtW
      rw [isotL_eq a b]
      kexactB (t.isot i π v)
    disj := fun i π π' hne => by
      unfold Hd.prtW
      rw [isotL_eq a b]
      kexactB (t.disj i π π' hne)
    read := (by with_unfolding_all exact (t.read :)) }, (by with_unfolding_all exact ((HEq.refl t.eW) :)), (by with_unfolding_all exact ((HEq.refl t.jMt) :))⟩

end GlobalTheory.Mem.R3.Rw
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  first | exact @GlobalTheory.Mem.R3.Rw.lfT_of_same | exact GlobalTheory.Mem.R3.Rw.lfT_of_same | (intros; apply GlobalTheory.Mem.R3.Rw.lfT_of_same <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m) (R : RealDat3 a.D A3 Ks) (F : Face3 a.D A3), letI := alg b iK; (∀ j v, etaOf (real3 b R) (face3 b F) j v = etaOf R F j ((by with_unfolding_all exact (v :)))) ∧ ∀ (y : Hd R.toRealDat) (y' : Hd (real3 b R).toRealDat) (bb : Bool) (E : Hs) jE jE' n c Xo, HEq jE' jE → RrT F y bb (E := E) jE n c Xo → RrT (face3 b F) y' bb (E := E) jE' n c ((by with_unfolding_all exact (Xo :))) := by
  first | exact @GlobalTheory.Mem.R3.Rw.rr_eta_tr | exact GlobalTheory.Mem.R3.Rw.rr_eta_tr | (intros; apply GlobalTheory.Mem.R3.Rw.rr_eta_tr <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Mv

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

def sameGrp {f : Fr B.toPre} (h : GrpTrue a.N f) (h' : GrpTrue b.N f) : SameGrp a b where
  e k := (by with_unfolding_all exact ((plEquiv a.N.naut b.N.naut k) :))
  pl k v := (by with_unfolding_all exact ((TypesTrue.plGw_plEquiv h h' k v) :))
  e0 g := (by with_unfolding_all exact ((h.typeIdempotent_coeff_across_layers h' g) :))

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by with_unfolding_all exact ((alg b z.alg) :))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

theorem levOf_tr {U : Set I.ι} {L : Links.LevCh a.D (TupU I U)} (h : LevOf a.st I U L) : LevOf b.st I U (levCh b L) := by
  constructor
  case is => exact (by with_unfolding_all exact ((levIs_tr b h.is) :))
  case C => exact (by with_unfolding_all exact ((congrArg (chFr b) h.C) :))
  case xiH => exact (by with_unfolding_all exact (h.xiH :))
  case Pg => exact (by with_unfolding_all exact (h.Pg :))
  case Q => exact (by with_unfolding_all exact (h.Q :))
  case beta => exact (by with_unfolding_all exact (h.beta :))

theorem goodSet_tr (s : SameGrp a b) {eR : Gc B px ≃* G0g a.D.nd} {Xg : Finset (Gc B px → B.LL)}
    (h : GoodSet a.st (px := px) eR Xg) : GoodSet b.st (px := px) (eR.trans s.iso) Xg := by
  have e : (fun g => a.D.ntypes.e0.coeff (eR g)) = fun g => b.D.ntypes.e0.coeff ((eR.trans s.iso) g) :=
    funext fun g => (s.e0 (eR g)).symm
  refine (goodSet_iff b.st (px := px) _ Xg).2 ?_
  tr_via (fun c : Gc B px → ℂ => (∀ χ : Gc B px → B.LL, χ ∈ Xg ↔ IsAbsIrrChar χ ∧
    ∑ g : Gc B px, c g * B.embLL (χ g) = B.embLL (χ 1)) ∧ ∀ g, B.embLL ((idemOf Xg).coeff g) = c g) e
    ((goodSet_iff a.st (px := px) eR Xg).1 h)

def cpDat (s : SameGrp a b) (z : Dat a.st I hX T Wt) : Dat b.st I hX T Wt :=
  @Dat.mk b.st px I hX T Wt
    (Xg := z.Xg)
    (tr := z.tr)
    (core := coreJ b z.core)
    (alg := (by with_unfolding_all exact ((alg b z.alg) :)))
    (alg_eq := (by with_unfolding_all exact (z.alg_eq :)))
    (R := cpR b z)
    (cG := (by with_unfolding_all exact ((z.cG.trans s.iso) :)))
    (geo := (by with_unfolding_all exact ((geoHalf b (iK := z.alg) z.geo) :)))
    (pins := (by with_unfolding_all exact ((pins_tr b (iK := z.alg) s z.pins) :)))
    (lev := (by with_unfolding_all exact ((levOf_tr b z.lev) :)))
    (idG := (by with_unfolding_all exact (z.idG :)))
    (good := (by with_unfolding_all exact ((goodSet_tr b s z.good) :)))
    (mu := (by with_unfolding_all exact (z.mu :)))
    (fieldValues_mem_fixedField := (by with_unfolding_all exact (z.fieldValues_mem_fixedField :)))
    (Ks_le := (by with_unfolding_all exact (z.Ks_le :)))

theorem lawsCore_tr {K : Formalism.L2.Pj.Core a.D} (h : Formalism.L2.Pj.LawsCore K) : Formalism.L2.Pj.LawsCore (core b K) := by
  constructor
  case toLawsM => exact (by with_unfolding_all exact ((lawsM_tr b h.toLawsM) :))
  case cuspMul => exact (by with_unfolding_all exact (h.cuspMul :))
  case latZ => exact (by with_unfolding_all exact (h.latZ :))
  case cuNe => exact (by with_unfolding_all exact (h.cuNe :))
  case expo => exact (by with_unfolding_all exact (h.expo :))

variable (s : SameGrp a b) (z : Dat a.st I hX T Wt)

theorem cp_holds (h : Holds z.R z.F) : Holds (cpDat b s z).R (cpDat b s z).F := (by with_unfolding_all exact ((holds_tr b (iK := z.alg) h) :))

theorem cp_exAt (h : z.R.toRealDat.ExAt) : (cpDat b s z).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr b (iK := z.alg) h) :))

theorem cp_inGeo (h : GlobalTheory.RealGeo.InGeo z.geo) : GlobalTheory.RealGeo.InGeo (cpDat b s z).geo := (by with_unfolding_all exact ((inGeo_tr b (iK := z.alg) h) :))

theorem cp_canon (h : z.core.Q.Canon) : (cpDat b s z).core.Q.Canon := (by with_unfolding_all exact (h :))

theorem forcedContentPlaces_eq_transport_sameFiniteGroup (F0) : (cpDat b s z).W1 F0 = z.W1 ((F0)) :=
  (by with_unfolding_all exact ((congrArg (fun X : Cx.CxData (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).fam3.amb3 =>
    {w : B.places.Pl | ∃ j, ∃ w' ∈ ({a.D.plEq w, Formalism.DivisionValues.conjPl (a.D.plEq w)} : Set (HeightOneSpectrum (𝓞 a.D.what₂.LL))),
    (X.data z.F.cr false).Iw j (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
    Formalism.DivisionValues.jw (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).HT j
              (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
      (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).Tl j
        (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ ((F0) : HeightOneSpectrum (𝓞 a.D.what₂.LL) → Fin a.D.R.m → ℝ) w' j ≠ 0})
    (toCx3_eq b (iK := z.alg) z.R z.F).symm) : _))

section Read

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def fixTup {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m} {R : RealDat a.D A Ks} (y : Hd R) (y' : HdB b R) : HdB b R :=
  letI := alg b iK
  { y' with tup := (by with_unfolding_all exact (y.tup :)), tupT := (by with_unfolding_all exact (y.tupT :)), tupT_tup := (by with_unfolding_all exact (y.tupT_tup :)), tup0 := (by with_unfolding_all exact (y.tup0 :)) }

theorem fixTup_same {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m} {R : RealDat a.D A Ks} {y : Hd R} {y' : HdB b R} (h : Same b y y') :
    Same b y (fixTup b y y') :=
  ⟨(by with_unfolding_all exact ((HEq.refl y.tup) :)), (by with_unfolding_all exact ((HEq.refl y.tupT) :)), (by with_unfolding_all exact (h.PY :)), (by with_unfolding_all exact (h.PW :))⟩

variable {A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m} {R : RealDat3 a.D A3 Ks} (F : Face3 a.D A3) (y : Hd R.toRealDat)
  (y' : HdB b R.toRealDat)

def hd3 : letI := alg b iK; Hd (real3 b R).toRealDat := (by with_unfolding_all exact ((fixTup b y y') :))

def mCp (mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G) : Bool → b.D.what₂.Tup → Mat1 b.D.what₂.LL G := (by with_unfolding_all exact (mA :))

def pCp (p : PkD a.D G) : PkD b.D G := (by with_unfolding_all exact (p :))

theorem dall_tr {n : ℕ} (h : n = Module.finrank ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
    (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))))) : letI := alg b iK
    n = Module.finrank ℂ (Mult.Mult (real3 b R).θ ((real3 b R).MY 0)
      (levS _ ((real3 b R).βY 0) ((real3 b R).dat0 ((real3 b R).toRealDat.levR (face3 b F).lv2 true)))
      (levChi _ ((real3 b R).βY 0) ((real3 b R).dat0 ((real3 b R).toRealDat.levR (face3 b F).lv2 true)))) := by
  tr_via (fun m : type_of% (@Mult.Mult a.D) => n = Module.finrank ℂ (m R.θ (R.MY 0)
    (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))))
    (mult_eq b a) h

set_option maxHeartbeats 1000000 in

theorem pkT_tr (hs : Same b y y') {mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G} {p : PkD a.D G} (t : PkT F y mA p) :
    letI := alg b iK
    ∃ t' : PkT (R := real3 b R) (face3 b F) (hd3 b y y') (mCp b mA) (pCp b p),
      HEq t'.tA t.tA ∧ HEq t'.rep t.rep ∧ (∀ c, HEq (t'.ch c).jE (t.ch c).jE) ∧ (∀ c, HEq (t'.ch c).jM (t.ch c).jM) ∧
        (∀ c, HEq (t'.ch c).jX (t.ch c).jX) ∧ HEq t'.lf.eW t.lf.eW ∧ HEq t'.lf.jMt t.lf.jMt := by
  letI := alg b iK
  have hs' := fixTup_same b hs
  have h1 := (GlobalTheory.T.typeRepresentativesParts_otherLaterStages B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs').1 p.Φ t.rep t.reps
  have h2 := fun c => GlobalTheory.T.chainComparison_transfer_otherLaterStages B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' c p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ => (p.sA c μ).A) :))) ((by with_unfolding_all exact ((p.ch c) :))) ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :))) ((by with_unfolding_all exact ((t.ch c) :)))
    ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x)) :)))
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ j => (p.sL μ j).A) :))) ((by with_unfolding_all exact (p.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :))) ((by with_unfolding_all exact (t.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x)) :)))
  have h4 := (GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B C a b G Pl0 I0 T₀ Ks A3 R F).2 y (hd3 b y y') true (p.ch true).EE (t.ch true).jE
    ((by with_unfolding_all exact ((h2 true).choose.jE :))) p.nR p.cR p.Xo ((by with_unfolding_all exact ((h2 true).choose_spec.1 :))) t.rr
  refine ⟨{ rep := (by with_unfolding_all exact (t.rep :))
            reps := (by with_unfolding_all exact (h1 :))
            tA := (by with_unfolding_all exact (t.tA :))
            lawsA := (by with_unfolding_all exact (t.lawsA :))
            lawsL := (by with_unfolding_all exact (t.lawsL :))
            hA := (by with_unfolding_all exact (t.hA :))
            hL := (by with_unfolding_all exact (t.hL :))
            ch := fun c => (by with_unfolding_all exact ((h2 c).choose :))
            lf := (by with_unfolding_all exact (l :))
            dall := (by with_unfolding_all exact ((dall_tr b F t.dall) :))
            rr := (by with_unfolding_all exact (h4 :)) }, ?_, ?_, fun c => ?_, fun c => ?_, fun c => ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl t.tA) :))
  · exact (by with_unfolding_all exact ((HEq.refl t.rep) :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.2 :))
  · exact (by with_unfolding_all exact (hl1 :))
  · exact (by with_unfolding_all exact (hl2 :))

end Read

set_option maxHeartbeats 1000000 in

theorem exists_moved : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Holds z₀.R z₀.F →
    z₀.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z₀.geo → GrpTrue Z₀.N f → o.Fits → ∃ m : Moved o, m.Copy ∧ m.Coh := by
  intro B f T w Z₀ hX Wt z₀ q o h1 h2 h3 h4 h5
  have s : SameGrp (B := B) (C := w.C) Z₀ o.Z := sameGrp o.Z h4 h5.grp
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C Z₀ o.Z _ _ _ _ _ _ _ _ z₀.alg _ z₀.R.toRealDat q.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := pkT_tr (a := Z₀) o.Z (iK := z₀.alg) z₀.F q.y y' hy q.t
  have he := (@GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B w.C Z₀ o.Z _ _ _ _ _ _ _ _ _ z₀.alg _ z₀.R z₀.F).1
  letI : Algebra z₀.core.Q.c.F (Late.D o.Z).what₂.LL := alg (a := Z₀) o.Z z₀.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% q.t.tA) = q.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have hs := fixTup_same (a := Z₀) o.Z (iK := z₀.alg) hy
  refine ⟨{ z := cpDat (a := Z₀) o.Z s z₀
            intersectionNumber_baseChange := cp_holds (a := Z₀) o.Z s z₀ h1
            exAt := cp_exAt (a := Z₀) o.Z s z₀ h2
            inGeo := cp_inGeo (a := Z₀) o.Z s z₀ h3
            Xg := rfl
            tr := rfl
            core := fun h => ⟨(by with_unfolding_all exact ((lawsCore_tr (a := Z₀) o.Z h.1) :)), cp_canon (a := Z₀) o.Z s z₀ h.2.1, (by with_unfolding_all exact (h.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2 :))⟩
            eta := (by with_unfolding_all exact (he :))
            W1 := (by with_unfolding_all exact ((forcedContentPlaces_eq_transport_sameFiniteGroup (a := Z₀) o.Z s z₀) :))
            y := (by with_unfolding_all exact ((hd3 (a := Z₀) o.Z (iK := z₀.alg) q.y y') :))
            tup := (by with_unfolding_all exact (q.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := fun c u => (by with_unfolding_all exact ((heq_of_eq (congrArg (fun r : type_of% q.t.tA => (r c ((u))).j) hA)) : _)) }, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact ((HEq.refl (coreJ (a := Z₀) o.Z z₀.core)) :))
  · exact (by with_unfolding_all exact ((HEq.refl (real3 (a := Z₀) o.Z (iK := z₀.alg) z₀.R)) :))
  · exact (by with_unfolding_all exact ((HEq.refl q.y.tupT) :))
  · exact (by with_unfolding_all exact (hy.PY :))
  · exact (by with_unfolding_all exact (hy.PW :))
  · exact (by with_unfolding_all exact (a2 :))
  · exact (by with_unfolding_all exact (a3 :))
  · exact (by with_unfolding_all exact (a4 :))
  · exact (by with_unfolding_all exact (a5 :))
  · exact (by with_unfolding_all exact (a6 :))
  · exact (by with_unfolding_all exact (a7 :))

end GlobalTheory.Mem.R3.Rw.Mv

end
end
