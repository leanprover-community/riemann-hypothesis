import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistOfDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistOfDiscreteSeries
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjTwOfOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjTupleAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjTupleAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjIdealEqCP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjCoefAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjCoefAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveMapToAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveMapToAbelian

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
section Lev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Lev
section Laws
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} {j : Fin D.R.m}
end Laws
section Point
open Classical in
def TwLevAtAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ ρ ρ' : Setup (Fm.D x i).ntw, ρ.Good → ρ'.Good → RealPin p.R p.cG ρ →
  SameBut ρ ρ' → (Adapted p w ρ ∨ Adapted p w ρ') →
  ∃ (χ χ' : Formalism.L2.Host.HChar (Fm.D x i).host.E) (xiR xiR' : ∀ PP : Pl (Fm.D x i).host.E, (kP PP)ˣ →* ℂˣ),
    TwLev p.R.toRealDat χ ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q) xiR ∧
    TwLev p.R.toRealDat χ' ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ').Q) xiR' ∧
    χ ≠ 1 ∧ χ' ≠ 1 ∧ (χ ≠ χ' ∨ (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi =
      (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)
end Point
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open GlobalTheory.BigOn.Exp.TwConj GlobalTheory.IdemSupport
open Formalism.L2.Host (HChar IsDelta IsPsi)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj.LevAt
section Places
variable {D : D7}
end Places
section Transfer
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Transfer
section Chars
variable {D : D7}
variable {q l : ℕ} {δ ψ : HChar D.host.E} {Q : Finset (Pl D.host.E)}
end Chars
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}
end Point
end GlobalTheory.BigOn.Exp.TwConj.LevAt
namespace GlobalTheory.BigOn.Exp.TwConj
open LevAt in
theorem twLevAt_holds_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter →
    _root_.GlobalTheory.BigOn.Exp.TwConj.TwLevAtAlt := fun _ _ _ hA hC => by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hC _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt)) fun Fm x hx i p hr hm w hw j H => ?_
  obtain ⟨⟨a1, -, -⟩, a2, a3⟩ := H
  intro ρ ρ' hρ hρ' hp hs hA
  have hl := ((Fm.D x i).ntw.lPrime ((Fm.ex x hx i).nch.twI w)).out
  have hlow : ∀ P ∈ (Fm.ex x hx i).nch.Q w,
      (((Fm.D x i).host.pde * (Fm.D x i).host.pde' : ℕ) : 𝓞 (Fm.D x i).host.E) ∉ P.asIdeal := fun P hP h => by
    refine Finset.disjoint_left.1 a1.2.1 hP (a3 P ?_)
    rw [mul_assoc _ (Fm.D x i).host.pde, ← mul_assoc, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ h
  have pw : ∀ σ σ' : Setup (Fm.D x i).ntw, σ.Good → Adapted p w σ → σ'.rc = σ.rc →
      ∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w σ').chi (p.Tp.psi w ^ (a + 1)) := fun σ σ' hσ hσA e => by
    obtain ⟨a, ha, h⟩ := exists_pow e ((Fm.ex x hx i).nch.sd w) a1
    rcases a with _ | a
    · exact absurd (Nat.coprime_zero_left _ |>.1 ha) hl.one_lt.ne'
    · exact ⟨a, ha, by rw [twW, h]; exact chrEq_pow (a2 σ hσ hσA).1 a⟩
  obtain ⟨⟨a, ha, hc⟩, a', ha', hc'⟩ : (∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w ρ).chi (p.Tp.psi w ^ (a + 1))) ∧
      ∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w ρ').chi (p.Tp.psi w ^ (a + 1)) :=
    hA.elim (fun h => ⟨pw ρ ρ hρ h rfl, pw ρ ρ' hρ h hs.1⟩) fun h => ⟨pw ρ' ρ hρ' h hs.1.symm, pw ρ' ρ' hρ' h rfl⟩
  obtain ⟨xiR, h1⟩ := twLev_pow hm.2.2 p.charW.base.fam p.qGuard hw j hlow hρ hp ha hc
  obtain ⟨xiR', h2⟩ := twLev_pow hm.2.2 p.charW.base.fam p.qGuard hw j hlow hρ hp ha' hc'
  have hQ : (twW (Fm.ex x hx i) w ρ').Q = half (ρ.ch ((Fm.ex x hx i).nch.twI w)) ((Fm.ex x hx i).nch.Q w) := by
    simp only [Setup.tw, twistOf, hs.2.1]
  obtain ⟨q, hq, hδ, -⟩ := exists_delta p.R.C ((Fm.ex x hx i).nch.twI w)
  obtain ⟨v, hv⟩ := exists_over (D := Fm.D x i) hq
  have hψ := p.Tp.psi_is w ((p.tw_iff w).1 hw)
  rw [← (Fm.ex x hx i).nch.twI_l] at hψ
  have hne : ∀ n : ℕ, p.R.C.delAt ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) * p.Tp.psi w ^ n ≠ 1 := fun n e =>
    not_unr hδ hψ hl n hv (by rw [e]; exact fun _ _ => rfl)
  refine ⟨_, _, xiR, xiR', h1, hQ ▸ h2, hne _, hne _, or_iff_not_imp_left.2 fun e => ?_⟩
  rw [Ne, not_not] at e
  exact GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ h1.xi (e ▸ h2.xi)
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
open Classical in
theorem tupAt_alt (h1 : GlobalTheory.Published.CuspRapidDecay) (h2 : GlobalTheory.Published.GlobalArtinReciprocity) (h3 : GlobalTheory.Published.RayClassFieldSt)
    (h4 : GlobalTheory.Published.DiscreteSeriesCover) (h5 : GlobalTheory.Published.CasselmanWallach) (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hC : _root_.GlobalTheory.BigOn.Exp.TwistCharacter) : _root_.GlobalTheory.BigOn.Exp.TwConj.TupleCondition := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt) (_root_.GlobalTheory.BigOn.Exp.TwConj.twLevAt_holds_alt h1 h2 h3 hA hC)) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨hadm, hlow⟩, hlev⟩ := H
  intro ρ ρ' hρ hρ' hp hS hAd
  have H0 := _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hr hm _ hadm.2.2 hlow j
  have hB : BaseOf p.R.toRealDat j (baseW (Fm.ex x hx i) w j ρ) := baseOf_of_realPin H0.core.lev hρ hp _ j _
  have hLaws : Laws p.T p.R.toRealDat (F2 p) p.κ p.v₀ p.O (phs p) j (baseW (Fm.ex x hx i) w j ρ) :=
    ⟨H0.core, H0.fin, H0.fw, H0.io, H0.guard, H0.pins, H0.phase, hB⟩
  obtain ⟨χ, χ', xiR, xiR', hT, hT', hne, hne', hd⟩ := hlev ρ ρ' hρ hρ' hp hS hAd
  obtain ⟨A0, R0, F0, v0, O0, hL0, hE0, hxi0, htr⟩ := GlobalTheory.BaseRestrict.restrict_to_base _ _ _ _ _ _ _ _ _ hLaws
  have hT0 := htr _ _ _ _ hT
  have hT0' := htr _ _ _ _ hT'
  have hQ : (twW (Fm.ex x hx i) w ρ').Q = (twW (Fm.ex x hx i) w ρ).Q := by simp only [Setup.tw, twistOf, hS.2.1]
  have hQde : ∀ (N : Type) (Qn : N → Finset (Pl (Fm.D x i).host.E)),
      (∀ n, Qn n = (baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q) →
      ∀ q ∈ ({(Fm.D x i).host.pde, (Fm.D x i).host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 (Fm.D x i).host.K),
        (∀ t, ∀ PP ∈ R0.Q t, ((q : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ PP.asIdeal → PP.under (𝓞 (Fm.D x i).host.K) = 𝔭) ∧
          ∀ n, ∀ PP ∈ Qn n, ((q : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ PP.asIdeal → PP.under (𝓞 (Fm.D x i).host.K) = 𝔭 := by
    intro N Qn hQn q hq
    obtain ⟨𝔭, h𝔭, h𝔭'⟩ := hT0.Q_de q hq
    exact ⟨𝔭, h𝔭, fun n => (hQn n).symm ▸ h𝔭'⟩
  rcases hd with hd | hd
  · obtain ⟨T', A', R', F', v', O', hL', hE', htup⟩ := GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws h1 h2 h3 h4 h5 p.T R0 F0 p.κ v0 O0 (phs p) j _ p.host hL0 Bool
      (fun b => if b then χ' else χ)
      (fun b => if b then (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi
        else (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi)
      (fun b => if b then (baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ').Q
        else (baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q)
      (fun b => if b then xiR' else xiR)
      (fun b => by cases b <;> assumption)
      (fun a b hab => by
        cases a <;> cases b
        · rfl
        · exact absurd hab hd
        · exact absurd hab.symm hd
        · rfl)
      (fun b t => by rw [hxi0]; cases b; exacts [hne, hne'])
      (hQde Bool _ fun b => by cases b <;> simp [hQ])
    obtain ⟨t, ht1, ht2⟩ := htup false
    obtain ⟨t', ht1', ht2'⟩ := htup true
    exact hasTuples_of_laws hL' (hE0.trans hE') (t := t) (t' := t') ⟨ht1, ht2⟩ ⟨ht1', ht2'⟩
  · obtain ⟨T', A', R', F', v', O', hL', hE', htup⟩ := GlobalTheory.T.realisation_extends_by_newTuples_keeping_laws h1 h2 h3 h4 h5 p.T R0 F0 p.κ v0 O0 (phs p) j _ p.host hL0 Unit
      (fun _ => χ) (fun _ => (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi)
      (fun _ => (baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q) (fun _ => xiR)
      (fun _ => hT0) (fun _ _ _ => rfl) (fun _ t => by rw [hxi0]; exact hne) (hQde Unit _ fun _ => rfl)
    obtain ⟨t, ht1, ht2⟩ := htup ()
    exact hasTuples_of_laws hL' (hE0.trans hE') (t := t) (t' := t) ⟨ht1, ht2⟩ ⟨ht1.trans hd, ht2.trans (by rw [hQ])⟩
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_tuple_at' : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwConj.TupleCondition := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.TwConj.tupAt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
open GlobalTheory.ConjTwist
theorem fixAt_holds_alt : GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition := by
  intro hRF hA
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt) fun Fm x hx k p hr hm w _ j H => ?_
  intro ρ hρ hp hL τ hτ
  have hR := _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx k p hr hm _ H.1.2.2 H.2 j
  have hτ' : ∀ z ∈ (Formalism.L2.Host.embLL0 (Fm.D x k)).fieldRange, τ z = z := by
    rintro _ ⟨y, rfl⟩
    exact hτ y
  have hFB : FixBase p.T p.R.toRealDat j τ :=
    GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField _ _ _ _ _ _ hRF p.T p.R p.cG p.Sx p.nexp (F2 p) p.κ p.v₀ hR.laws hR.core hR.fw hR.tieIn hR.galois
      hR.small.val hR.small.ray hR.small.roots j τ hτ'
  refine ⟨hFB, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := de_chi_eq hρ ((Fm.ex x hx k).nch.twI w) j ((Fm.ex x hx k).nch.sd w) y
    change τ (((ρ.B _ j _).de.chi y : Circle) : ℂ) = _
    rw [hσ]
    refine GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values ρ hρ _ j _ (p.R.C.delAt ((Fm.D x k).ntw.l ((Fm.ex x hx k).nch.twI w))) (hp.delta _ j _) ?_ τ hτ σ
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [hR.small.val.del', hR.small.val.del]
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := (ρ.eG ((Fm.ex x hx k).nch.twI w) j ((Fm.ex x hx k).nch.sd w)).surjective q
    obtain ⟨g, rfl⟩ := (p.R.eG.trans p.cG).surjective y
    have hg := (mem_level_iff hm.2.2 hL _ j _ g).1 hq
    obtain ⟨z, hz⟩ := (level_chi hm.2.2 hρ hL _ j _ ⟨g, hg⟩ hq).2
    change τ ((((ρ.B _ j _).G.P.chi ⟨_, hq⟩ : ℂˣ) : ℂ)) = _
    rw [← hz]
    exact hτ z
  · exact (baseOf_of_realPin hR.core.lev hρ hp _ j _).fix_mu hR.core.lev (hρ.base _ j _) hFB.chi
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_fix_at' : GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.TwConj.fixAt_holds_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
open GlobalTheory.ConjTwist
set_option maxHeartbeats 4000000 in
theorem coefAt_of_twAdm_alt : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.CoefficientCondition := by
  intro hA
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨-, -, hin⟩, hlow⟩ := H
  have hR := _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hr hm _ hin hlow j
  intro ρ ν hρ hp hN
  obtain ⟨hν0, c₀, hsc, n, hn, hνn⟩ := hN
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hsc
  obtain ⟨c, hc⟩ := GlobalTheory.ExtCoeff.exists_extC _ _ _ _ _ _ _ j Unit (fun _ => p.P.A3.A.μ0) (p.O j)
  have hB := hρ.base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hBo := baseOf_of_realPin hR.core.lev hρ hp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have H1 := GlobalTheory.CoefLatConj.coefLat_conj (Fm.D x i) _ _ _ p.P.A3.A p.T p.R.toRealDat (F2 p) p.κ p.v₀ p.O hR.core hR.fw hR.io j
    hR.pins c hc u hu _ hB hBo
  obtain ⟨κ, hκ0, hκ, H2⟩ := H1
  have hspan := (H2.2 _ (Formalism.L2.Host.embLL0 _) (labLL0 _) (smallInt _) (smallInt_isCoefRing _)).1
  have hO : OMPins p.T p.R.toRealDat p.κ p.v₀ p.O j := hR.pins
  have hfield := hO.2.lift.field
  have hc0 := hO.2.lift.c0
  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hc0
  have hcL : ∀ F : VV (Fm.D x i).what₂.LL (lamV (Fm.D x i) j),
      c (GlobalTheory.CoefModel.mapVV (Fm.D x i).what₂.embLL (lamV (Fm.D x i) j) F) = c0L j F := fun F => by
    obtain ⟨v', hv', hv0⟩ := hbc F
    refine (hc v' _ ?_).trans hv0
    change MvPolynomial.map (Fm.D x i).what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]
  have hκs : IsScale p.R p.v₀ (baseW (Fm.ex x hx i) w j ρ) κ := ⟨gramR, c0R, c0L, hft, u, hu, fun F =>
    (congrArg (fun z => harmFn _ _ _ (p.R.ioP j (PiTensorProduct.tprod ℂ u) z)) (hcL F)).symm.trans
      ((hκ _).trans (congrArg (κ • ·) (coefFn_map_eq _ _ _)))⟩
  obtain ⟨k, hk, hkk⟩ := scale_pow_eq_of_isScale p.R p.v₀ _ hsc hκs
  have hφc : phs p j * c₀ ≠ 0 := fun h0 => hν0 ((pow_eq_zero_iff hn).1 (hνn.trans (by rw [h0, zero_pow hn])))
  have hφ : phs p j ≠ 0 := left_ne_zero_of_mul hφc
  refine ⟨c, u, ν / (phs p j * κ), hc, hu, ⟨n * k, Nat.pos_of_ne_zero (Nat.mul_ne_zero hn hk), ?_⟩, ?_⟩
  · have e : ν ^ (n * k) = (phs p j * κ) ^ (n * k) := by
      rw [pow_mul, hνn, ← pow_mul, mul_pow, mul_pow, mul_comm n k, pow_mul c₀, pow_mul κ, hkk]
    rw [div_pow, e, div_self (pow_ne_zero _ (mul_ne_zero hφ hκ0))]
  · intro h₀ P hP
    obtain ⟨y, hPy, hy⟩ := exists_fixed_of_mem_span j (p.R.ioP j (PiTensorProduct.tprod ℂ u)) c κ⁻¹ _
      ((hspan (finPt _ h₀)).le hP)
    refine ⟨y, ?_, hy⟩
    have e : ν * κ⁻¹ = ν / (phs p j * κ) * phs p j := by field_simp
    exact (congrArg (ν • ·) hPy).trans ((smul_smul ν κ⁻¹ _).trans (congrArg (· • _) e))
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_coef_at' : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwConj.CoefficientCondition := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.TwConj.coefAt_of_twAdm_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ConjExpandRational
end GlobalTheory.ConjExpandRational
theorem GlobalTheory.ConjExpandRational.exists_evW_expansion_of_conjFun : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ τ : ℂ ≃+* ℂ,
  (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
  ∀ Φ Φ' : GA (Fm.D x i) (Wc (Fm.D x i) j) → ℂ, GlobalTheory.ConjTwist.ConjFun (p.O j) (p.κ j) τ 1 Φ Φ' →
    ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
      Φ = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧ ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val = Φ' := by
  intro _ _ _ _
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j τ hτ Φ Φ' hC => ?_⟩⟩⟩
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hb := GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls.base_of_tie (i := j) p.fw
  have hso : (p.O j).s0 = res p.T (sg0 _ p.P.A3.A) := (sOv_eq p.T.toCore (p.O j).c' (p.O j).hle).trans hb.1.symm
  have hev := GlobalTheory.ConjExpandRational.evaluates_of_unif' p.fw hU j (sg0 _ p.P.A3.A) hb.2.1 hb.2.2
  let gf : p.T.cuspA ((j : ℕ) + 1) (wtA (p.κ j)) (p.κ j).n → NX.FmK p.Sx ((j : ℕ) + 1) := fun f =>
    ⟨(p.nexp.fi j).e.symm (p.fw.e j f), ((p.nexp.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact (p.fw.e j f).2)⟩
  have hread : ∀ (f : p.T.cuspA ((j : ℕ) + 1) (wtA (p.κ j)) (p.κ j).n) h,
      (lieFac (p.T.Q.Dw ((j : ℕ) + 1)) (xiR (Fm.D x i)) (wtA (p.κ j)) : ℂ) *
      (p.O j).phi (p.T.cE ((j : ℕ) + 1) (p.O j).s0) (f : p.T.R ((j : ℕ) + 1)) h = evW p.nexp p.v₀ j (gf f).val h := by
    intro f h
    rw [phi_cE p.T p.R.toRealDat p.O j]
    refine Eq.trans ?_ ((congrFun (hev f) h).symm.trans ?_)
    · exact congrFun (GlobalTheory.LiftRatObj.phiC_congr p.T hso (p.O j).hV hb.2.2 _ _) h
    · show _ = ((p.R.HW j (sg0 _ p.P.A3.A)).e (((p.R.FW j).j (sg0 _ p.P.A3.A)) ((p.nexp.fi j).e
        ((p.nexp.fi j).e.symm (p.fw.e j f))))) (p.v₀ j (sg0 _ p.P.A3.A)) h
      rw [LinearEquiv.apply_symm_apply]
      rfl
  obtain ⟨⟨n, a, f, hf⟩, h2⟩ := hC
  have hf' := h2 n a f hf
  refine ⟨n, a, fun k => gf (f k), funext fun h => ?_, funext fun h => ?_⟩
  · rw [hf h, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hread]
  · rw [hf' h, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hread]
    simp only [one_mul]
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjTwist_function_eq_sum_evaluations_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ τ : ℂ ≃+* ℂ,
  (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
  ∀ Φ Φ' : GA (Fm.D x i) (Wc (Fm.D x i) j) → ℂ, GlobalTheory.ConjTwist.ConjFun (p.O j) (p.κ j) τ 1 Φ Φ' →
    ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
      Φ = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧ ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val = Φ' := by
  atlas_forward_decl _root_.GlobalTheory.ConjExpandRational.exists_evW_expansion_of_conjFun
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
open GlobalTheory.ConjTwist
theorem normAt_alt : _root_.GlobalTheory.BigOn.Exp.TwConj.NormCondition := _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun _ _ _ _ p _ _ _ _ _ B ν ν' ⟨_, c, hc, n, hn, hνn⟩ ⟨_, c', hc', m, hm, hνm⟩ => by
  obtain ⟨k, hk, hkk⟩ := scale_pow_eq p.R p.v₀ B hc hc'
  refine ⟨n * m * k, Nat.mul_ne_zero (Nat.mul_ne_zero hn hm) hk, ?_⟩
  have e1 : ν' ^ (n * m * k) = (ν' ^ m) ^ (n * k) := by rw [← pow_mul]; ring_nf
  have e2 : ν ^ (n * m * k) = (ν ^ n) ^ (m * k) := by rw [← pow_mul]; ring_nf
  have e3 : c' ^ (n * m * k) = c ^ (n * m * k) := by
    rw [show n * m * k = k * (n * m) by ring, pow_mul c', pow_mul c, hkk]
  rw [e1, e2, hνm, hνn, ← pow_mul, ← pow_mul, mul_pow, mul_pow,
    show m * (n * k) = n * m * k by ring, show n * (m * k) = n * m * k by ring, e3]
theorem twOne_of_steps_alt (hA : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt) (hT : _root_.GlobalTheory.BigOn.Exp.TwConj.TupleCondition) (hF : _root_.GlobalTheory.BigOn.Exp.TwConj.FixedPointCondition) (hC : _root_.GlobalTheory.BigOn.Exp.TwConj.CoefficientCondition)
    (hE : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x _ i p _ j => ∀ τ : ℂ ≃+* ℂ,
      (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∀ Φ Φ' : GA (Fm.D x i) (Wc (Fm.D x i) j) → ℂ, ConjFun (p.O j) (p.κ j) τ 1 Φ Φ' →
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          Φ = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧ ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val = Φ') : _root_.GlobalTheory.BigOn.Exp.TwConj.TwistTrivialCondition := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hA hT) (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hF (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hC hE))) fun Fm x hx i p hr hm w _ j H => ?_
  obtain ⟨⟨a1, a2⟩, a3, a4, a5⟩ := H
  intro ρ ρ' ν hρ hρ' hp hS hL hAd hN h₀ P hP h hh τ hτ hcc
  obtain ⟨c, u, ξ, hc, hu, hξ, K⟩ := a4 ρ ν hρ hp hN
  obtain ⟨y, hy, hyy⟩ := K h₀ P hP
  obtain ⟨f1, f2⟩ := a3 ρ hρ hp hL τ hτ
  obtain ⟨g1, g2, -⟩ := GlobalTheory.TwistGood.tw_good _ _ _ ρ hρ _ j ((Fm.ex x hx i).nch.sd w) _ _ _ a1.1
  obtain ⟨g3, -, -⟩ := GlobalTheory.TwistGood.tw_good _ _ _ ρ' hρ' _ j ((Fm.ex x hx i).nch.sd w) _ _ _ a1.1
  obtain ⟨ζ, hζ, hcf⟩ := conjFun_gen (Fm.parT x hx i).nV_ge (a2 ρ ρ' hρ hρ' hp hS hAd) (hρ.base _ _ _) (hρ.weil_base _ _ _) g1 g3 g2
    (hcc.1.symm ▸ g2) (root_delta hρ _ _ _) (root_charOf _ _ a1.1.2.2.1) hc hu f1 f2 hcc hh (hyy τ hτ)
  have hcf1 := (GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).2
    (GlobalTheory.ConjGen.cf_one_of (root_ne hζ) ((GlobalTheory.ConjClassSum.conjFun_iff _ _ _ _ _ _).1 hcf))
  obtain ⟨n, b, g, e1, e2⟩ := a5 τ hτ _ _ hcf1
  have hsm : ∀ ψ, ν • genW (Fm.ex x hx i) w j ρ ψ h P =
      ξ • phs p j • genW (Fm.ex x hx i) w j ρ ψ h (p.R.ioP j (PiTensorProduct.tprod ℂ u) (c y)) := fun ψ =>
    smul_apply_of _ hy
  exact ⟨_, root_mul (root_mul (root_map τ hξ) (root_inv hζ)) (root_inv hξ), n, fun l => ξ * b l, g,
    rescale τ (root_ne hξ) (hsm _) (hsm _) e1 e2⟩
theorem conj_tw_of_prints : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS →
    _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.ConjugateTwist := fun h1 h2 h3 hD hW h4 hA hC =>
  _root_.GlobalTheory.BigOn.Exp.TwConj.conjTw_of_twAdm_latSmallGen_normAt_twOne hA _root_.GlobalTheory.T.latSmallGen' _root_.GlobalTheory.BigOn.Exp.TwConj.normAt_alt (_root_.GlobalTheory.BigOn.Exp.TwConj.twOne_of_steps_alt hA (_root_.GlobalTheory.T.twisted_conj_tuple_at' h1 h2 h3 hD hW hA hC) (_root_.GlobalTheory.T.twisted_conj_fix_at' h3 hA) (_root_.GlobalTheory.T.twisted_conj_coef_at' hA)
    (_root_.GlobalTheory.T.conjTwist_function_eq_sum_evaluations_alt h1 h2 h3 h4))
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjTw_of_discrete_series_and_casselman_wallach : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.ConjugateTwist := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.TwConj.conj_tw_of_prints
end
end
