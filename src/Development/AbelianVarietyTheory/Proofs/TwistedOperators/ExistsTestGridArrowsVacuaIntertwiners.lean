import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerLargerSourceMirrorCase
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsRemoveBlockArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpIffHasInfQ
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColIntertwiner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDownArrowRealIntertwinerWithAdjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectors

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem exists_wRep_of_negSp {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χS χT om) :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ true S T χS χT ω ∧ HEq (ω.toSgn true) om := by
  subst hS; subst hT
  let ω : GlobalTheory.Grid.WRep S T :=
    om.comp (((GlobalTheory.Grid.ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _) :
      GA D S × GA D T →* GA D (negSp S) × GA D T))
  have e : ω.toSgn true = om := MonoidHom.ext fun _ => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  show IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (ω.toSgn true)
  rw [e]
  exact h

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

theorem exists_omX_of_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V, GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω ∧ HEq (ω.toSgn true) (W.om (.chi i j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hG _ hsp _ i j hi hj
  have hv1 := (hsp.vert (i + 1) j (by omega) hj).sp
  have hv0 := (hsp.vert i j (by omega) hj).sp
  have hom := W.om_is (.chi i j) ⟨by omega, hj⟩
  rw [hW.ψ] at hom
  obtain ⟨ω, h1, h2⟩ := exists_wRep_of_negSp hv1 hv0 R.ψ _ _ (W.om (.chi i j)) hom
  refine ⟨ω, ?_, h2⟩
  have hchi : G.chi (D.R.m - i) = G'.ch.chi (D.R.m - i) := hsp.chi _ (by omega) (by omega)
  have rS : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← hv1]; exact (hG.vert i j (by omega) hj).rank
  have rT : (G'.V (.grid i j)).rank = rkV D i j := by
    rw [← hv0]
    cases i with
    | succ k => exact (hG.vert k j (by omega) hj).rank
    | zero =>
      rw [hv0]
      show (columnBlock R.toLevCh j).sp.rank = _
      simp only [rkV, zero_mul, add_zero]
      rcases hj.eq_or_lt with rfl | hk
      · rw [colY_m]; exact D.sp.X'_rank
      · rw [colY_lt _ hk]
        exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  have cS : G'.chrS (.chi i j) = G.chiAt (D.R.m - i) (rkV D (i + 1) j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid (i + 1) j)).rank = _
    rw [rS, ← hchi]
  have cT : G'.chrT (.chi i j) = G.chiAt (D.R.m - i) (rkV D i j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid i j)).rank = _
    rw [rT, ← hchi]
  rw [cS, cT] at h1
  exact h1

end GlobalTheory.GridJoin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin.VacX

variable {D : D7}

theorem transport (ψ ψ' : AddChar (AF D.host.F) ℂ) (θ θ' : InfFam D) (hψ : ψ' = ψ) (hθ : θ' = θ)
    {S S' T T' : HSp D} (hS : S = S') (hT : T = T')
    {cS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {cS' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ}
    (hcS : HEq cS cS')
    {cT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {cT' : D.what₂.Tau → Matrix (Fin T'.rank) (Fin T'.rank) ℂ}
    (hcT : HEq cT cT')
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    (hΛS : HEq ΛS ΛS')
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hΛT : HEq ΛT ΛT')
    {f : WO (negSp S') T' → ℂ}
    (h : IsVacO ψ' θ' (negSp S') T' (fun τ => -cS' τ) cT' (ΛS' : Set _) (ΛT' : Set _) f) :
    ∃ f' : WO (GlobalTheory.Grid.sgn true S) T → ℂ,
      IsVacO ψ θ (GlobalTheory.Grid.sgn true S) T (fun τ => GlobalTheory.Grid.sgnM true (cS τ)) cT (ΛS : Set _) (ΛT : Set _) f' ∧ HEq f' f := by
  subst hS hT hψ hθ
  obtain rfl := eq_of_heq hcS
  obtain rfl := eq_of_heq hcT
  obtain rfl := eq_of_heq hΛS
  obtain rfl := eq_of_heq hΛT
  exact ⟨f, h, HEq.rfl⟩

end GlobalTheory.GridJoin.VacX

open GlobalTheory.GridJoin.VacX in

theorem GlobalTheory.GridJoin.exists_vacX : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f ∧ (j = 0 → HEq f (W.vac i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hag _ i j hi hj
  have hS := hag.vert (i + 1) j (by omega) hj
  have hT := hag.vert i j (by omega) hj
  have key : ∀ f, W.IsVac (.chi i j) f → ∃ f' : WO (G.V (i + 1) j).V (G.V i j).V → ℂ,
      GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f' ∧ HEq f' f := fun f hf =>
    transport R.ψ W.ψ R.θ W.θ hW.ψ hW.θ hS.sp hT.sp hS.cart hT.cart hS.lat hT.lat hf
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · obtain ⟨f, h1, h2⟩ := key (W.vac i) (W.vac_is i hi)
    exact ⟨f, h1, fun _ => h2⟩
  · obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .chi i j) ⟨hi, hj⟩
    obtain ⟨f', h1, -⟩ := key f hf
    exact ⟨f', h1, fun h => by omega⟩
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiner_largerSource_mirrorCase : ∀ {D : D7} (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (t : ℕ) (aS aT : D.what₂.Tau → ℚ), GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → IsInfFam θ → (∀ τ, ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm t [] be [] de ∧ S τ = dualPar (GlobalTheory.Chain.signed de (Formalism.BasicNotions.TH.block t ++ be) (aT τ)) ∧ S' τ = dualPar (GlobalTheory.Chain.signed be de (aS τ))) → ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → (∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)) → ∀ f, GlobalTheory.Chain.IsVacVec ψ θ M M' f → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It := by
  first | exact @GlobalTheory.Chain.RealItLarge.itLarge | exact GlobalTheory.Chain.RealItLarge.itLarge | (intros; apply GlobalTheory.Chain.RealItLarge.itLarge <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NegModel

variable {n : ℕ}

def flip (ε : Fin n → Bool) : Fin n → Bool := fun a => !ε a

theorem flip_eq_iff (ε : Fin n → Bool) (a b : Fin n) : flip ε a = flip ε b ↔ ε a = ε b := by
  unfold flip; cases ε a <;> cases ε b <;> simp

theorem flip_ne_iff (ε : Fin n → Bool) (a b : Fin n) : flip ε a ≠ flip ε b ↔ ε a ≠ ε b :=
  not_congr (flip_eq_iff ε a b)

theorem Jm_flip (ε : Fin n → Bool) : Formalism.REAL.Jm (flip ε) = -Formalism.REAL.Jm ε := by
  ext a b
  unfold Formalism.REAL.Jm flip
  by_cases h : a = b
  · subst h; rcases hε : ε a with _ | _ <;> simp [hε]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem inUJ_flip (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inUJ (flip ε) g ↔ Formalism.REAL.inUJ ε g := by
  unfold Formalism.REAL.inUJ
  rw [Jm_flip, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem UJset_flip (ε : Fin n → Bool) : UJset (flip ε) = UJset ε := by
  ext g; exact inUJ_flip ε g

theorem UJ_flip (ε : Fin n → Bool) : Formalism.REAL.UJ (flip ε) = Formalism.REAL.UJ ε := by
  ext g; exact inUJ_flip ε _

theorem Kset_flip (ε : Fin n → Bool) : Formalism.REAL.Kset (flip ε) = Formalism.REAL.Kset ε := by
  ext g
  unfold Formalism.REAL.Kset
  simp only [Set.mem_setOf_eq, Jm_flip, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem rhoC_flip (ε : Fin n → Bool) : Formalism.REAL.rhoC (flip ε) = Formalism.REAL.rhoC ε := by
  funext a
  unfold Formalism.REAL.rhoC
  simp only [flip_eq_iff]

theorem rhoN_flip (ε : Fin n → Bool) : Formalism.REAL.rhoN (flip ε) = Formalism.REAL.rhoN ε := by
  funext a
  unfold Formalism.REAL.rhoN
  simp only [flip_ne_iff]

theorem lowK_flip (ε : Fin n → Bool) (lam : Fin n → ℝ) : Formalism.QuantumDeterminants.lowK (flip ε) lam = Formalism.QuantumDeterminants.lowK ε lam := by
  unfold Formalism.QuantumDeterminants.lowK; rw [rhoC_flip, rhoN_flip]

theorem vNormSq_flip (ε : Fin n → Bool) (μ : Fin n → ℝ) : vNormSq (flip ε) μ = vNormSq ε μ := by
  unfold vNormSq; rw [rhoC_flip]

theorem cDom_flip (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) : CDom (flip ε) μ Λ ↔ CDom ε μ Λ := by
  unfold CDom; simp only [flip_eq_iff]

theorem isKTypeOf_flip {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    IsKTypeOf (flip ε) σ Λ S ↔ IsKTypeOf ε σ Λ S := by
  unfold IsKTypeOf IsKStableOn
  simp only [Kset_flip, cDom_flip]

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel

variable {n : ℕ}

theorem memLp_UJ_congr {ε ε' : Fin n → Bool} (h : Formalism.REAL.UJ ε = Formalism.REAL.UJ ε') (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hf : MemLp (fun g : Formalism.REAL.UJ ε => f ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) 2
      (Formalism.REAL.muG ε)) :
    MemLp (fun g : Formalism.REAL.UJ ε' => f ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) 2
      (Formalism.REAL.muG ε') := by
  have key : ∀ (G G' : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ), G = G' → ∀ (_ : LocallyCompactSpace G)
      (_ : LocallyCompactSpace G'),
      (letI : MeasurableSpace G := borel G; haveI : BorelSpace G := ⟨rfl⟩;
        MemLp (fun g : G => f ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) 2 Measure.haar) →
      (letI : MeasurableSpace G' := borel G'; haveI : BorelSpace G' := ⟨rfl⟩;
        MemLp (fun g : G' => f ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) 2 Measure.haar) := by
    intro G G' hG _ _ hm
    subst hG
    exact hm
  exact key _ _ h inferInstance inferInstance hf

theorem isSqIntOn_flip {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsSqIntOn ε σ) : IsSqIntOn (flip ε) σ := fun v w =>
  memLp_UJ_congr (UJ_flip ε).symm (fun g => ⟪w, σ g v⟫_ℂ) (h v w)

theorem isDS_flip {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsDS ε lam σ) : IsDS (flip ε) lam σ := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨S, hS⟩, h7⟩ := h
  refine ⟨h1, h2, ?_, ?_, isSqIntOn_flip ε σ h5, ⟨S, ?_⟩, ?_⟩
  · rw [UJset_flip]; exact h3
  · rw [UJset_flip]; exact h4
  · rw [lowK_flip, isKTypeOf_flip]; exact hS
  · intro μ S' hS'
    rw [lowK_flip, vNormSq_flip, vNormSq_flip]
    exact h7 μ S' ((isKTypeOf_flip ε σ μ S').1 hS')

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel

variable {D : D7}

theorem gramAt_neg (V : HSp D) (τ : D.what₂.Tau) : gramAt D (GlobalTheory.Grid.sgn true V) τ = -gramAt D V τ := by
  ext i j; simp [gramAt, GlobalTheory.Grid.neg_gram]

theorem UH_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Formalism.QuantumDeterminants.UH (-H) = Formalism.QuantumDeterminants.UH H := by
  ext g
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem UH_sgn (V : HSp D) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.UH (gramAt D (GlobalTheory.Grid.sgn true V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  rw [gramAt_neg, UH_neg]

theorem lieAt_sgn (V : HSp D) (τ : D.what₂.Tau) : lieAt (GlobalTheory.Grid.sgn true V) τ = lieAt V τ := by
  ext X
  simp only [lieAt, Set.mem_setOf_eq]
  rw [gramAt_neg, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero]

@[reducible] def negModel {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) :
    DSModel (GlobalTheory.Grid.sgn true V) (fun τ => (S τ).image fun x => (x.1, !x.2)) where
  H := M.H
  nacg := M.nacg
  ips := M.ips
  σ := M.σ
  lam := M.lam
  ε := fun τ => flip (M.ε τ)
  fr := M.fr
  enum τ := by
    obtain ⟨h1, q, hq, hS⟩ := M.enum τ
    refine ⟨h1, q, hq, ?_⟩
    rw [hS, Finset.image_image]
    rfl
  ds τ := isDS_flip _ _ _ (M.ds τ)
  fr_unit := M.fr_unit
  fr_gram τ := by
    rw [gramAt_neg, ← M.fr_gram τ, Jm_flip, Matrix.mul_neg, Matrix.neg_mul]

theorem cart_negModel {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    cart (negModel M) τ = -cart M τ := by
  show (M.fr τ)⁻¹ * Formalism.REAL.Jm (flip (M.ε τ)) * M.fr τ = -((M.fr τ)⁻¹ * Formalism.REAL.Jm (M.ε τ) * M.fr τ)
  rw [Jm_flip, Matrix.mul_neg, Matrix.neg_mul]

theorem onb_negModel {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    onb (negModel M) τ = onb M τ := rfl

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel

variable {D : D7}

theorem val_dite_congr {G : Type*} [Group G] {H H' : Subgroup G} (hH : H = H') (p : H → Prop) (p' : H' → Prop)
    [Decidable (∃ x, p x)] [Decidable (∃ x, p' x)]
    (hp : ∀ x : H, p x ↔ p' ⟨x.1, hH ▸ x.2⟩) :
    (((if h : ∃ x, p x then h.choose else 1 : H)) : G) = ((if h : ∃ x, p' x then h.choose else 1 : H') : G) := by
  subst hH
  have : p = p' := funext fun x => propext (hp x)
  subst this
  congr

theorem isAtTau_sgn (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (x : GA D (GlobalTheory.Grid.sgn true V)) :
    IsAtTau θ (GlobalTheory.Grid.sgn true V) τ g x ↔ IsAtTau θ V τ g (GlobalTheory.Grid.ofSgn true V x) := Iff.rfl

theorem ofSgn_atTau (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    GlobalTheory.Grid.ofSgn true V (atTau θ (GlobalTheory.Grid.sgn true V) τ g) = atTau θ V τ g := by
  classical
  have h := val_dite_congr (G := GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
    (H := HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.Grid.sgn true V).gram) (H' := HR (AF D.host.F) D.sp.cm.sig V.gram)
    (GlobalTheory.Grid.hr_sgn true V) (fun x => IsAtTau θ (GlobalTheory.Grid.sgn true V) τ g x) (fun x => IsAtTau θ V τ g x)
    (fun x => isAtTau_sgn θ V τ g x)
  exact Subtype.ext h

theorem ofSgn_oneP (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    GlobalTheory.Grid.ofSgn true V (oneP θ (GlobalTheory.Grid.sgn true V) τ X t) = oneP θ V τ X t :=
  ofSgn_atTau θ V τ _

end GlobalTheory.NegModel

namespace GlobalTheory.NegModel

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_negModel (M : DSModel V S) (τ : D.what₂.Tau) : (negModel M).sm τ = M.sm τ := by
  show Submodule.span ℂ {w | SmoothVec (lieAt (GlobalTheory.Grid.sgn true V) τ) (M.rep τ) w} =
    Submodule.span ℂ {w | SmoothVec (lieAt V τ) (M.rep τ) w}
  rw [lieAt_sgn]

theorem exists_equiv_incl {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, AddCommGroup (H i)] [∀ i, Module ℂ (H i)]
    (p q : ∀ i, Submodule ℂ (H i)) (h : p = q) :
    ∃ e : (⨂[ℂ] i, p i) ≃ₗ[ℂ] (⨂[ℂ] i, q i), ∀ x,
      PiTensorProduct.map (fun i => (q i).subtype) (e x) = PiTensorProduct.map (fun i => (p i).subtype) x := by
  subst h
  exact ⟨LinearEquiv.refl ℂ _, fun _ => rfl⟩

theorem exists_negModel_transfer : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S), ∃ M₁ : DSModel (GlobalTheory.Grid.sgn true V) (fun τ => (S τ).image fun x => (x.1, !x.2)), (∀ τ, cart M₁ τ = -cart M τ) ∧ (∀ τ, onb M₁ τ = onb M τ) ∧ ∀ {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (θ : InfFam D), IsInfFam θ → ∀ (ω : GlobalTheory.Grid.WRep V W) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It₁ : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M₁), IsItW θ M₁ M' (GlobalTheory.Grid.WRep.toSgn true ω) pt It₁ → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω pt It := by
  intro D V S M
  refine ⟨negModel M, cart_negModel M, onb_negModel M, ?_⟩
  intro W S' M' θ _ ω pt It₁ h₁
  obtain ⟨e, he⟩ := exists_equiv_incl (H := M.H) (fun τ => (negModel M).sm τ) (fun τ => M.sm τ)
    (funext (sm_negModel M))
  have he' : ∀ x : SmT (negModel M), inclT M (e x) = inclT (negModel M) x := he
  refine ⟨It₁.compr₂ e.toLinearMap, ?_⟩
  have hIt : ∀ φ v, It₁.compr₂ e.toLinearMap φ v = e (It₁ φ v) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply h₁.ne
    refine LinearMap.ext fun φ => LinearMap.ext fun v => ?_
    have h2 : e (It₁ φ v) = 0 := by rw [← hIt, h0]; rfl
    simpa using h2
  · intro φ w
    obtain ⟨c, hc⟩ := h₁.bdd φ w
    refine ⟨c, fun v => ?_⟩
    rw [hIt, he']
    exact hc v
  · intro τ g hg φ φ' hpt v
    rw [hIt, hIt, he', he']
    refine h₁.eqK τ g (by rw [UH_sgn]; exact hg) φ φ' ?_ v
    rw [hpt]
    show ω (atTau θ V τ g, 1) (pt φ) = ω (GlobalTheory.Grid.ofSgn true V (atTau θ (GlobalTheory.Grid.sgn true V) τ g), 1) (pt φ)
    rw [ofSgn_atTau]
  · intro τ X hX φ φ' hd v w
    rw [hIt, hIt, he', he']
    refine h₁.eqg τ X (by rw [lieAt_sgn]; exact hX) φ φ' (fun z => ?_) v w
    have h3 : (fun t : ℝ => (GlobalTheory.Grid.WRep.toSgn true ω) (oneP θ (GlobalTheory.Grid.sgn true V) τ X t, 1) (pt φ) z) =
        fun t : ℝ => ω (oneP θ V τ X t, 1) (pt φ) z := by
      funext t
      show ω (GlobalTheory.Grid.ofSgn true V (oneP θ (GlobalTheory.Grid.sgn true V) τ X t), 1) (pt φ) z = _
      rw [ofSgn_oneP]
    rw [h3]
    exact hd z
  · intro τ h hh φ φ' v v' hpt hv
    rw [hIt, hIt, h₁.invK τ h hh φ φ' v v' ?_ hv]
    rw [hpt]
    show ω (1, atTau θ W τ h) (pt φ) = ω (GlobalTheory.Grid.ofSgn true V 1, atTau θ W τ h) (pt φ)
    rw [map_one]
  · intro τ X hX φ φ' v v' hd hv
    rw [hIt, hIt, ← map_add, h₁.invg τ X hX φ φ' v v' ?_ hv, map_zero]
    intro z
    have h3 : (fun t : ℝ => (GlobalTheory.Grid.WRep.toSgn true ω) (1, oneP θ W τ X t) (pt φ) z) =
        fun t : ℝ => ω (1, oneP θ W τ X t) (pt φ) z := by
      funext t
      show ω (GlobalTheory.Grid.ofSgn true V 1, oneP θ W τ X t) (pt φ) z = _
      rw [map_one]
    rw [h3]
    exact hd z

end GlobalTheory.NegModel
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteSeriesModel_negSpace_transfer : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S), ∃ M₁ : DSModel (GlobalTheory.Grid.sgn true V) (fun τ => (S τ).image fun x => (x.1, !x.2)), (∀ τ, cart M₁ τ = -cart M τ) ∧ (∀ τ, onb M₁ τ = onb M τ) ∧ ∀ {W : HSp D} {S' : D.what₂.Tau → SPar} (M' : DSModel W S') (θ : InfFam D), IsInfFam θ → ∀ (ω : GlobalTheory.Grid.WRep V W) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) (It₁ : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M₁), IsItW θ M₁ M' (GlobalTheory.Grid.WRep.toSgn true ω) pt It₁ → ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω pt It := by
  atlas_forward_decl GlobalTheory.NegModel.exists_negModel_transfer
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin.ArrXPar

open GlobalTheory.SignedHC GlobalTheory.RemoveBlock GlobalTheory.PairLift GlobalTheory.Chain

theorem mem_signed {l₁ l₂ : List ℚ} {c : ℚ} {x : ℚ × Bool} :
    x ∈ signed l₁ l₂ c ↔ (x.2 = true ∧ x.1 - c ∈ l₁) ∨ (x.2 = false ∧ x.1 - c ∈ l₂) := by
  obtain ⟨a, s⟩ := x
  simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨y, hy, rfl, rfl⟩ | ⟨y, hy, rfl, rfl⟩)
    · left; simpa using hy
    · right; simpa using hy
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · left; exact ⟨_, h, by ring, rfl⟩
    · right; exact ⟨_, h, by ring, rfl⟩

theorem gapGt_ofBlocks {p q : ℕ} {l₁ l₂ : List ℚ} (hp : l₁.length = p) (hq : l₂.length = q) {h : ℝ}
    (H : ∀ x ∈ l₁, ∀ y ∈ l₂, h < |((x - y : ℚ) : ℝ)|) : GapGt (ofBlocks l₁ l₂ : Ix p q → ℚ) h := by
  subst hp hq
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · simp only [ofBlocks, List.getD_eq_getElem _ _ a.2, List.getD_eq_getElem _ _ b.2]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · simp only [ofBlocks, List.getD_eq_getElem _ _ a.2, List.getD_eq_getElem _ _ b.2]
    rw [← neg_sub, Rat.cast_neg, abs_neg]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · exact (hab trivial).elim

theorem gapGe_ofBlocks {p q : ℕ} {l₁ l₂ : List ℚ} (hp : l₁.length = p) (hq : l₂.length = q) {h : ℝ}
    (H : ∀ x ∈ l₁, ∀ y ∈ l₂, h ≤ |((x - y : ℚ) : ℝ)|) : GapGe (ofBlocks l₁ l₂ : Ix p q → ℚ) h := by
  subst hp hq
  rintro (a | a) (b | b) hab
  · exact (hab trivial).elim
  · simp only [ofBlocks, List.getD_eq_getElem _ _ a.2, List.getD_eq_getElem _ _ b.2]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · simp only [ofBlocks, List.getD_eq_getElem _ _ a.2, List.getD_eq_getElem _ _ b.2]
    rw [← neg_sub, Rat.cast_neg, abs_neg]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · exact (hab trivial).elim

end GlobalTheory.GridJoin.ArrXPar

namespace GlobalTheory.GridJoin.ArrXPar

open GlobalTheory.SignedHC GlobalTheory.RemoveBlock GlobalTheory.PairLift GlobalTheory.Chain GlobalTheory.Grid

theorem att_succ (c : ℚ) (D : D7) (i j : ℕ) :
    att c (rkV D (i + 1) j) = c + (if Odd (i + j) then -(1 / 2) else 0) ∧
      att c (rkV D i j) = c + (if Odd (i + 1 + j) then -(1 / 2) else 0) := by
  have e : i + 1 + j = i + j + 1 := by ring
  unfold att
  simp only [odd_rkV, e, Nat.odd_add_one]
  by_cases h : Odd (i + j) <;> simp [h] <;> ring

theorem nat_cube_le {a R : ℕ} (h : a ≤ R) : ((a : ℕ) : ℚ) ^ 3 ≤ (R : ℚ) ^ 3 :=
  pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h) 3

theorem gridJoin_cubic_size_bound {n mm N : ℕ} (hn : n ≤ N) (hmm : 2 * mm ≤ N) (hN : 1800 ≤ N) :
    120 * (n : ℝ) * (mm : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hm' : 2 * (mm : ℝ) ≤ N := by exact_mod_cast hmm
  have hN' : (1800 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : (0 : ℝ) ≤ mm := Nat.cast_nonneg _
  have e : (mm : ℝ) ^ ((3 : ℝ) / 2) = mm * √(mm : ℝ) := by
    rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add' hm0 (by norm_num), Real.rpow_one]
  have hs : √(mm : ℝ) ≤ N / 30 := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have hm2 : (mm : ℝ) ≤ N / 2 := by linarith
  rw [e]
  calc 120 * (n : ℝ) * (mm * √(mm : ℝ)) ≤ 120 * (N : ℝ) * ((N / 2) * (N / 30)) := by gcongr
    _ = 2 * (N : ℝ) ^ 3 := by ring

theorem par_pair (D : D7) (hN : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (τ : D.what₂.Tau) (i j : ℕ)
    (hi : i < D.R.m) (hj : j ≤ D.R.m) : ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm (GlobalTheory.Grid.sLen D) [] be [] de ∧
      (parV D (i + 1) j τ).image (fun x => (x.1, !x.2)) =
        dualPar (signed de (Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D) ++ be) (att (cen D τ (D.R.m - i) : ℚ) (rkV D i j))) ∧
      parV D i j τ = dualPar (signed be de (att (cen D τ (D.R.m - i) : ℚ) (rkV D (i + 1) j))) := by
  set c : ℚ := (cen D τ (D.R.m - i) : ℚ) with hc
  set P := (grid D τ).parD i j with hP
  obtain ⟨hS, hT⟩ := att_succ c D i j
  rw [hS, hT]
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδ
  set δ' : ℚ := if Odd (i + 1 + j) then -(1 / 2) else 0 with hδ'
  set Pp : Finset ℚ := (P.filter fun x => x.2 = true).image Prod.fst with hPp
  set Pm : Finset ℚ := (P.filter fun x => x.2 = false).image Prod.fst with hPm
  have mPp : ∀ y, y ∈ Pp ↔ (y, true) ∈ P := by
    intro y; simp only [hPp, Finset.mem_image, Finset.mem_filter]
    exact ⟨fun ⟨x, ⟨h1, h2⟩, h3⟩ => by rw [← h3, ← h2]; exact h1, fun h => ⟨_, ⟨h, rfl⟩, rfl⟩⟩
  have mPm : ∀ y, y ∈ Pm ↔ (y, false) ∈ P := by
    intro y; simp only [hPm, Finset.mem_image, Finset.mem_filter]
    exact ⟨fun ⟨x, ⟨h1, h2⟩, h3⟩ => by rw [← h3, ← h2]; exact h1, fun h => ⟨_, ⟨h, rfl⟩, rfl⟩⟩
  set be := (descList Pp).map (· - c) with hbe
  set de := (descList Pm).map (· - c) with hde
  have mbe : ∀ e, e ∈ be ↔ (e + c, true) ∈ P := by
    intro e; rw [hbe, List.mem_map, ← mPp]
    exact ⟨fun ⟨y, hy, h⟩ => by rw [← h, sub_add_cancel]; exact mem_descList.1 hy,
      fun h => ⟨_, mem_descList.2 h, by ring⟩⟩
  have mde : ∀ e, e ∈ de ↔ (e + c, false) ∈ P := by
    intro e; rw [hde, List.mem_map, ← mPm]
    exact ⟨fun ⟨y, hy, h⟩ => by rw [← h, sub_add_cancel]; exact mem_descList.1 hy,
      fun h => ⟨_, mem_descList.2 h, by ring⟩⟩
  have mP' : ∀ x, x ∈ (grid D τ).parD (i + 1) j ↔ x ∈ P ∨ (x.1 ∈ (grid D τ).blockC (D.R.m - i) ∧ x.2 = true) := by
    intro x
    rw [hP, GridData.mem_parD, GridData.mem_parD]
    have hm : (grid D τ).m = D.R.m := rfl
    rw [hm]
    constructor
    · rintro (h | h | h | ⟨l, hl1, hl2, hx, hs⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · rcases (show l = D.R.m - i ∨ D.R.m - i + 1 ≤ l by omega) with rfl | h
        · exact Or.inr ⟨hx, hs⟩
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨l, h, hl2, hx, hs⟩)))
    · rintro ((h | h | h | ⟨l, hl1, hl2, hx, hs⟩) | ⟨hx, hs⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨l, by omega, hl2, hx, hs⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨D.R.m - i, by omega, by omega, hx, hs⟩))
  have mblk : ∀ y, y ∈ Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D) ↔ y + c ∈ (grid D τ).blockC (D.R.m - i) := by
    intro y
    show _ ↔ y + c ∈ TPar.block c (GlobalTheory.Grid.sLen D)
    have h1 : y ∈ Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D) ↔ y ∈ TPar.block 0 (GlobalTheory.Grid.sLen D) := by
      simp [mem_block, Formalism.BasicNotions.TH.block, eq_comm]
    have h2 := sub_mem_block (c := (0 : ℚ)) (x := y + c) (h := c) (t := GlobalTheory.Grid.sLen D)
    rw [add_sub_cancel_right, zero_add] at h2
    rw [h1, h2]
  refine ⟨be, de, ?_, ?_, ?_⟩
  · have hN0 : (0 : ℚ) ≤ 2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
    have hga := GlobalTheory.GridParD.grid_hga D τ
    have hgapA : ∀ i', GapOver ((grid D τ).parD i' j) (2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3) := fun i' =>
      GlobalTheory.GridParD.gapOver_parD (grid D τ) i' j hN0 (grid_nearMid D τ) (GlobalTheory.GridParD.gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ)
        (GlobalTheory.GridParD.grid_heb D τ) (GlobalTheory.GridParD.grid_hbb D τ hN) hga
    have hgap := hgapA i
    have hbel : ∀ x ∈ entries P, x + ((GlobalTheory.Grid.sLen D : ℚ) + 1) / 2 ≤ c :=
      GlobalTheory.GridParD.entries_parD_le (grid D τ) hi hj (grid_nearMid D τ) (GlobalTheory.GridParD.gridDataAtRealPlace_neg_firstLowEnd_lt_cloud D τ)
        (GlobalTheory.GridParD.grid_hbe D τ) (by linarith)
    have hint := int_parD D τ i j
    have hcard0 : P.card ≤ rkV D i j := card_parD_le D τ i j hi.le
    set R : ℕ := rkV D D.R.m D.R.m with hRdef
    set H : ℚ := 2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3 with hH
    have hR0 : (0 : ℚ) ≤ (R : ℚ) ^ 3 := by positivity
    have hr : Odd D.R.r := by
      obtain ⟨a, ha⟩ := D.R.k_even; obtain ⟨b, hb⟩ := D.R.m_even
      have := D.R.two_le_m
      exact ⟨a + b - 1, by unfold Ranks.r; omega⟩
    have hs : Odd (GlobalTheory.Grid.sLen D) := by unfold GlobalTheory.Grid.sLen; exact hr.add_even (by decide)
    obtain ⟨q, hq⟩ := hs
    have hs1 : (1 : ℚ) ≤ (GlobalTheory.Grid.sLen D : ℚ) := by
      rw [hq]; push_cast; have : (0 : ℚ) ≤ q := by positivity
      linarith
    have hbN : (0 : ℚ) ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := by positivity
    have ebe : ∀ e ∈ be, e + c ∈ entries P := fun e he => fst_mem_entries ((mbe e).1 he)
    have ede : ∀ e ∈ de, e + c ∈ entries P := fun e he => fst_mem_entries ((mde e).1 he)
    have hneg : ∀ e, e + c ∈ entries P → e + ((GlobalTheory.Grid.sLen D : ℚ) + 1) / 2 ≤ 0 := by
      intro e he; have := hbel _ he; linarith
    have hent : ∀ e ∈ be ++ de, e + c ∈ entries P := by
      intro e he
      rcases List.mem_append.1 he with h | h
      · exact ebe e h
      · exact ede e h
    have pbe : be.Pairwise (· > ·) := (pairwise_descList Pp).map _ fun a b (h : a > b) => show a - c > b - c by linarith
    have pde : de.Pairwise (· > ·) := (pairwise_descList Pm).map _ fun a b (h : a > b) => show a - c > b - c by linarith
    have hlen : be.length + de.length = P.card := by
      have h1 : Pp.card = (P.filter fun x => x.2 = true).card :=
        Finset.card_image_of_injOn fun x hx y hy e => Prod.ext e (by
          rw [(Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2, (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2])
      have h2 : Pm.card = (P.filter fun x => x.2 = false).card :=
        Finset.card_image_of_injOn fun x hx y hy e => Prod.ext e (by
          rw [(Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2, (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2])
      simp only [hbe, hde, List.length_map, descList, Finset.length_sort, h1, h2]
      exact nPlus_add_nMinus P
    have hv : (((grid D τ).v 2 : ℚ), true) ∈ P := GridData.mem_parD.2 (Or.inl ⟨GridData.mem_cloud.2
      ⟨2, le_rfl, by have := D.R.m_add_three_le_k; show 2 ≤ D.R.k; omega, rfl⟩, rfl⟩)
    have hvbe : ((grid D τ).v 2 : ℚ) - c ∈ be := (mbe _).2 (by rw [sub_add_cancel]; exact hv)
    have hRi : rkV D (i + 1) j = rkV D i j + GlobalTheory.Grid.sLen D := by unfold rkV; ring
    have hRm : rkV D (i + 1) j ≤ R := by
      have a1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
      have a2 : (i + 1) * GlobalTheory.Grid.sLen D ≤ D.R.m * GlobalTheory.Grid.sLen D := Nat.mul_le_mul_right _ hi
      simp only [hRdef, rkV]; omega
    have hNR : be.length + de.length + GlobalTheory.Grid.sLen D ≤ R := by omega
    have hRB : R ≤ GlobalTheory.Grid.bigN D := by
      have : D.R.m * (D.R.t + GlobalTheory.Grid.sLen D + 1) = D.R.m * D.R.t + D.R.m * GlobalTheory.Grid.sLen D + D.R.m := by ring
      simp only [hRdef, rkV, GlobalTheory.Grid.bigN]; unfold Ranks.r; omega
    have hRBq : (R : ℚ) ^ 3 ≤ (GlobalTheory.Grid.bigN D : ℚ) ^ 3 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hRB) 3
    have hpm : ∀ x ∈ be, ∀ y ∈ de, H < |x - y| := by
      intro x hx y hy
      have := hgap _ ((mbe x).1 hx) _ ((mde y).1 hy) (by simp)
      simp only at this
      rwa [show x + c - (y + c) = x - y by ring] at this
    have hblen : (Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D)).length = GlobalTheory.Grid.sLen D := by simp [Formalism.BasicNotions.TH.block]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨by unfold GlobalTheory.Grid.sLen; omega, ?_, List.Pairwise.nil, pbe, List.Pairwise.nil, pde, ?_, by simp, ?_, ?_, ?_⟩
      · have := List.length_pos_of_mem hvbe
        simp only [List.length_nil]; omega
      · rw [List.nil_append, List.append_nil, List.Nodup, List.pairwise_append]
        refine ⟨pbe.imp ne_of_gt, pde.imp ne_of_gt, fun a ha b hb hab => ?_⟩
        have := hpm a ha b hb
        rw [hab, sub_self, abs_zero] at this
        linarith
      · intro e he
        have := hneg e (hent e he)
        linarith
      · intro e he
        rw [List.nil_append, List.append_nil] at he
        obtain ⟨z, hz⟩ := hint _ (hent e he)
        refine ⟨z - cen D τ (D.R.m - i) - (q + 1), ?_⟩
        rw [hq, hc] at *
        push_cast
        linarith
      · intro e he
        rw [List.nil_append, List.append_nil] at he
        have := hneg e (hent e he)
        rw [abs_of_neg (by linarith)]
        linarith
    · unfold lamA
      refine gapGt_ofBlocks (by simp) (by simp) fun x hx y hy => ?_
      rw [List.nil_append] at hx hy
      have key : ((([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length + GlobalTheory.Grid.sLen D : ℕ) : ℚ) ^ 3 < |x - y| := by
        have h2 := nat_cube_le (a := ([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length + GlobalTheory.Grid.sLen D)
          (R := R) (by simp only [List.length_nil]; omega)
        have := hpm x hx y hy
        linarith
      exact_mod_cast key
    · unfold lamM'
      refine gapGt_ofBlocks (by simp) (by simp [hblen]; omega) fun x hx y hy => ?_
      rw [List.nil_append] at hx
      rw [List.nil_append] at hy
      have h2 := nat_cube_le (a := ([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length + GlobalTheory.Grid.sLen D)
        (R := R) (by simp only [List.length_nil]; omega)
      have key : ((([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length + GlobalTheory.Grid.sLen D : ℕ) : ℚ) ^ 3 < |x - y| := by
        rcases List.mem_append.1 hy with hy | hy
        · have := hgapA (i + 1) (x + c, false) ((mP' _).2 (Or.inl ((mde x).1 hx))) (y + c, true)
            ((mP' _).2 (Or.inr ⟨(mblk y).1 hy, rfl⟩)) (by simp)
          simp only at this
          rw [show x + c - (y + c) = x - y by ring] at this
          linarith
        · have := hpm y hy x hx
          rw [abs_sub_comm] at this
          linarith
      exact_mod_cast key
    · unfold lamA
      refine gapGe_ofBlocks (by simp) (by simp) fun x hx y hy => ?_
      rw [List.nil_append] at hx hy
      have hb := gridJoin_cubic_size_bound (n := ([] : List ℚ).length + be.length + ([] : List ℚ).length + de.length)
        (mm := min (([] : List ℚ).length + be.length) (([] : List ℚ).length + de.length)) (N := GlobalTheory.Grid.bigN D)
        (by simp only [List.length_nil]; omega) (by simp only [List.length_nil]; omega)
        (by have h1 := hN.1; have h2 : D.R.r ≤ R := by simp only [hRdef, rkV]; omega
            omega)
      have hxy : (H : ℝ) < |((x - y : ℚ) : ℝ)| := by exact_mod_cast hpm x hx y hy
      have hH' : (H : ℝ) = 2 * (GlobalTheory.Grid.bigN D : ℝ) ^ 3 := by rw [hH]; push_cast; ring
      linarith
  · ext ⟨a, s⟩
    show (a, s) ∈ flip (parV D (i + 1) j τ) ↔ (a, s) ∈ negate _
    rw [mem_flip, mem_negate]
    show (a, !s) ∈ negate (shift δ' _) ↔ _
    rw [mem_negate, mem_shift, mem_signed]
    simp only
    rw [mP', mde, List.mem_append, mbe, mblk]
    have e1 : -a - (c + δ') + c = -a - δ' := by ring
    rw [e1]
    cases s <;> simp [or_comm]
  · show dualPar (shift δ P) = _
    congr 1
    ext ⟨a, s⟩
    rw [mem_shift, mem_signed]
    simp only
    rw [mbe, mde]
    have e1 : a - (c + δ) + c = a - δ := by ring
    rw [e1]
    cases s <;> simp

end GlobalTheory.GridJoin.ArrXPar

namespace GlobalTheory.GridJoin.ArrXPar

open GlobalTheory.SignedHC GlobalTheory.RemoveBlock GlobalTheory.PairLift GlobalTheory.Chain GlobalTheory.Grid

theorem arrowX_par : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.IsChars → ∀ i j, i < D.R.m → j ≤ D.R.m → ∀ τ : D.what₂.Tau, ∃ aS aT : ℚ, HasInfExp D (G.chiAt (D.R.m - i) (GlobalTheory.Grid.rkV D (i + 1) j)) τ aS ∧ HasInfExp D (G.chiAt (D.R.m - i) (GlobalTheory.Grid.rkV D i j)) τ aT ∧ ∃ be de : List ℚ, Formalism.MainNotions.SchurIrreducible.DataARm (GlobalTheory.Grid.sLen D) [] be [] de ∧ (GlobalTheory.Grid.parV D (i + 1) j τ).image (fun x => (x.1, !x.2)) = dualPar (GlobalTheory.Chain.signed de (Formalism.BasicNotions.TH.block (GlobalTheory.Grid.sLen D) ++ be) aT) ∧ GlobalTheory.Grid.parV D i j τ = dualPar (GlobalTheory.Chain.signed be de aS) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F hN hC G hch i j hi hj τ
  have hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R := ⟨hC.lev, hC.models.inf, hC.models.νY, hC.models.νY', hC.models.νX⟩
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have hexp : HasInfExp D (G.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) :=
    (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ D _ _ (fun τ => (GlobalTheory.Grid.cen D τ (D.R.m - i) : ℚ))
      (hch.tie _ hm1 hm2)).2 (hch.aux _ hm1 hm2).inf τ
  obtain ⟨be, de, hd, e1, e2⟩ := par_pair D hN τ i j hi hj
  exact ⟨_, _, hasInfExp_att hexp (exp_eta hR τ) _, hasInfExp_att hexp (exp_eta hR τ) _, be, de, hd, e1, e2⟩

end GlobalTheory.GridJoin.ArrXPar
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin.ArrX

theorem vertex_par {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R) (hS : G.IsSpaces)
    (i j : ℕ) (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  rcases i with _ | i
  · rw [GlobalTheory.Grid.parV_zero D hj]
    show (GlobalTheory.Grid.row0 R j).S = _
    rcases j with _ | j
    · rfl
    · by_cases hlt : j + 1 < D.R.m
      · rw [← GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R hlt]
        dsimp only [GlobalTheory.Grid.nodeY]
        rw [Nat.min_eq_left hlt.le]
      · rw [← GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R hlt]
        have hm : j + 1 = D.R.m := by omega
        rw [hm]
  · exact (hS.vert i j hi hj).par

theorem exists_intertwiner : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V) (f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f → ∃ It : GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j) →ₗ[ℂ] SmT (G.V i j).M →ₗ[ℂ] SmT (G.V (i + 1) j).M, IsItW R.θ (G.V (i + 1) j).M (G.V i j).M ω (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDS hHC hHost hSz F hCore hgap G' W hW G hS hC hSp hTh i j hi hj ω f hω hf
  have hθ : IsInfFam R.θ := hCore.models.inf
  obtain ⟨M₁, hcart, honb, hback⟩ := GlobalTheory.T.exists_discreteSeriesModel_negSpace_transfer (G.V (i + 1) j).M
  choose aS aT haS haT be de hdat hflip hlow using
    fun τ => GlobalTheory.GridJoin.ArrXPar.arrowX_par hSz hCore G hC i j hi hj τ
  have hSn := vertex_par G hS (i + 1) j hi hj
  have hSo := vertex_par G hS i j hi.le hj
  have hc : cart M₁ = GlobalTheory.Grid.cartS true (G.V (i + 1) j) := funext fun τ => (hcart τ).trans rfl
  have ho : onb M₁ = onb (G.V (i + 1) j).M := funext honb
  have hfin := hf.isFinVec
  have hne : f ≠ 0 := by
    unfold GlobalTheory.Grid.IsVac IsVacO at hf
    obtain ⟨-, ⟨-, -, -, -, ⟨⟨p, hp⟩, hq⟩⟩⟩ := hf
    intro h0
    have h1 := hq p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hvac : GlobalTheory.Chain.IsVacVec R.ψ R.θ M₁ (G.V i j).M f :=
    ⟨hfin.1, hne, fun τ => by rw [hc]; exact hfin.2 τ⟩
  obtain ⟨It₁, hIt₁⟩ := GlobalTheory.T.exists_realIntertwiner_largerSource_mirrorCase (GlobalTheory.Grid.sgn true (G.V (i + 1) j).V) (G.V i j).V
    (fun τ => ((G.V (i + 1) j).S τ).image fun x => (x.1, !x.2)) (G.V i j).S M₁ (G.V i j).M R.θ R.ψ
    (GlobalTheory.Grid.sLen D) aS aT hDS hHC hθ
    (fun τ => ⟨be τ, de τ, hdat τ, by rw [hSn]; exact hflip τ, by rw [hSo]; exact hlow τ⟩)
    _ _ (GlobalTheory.Grid.WRep.toSgn true ω) hω (fun τ => ⟨haS τ, haT τ⟩) f hvac
  obtain ⟨It, hIt⟩ := hback (G.V i j).M R.θ hθ ω _ It₁ hIt₁
  have hpt : GlobalTheory.Chain.ptOf R.ψ R.θ M₁ (G.V i j).M f =
      ⇑(GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) := by
    unfold GlobalTheory.Chain.ptOf GlobalTheory.Grid.fock
    rw [hc, ho]
  exact ⟨It, hpt ▸ hIt⟩

end GlobalTheory.GridJoin.ArrX
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_real_intertwiner_grid_arrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∀ (ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V) (f : WO (G.V (i + 1) j).V (G.V i j).V → ℂ), GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω → GlobalTheory.Grid.IsVac R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f → ∃ It : GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j) →ₗ[ℂ] SmT (G.V i j).M →ₗ[ℂ] SmT (G.V (i + 1) j).M, IsItW R.θ (G.V (i + 1) j).M (G.V i j).M ω (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) f) It := by
  atlas_forward_decl GlobalTheory.GridJoin.ArrX.exists_intertwiner
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JoinArrows

theorem weil_arrow_transport {D : D7} {ψ : AddChar (AF ↥D.host.F) ℂ} {S T S' T' : HSp D}
    (hS : S = S') (hT : T = T') {χS χT χS' χT' : (AE D)ˣ →* Circle} (h1 : χS = χS') (h2 : χT = χT')
    (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS' χT' ω') :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ false S T χS χT ω ∧ HEq ω ω' := by
  cases hS
  cases hT
  cases h1
  cases h2
  refine ⟨ω', ?_, HEq.rfl⟩
  rw [GlobalTheory.Grid.isWeil_false]
  exact h

theorem exists_weil_rowArrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) ω ∧ HEq ω (W.om (.mu t (i + 1) j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hSp _ hAg _ t i j hi hj

  have hw := W.om_is (.mu t (i + 1) j) ⟨hi, hj⟩
  rw [hW.ψ] at hw

  have e1 : (G.nV i j).V = G'.V (.grid (i + 1) j) := (hAg.vert (i + 1) j hi (by omega)).sp
  have e2 : (G.nV i (j + 1)).V = G'.V (.grid (i + 1) (j + 1)) := (hAg.vert (i + 1) (j + 1) hi hj).sp

  have r1 : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← e1]; exact (hSp.vert i j hi (by omega)).rank
  have r2 : (G'.V (.grid (i + 1) (j + 1))).rank = rkV D (i + 1) (j + 1) := by
    rw [← e2]; exact (hSp.vert i (j + 1) hi hj).rank

  have c1 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j) = G'.chrS (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) j)).rank
    rw [r1]
    rfl
  have c2 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1)) = G'.chrT (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) (j + 1))).rank
    rw [r2]
    rfl
  exact weil_arrow_transport e1 e2 c1 c2 (W.om (.mu t (i + 1) j)) hw

end GlobalTheory.JoinArrows
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GridJoin

theorem isVacO_transport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) :
    ∀ (S S' S₀ S₀' : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (a' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ)
      (a₀ : D.what₂.Tau → Matrix (Fin S₀.rank) (Fin S₀.rank) ℂ)
      (a₀' : D.what₂.Tau → Matrix (Fin S₀'.rank) (Fin S₀'.rank) ℂ)
      (Λ : Set (Fin S.rank → D.host.E)) (Λ' : Set (Fin S'.rank → D.host.E))
      (Λ₀ : Set (Fin S₀.rank → D.host.E)) (Λ₀' : Set (Fin S₀'.rank → D.host.E)),
      S = S₀ → S' = S₀' → HEq a a₀ → HEq a' a₀' → HEq Λ Λ₀ → HEq Λ' Λ₀' →
      (∃ f, IsVacO ψ θ S₀ S₀' a₀ a₀' Λ₀ Λ₀' f) → ∃ f, IsVacO ψ θ S S' a a' Λ Λ' f := by
  rintro S S' _ _ a a' a₀ a₀' Λ Λ' Λ₀ Λ₀' rfl rfl h1 h2 h3 h4 h
  cases eq_of_heq h1; cases eq_of_heq h2; cases eq_of_heq h3; cases eq_of_heq h4
  exact h

theorem heq_coe_lat {D : D7} {V V' : HSp D} (h : V = V') {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (hΛ : HEq Λ Λ') :
    HEq (Λ : Set (Fin V.rank → D.host.E)) (Λ' : Set (Fin V'.rank → D.host.E)) := by
  subst h; cases eq_of_heq hΛ; rfl

theorem exists_isVac_th_rows : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hS _ i j hi hj
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .mu A.μ0 (i + 1) j) ⟨hi, by omega⟩
  have a := hS.vert (i + 1) j hi hj.le
  have b := hS.vert (i + 1) (j + 1) hi hj
  rw [← hW.ψ, ← hW.θ]
  exact isVacO_transport W.ψ W.θ _ _ _ _ _ _ _ _ _ _ _ _ a.sp b.sp a.cart b.cart
    (heq_coe_lat a.sp a.lat) (heq_coe_lat b.sp b.lat) ⟨f, hf⟩

end GlobalTheory.GridJoin
end

section
section
noncomputable section

section Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem itPair_of_par (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') {θ : InfFam D} (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ)
    (hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ Formalism.BasicNotions.TH.block t ++ de) (ga ++ be) (aS τ))) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
      ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ),
        GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨t, al, be, ga, de, hd, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) M M' τ hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, hI.ne, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
    fun τ => (hv τ).2.2

end GlobalTheory.RowThetaIt

end Gen

section Par

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid GlobalTheory.PairLift GlobalTheory.SignedHC GlobalTheory.RemoveBlock
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem dataAR_row (D : D7) (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (i j : ℕ) (τ : D.what₂.Tau) (hi : i ≤ D.R.m) (hj : j < D.R.m) :
    ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      parV D i j τ = dualPar (signed (al ++ be) (ga ++ de) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)))) ∧
      parV D i (j + 1) τ =
        dualPar (signed (al ++ Formalism.BasicNotions.TH.block t ++ de) (ga ++ be) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j))) := by
  have he : (D.hc τ).e ⟨j, hj⟩ = ((grid D τ).e (j + 1) : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.2 ⟨j, hj⟩
  set G := grid D τ with hG
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδ
  set δ' : ℚ := if Odd (i + (j + 1)) then -(1 / 2) else 0 with hδ'
  have hT : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)) = -(G.e (j + 1) : ℚ) + δ := by
    simp only [att, he, hδ]
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_true]; ring
    · have h' : ¬ Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_false]; ring
  have hS' : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j) = -(G.e (j + 1) : ℚ) + δ' := by
    simp only [att, he, hδ']
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i j) ↔ False := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) ↔ False := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_false]; ring
    · have h' : Odd (rkV D i j) := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_true]; ring
  rw [hT, hS']
  set P := shift δ (G.parD i j) with hP
  have hpart := partner_parD D τ i j hi hj δ δ'
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hN : 1800 < bigN D := by
    have h1 := hS.1
    have h2 : D.R.m ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold bigN; unfold Ranks.r at h1
    omega
  have hgap : GapOver P (2 * (bigN D : ℚ) ^ 3) := GlobalTheory.RemoveBlock.gapOver_shift (gapOver_parD D hS τ i j hi hj.le)
  have hgap' : GapOver (partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) (-(G.e (j + 1) : ℚ) + δ') P)
      (2 * (bigN D : ℚ) ^ 3) := by
    rw [hP, ← hpart]; exact GlobalTheory.RemoveBlock.gapOver_shift (gapOver_parD D hS τ i (j + 1) hi hj)
  have hreg : IsRegular P := isRegular_of_gapOver (by positivity) hgap
  have hfar3 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 3) / 2) P := farFrom_shift (farFrom_parD D τ i j hi hj)
  have hfar1 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 1) / 2) P := fun x hx =>
    le_trans (by linarith) (hfar3 x hx)
  have hne : P.Nonempty := by
    have hv : ((grid D τ).v 2 : ℚ) ∈ (grid D τ).cloud :=
      GridData.mem_cloud.2 ⟨2, le_rfl, by have := D.R.m_add_three_le_k; show 2 ≤ D.R.k; omega, rfl⟩
    have hmem : (((grid D τ).v 2 : ℚ), true) ∈ (grid D τ).parD i j := GridData.mem_parD.2 (Or.inl ⟨hv, rfl⟩)
    exact ⟨_, mem_shift' hmem⟩
  have hcard : P.card + D.R.t ≤ bigN D := by
    rw [hP, card_shift]
    have h0 : (G.parD i j).card ≤ rkV D i j := card_parD_le D τ i j hi
    have a : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
    have b : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
    have c : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    have d : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
    show _ ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    unfold rkV Ranks.r at h0
    omega
  have hcos : InCoset (-(G.e (j + 1) : ℚ) + δ + ((D.R.t : ℚ) + 1) / 2) (entries P) := by
    intro x hx
    obtain ⟨s, hs⟩ := mem_entries.1 hx
    have hy := fst_mem_entries (mem_shift.1 hs)
    obtain ⟨z, hz⟩ := int_parD D τ i j _ hy
    simp only at hz
    obtain ⟨q, hq⟩ := D.R.t_odd
    have htq : ((D.R.t : ℚ) + 1) / 2 = q + 1 := by rw [hq]; push_cast; ring
    refine ⟨z + G.e (j + 1) - (q + 1), ?_⟩
    rw [htq]; push_cast; linarith
  obtain ⟨al, be, ga, de, hPe, hP'⟩ :=
    GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter D.R.t true _ _ P (bigN D) ht hne hreg hcos hfar1 hcard hN hgap hgap'
  rcases hP' with ⟨hd, hP'⟩ | ⟨-, hP'⟩
  · refine ⟨D.R.t, al, be, ga, de, hd, ?_, ?_⟩
    · rw [← hPe]; rfl
    · rw [← hP', ← hpart]; rfl
  · exfalso
    set c' : ℚ := -(G.e (j + 1) : ℚ) + δ' with hc'
    have hx0 : ((D.R.t : ℚ) - 1) / 2 ∈ Formalism.BasicNotions.TH.block D.R.t :=
      by simp only [Formalism.BasicNotions.TH.block, List.mem_map, List.mem_range]; simp; exact ⟨0, by omega, by simp⟩
    have m1 : (((D.R.t : ℚ) - 1) / 2 + c', false) ∈ partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) c' P := by
      rw [hP']
      simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map]
      exact Or.inr ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hx0))), rfl⟩
    have m2 : (((D.R.t : ℚ) - 1) / 2 + c', true) ∈ partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) c' P := by
      simp only [partner, Finset.mem_union, Finset.mem_image]
      refine Or.inr ⟨_, mem_block.2 ⟨0, by omega, by push_cast; ring⟩, rfl⟩
    have := hgap' _ m1 _ m2 (by simp)
    simp only [sub_self, abs_zero] at this
    have : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
    linarith

end GlobalTheory.RowThetaIt

end Par

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem rowTheta_it : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∀ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ), (∀ t, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) (ω t)) → GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f → ∃ It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M, ∀ t, IsItW R.θ (G.nV i j).M (G.nV i (j + 1)).M (ω t) (GlobalTheory.Grid.fock R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f) It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hD hH _ hSz F hc _ G' W _ G hSp _ _ _ i j hi hj ω f hω hf
  have hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R := ⟨hc.lev, hc.models.inf, hc.models.νY, hc.models.νY', hc.models.νX⟩
  have hV := hSp.vert i j hi hj.le
  have hV' := hSp.vert i (j + 1) hi hj
  obtain ⟨It, -, hIt⟩ := itPair_of_par hD hH (G.nV i j).M (G.nV i (j + 1)).M hR.inf R.ψ
    (fun τ => GlobalTheory.PairLift.att (-(D.hc τ).e ⟨j, hj⟩) (rkV D (i + 1) j))
    (fun τ => GlobalTheory.PairLift.att (-(D.hc τ).e ⟨j, hj⟩) (rkV D (i + 1) (j + 1)))
    (fun τ => by rw [hV.par, hV'.par]; exact dataAR_row D hSz (i + 1) j τ hi hj)
  refine ⟨It, fun t => hIt (ω t) f ⟨_, _, hω t, fun τ =>
    ⟨GlobalTheory.PairLift.hasInfExp_att (GlobalTheory.PairLift.exp_mu hR t hj τ) (GlobalTheory.PairLift.exp_eta hR τ) _,
      GlobalTheory.PairLift.hasInfExp_att (GlobalTheory.PairLift.exp_mu hR t hj τ) (GlobalTheory.PairLift.exp_eta hR τ) _⟩⟩
    ⟨hf.isFinVec.1, GlobalTheory.PairLift.vac_ne hf, hf.isFinVec.2⟩⟩

end GlobalTheory.RowThetaIt

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridRowArrow_exists_common_realIntertwiner : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∀ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ), (∀ t, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) (ω t)) → GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f → ∃ It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M, ∀ t, IsItW R.θ (G.nV i j).M (G.nV i (j + 1)).M (ω t) (GlobalTheory.Grid.fock R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f) It := by
  atlas_forward_decl GlobalTheory.RowThetaIt.rowTheta_it
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isWeil_of_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S S' T' Tg : HSp D} (hS : S = S') (hT : Tg = T')
    {χS χT : (AE D)ˣ →* Circle} (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS χT ω') :
    ∃ ω : GlobalTheory.Grid.WRep S Tg, GlobalTheory.Grid.IsWeil ψ false S Tg χS χT ω ∧ HEq ω ω' := by
  subst hS hT
  exact ⟨ω', h, HEq.rfl⟩

theorem omCol_of_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V, GlobalTheory.Grid.IsWeil R.ψ false (G.Xp j).V (G.nX j).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ω ∧ HEq ω (W.om (.top t j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ t j hj
  have hS : (G.Xp j).V = G'.V (.top j) := (hSp.top j hj.le).sp
  have hT : (G.nX j).V = G'.V (.top (j + 1)) := (hSp.top (j + 1) hj).sp
  have hω := W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have hr : ∀ k, k ≤ D.R.m → Even (G'.V (.top k)).rank := fun k hk => by
    have := (G'.isV (X := .top k) hk (fun _ h => by cases h)).rank
    rw [this]; exact even_rankX D k
  have eS : G'.chrS (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrS, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr j hj.le)]
  have eT : G'.chrT (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrT, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr (j + 1) hj)]
  rw [eS, eT, hW.ψ] at hω
  exact exists_isWeil_of_eq hS hT _ hω

end GlobalTheory.GridJoin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isVac_of_nodeAgree {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}
    {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) {N₁ N₂ : GlobalTheory.Grid.Node D} {X₁ X₂ : GlobalTheory.ChiGrid.Node}
    (h₁ : NodeAgree N₁ W X₁) (h₂ : NodeAgree N₂ W X₂) (f : WO (G'.V X₁) (G'.V X₂) → ℂ)
    (hf : IsVacO W.ψ W.θ (G'.V X₁) (G'.V X₂) (W.cart X₁) (W.cart X₂) (G'.Λ X₁ : Set _) (G'.Λ X₂ : Set _) f) :
    ∃ f' : WO N₁.V N₂.V → ℂ, GlobalTheory.Grid.IsVac W.ψ W.θ false N₁ N₂ f' := by
  obtain ⟨V₁, S₁, M₁, Λ₁, β₁⟩ := N₁
  obtain ⟨V₂, S₂, M₂, Λ₂, β₂⟩ := N₂
  obtain ⟨sp₁, lat₁, cart₁, -⟩ := h₁
  obtain ⟨sp₂, lat₂, cart₂, -⟩ := h₂
  dsimp only at sp₁ sp₂ lat₁ lat₂ cart₁ cart₂
  subst sp₁ sp₂
  cases eq_of_heq lat₁
  cases eq_of_heq lat₂
  refine ⟨f, ?_⟩
  have c₁ := eq_of_heq cart₁
  have c₂ := eq_of_heq cart₂
  unfold GlobalTheory.Grid.IsVac GlobalTheory.Grid.cartS
  simp only [GlobalTheory.Grid.sgnM, cond]
  rw [c₁, c₂]
  exact hf

theorem exists_isVac_col : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ j, j < D.R.m → ∃ f : WO (G.Xp j).V (G.nX j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.Xp j) (G.nX j) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hA _ j hj
  have hp : (GlobalTheory.ChiGrid.Pair.top A.μ0 j).InRange D.R.m := by
    simp only [GlobalTheory.ChiGrid.Pair.InRange, GlobalTheory.ChiGrid.Pair.big, GlobalTheory.ChiGrid.Node.InRange]
    omega
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev hp
  obtain ⟨f', hf'⟩ := exists_isVac_of_nodeAgree W (hA.top j hj.le) (hA.top (j + 1) hj) f hf
  rw [hW.ψ, hW.θ] at hf'
  exact ⟨f', hf'⟩

end GlobalTheory.GridJoin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid in

theorem exists_wrep_of_eq {D : D7} {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χ χ' : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χ χ' om) :
    ∃ ω : WRep S T, IsWeil ψ true S T χ χ' ω ∧ HEq (ω.toSgn true) om := by
  subst hS hT
  let ω : WRep S T := om.comp ((ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _))
  have e : ω.toSgn true = om := MonoidHom.ext fun x => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  unfold IsWeil
  rw [e]
  exact h

theorem core_arrows_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.P (i + 1)).V (G.P i).V, GlobalTheory.Grid.IsWeil R.ψ true (G.P (i + 1)).V (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ω ∧ HEq (ω.toSgn true) (W.om (.core i)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ i hi
  have h1 : 1 ≤ D.R.m - i := by omega
  have h2 : D.R.m - i ≤ D.R.m := Nat.sub_le _ _
  have hom := W.om_is (.core i) (show (i + 1) ≤ D.R.m by omega)
  rw [(G'.chr_core (by omega : i + 1 ≤ D.R.m)).1, (G'.chr_core (by omega : i + 1 ≤ D.R.m)).2, hW.ψ,
    ← hSp.chi _ h1 h2] at hom
  exact exists_wrep_of_eq (hSp.core (i + 1) (by omega)).sp (hSp.core i (by omega)).sp _ _ _ _ hom

end GlobalTheory.GridJoin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem exists_isVac_true_of_agree {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {N₁ N₀ : GlobalTheory.Grid.Node D} {V₁ V₀ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)}
    {c₁ : D.what₂.Tau → Matrix (Fin V₁.rank) (Fin V₁.rank) ℂ} {c₀ : D.what₂.Tau → Matrix (Fin V₀.rank) (Fin V₀.rank) ℂ}
    (h₁ : N₁.V = V₁) (hΛ₁ : HEq N₁.Λ Λ₁) (hc₁ : HEq (Formalism.IndefR.Links.cart N₁.M) c₁)
    (h₀ : N₀.V = V₀) (hΛ₀ : HEq N₀.Λ Λ₀) (hc₀ : HEq (Formalism.IndefR.Links.cart N₀.M) c₀)
    {f : WO (negSp V₁) V₀ → ℂ} (hf : IsVacO ψ θ (negSp V₁) V₀ (fun τ => -c₁ τ) c₀ (Λ₁ : Set _) (Λ₀ : Set _) f) :
    ∃ f' : WO N₁.V N₀.V → ℂ, GlobalTheory.Grid.IsVac ψ θ true N₁ N₀ f' := by
  subst h₁ h₀
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₀
  obtain rfl := eq_of_heq hc₁
  obtain rfl := eq_of_heq hc₀
  exact ⟨f, hf⟩

end GlobalTheory.GridJoin

theorem GlobalTheory.GridJoin.exists_isVac_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ f : WO (G.P (i + 1)).V (G.P i).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hsp _ i hi
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .core i) (show (GlobalTheory.ChiGrid.Node.core (i + 1)).InRange D.R.m from (by show i + 1 ≤ D.R.m; omega))
  have a₁ := hsp.core (i + 1) (by omega)
  have a₀ := hsp.core i (by omega)
  unfold GlobalTheory.ChiGrid.GridData.Weil.IsVac at hf
  rw [hW.ψ, hW.θ] at hf
  exact GlobalTheory.GridJoin.exists_isVac_true_of_agree a₁.sp a₁.lat a₁.cart a₀.sp a₀.lat a₀.cart hf

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem arrS_cast_weil_vac {D : D7} {S S' T T' : Node D} (hS : S = S') (hT : T = T') (a : ArrS S T)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) {α : Type} (ω' : α)
    (hw : IsWeil ψ false S.V T.V χS χT a.ω) (hv : IsVac ψ θ false S T a.vac) (ho : HEq a.ω ω') :
    IsWeil ψ false S'.V T'.V χS χT (a.cast hS hT).ω ∧ IsVac ψ θ false S' T' (a.cast hS hT).vac ∧
      HEq (a.cast hS hT).ω ω' := by
  subst hS hT
  exact ⟨hw, hv, ho⟩

theorem chainStepCharacters_eq_gridRowZero_ranks {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (j : ℕ) :
    Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) =
      (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

theorem testGridRowZeroArrows_weil_vacua_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → GlobalTheory.Grid.IsWeil R.ψ false (GlobalTheory.Grid.row0 R j).V (GlobalTheory.Grid.row0 R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (GlobalTheory.Grid.th0 R t j).ω ∧ GlobalTheory.Grid.IsVac R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac ∧ HEq (GlobalTheory.Grid.th0 R t j).ω (W.om (.mu t 0 j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ _ _ t j hj
  have hc := chainStepCharacters_eq_gridRowZero_ranks R t j
  by_cases h : j + 1 < D.R.m
  · have hw : IsWeil R.ψ false (nodeY R j).V (nodeY R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepY R t j).ω := by
      have := hR.chain.ωY t j h
      rw [hc] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R j) (nodeY R (j + 1)) (stepY R t j).vac := (hR.chain.vY t j h).1
    have key := arrS_cast_weil_vac (nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (nodeY_eq_chainVertexAtRowZero_of_lt R h) (stepY R t j) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omY t j h).symm
    unfold th0
    rw [dif_pos h]
    exact key
  · have h' : j + 1 = D.R.m := by omega
    have hw : IsWeil R.ψ false (nodeY R (D.R.m - 1)).V (nodeX R).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepX R t).ω := by
      have hc' : Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m =
          (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
        rw [← h']; exact hc
      have := hR.chain.ωX t
      rw [hc'] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R (D.R.m - 1)) (nodeX R) (stepX R t).vac := (hR.chain.vX t).1
    have key := arrS_cast_weil_vac (nodeY_pred_eq_chainVertexAtRowZero_last R h') (nodeX_eq_chainVertexAtRowZero_of_ge R h) (stepX R t) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omX t j h').symm
    unfold th0
    rw [dif_neg h, dif_pos h']
    exact key

end GlobalTheory.GridJoin

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin.RowArrows

theorem vY_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) {k : ℕ} (hk : k + 1 < D.R.m) : R.vY t k ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D k) (Yc D (k + 1)) // a.map (infPart D) = 0} => heisO R.ψ _ _ a (R.vac k)) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ hk)) (h.chain.vY t k hk)

theorem vX_mem_span_core {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (h : GlobalTheory.Hk3.Core R F) (t : T) : R.vX t ∈ Submodule.span ℂ (Set.range
    fun a : {a : WO (Yc D (D.R.m - 1)) D.sp.X' // a.map (infPart D) = 0} => heisO R.ψ _ _ a R.vacX) :=
  GlobalTheory.Grid.stepVec_mem_span (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (h.lev.βY _ (by have := D.R.two_le_m; omega)))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ h.lev.βX) (h.chain.vX t)

theorem chainIntertwiners_rowZero_unitVacua : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → IsItW R.θ (GlobalTheory.Grid.row0 R j).M (GlobalTheory.Grid.row0 R (j + 1)).M (GlobalTheory.Grid.th0 R t j).ω (GlobalTheory.Grid.fock R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac) (GlobalTheory.Grid.th0 R t j).It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F h _ G' W _ G _ _ _ _ t j hj
  unfold GlobalTheory.Grid.th0
  by_cases h1 : j + 1 < D.R.m
  · rw [dif_pos h1]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepY R t j)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (GlobalTheory.Grid.nodeY_eq_chainVertexAtRowZero_of_lt R h1))
    have hω := h.chain.ωY t j h1
    rw [GlobalTheory.Grid.chrStep_eq_muAt] at hω
    exact (hc.2 ⟨hω, (h.chain.vY t j h1).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vY t j h1).1.2.theta (vY_mem_span_core h t h1) (h.chain.ItY t j h1)⟩).intw
  · have h2 : j + 1 = D.R.m := by omega
    rw [dif_neg h1, dif_pos h2]
    have hc := (GlobalTheory.Grid.ArrS.is_cast (ψ := R.ψ) (θ := R.θ) (ε := false) (a := GlobalTheory.Grid.stepX R t)
      (χS := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 j))
      (χT := GlobalTheory.Grid.GridPre.muAt R t (j + 1) (GlobalTheory.Grid.rkV D 0 (j + 1))) (GlobalTheory.Grid.nodeY_pred_eq_chainVertexAtRowZero_last R h2) (GlobalTheory.Grid.nodeX_eq_chainVertexAtRowZero_of_ge R h1))
    have hω := h.chain.ωX t
    rw [(congrArg _ h2.symm).trans (GlobalTheory.Grid.chrStep_eq_muAt R t j)] at hω
    exact (hc.2 ⟨hω, (h.chain.vX t).1,
      GlobalTheory.Grid.isItW_of_mem_span hω h.models.inf (h.chain.vX t).1.2.theta (vX_mem_span_core h t) (h.chain.ItX t)⟩).intw

end GlobalTheory.GridJoin.RowArrows

end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

theorem exists_arrows : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∃ X ωT vacT ItT ωC vacC ItC dn ItU vC, (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsArrows ∧ (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsData ∧ ArrAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH hS F hR hsc G' W hW G hsp hch hag hcos
  have wX := GlobalTheory.GridJoin.exists_omX_of_agree hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vX := GlobalTheory.GridJoin.exists_vacX hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iX := GlobalTheory.T.exists_nonzero_real_intertwiner_grid_arrow hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
  have wT := GlobalTheory.JoinArrows.exists_weil_rowArrow hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vT := GlobalTheory.GridJoin.exists_isVac_th_rows hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iT := GlobalTheory.T.gridRowArrow_exists_common_realIntertwiner hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
  have wC := GlobalTheory.GridJoin.omCol_of_weil hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vC := GlobalTheory.GridJoin.exists_isVac_col hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iC := GlobalTheory.GridJoin.ColIt.exists_col_intertwiner hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have wD := GlobalTheory.GridJoin.core_arrows_weil hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have vD := GlobalTheory.GridJoin.exists_isVac_down hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have iD := GlobalTheory.T.exists_downArrow_realIntertwiner_with_adjoint hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have r0w := GlobalTheory.GridJoin.testGridRowZeroArrows_weil_vacua_agree hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have r0i := GlobalTheory.GridJoin.RowArrows.chainIntertwiners_rowZero_unitVacua hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have dT := GlobalTheory.T.exists_gridCosetData_eq_weilCosetVectors hDC hHC hH hR hsc W hW G hsp hch hag hcos
  have hXa : ∀ i j, ∃ a : GlobalTheory.Grid.ArrS (G.V (i + 1) j) (G.V i j), i < D.R.m → j ≤ D.R.m →
      a.Is R.ψ R.θ true (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ∧
      HEq (a.ω.toSgn true) (W.om (.chi i j)) ∧ (j = 0 → HEq a.vac (W.vac i)) := by
    intro i j
    by_cases h : i < D.R.m ∧ j ≤ D.R.m
    · obtain ⟨ω, hω, hωa⟩ := wX i j h.1 h.2
      obtain ⟨f, hf, hf0⟩ := vX i j h.1 h.2
      obtain ⟨It, hIt⟩ := iX i j h.1 h.2 ω f hω hf
      exact ⟨⟨ω, f, It⟩, fun _ _ => ⟨⟨hω, hf, hIt⟩, hωa, hf0⟩⟩
    · exact ⟨⟨1, 0, 0⟩, fun a b => absurd ⟨a, b⟩ h⟩
  choose X hX using hXa
  have hTa : ∀ i j, ∃ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ)
      (It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M),
      i + 1 ≤ D.R.m → j < D.R.m → ∀ t, (⟨ω t, f, It⟩ : GlobalTheory.Grid.ArrS (G.nV i j) (G.nV i (j + 1))).Is R.ψ R.θ false
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) ∧
        HEq (ω t) (W.om (.mu t (i + 1) j)) := by
    intro i j
    by_cases h : i + 1 ≤ D.R.m ∧ j < D.R.m
    · choose ω hω hωa using fun t => wT t i j h.1 h.2
      obtain ⟨f, hf⟩ := vT i j h.1 h.2
      obtain ⟨It, hIt⟩ := iT i j h.1 h.2 ω f hω hf
      exact ⟨ω, f, It, fun _ _ t => ⟨⟨hω t, hf, hIt t⟩, hωa t⟩⟩
    · exact ⟨fun _ => 1, 0, 0, fun a b => absurd ⟨a, b⟩ h⟩
  choose ωT vacT ItT hT using hTa
  have hCa : ∀ j, ∃ (ω : T → GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V) (f : WO (G.Xp j).V (G.nX j).V → ℂ)
      (It : GlobalTheory.Grid.Pol (G.Xp j) (G.nX j) →ₗ[ℂ] SmT (G.Xp j).M →ₗ[ℂ] SmT (G.nX j).M),
      j < D.R.m → ∀ t, (⟨ω t, f, It⟩ : GlobalTheory.Grid.ArrT (G.Xp j) (G.Xp (j + 1))).Is R.ψ R.θ false
        (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ∧ HEq (ω t) (W.om (.top t j)) := by
    intro j
    by_cases h : j < D.R.m
    · choose ω hω hωa using fun t => wC t j h
      obtain ⟨f, hf⟩ := vC j h
      obtain ⟨It, hIt⟩ := iC j h ω f hω hf
      exact ⟨ω, f, It, fun _ t => ⟨⟨hω t, hf, hIt t⟩, hωa t⟩⟩
    · exact ⟨fun _ => 1, 0, 0, fun a => absurd a h⟩
  choose ωC vacC ItC hC using hCa
  have hDa : ∀ i, ∃ (a : GlobalTheory.Grid.ArrT (G.P (i + 1)) (G.P i))
      (U : GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M), i < D.R.m →
      a.Is R.ψ R.θ true (G.chi (D.R.m - i)) (G.chi (D.R.m - i)) ∧ a.IsAdj U ∧ HEq (a.ω.toSgn true) (W.om (.core i)) := by
    intro i
    by_cases h : i < D.R.m
    · obtain ⟨ω, hω, hωa⟩ := wD i h
      obtain ⟨f, hf⟩ := vD i h
      obtain ⟨It, U, hIt, hU⟩ := iD i h ω f hω hf
      exact ⟨⟨ω, f, It⟩, U, fun _ => ⟨⟨hω, hf, hIt⟩, hU, hωa⟩⟩
    · exact ⟨⟨1, 0, 0⟩, 0, fun a => absurd a h⟩
  choose dn ItU hD using hDa
  have hVa : ∀ i, ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), i < D.R.m →
      (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c (X i 0).vac (v c)) ∧
      (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
    intro i
    by_cases h : i < D.R.m
    · obtain ⟨v, hv⟩ := dT i h (X i 0).vac ((hX i 0 h (Nat.zero_le _)).2.2 rfl)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨fun _ _ => 0, fun h' => absurd h' h⟩
  choose vCo hvC using hVa
  refine ⟨X, fun t i j => ωT i j t, vacT, ItT, fun t j => ωC j t, vacC, ItC, dn, ItU, vCo,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun i j hi hj => (hX i j hi hj).1
  · intro t i j hi hj
    cases i with
    | zero => exact ⟨(r0w t j hj).1, (r0w t j hj).2.1, r0i t j hj⟩
    | succ i => exact (hT i j hi hj t).1
  · exact fun t j hj => (hC j hj t).1
  · exact fun i hi => (hD i hi).1
  · exact fun i hi => (hD i hi).2.1
  · exact fun i hi c => (hvC i hi).1 c
  · exact fun i j hi hj => (hX i j hi hj).2.1
  · intro t i j hi hj
    cases i with
    | zero => exact (r0w t j hj).2.2
    | succ i => exact (hT i j hi hj t).2
  · exact fun t j hj => (hC j hj t).2
  · exact fun i hi => (hD i hi).2.2
  · exact fun i hi => (hX i 0 hi (Nat.zero_le _)).2.2 rfl
  · exact fun i hi => (hvC i hi).2

end GlobalTheory.GridJoin

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_testGrid_arrows_vacua_intertwiners : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∃ X ωT vacT ItT ωC vacC ItC dn ItU vC, (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsArrows ∧ (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsData ∧ ArrAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
  atlas_forward_decl GlobalTheory.GridJoin.exists_arrows
end
