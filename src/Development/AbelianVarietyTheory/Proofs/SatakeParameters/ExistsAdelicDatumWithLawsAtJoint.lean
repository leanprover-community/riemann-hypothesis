import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAut
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointRightTranslateByChartLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetEqChartPointCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChain
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwChainWtSharpDivDe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastColumnStepDatumEqTwistTopDatum
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepKernelDataIntegralAwayFromLevels
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumDependsOnlyAtBadPlacesMatrixStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelEquivarianceAtMatrixSteps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumDependsOnlyAtBadPlacesFirstCoupledSte
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumLevelEquivarianceFirstCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SymmTransSymm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivariance

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalCoords_conj_unitary_standard_form : ∀ (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (crd γ : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E) = J → γ ∈ UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J → cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  first | exact @GlobalTheory.unitary_conj_orthonormal | exact GlobalTheory.unitary_conj_orthonormal | (intros; apply GlobalTheory.unitary_conj_orthonormal <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.RatLat

theorem lat_gmap {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat (Formalism.HermitianLatticesTheory.gmap g N) = Formalism.MainNotions.G.KAat.mvL (seamGL s g) (s.lat N) := by
  unfold Seam.lat Formalism.HermitianLatticesTheory.gmap Formalism.MainNotions.G.KAat.mvL
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  rw [Formalism.MainNotions.G.KAat.toLE_apply, seamGL_mulVec]

end GlobalTheory.RatLat
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedLattice_of_linearAutImage_eq_matrixImage : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)), s.lat (Formalism.HermitianLatticesTheory.gmap g N) = Formalism.MainNotions.G.KAat.mvL (seamGL s g) (s.lat N) := by
  atlas_forward_decl GlobalTheory.RatLat.lat_gmap
end

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : Formalism.L2.Forms.StepLevel D.host.F D.host.E (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (hh : GLG X.E (D.R.N i) SG), FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (ratA D.host.F (seamGL s g) * x) (d.act g hh) := by
  first | exact @GlobalTheory.TwU.funMoved_ratA_act | exact GlobalTheory.TwU.funMoved_ratA_act | (intros; apply GlobalTheory.TwU.funMoved_ratA_act <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST SG) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG X.E n SG)) • d).1.liftFr w)) := by
  first | exact @GlobalTheory.FrameRat.nearAt_liftFr_smul | exact GlobalTheory.FrameRat.nearAt_liftFr_smul | (intros; apply GlobalTheory.FrameRat.nearAt_liftFr_smul <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem ratPt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi β x x' p γ hγ hx hp
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_unitaryAut_columnField_of_standard_unitary_matrix t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹) (GlobalTheory.T.orthonormalCoords_conj_unitary_standard_form D _ _ _ (hP.crd_orth i hi) hγ)
  have hmv : ∀ y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      ratA D.host.F (A.crd i hi) * (ratA D.host.F γ * y) = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * y) := by
    intro y
    rw [hg, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel_right]
  let a' : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K)) := (g, 1, 1)
  refine ⟨a' • p, ?_, ?_, ?_⟩
  · have e1 : (a' • p).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
    rw [e1, GlobalTheory.T.transportedLattice_of_linearAutImage_eq_matrixImage, hg, hp.lat, hx, latCo_rat _ _ _ hγ]
  · intro P
    have hb := hp.frame P
    rw [hx, hmv, mul_assoc (ratA D.host.F (seamGL t.seam g.1))]
    by_cases hPg : P.1 ∈ t.Pr.vGs
    · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hPg
      have e0 : frsF t.sel (t.tup μ) p P = p.deco.1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = ((g, (1 : GLG t.X.E (D.R.N i) t.Pr.vGs)) • p.deco).1.liftFr ⟨P.1, hPg⟩ := dif_pos hPg
      rw [hD, e0] at hb
      rw [hD, e1]
      exact GlobalTheory.T.levelFrameLift_unitaryAut_near_adelicMatrix_depth_one t.seam p.deco ⟨P.1, hPg⟩ g (mq_rowSG_unif (t.tup μ) hP.fields.ok t.pr_ok hP.sel P) _ hb
    · have e1 : frsF (R := D.R) t.sel (t.tup μ) (a' • p) P = g.1 * frsF t.sel (t.tup μ) p P := by
        unfold frsF
        rw [dif_neg hPg, dif_neg hPg]
        show g.1 * p.fr _ * (((1 : GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) _)⁻¹).1 = _
        simp
      rw [e1, map_mul, nearAt_rat_mul]
      exact hb
  · intro P v h hv
    rw [hx, hmv]
    exact GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)

end GlobalTheory.TwRat
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoint_leftTranslate_rationalUnitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  atlas_forward_decl GlobalTheory.TwRat.ratPt
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cls

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

theorem isPtAd_cls (H : AdTie A dtU a) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i) :
    IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) where
  lat := by
    rw [← H.N_eq i hi c]
    exact H.lat i hi c
  frame := fun P => H.frame i hi c P
  fnl := by
    intro P v h hv
    exact Classical.epsilon_spec (H.fnl i hi ((St i hi).chOf c) P v h hv) c rfl

theorem exists_cls_eq (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) :
    ∃ c : (D.chTw u μ).cls i, (St i hi).chOf c = β ∧ ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      ∃ κ : ((St i hi).K β).lev.U, x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 := by
  obtain ⟨⟨c, rfl⟩, hc⟩ := ((St i hi).K β).y_bij.2 (Quotient.mk'' x)
  obtain ⟨g, hg, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 hc
  rw [Subgroup.mem_subgroupOf] at hg hk
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.1 hg
  refine ⟨c, rfl, γ, hγ, ⟨k.1, hk⟩, ?_⟩
  have e1 := congrArg Subtype.val e
  simp only [Subgroup.coe_mul] at e1
  rw [e1, ← hγg]
  rfl

end Cls

theorem ptEx_of_tie (hR : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) (hL : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie
  have hcls : ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) :=
    fun i hi c => isPtAd_cls hTie i hi c
  refine ⟨fun i hi β x => ?_, hcls⟩
  obtain ⟨c, hcβ, γ, hγ, κ, hx⟩ := exists_cls_eq (St := St) i hi β x
  subst hcβ

  let k : UA D i hi := ⟨κ.1, (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2 |>.1⟩

  let x₁ : UA D i hi := x * k⁻¹
  have hx₁ : x₁.1 = ratA D.host.F γ * ((St i hi).y c).1 := by
    show x.1 * (κ.1)⁻¹ = _
    rw [hx, mul_inv_cancel_right]
  obtain ⟨p₁, hp₁⟩ := hR A dtU a hPin hTie i hi _ ((St i hi).y c) x₁ (A.pt i hi c) γ hγ hx₁ (hcls i hi c)
  have hxk : x.1 = x₁.1 * κ.1 := by
    show x.1 = x.1 * (κ.1)⁻¹ * κ.1
    rw [inv_mul_cancel_right]
  exact hL A dtU a hPin hTie i hi _ x₁ x p₁ κ hxk hp₁

theorem ptEx_isPtAd : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) :=
  ptEx_of_tie GlobalTheory.T.chartPoint_leftTranslate_rationalUnitary GlobalTheory.T.chartBasePoint_rightTranslate_by_chartLevel

end GlobalTheory.TwV
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoints_exist_and_classPoints_representatives : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) := by
  atlas_forward_decl GlobalTheory.TwV.ptEx_isPtAd
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_eq_chartPointCoset : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c) := by
  first | exact @GlobalTheory.TwV.cosetOf_eq_yb | exact GlobalTheory.TwV.cosetOf_eq_yb | (intros; apply GlobalTheory.TwV.cosetOf_eq_yb <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCharacterLaws_normOneIdeles_of_kernelChain : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU) := by
  first | exact @GlobalTheory.TwV.MuLawPf.muLaw_underTie | exact GlobalTheory.TwV.MuLawPf.muLaw_underTie | (intros; apply GlobalTheory.TwV.MuLawPf.muLaw_underTie <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DatTransport

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem mem_localization_of_smul_mem₂ {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (q : Ideal (𝓞 E)) [q.IsPrime] (L : Submodule (𝓞 E) W)
    {t : 𝓞 E} (ht : t ∈ q.primeCompl) {v : W} (h : t • v ∈ Formalism.HermitianLatticesTheory.localization₂ q L) : v ∈ Formalism.HermitianLatticesTheory.localization₂ q L := by
  obtain ⟨u, hu, huv⟩ := h
  exact ⟨u * t, q.primeCompl.mul_mem hu ht, by rw [mul_smul]; exact huv⟩

theorem mem_localization_map_iff {n : ℕ} (f : (Fin n → E) ≃ₗ[E] (Fin n → E)) (q : Ideal (𝓞 E)) [q.IsPrime]
    (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ q (L.map (f.toLinearMap.restrictScalars (𝓞 E))) ↔ f.symm y ∈ Formalism.HermitianLatticesTheory.localization₂ q L := by
  have hf : ∀ (r : 𝓞 E) (v : Fin n → E), f (r • v) = r • f v := fun r v => (f.toLinearMap.restrictScalars (𝓞 E)).map_smul r v
  constructor
  · rintro ⟨r, hr, z, hz, hzy⟩
    refine ⟨r, hr, ?_⟩
    have e1 : r • f.symm y = z := by
      apply f.injective
      rw [hf, f.apply_symm_apply]
      exact hzy.symm
    rw [e1]
    exact hz
  · rintro ⟨r, hr, hy⟩
    refine ⟨r, hr, r • f.symm y, hy, ?_⟩
    show f (r • f.symm y) = r • y
    rw [hf, f.apply_symm_apply]

end Gen

end GlobalTheory.DatTransport

namespace GlobalTheory.DatTransport

section PerO

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem perO_apply_mem (AA : Submodule (𝓞 E) E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (hAA : AA ≤ Formalism.HermitianLatticesTheory.localization₂ q (1 : Submodule (𝓞 E) E)) (M : Submodule (𝓞 E) (Sp E a)) (M' : Submodule (𝓞 E) (Sp E b))
    (w : HomE E a b) (hw : w ∈ Formalism.HermitianLatticesTheory.localization₂ q (perO AA M M')) :
    ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ q M, w y ∈ Formalism.HermitianLatticesTheory.localization₂ q M' := by
  intro y hy
  obtain ⟨t, ht, htw⟩ := hw
  have key : ∀ z ∈ perO AA M M', z y ∈ Formalism.HermitianLatticesTheory.localization₂ q M' := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨r, hr, x, hx, rfl⟩ := hz
      obtain ⟨t1, ht1, hy1⟩ := hy
      have hxy : t1 • x y ∈ M' := by
        have e0 : x (t1 • y) = t1 • x y := (x.restrictScalars (𝓞 E)).map_smul t1 y
        rw [← e0]
        exact hx _ hy1
      obtain ⟨t2, ht2, hr2⟩ := hAA hr
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 hr2
      refine ⟨t2 * t1, q.primeCompl.mul_mem ht2 ht1, ?_⟩
      have e1 : (t2 * t1) • ((r • x) y) = o • (t1 • x y) := by
        funext l
        rw [Algebra.smul_def] at ho
        simp only [LinearMap.smul_apply, Pi.smul_apply, Algebra.smul_def, smul_eq_mul, map_mul, ho, Pi.mul_apply,
          Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        ring
      rw [e1]
      exact M'.smul_mem o hxy
    | zero => exact zero_mem _
    | add z z' _ _ h1 h2 =>
      rw [LinearMap.add_apply]
      exact add_mem h1 h2
    | smul c z _ h =>
      rw [LinearMap.smul_apply]
      exact Submodule.smul_mem _ c h
  have h1 := key _ htw
  rw [LinearMap.smul_apply] at h1
  exact mem_localization_of_smul_mem₂ q M' ht h1

end PerO

end GlobalTheory.DatTransport

namespace GlobalTheory.DatTransport

section Seam

variable {D : D7} {X : Fields} (s : Seam D X)

theorem tr_smul {n : ℕ} (c : 𝓞 X.E) (x : Sp X.E n) :
    (fun i => s.iE ((c • x) i)) = RingOfIntegers.mapRingEquiv s.iE c • (fun i => s.iE (x i)) := by
  funext i
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
  rfl

theorem mem_seamLat_iff {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ ∃ x ∈ N, (fun i => s.iE (x i)) = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, N.zero_mem, by funext i; simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hz
      exact ⟨a + b, N.add_mem ha hb, by funext i; simp⟩
    | smul r y _ hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • a, N.smul_mem _ ha, ?_⟩
      rw [tr_smul, RingEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem tr_injective {n : ℕ} : Function.Injective (fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) := by
  intro x y h
  funext i
  exact s.iE.injective (congrFun h i)

theorem mem_localization_seamLat_iff (P : HeightOneSpectrum (𝓞 X.E)) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (x : Sp X.E n) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ (fun i => s.iE (x i)) ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  constructor
  · rintro ⟨c, hc, hcx⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE c, fun h => hc ((mem_seamP s P c).1 h), ?_⟩
    rw [← tr_smul]
    exact (mem_seamLat_iff s N _).2 ⟨_, hcx, rfl⟩
  · rintro ⟨d, hd, hdx⟩
    obtain ⟨c, rfl⟩ := (RingOfIntegers.mapRingEquiv s.iE).surjective d
    refine ⟨c, fun h => hd ((mem_seamP s P c).2 h), ?_⟩
    rw [← tr_smul] at hdx
    obtain ⟨x', hx', e⟩ := (mem_seamLat_iff s N _).1 hdx
    rw [tr_injective s e] at hx'
    exact hx'

theorem aaOf_le_locP_seamP (cc : Ideal (𝓞 D.host.K)) (Q : HeightOneSpectrum (𝓞 X.E))
    (h : Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0,
      r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (1 : Submodule (𝓞 X.E) X.E)) :
    Formalism.L2.PairingIndexBounds.F.aaOf D cc ≤ Formalism.HermitianLatticesTheory.localization₂ (seamP s Q).asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  unfold Formalism.L2.PairingIndexBounds.F.aaOf
  rw [Submodule.span_le]
  rintro _ ⟨c, hc, t, ht, rfl⟩
  have h1 : s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t) ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
    rw [← h]
    exact ⟨1, Q.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact Submodule.subset_span ⟨c, hc, t, ht, rfl⟩⟩
  obtain ⟨u, hu, hu1⟩ := h1
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 hu1
  refine ⟨RingOfIntegers.mapRingEquiv s.iE u, fun hh => hu ((mem_seamP s Q u).1 hh), ?_⟩
  refine Submodule.mem_one.2 ⟨RingOfIntegers.mapRingEquiv s.iE o, ?_⟩
  rw [Algebra.smul_def] at ho ⊢
  have e1 := congrArg s.iE ho
  rw [map_mul, RingEquiv.apply_symm_apply] at e1
  exact e1

end Seam

end GlobalTheory.DatTransport

namespace GlobalTheory.DatTransport

section Hom

variable {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ}

theorem seam_inFr_apply (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E))
    (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (w : HomE D.host.E a b) (u : Sp X.E a) :
    (fun l => s.iE (seamHom s (inFr f f' w) u l)) = f'.symm (w (f (fun k => s.iE (u k)))) := by
  funext l
  rw [seamHom_apply]
  rfl

theorem homAtP_iff (Q : HeightOneSpectrum (𝓞 X.E)) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E))
    (w : HomE D.host.E a b) :
    (∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s Q).asIdeal ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))),
        w y ∈ Formalism.HermitianLatticesTheory.localization₂ (seamP s Q).asIdeal ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) ↔
      ∀ u ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal N, seamHom s (inFr f f' w) u ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal N' := by
  have hi : ∀ u : Sp X.E a, f (fun k => s.iE (u k)) ∈
      Formalism.HermitianLatticesTheory.localization₂ (seamP s Q).asIdeal ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ↔
        u ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal N := by
    intro u
    rw [mem_localization_map_iff, f.symm_apply_apply, ← mem_localization_seamLat_iff]
  constructor
  · intro h u hu
    rw [mem_localization_seamLat_iff s Q N', seam_inFr_apply]
    exact (mem_localization_map_iff f' _ _ _).1 (h _ ((hi u).2 hu))
  · intro h y hy
    have hyu : y = f (fun k => s.iE ((fun k => s.iE.symm ((f.symm y) k)) k)) := by
      simp
    rw [hyu] at hy ⊢
    have h1 := (mem_localization_seamLat_iff s Q N' _).1 (h _ ((hi _).1 hy))
    rw [seam_inFr_apply] at h1
    exact (mem_localization_map_iff f' _ _ _).2 h1

theorem mem_homAt_iff (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E))
    (w : HomE D.host.E a b) :
    w ∈ homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)
        ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E))) ↔
      seamHom s (inFr f f' w) ∈ homAt S N N' := by
  constructor
  · intro h Q hQ
    exact (homAtP_iff s Q N N' f f' w).1 (h (seamP s Q) (Finset.mem_map_of_mem _ hQ))
  · intro h P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.1 hP
    exact (homAtP_iff s Q N N' f f' w).2 (h Q hQ)

theorem seamHom_inFr_sub (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E))
    (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (w w' : HomE D.host.E a b) :
    seamHom s (inFr f f' (w - w')) = seamHom s (inFr f f' w) - seamHom s (inFr f f' w') := by
  refine LinearMap.ext fun u => funext fun l => s.iE.injective ?_
  have e1 := congrFun (seam_inFr_apply s f f' (w - w') u) l
  have e2 := congrFun (seam_inFr_apply s f f' w u) l
  have e3 := congrFun (seam_inFr_apply s f f' w' u) l
  rw [e1]
  simp only [LinearMap.sub_apply, map_sub, Pi.sub_apply]
  rw [e2, e3]

theorem seamHom_inFr_natCast_smul (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E))
    (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (c : ℕ) (w : HomE D.host.E a b) :
    seamHom s (inFr f f' ((c : 𝓞 D.host.E) • w)) = (c : 𝓞 X.E) • seamHom s (inFr f f' w) := by
  refine LinearMap.ext fun u => funext fun l => s.iE.injective ?_
  have e1 := congrFun (seam_inFr_apply s f f' ((c : 𝓞 D.host.E) • w) u) l
  have e2 := congrFun (seam_inFr_apply s f f' w u) l
  rw [e1]
  simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul, map_nsmul, Pi.smul_apply]
  rw [e2]

end Hom

end GlobalTheory.DatTransport

namespace GlobalTheory.DatTransport

theorem datLoc_seam_inFr : ∀ {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (S : Finset (HeightOneSpectrum (𝓞 X.E))) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (cA cB : ℕ), 0 < cA → 0 < cB → ∀ (Ξ : HomE X.E a b → X.K), (∀ P ∈ S, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → DatLoc D cc (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (cA * cB) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E))) (fun z => s.σ₀ (Ξ (seamHom s (inFr f f' z)))) ∧ ∀ z, s.σ₀ (Ξ (seamHom s (inFr f f' z))) ≠ 0 → z ∈ divLat (cA * cB) (homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) := by
  intro D X s cc S a b N N' f f' cA cB hA hB Ξ hAA hsupp hinv
  have hH := mem_homAt_iff s S N N' f f'
  constructor
  · intro x x' hx
    have hAA' : ∀ P ∈ S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding,
        Formalism.L2.PairingIndexBounds.F.aaOf D cc ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.1 hP
      exact aaOf_le_locP_seamP s cc Q (hAA Q hQ)
    set d := (((cA * cB : ℕ) : D.host.E))⁻¹ • (x - x') with hd
    have hdH : d ∈ homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)
        ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E))) :=
      fun P hP y hy => perO_apply_mem _ P.asIdeal (hAA' P hP) _ _ d (hx P hP) y hy
    have hne : ((cA * cB : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_ne_zero hA.ne' hB.ne')
    have hxx : x - x' = ((cA * cB : ℕ) : 𝓞 D.host.E) • d := by
      rw [hd, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hne, one_smul]
    have hu : (cA : 𝓞 X.E) • seamHom s (inFr f f' d) ∈ homAt S N N' :=
      Submodule.smul_mem _ _ ((hH d).1 hdH)
    have hm : seamHom s (inFr f f' x) - seamHom s (inFr f f' x') ∈ mulLat cB (homAt S N N') := by
      rw [← seamHom_inFr_sub, hxx, seamHom_inFr_natCast_smul, Nat.cast_mul, mul_comm, mul_smul]
      exact ⟨_, hu, rfl⟩
    show s.σ₀ (Ξ (seamHom s (inFr f f' x))) = s.σ₀ (Ξ (seamHom s (inFr f f' x')))
    rw [← hinv (seamHom s (inFr f f' x')) _ hm, add_sub_cancel]
  · intro z hz
    have h1 : Ξ (seamHom s (inFr f f' z)) ≠ 0 := fun h => hz (by rw [h, map_zero])
    have h2 : (cA : 𝓞 X.E) • seamHom s (inFr f f' z) ∈ homAt S N N' := hsupp _ h1
    have h3 := (hH ((cA : 𝓞 D.host.E) • z)).2 (by rw [seamHom_inFr_natCast_smul]; exact h2)
    rw [Formalism.L2.Col.divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ h3

end GlobalTheory.DatTransport
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_invariance_support_transport_frames : ∀ {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (S : Finset (HeightOneSpectrum (𝓞 X.E))) {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) (cA cB : ℕ), 0 < cA → 0 < cB → ∀ (Ξ : HomE X.E a b → X.K), (∀ P ∈ S, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E)) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → DatLoc D cc (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (cA * cB) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E))) (fun z => s.σ₀ (Ξ (seamHom s (inFr f f' z)))) ∧ ∀ z, s.σ₀ (Ξ (seamHom s (inFr f f' z))) ≠ 0 → z ∈ divLat (cA * cB) (homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) := by
  atlas_forward_decl GlobalTheory.DatTransport.datLoc_seam_inFr
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameCongApprox

variable {E : Type} [Field E] [NumberField E]

theorem intAt_of_val_le {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : P.valuation E a ≤ 1) : IntAt P a := by
  obtain ⟨r, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer a h
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hs⟩

theorem exists_depth (P : HeightOneSpectrum (𝓞 E)) {w : 𝓞 E} (hw : w ≠ 0) :
    ∃ k : ℕ, ∀ z : 𝓞 E, z ∈ P.asIdeal ^ k →
      IntAt P (algebraMap (𝓞 E) E z / algebraMap (𝓞 E) E w) := by
  have h0 : P.intValuation w ≠ 0 := P.intValuation_ne_zero w hw
  refine ⟨(P.intValuation w).log.natAbs, fun z hz => intAt_of_val_le ?_⟩
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    div_le_one₀ (zero_lt_iff.2 h0)]
  refine ((P.intValuation_le_pow_iff_mem z _).2 hz).trans ?_
  conv_rhs => rw [← WithZero.exp_log h0]
  rw [WithZero.exp_le_exp]
  omega

theorem exists_approx (T : Finset (HeightOneSpectrum (𝓞 E))) (t : T → E) (u : T → 𝓞 E) (hu : ∀ P, u P ≠ 0) :
    ∃ y : E, ∀ P : T, IntAt P.1 ((y - t P) / algebraMap (𝓞 E) E (u P)) := by
  have inj := IsFractionRing.injective (𝓞 E) E
  choose a b hb hab using fun P => IsFractionRing.div_surjective (𝓞 E) (t P)
  have hb0 : ∀ P, b P ≠ 0 := fun P => nonZeroDivisors.ne_zero (hb P)
  set D : 𝓞 E := ∏ Q, b Q with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun Q _ => hb0 Q
  have hw : ∀ P, D * u P ≠ 0 := fun P => mul_ne_zero hD0 (hu P)
  choose k hk using fun P : T => exists_depth P.1 (hw P)
  obtain ⟨x, hx⟩ := exists_forall_sub_mem_ideal (s := T) (fun P => P.asIdeal)
    (fun P => if h : P ∈ T then k ⟨P, h⟩ else 0) (fun P _ => P.prime)
    (fun P _ Q _ h h' => h (HeightOneSpectrum.ext h')) (fun P => a P * ∏ Q ∈ Finset.univ.erase P, b Q)
  refine ⟨algebraMap (𝓞 E) E x / algebraMap (𝓞 E) E D, fun P => ?_⟩
  have hxP := hx P.1 P.2
  simp only [dif_pos P.2] at hxP
  have h1 := hk P _ hxP
  convert h1 using 1
  have hsplit : D = b P * ∏ Q ∈ Finset.univ.erase P, b Q := (Finset.mul_prod_erase _ _ (Finset.mem_univ P)).symm
  have hbE : algebraMap (𝓞 E) E (b P) ≠ 0 := (map_ne_zero_iff _ inj).2 (hb0 P)
  have hBE : algebraMap (𝓞 E) E (∏ Q ∈ Finset.univ.erase P, b Q) ≠ 0 :=
    (map_ne_zero_iff _ inj).2 (Finset.prod_ne_zero_iff.2 fun Q _ => hb0 Q)
  have huE : algebraMap (𝓞 E) E (u P) ≠ 0 := (map_ne_zero_iff _ inj).2 (hu P)
  rw [← hab P, map_mul, map_sub, map_mul, hsplit, map_mul]
  field_simp

theorem exists_den {n : ℕ} (g : (Fin n → E) →ₗ[E] (Fin n → E)) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ (P : HeightOneSpectrum (𝓞 E)) (z : Fin n → E), (∀ l, IntAt P (z l)) →
      ∀ l, IntAt P (algebraMap (𝓞 E) E d * g z l) := by
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E))
    (Finset.univ : Finset (Fin n × Fin n)) (fun p => g (fun k => if p.1 = k then 1 else 0) p.2)
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun P z hz l => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ g z, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ => IntAt.add) (by simpa using IntAt.coe P 0) fun j _ => ?_
  obtain ⟨r, hr⟩ := hdi (j, l) (Finset.mem_univ _)
  rw [Algebra.smul_def] at hr
  rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  exact (hz j).mul (by rw [← hr]; exact IntAt.coe P r)

end GlobalTheory.FrameCongApprox

namespace GlobalTheory.FrameCongApprox

theorem exists_sameCoset {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ}
    (fr : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n)) (y0 : rowSG Pr sel mu → Sp X.E n) :
    ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((fr P).symm y) (y0 P) := by
  have inj := IsFractionRing.injective (𝓞 X.E) X.E
  choose d hd0 hd using fun P : rowSG Pr sel mu => exists_den (fr P).symm.toLinearMap
  let e : rowSG Pr sel mu → ℕ := fun P => if P.1 ∈ Pr.vGs then 0 else cst.M
  let m : rowSG Pr sel mu → 𝓞 X.E := fun P => d P * ((qOf P.1 : ℕ) : 𝓞 X.E) ^ e P
  have hq : ∀ P : rowSG Pr sel mu, ((qOf P.1 : ℕ) : X.E) ≠ 0 := fun P => by
    rw [Nat.cast_ne_zero]
    unfold qOf
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  have hmE : ∀ P, algebraMap (𝓞 X.E) X.E (m P) = algebraMap (𝓞 X.E) X.E (d P) * ((qOf P.1 : ℕ) : X.E) ^ e P := fun P => by
    simp [m, map_mul, map_pow, map_natCast]
  have hm : ∀ P, m P ≠ 0 := fun P h => by
    have h2 := hmE P
    rw [h, map_zero] at h2
    exact mul_ne_zero ((map_ne_zero_iff _ inj).2 (hd0 P)) (pow_ne_zero _ (hq P)) h2.symm
  choose yl hyl using fun l : Fin n => exists_approx (rowSG Pr sel mu) (fun P => fr P (y0 P) l) m hm
  refine ⟨yl, fun P l => ?_⟩
  have hmP : algebraMap (𝓞 X.E) X.E (m P) ≠ 0 := (map_ne_zero_iff _ inj).2 (hm P)
  set z : Sp X.E n := fun l => (yl l - fr P (y0 P) l) / algebraMap (𝓞 X.E) X.E (m P) with hz
  have hy : yl = fr P (y0 P) + algebraMap (𝓞 X.E) X.E (m P) • z := by
    funext l
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hdiff : (fr P).symm yl - y0 P = algebraMap (𝓞 X.E) X.E (m P) • (fr P).symm z := by
    rw [hy, map_add, map_smul, LinearEquiv.symm_apply_apply, add_sub_cancel_left]
  have key := hd P P.1 z (fun l => hyl l P) l
  show IntAt P.1 (((qOf P.1 : X.E) ^ e P)⁻¹ * ((fr P).symm yl - y0 P) l)
  rw [hdiff, Pi.smul_apply, smul_eq_mul, hmE]
  have : (((qOf P.1 : ℕ) : X.E) ^ e P)⁻¹ * (algebraMap (𝓞 X.E) X.E (d P) * ((qOf P.1 : ℕ) : X.E) ^ e P * (fr P).symm z l) =
      algebraMap (𝓞 X.E) X.E (d P) * (fr P).symm.toLinearMap z l := by
    have hqe := pow_ne_zero (e P) (hq P)
    simp only [LinearEquiv.coe_coe]
    field_simp
  rw [this]
  exact key

end GlobalTheory.FrameCongApprox
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_sameCouplingCoset_all_bad_primes : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (fr : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n)) (y0 : rowSG Pr sel mu → Sp X.E n), ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((fr P).symm y) (y0 P) := by
  atlas_forward_decl GlobalTheory.FrameCongApprox.exists_sameCoset
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU

theorem repY_yb_coset_bdd {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E} (H : AdTie A dtU a)
    (c : (D.chTw u μ).cls (t.m2 + 1)) (P : SB t μ) :
    SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)))
        (A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) P) ∧
      ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M)) *
        (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) P).symm (repY (A.yb c)) l) := by
  obtain ⟨w, hw1, hw⟩ := H.chain.2.1 c
  have hwm : w ∈ A.yb c := by
    rw [hw, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  have hmem : repY (A.yb c) ∈ A.yb c := Classical.epsilon_spec (p := fun y => y ∈ A.yb c) ⟨w, hwm⟩
  refine ⟨H.coset c _ hmem P, ?_⟩
  have hd := (Set.ext_iff.1 hw (repY (A.yb c))).1 hmem
  rw [Set.mem_setOf_eq] at hd
  have h0 := (Submodule.mem_iInf _).1 hd P
  have h1 := (Submodule.mem_iInf _).1 hw1 P
  rw [Submodule.mem_comap] at h0 h1
  have hf := GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)
  set fr := frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) with hfr
  have toStd : ∀ v, v ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (A.pt (t.m2 + 1) (cpl_lt t μ).le c).deco.1.N → ∀ l, IntAt P.1 ((fr P).symm v l) := by
    intro v hv
    refine GlobalTheory.TopStep.mem_stdAt.1 ((hf P _).1 ?_)
    rwa [LinearEquiv.apply_symm_apply]
  have k0 := toStd _ h0
  have k1 := toStd _ h1
  simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at k0 k1
  intro l
  have hq : (qOf P.1 : t.X.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ipow : ∀ n : ℕ, IntAt P.1 ((qOf P.1 : t.X.E) ^ n) := fun n => by
    simpa using IntAt.coe P.1 ((qOf P.1 : 𝓞 t.X.E) ^ n)
  have a0 := k0 l
  have a1 := k1 l
  by_cases hP : P.1 ∈ t.Pr.vGs
  · simp only [hP, if_true] at a0 a1 ⊢
    have e : (qOf P.1 : t.X.E) ^ 1 * (fr P).symm (repY (A.yb c)) l =
        (qOf P.1 : t.X.E) ^ 1 * (((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l - ((qOf P.1 : t.X.E) ^ (0 : ℤ))⁻¹ * (fr P).symm w l) +
          ((qOf P.1 : t.X.E) ^ (-1 : ℤ))⁻¹ * (fr P).symm w l := by
      simp only [zpow_zero, inv_one, one_mul, _root_.zpow_neg, zpow_one, inv_inv, pow_one]
      ring
    rw [e]
    exact IntAt.add (IntAt.mul (ipow 1) a0) a1
  · simp only [hP, if_false] at a0 a1 ⊢
    have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * (fr P).symm (repY (A.yb c)) l =
        (qOf P.1 : t.X.E) ^ (2 * (t.cst μ).M) * (((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm (repY (A.yb c)) l -
          ((qOf P.1 : t.X.E) ^ ((t.cst μ).M : ℤ))⁻¹ * (fr P).symm w l) +
          ((qOf P.1 : t.X.E) ^ (-((t.cst μ).M : ℤ)))⁻¹ * (fr P).symm w l := by
      simp only [_root_.zpow_neg, inv_inv, zpow_natCast]
      field_simp
      ring
    rw [e]
    exact IntAt.add (IntAt.mul (ipow _) a0) a1

theorem baseCosetRepresentative_bounded_at_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ} (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (x : UA D (t.m2 + 1) (cpl_lt t μ).le) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))), IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β Q l) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H β x Q l
  obtain ⟨⟨c, hc⟩, -⟩ := ((St _ (cpl_lt t μ).le).K β).y_bij.2 (Quotient.mk'' x)
  subst hc
  obtain ⟨hs, hb⟩ := repY_yb_coset_bdd H c Q
  set w := (frsF t.sel (t.tup μ) (A.pt (t.m2 + 1) (cpl_lt t μ).le c) Q).symm (repY (A.yb c)) with hw
  have hsl := hs l
  have hbl := hb l
  simp only [Pi.sub_apply] at hsl
  have hq : (qOf Q.1 : t.X.E) ≠ 0 := Nat.cast_ne_zero.2 fun h => Q.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ineg : ∀ n : ℕ, IntAt Q.1 (-((qOf Q.1 : t.X.E) ^ n)) := fun n => by
    simpa using IntAt.coe Q.1 (-((qOf Q.1 : 𝓞 t.X.E) ^ n))
  by_cases hP : Q.1 ∈ t.Pr.vGs
  · simp only [hP, if_true] at hsl hbl ⊢
    have e : (qOf Q.1 : t.X.E) ^ 1 * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l =
        (qOf Q.1 : t.X.E) ^ 1 * w l + (-((qOf Q.1 : t.X.E) ^ 1)) *
          (((qOf Q.1 : t.X.E) ^ 0)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l)) := by
      simp only [pow_zero, inv_one, one_mul]
      ring
    rw [e]
    exact IntAt.add hbl (IntAt.mul (ineg 1) hsl)
  · simp only [hP, if_false] at hsl hbl ⊢
    have e : (qOf Q.1 : t.X.E) ^ (t.cst μ).M * A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l =
        (qOf Q.1 : t.X.E) ^ (t.cst μ).M * w l + (-((qOf Q.1 : t.X.E) ^ (2 * (t.cst μ).M))) *
          (((qOf Q.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (w l - A.y0 ((St (t.m2 + 1) (cpl_lt t μ).le).chOf c) Q l)) := by
      field_simp
      ring
    rw [e]
    exact IntAt.add hbl (IntAt.mul (ineg _) hsl)

end GlobalTheory.TwU
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intAt_qOf_pow_mul_y0_of_adTie : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ} (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (x : UA D (t.m2 + 1) (cpl_lt t μ).le) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))), IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β Q l) := by
  atlas_forward_decl GlobalTheory.TwU.baseCosetRepresentative_bounded_at_bad_primes
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwV.EntrySupportBounds

open GlobalTheory.Mem.Col2 GlobalTheory.TopStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem top_supp (hL : L.Ok Ch sel mu cst G m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (x : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)))
    (hx : XiTop Ch sel mu cst (m2 + 1) p Y p' x ≠ 0) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) := by
  have hm : m2 + 1 + 1 = R.m := hL.hm.symm
  rw [← xiOver_eq_XiTop _ _ _ _ _ _ _ _ _ _ hm] at hx
  unfold xiOver at hx
  refine GlobalTheory.GO.mem_divLat_of_loc _ _ (left_ne_zero_of_mul hx) fun Q s l => ?_
  have h := GlobalTheory.GO.locTop_den hL.hm hL.cst_ok (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) Q (Finset.mem_univ _)) s
    (Fin.cast (congrArg R.N hm) l)
  simpa [castSp, LinearMap.funLeft_apply] using h

open Classical in
theorem top_add (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (p' : ChPt (R := R) sel mu u (m2 + 1 + 1))
    (hY : ∀ (Q : rowSG Pr sel mu) l, IntAt Q.1 ((qOf Q.1 : X.E) ^ (if Q.1 ∈ Pr.vGs then 1 else cst.M) * (frsF sel mu p Q).symm (repY Y) l))
    (x y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiTop Ch sel mu cst (m2 + 1) p Y p' (x + y) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  have hm : m2 + 1 + 1 = R.m := hL.hm.symm
  obtain ⟨h1, h2⟩ := GlobalTheory.GO.loc_of_mem_mulLat hPr _ _ x hy
  rw [← xiOver_eq_XiTop _ _ _ _ _ _ _ _ _ _ hm]
  unfold xiOver
  refine congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun Q _ => ?_)
  rw [GlobalTheory.inFr_add, LinearMap.comp_add]
  refine GlobalTheory.GO.locTop_add hL.hm hL.cst_ok (hL.depthQ Q) _ (fun s l => ?_) (hY Q)
  simpa [castSp, LinearMap.funLeft_apply] using h2 Q s (Fin.cast (congrArg R.N hm).symm l)

theorem entry_supp (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1)))
    (hx : XiEntry Ch sel mu cst L i al be p p' x ≠ 0) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) :=
  GlobalTheory.GO.mem_divLat_of_loc _ _ (left_ne_zero_of_mul hx) fun Q =>
    hL.xiSupp i hi al be Q _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) Q (Finset.mem_univ _))

theorem entry_add (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (x y : HomE X.E (R.N i) (R.N (i + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiEntry Ch sel mu cst L i al be p p' (x + y) = XiEntry Ch sel mu cst L i al be p p' x := by
  obtain ⟨h1, h2⟩ := GlobalTheory.GO.loc_of_mem_mulLat hPr _ _ x hy
  exact congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun Q _ =>
    (congrArg _ (GlobalTheory.inFr_add _ _ x y)).trans (hL.xiInv i hi al be Q _ _ (h2 Q)))

theorem cpl_supp (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (x : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hx : XiCpl1 Ch sel mu cst L m2 al p₀ p Y x ≠ 0) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p₀.deco.1.N p.deco.1.N) :=
  GlobalTheory.GO.mem_divLat_of_loc _ _ (left_ne_zero_of_mul hx) fun Q =>
    hL.psiSuppX al Q _ _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) Q (Finset.mem_univ _))

theorem cpl_add (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (x y : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p₀.deco.1.N p.deco.1.N)) :
    XiCpl1 Ch sel mu cst L m2 al p₀ p Y (x + y) = XiCpl1 Ch sel mu cst L m2 al p₀ p Y x := by
  obtain ⟨h1, h2⟩ := GlobalTheory.GO.loc_of_mem_mulLat hPr _ _ x hy
  exact congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun Q _ =>
    (congrArg (fun t => PsiAt Ch sel mu cst m2 Q _ t _) (GlobalTheory.inFr_add _ _ x y)).trans (hL.psiInvX al Q _ _ _ (h2 Q)))

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem transport {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E))
    (cA cB : ℕ) (hA : 0 < cA) (hB : 0 < cB) (Ξ : HomE X.E a b → X.K)
    (hAA : ∀ P ∈ S, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0,
      r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E))
    (h1 : ∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) (h2 : ∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) :
    DatLoc D cc (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (cA * cB)
        ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))
        (fun z => s.σ₀ (Ξ (seamHom s (inFr f f' z)))) ∧
      ∀ z, s.σ₀ (Ξ (seamHom s (inFr f f' z))) ≠ 0 → z ∈ divLat (cA * cB)
        (homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)
          ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) :=
  GlobalTheory.T.finiteDatum_invariance_support_transport_frames s cc S N N' f f' cA cB hA hB Ξ hAA h1 h2

theorem cosetNonempty {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (fr : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (y0 : rowSG Pr sel mu → Sp X.E n) : ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((fr P).symm y) (y0 P) :=
  GlobalTheory.T.exists_vector_sameCouplingCoset_all_bad_primes sel mu cst fr y0

open Classical in
theorem couplingBaseVector_bound_kernelChain {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E) (H : AdTie A dtU a)
    (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (x : UA D (t.m2 + 1) (cpl_lt t μ).le) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))) :
    IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β Q l) :=
  GlobalTheory.T.intAt_qOf_pow_mul_y0_of_adTie A dtU a H β x Q l

open Classical in
theorem cosetBound {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E) (H : AdTie A dtU a)
    (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (x : UA D (t.m2 + 1) hi)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))) :
    IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) *
      (frsF t.sel (t.tup μ) p Q).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l) := by
  have hy0 : ∀ P, y0At A (t.m2 + 1) hi β P = A.y0 β P := fun P => by simp [y0At]
  obtain ⟨y, hy⟩ := cosetNonempty t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) p P) (fun P => A.y0 β P)
  have hne : repY (cosetOf A (t.m2 + 1) hi β p) ∈ cosetOf A (t.m2 + 1) hi β p := by
    unfold repY
    exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β p) ⟨y, fun P => by rw [hy0]; exact hy P⟩
  have h1 := hne Q l
  rw [hy0] at h1
  have h2 := couplingBaseVector_bound_kernelChain A dtU a H β x Q l
  generalize (frsF t.sel (t.tup μ) p Q).symm (repY (cosetOf A (t.m2 + 1) hi β p)) = v at h1 ⊢
  rw [Pi.sub_apply] at h1
  have hq := GlobalTheory.TopInv.qOf_ne (E := t.X.E) Q.1
  split_ifs at h1 h2 ⊢ with hQ
  · have e : (qOf Q.1 : t.X.E) ^ 1 * v l = (qOf Q.1 : t.X.E) * (((qOf Q.1 : t.X.E) ^ 0)⁻¹ * (v l - A.y0 β Q l)) +
        (qOf Q.1 : t.X.E) ^ 1 * A.y0 β Q l := by ring
    rw [e]
    exact ((GlobalTheory.TopStep.intAt_nat _).mul h1).add h2
  · have e : (qOf Q.1 : t.X.E) ^ (t.cst μ).M * v l = (qOf Q.1 : t.X.E) ^ (t.cst μ).M * (qOf Q.1 : t.X.E) ^ (t.cst μ).M *
        (((qOf Q.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v l - A.y0 β Q l)) + (qOf Q.1 : t.X.E) ^ (t.cst μ).M * A.y0 β Q l := by
      field_simp
      ring
    rw [e]
    exact (((GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _)).mul h1).add h2

set_option maxHeartbeats 800000 in
theorem sizeLaw_of_tie' : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → SizeLaw A a) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT hPt i hi β β' x x'
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  have hL := t.idx_ok μ
  have hPr := t.pr_ok
  have hp := (hPt i (Nat.le_of_succ_le hi) β x).choose_spec
  have hp' := (hPt (i + 1) hi β' x').choose_spec
  have hxi : xiAd A a i hi β β' x x' = fun z => t.seam.σ₀ (xiPt A i hi β β' (hPt i (Nat.le_of_succ_le hi) β x).choose
      (hPt (i + 1) hi β' x').choose (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) :=
    funext fun z => dif_pos ⟨⟨_, hp⟩, ⟨_, hp'⟩⟩
  generalize (hPt i (Nat.le_of_succ_le hi) β x).choose = p at hp hxi
  generalize (hPt (i + 1) hi β' x').choose = p' at hp' hxi
  have hS : ssRec t u μ = (Sall t.sel (t.tup μ) (t.word u)).map
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv t.seam.iE)).toEmbedding := by
    unfold ssRec
    rw [hSS]
  rw [hxi, hS, hlev, latK_eq_map _ (A.crd i (Nat.le_of_succ_le hi)), latK_eq_map _ (A.crd (i + 1) hi), ← hp.lat, ← hp'.lat]
  unfold levC
  refine transport t.seam t.cc _ _ _ _ _ _ _ GlobalTheory.GO.twDen_pos (GlobalTheory.GO.twMod_pos (hPr.T_prime _).pos) _
    (fun P hP => hT.aa P hP) ?_ ?_
  · intro z hz
    unfold xiPt at hz
    split_ifs at hz with h1 h2
    · exact entry_supp hL h1 _ _ _ _ z hz
    · subst h2
      exact cpl_supp hL _ _ _ _ z hz
    · obtain rfl : i = t.m2 + 1 := by have := m_eq t μ; omega
      exact top_supp hL _ _ _ z hz
  · intro z y hy
    unfold xiPt
    split_ifs with h1 h2
    · exact entry_add hPr hL h1 _ _ _ _ z y hy
    · subst h2
      exact cpl_add hPr hL _ _ _ _ z y hy
    · obtain rfl : i = t.m2 + 1 := by have := m_eq t μ; omega
      exact top_add hPr hL _ _ _ (fun Q l => cosetBound A dtU a hT _ β x _ Q l) z y hy

end GlobalTheory.TwV.EntrySupportBounds

theorem GlobalTheory.TwV.sizeLaw_of_tie : GlobalTheory.TwV.UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => GlobalTheory.TwV.PtEx A a → GlobalTheory.TwV.SizeLaw A a) :=
  GlobalTheory.TwV.EntrySupportBounds.sizeLaw_of_tie'
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDatum_invariance_support_kernelChain : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → SizeLaw A a) := by
  atlas_forward_decl GlobalTheory.TwV.sizeLaw_of_tie
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV.AdInt

theorem norm_le_one_of_isIntegral' {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem intOff_of_isIntegral {K : Type} [Field K] (σ : K →+* ℂ) (S : Finset ℕ) {x : K} (hx : IsIntegral ℤ x) :
    IntOff S (σ x) := by
  have hx' : IsIntegral ℤ (σ x) := map_isIntegral_int σ hx
  have h : σ x ∈ TaylorLogMetric.Qbar := mem_algebraicClosure_iff'.2 hx'.tower_top
  refine ⟨h, fun p _ lam _ => ?_⟩
  rw [lamC_of_mem lam h]
  have h1 : IsIntegral ℤ (⟨σ x, h⟩ : TaylorLogMetric.Qbar) :=
    (isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx'
  exact norm_le_one_of_isIntegral' (map_isIntegral_int lam h1)

end GlobalTheory.TwV.AdInt

namespace GlobalTheory.TwV.AdInt

section Ft

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ftY_intOff_of_psi (P : rowSG Pr sel mu) (hpsi : ∀ a, IsIntegral ℤ (cst.psi P a)) (σ : X.K →+* ℂ) {B : Finset ℕ}
    (hB : SNum B (qOf P.1)) {n : ℕ} (η : Sp X.E n →ₗ[X.E] X.E) (y : Sp X.E n) :
    IntOff B (σ (ftY sel mu cst P η y)) := by
  unfold ftY
  split_ifs
  · exact intOff_of_isIntegral σ B (hpsi _)
  · simpa using (IntOff.zero : IntOff B 0)
  · rw [map_mul, map_inv₀, map_pow, map_natCast]
    refine IntOff.mul ?_ (intOff_of_isIntegral σ B (hpsi _))
    have hB' : SNum B (qOf P.1 ^ (cst.M * n)) :=
      ⟨pow_pos hB.1 _, fun q hq hd => hB.2 q hq (hq.dvd_of_dvd_pow hd)⟩
    simpa [Nat.cast_pow] using IntOff.inv_nat hB'
  · simpa using (IntOff.zero : IntOff B 0)

end Ft

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX}

theorem xiTop_intOff_of_psi (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (hpsi : ∀ P x, IsIntegral ℤ ((t.cst μ).psi P x)) (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i)
    (Yb : Set (Sp t.X.E (D.R.N i))) (p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1))
    (x : HomE t.X.E (D.R.N i) (D.R.N (i + 1))) :
    IntOff (t.O u μ).S (t.seam.σ₀ (XiTop t.Ch t.sel (t.tup μ) (t.cst μ) i p Yb p' x)) := by
  unfold XiTop XiTopG
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (GlobalTheory.intOff_finset_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul ((GlobalTheory.TopInt.phiTopG_root _ _ _ _ _ _ _ _).intOff _ _) ?_
    exact ftY_intOff_of_psi t.sel (t.tup μ) (t.cst μ) P (hpsi P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl Kc Y cX ex t u μ P) _ _

theorem plc_dvd_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

theorem g_not_mem_Qp (t : KerEntTied ex) (hsel : IsSel t.X t.sel) (hg : ∀ k, t.Pr.g k ∈ t.S) (μ : D.what₂.Tup) (k : Fin 2) :
    D.host.g k ∉ Y.Qp μ := by
  classical
  intro hk
  obtain ⟨hp, P, hPQ, hgP⟩ := (t.Q_rec μ (D.host.g k)).1 hk
  unfold QE at hPQ
  split_ifs at hPQ with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPQ
    rw [Set.Finite.mem_toFinset] at hv
    have hgood : GoodPl t.X.E t.S v := by
      by_contra hg'
      apply hv
      have h2 := (Subgroup.mem_inf.1 (t.tup μ).2).2
      exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg'
    have hvF : ((D.host.g k : ℕ) : 𝓞 t.X.F) ∈ v.asIdeal := by
      rw [← hsel v]
      change algebraMap (𝓞 t.X.F) (𝓞 t.X.E) _ ∈ (t.sel v).asIdeal
      rw [map_natCast]
      exact hgP
    have hd := (plc_dvd_iff v _).2 hvF
    have hpl : Formalism.EigenvalueLevelCeiling.plc v = D.host.g k :=
      ((Nat.dvd_prime hp).1 hd).resolve_left fun e => by
        have h1 := (plc_dvd_iff v 1).1 (by rw [e])
        rw [Nat.cast_one] at h1
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    apply hgood.2.2
    rw [hpl, ← t.g_rec k]
    exact hg k
  · simp at hPQ

end GlobalTheory.TwV.AdInt

namespace GlobalTheory.TwV

theorem xiAd_intOff : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → ∀ i hi β β' x x' z,
    IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ _ i hi β β' x x' z
  have hmu : ∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j) := fun j => ⟨_, hP.mu0 j⟩
  have hval : ∀ (j : Fin D.R.m) (v : HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) →
      t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ) := fun j v hv => by
    have h := hP.ch.muVal j v hv
    rwa [t.glob_σ] at h
  have hg : ∀ k, D.host.g k ∉ Y.Qp μ := AdInt.g_not_mem_Qp t hP.sel hP.avoid.1 μ
  unfold xiAd
  split_ifs with h
  · unfold xiPt
    split_ifs with h1 h2
    · exact GlobalTheory.KerTie.intOff_xiEntry D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg i h1 _ _ _ _ _
    · subst h2
      exact GlobalTheory.xiCpl1_intOff D L hT Gi Gl Kc Y cX ex t hmu hval u μ hg _ _ _ _ _
    · exact AdInt.xiTop_intOff_of_psi t u μ hP.psi _ _ _ _ _
  · exact IntOff.zero

end GlobalTheory.TwV
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFiniteDatum_integralOffBadPrimes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → ∀ i hi β β' x x' z, IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z)) := by
  atlas_forward_decl GlobalTheory.TwV.xiAd_intOff
end

section
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {a : 𝓞 D.host.E}

theorem xiAd_eq_of_isPtAd (hW : ∀ i hi, PtAway A a i hi) {i : ℕ} {hi : i + 1 ≤ D.R.m}
    {β : (St i (Nat.le_of_succ_le hi)).Ch} {β' : (St (i + 1) hi).Ch} {x : UA D i (Nat.le_of_succ_le hi)} {x' : UA D (i + 1) hi}
    {p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i} {p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1)}
    (hp : IsPtAd A a i (Nat.le_of_succ_le hi) β x p) (hp' : IsPtAd A a (i + 1) hi β' x' p') (z : HomE D.host.E (D.R.N i) (D.R.N (i + 1))) :
    xiAd A a i hi β β' x x' z = t.seam.σ₀ (xiPt A i hi β β' p p' (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) := by
  have h : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩
  dsimp only [xiAd]
  rw [dif_pos h, hW i hi β β' x x' x x' p p' _ _ hp hp' h.1.choose_spec h.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)]

theorem exists_u1Af_det (k : ℕ) (hk : k ≤ D.R.m) {g : GL (Fin (D.R.N k)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (hg : g ∈ UPts (sigD D) (gramN D k hk) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det g := by
  have hU := det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D k hk) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D k hk) g hg
  set x := Matrix.GeneralLinearGroup.det g with hx
  have hx1 : x * conjId (sigD D) x = 1 := hU
  have h2 : (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) * sigR (sigD D) _ (x : _) = 1 := congrArg Units.val hx1
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1) : _ →+* Matrix (Fin 1) (Fin 1) _).toMonoidHom x, ?_⟩, ?_⟩
  · change cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Matrix.scalar (Fin 1) (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (1 : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * Matrix.scalar (Fin 1) (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) = (1 : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    simp only [cT, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1; funext _; rw [mul_comm]; exact h2
  · apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

end Pt

theorem adLawAt_xiAd : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie
  have hPt : PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) := GlobalTheory.T.chartPoints_exist_and_classPoints_representatives A dtU a hPin hTie
  have hE := hPt.1
  have hCo : ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c :=
    GlobalTheory.T.couplingCoset_eq_chartPointCoset A dtU a hPin hTie
  have hMu : MuLaw t u μ dtU := GlobalTheory.T.stepCharacterLaws_normOneIdeles_of_kernelChain A dtU a hPin hTie
  have hm := m_eq t μ
  have hW : ∀ i hi, PtAway A a i hi := by
    intro i hi
    rcases lt_trichotomy i t.m2 with h | h | h
    · exact GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_matrixStep A dtU a hPin hTie i hi h
    · exact GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_firstCoupledStep A dtU a hPin hTie i hi h
    · exact GlobalTheory.TwV.AwayTop.ptAway_top A dtU a hPin hTie i hi (by omega)
  have hLev : ∀ i hi, LevAt A dtU a i hi := by
    intro i hi
    rcases lt_trichotomy i t.m2 with h | h | h
    · exact GlobalTheory.T.finiteDatum_levelEquivariance_at_matrixSteps A dtU a hPin hTie hE hMu i hi h (hW i hi)
    · exact GlobalTheory.T.adelicDatum_level_equivariance_first_coupled_step A dtU a hPin hTie hE hMu i hi h (hW i hi)
    · exact GlobalTheory.T.lastStep_adelicDatum_level_equivariance A dtU a hPin hTie hE hMu i hi (by omega) (hW i hi)
  have hRat : RatLaw A a := GlobalTheory.T.finiteAdelicDatum_rationalInvariance_of_kernelChain A dtU a hPin hTie hE hW
  have hSize : SizeLaw A a := GlobalTheory.T.adelicDatum_invariance_support_kernelChain A dtU a hPin hTie hE
  have hInt : ∀ i hi β β' x x' z, IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z) := GlobalTheory.T.adelicFiniteDatum_integralOffBadPrimes A dtU a hPin hTie hE
  refine
    { read := ?_
      rat := hRat
      lev := fun i hi => hLev i hi
      away := ?_
      loc := fun i hi β β' x x' => (hSize i hi β β' x x').1
      supp := fun i hi β β' x x' => (hSize i hi β β' x x').2
      int := hInt
      mu_read := fun i hi => (hMu i hi).1
      mu_cls := ?_
      mu_mul := fun i hi => (hMu i hi).2.1
      mu_alg := fun i hi => (hMu i hi).2.2.1
      mu_unr := fun i hi => (hMu i hi).2.2.2.1
      mu_rat := fun i hi => (hMu i hi).2.2.2.2 }
  · intro i hi c c' z
    rw [xiAd_eq_of_isPtAd hW (hPt.2 i _ c) (hPt.2 (i + 1) hi c')]
    rcases lt_trichotomy i t.m2 with h | h | h
    · rw [hTie.chain.2.2.1 i h c c', xiPt, dif_pos h]
    · subst h
      rw [hTie.chain.2.2.2.1 c c', xiPt, dif_neg (lt_irrefl _), if_pos rfl, hCo c']
    · obtain rfl : i = t.m2 + 1 := by omega
      rw [hTie.chain.2.2.2.2.1.2 c c', xiPt, dif_neg (by omega), if_neg (by omega), hCo c]
  · intro i hi β β' x x' x₁ x₁' hx
    funext z
    obtain ⟨p, hp⟩ := hE i _ β x
    obtain ⟨p', hp'⟩ := hE (i + 1) hi β' x'
    obtain ⟨p₁, hp₁⟩ := hE i _ β x₁
    obtain ⟨p₁', hp₁'⟩ := hE (i + 1) hi β' x₁'
    rw [xiAd_eq_of_isPtAd hW hp₁ hp₁', xiAd_eq_of_isPtAd hW hp hp', hW i hi β β' x x' x₁ x₁' p p' p₁ p₁' hp hp' hp₁ hp₁' hx]
  · intro i hi k hk c
    obtain ⟨y, hy⟩ := exists_u1Af_det k hk ((St k hk).y c).2
    rw [← hy, (hMu i hi).1 y, hTie.dt k hk c y hy]

end GlobalTheory.TwV
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicChainDatum_characterLaws_jointKernel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU)) := by
  atlas_forward_decl GlobalTheory.TwV.adLawAt_xiAd
end

section
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.exists_adLawAt_joint : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ Xi muT, AdLawAt J.A J.dtU J.a Xi muT :=
  by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ J
  exact ⟨_, _, GlobalTheory.T.adelicChainDatum_characterLaws_jointKernel J.A J.dtU J.a J.pins J.tie⟩
end

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicDatum_with_laws_at_joint : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ Xi muT, AdLawAt J.A J.dtU J.a Xi muT := by
  atlas_forward_decl GlobalTheory.TwV.exists_adLawAt_joint
end
