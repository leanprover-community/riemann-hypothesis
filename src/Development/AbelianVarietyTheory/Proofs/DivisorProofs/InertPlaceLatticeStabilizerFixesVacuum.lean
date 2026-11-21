import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerPreservesVacuumConditionAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledFirstFactorMemSiegelClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSiegelParabolicDiagonalActionIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonCharacterDetEqOneInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaIntegralAtInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryStabilizer_preserves_vacuumCondition_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, k)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ₁)) := by
  first | exact @GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | exact GlobalTheory.InertSph.acts_vacCond_of_mem_KAt | (intros; apply GlobalTheory.InertSph.acts_vacCond_of_mem_KAt <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.WeilLocalityDbl

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a')
    (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
    (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ))
    (hW : IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd)
    (v : Pl F) (g : UG (cA σ) (dbl (incM F G.W.J))) (hg : At (evFin F v) (GlobalTheory.InertDbl.matD g - 1))
    (u : AF F) (hu : evFin F v u = 0) (p q : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F)
    (Φ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) :
      omd g (GlobalTheory.WeilM.schr B.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr B.ψ (u • p, u • q) (omd g Φ) := by

  have hw0 : dd.e.symm (u • p, u • q) = u • dd.e.symm (p, q) := by
    rw [← Prod.smul_mk, LinearEquiv.map_smul]
  have hM : u • GlobalTheory.InertDbl.matD g = u • (1 : Matrix _ _ (AE F E)) := by
    rw [← sub_eq_zero, ← smul_sub]
    exact hg u hu
  have hact : actB (cA σ) g (dd.e.symm (u • p, u • q)) = dd.e.symm (u • p, u • q) := by
    rw [hw0]
    show (u • dd.e.symm (p, q)) * (GlobalTheory.InertDbl.matD g)ᵀ = u • dd.e.symm (p, q)
    rw [Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, hM, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one]
  have h := hW.impl g (dd.e.symm (u • p, u • q)) Φ hΦ
  rw [hact] at h
  simpa only [Darboux.rho, LinearEquiv.apply_symm_apply] using h

private lemma at_add_divisor {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) {z z' : κ → AF F}
    (hz : At (evFin F v) z) (hz' : At (evFin F v) z') : At (evFin F v) (z + z') := by
  intro u hu
  rw [smul_add, hz u hu, hz' u hu, add_zero]

private lemma at_liftV' {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) (t : κ → Fv F v) :
    At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
  intro u hu
  funext i
  show u • GlobalTheory.LatVac.liftV v (t i) = 0
  exact GlobalTheory.LatVac.at_liftV v (t i) u hu

theorem locality : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ g : UG (cA σ) (dbl (incM F G.W.J)), At (evFin F v) (GlobalTheory.InertDbl.matD g - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), Acts (evFin F v) (omd g) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v dd omd hWS g hg φ hφ
  have hW := hWS.2.1

  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) v
  have hRφ := hR φ hφ

  have htr : ∀ c : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F, (∀ i, evFin F v (c i) = 0) →
      ∀ Φ ∈ schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')),
        omd g (fun x => Φ (x + c)) = fun x => omd g Φ (x + c) := by
    intro c hc Φ hΦ
    have hu : evFin F v (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) = 0 := by
      rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]
    have huc : (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • c = c := by
      funext i
      show (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • c i = c i
      rw [smul_eq_mul, sub_mul, one_mul, GlobalTheory.WeilLocalityW.liftV_one_mul, hc i, map_zero, sub_zero]
    have h := comm_off B G dd omd hW v g hg _ hu c 0 Φ hΦ
    rw [huc, smul_zero] at h
    have hs : ∀ Ψ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ,
        GlobalTheory.WeilM.schr B.ψ (c, 0) Ψ = fun x => Ψ (x + c) := by
      intro Ψ
      funext x
      simp [GlobalTheory.WeilM.schr]
    rw [hs, hs] at h
    exact h

  refine ⟨fun t => (R 0)⁻¹ * omd g (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h1 : omd g (tens (evFin F v) φ R) ∈ schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) :=
      hW.pres g _ hRφ.2
    exact (SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ h1)
  · intro r hr
    funext y

    obtain ⟨yv, hyv⟩ : ∃ yv : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F,
        yv = fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) := ⟨_, rfl⟩
    obtain ⟨y', hy'⟩ : ∃ y' : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F, y' = y - yv := ⟨_, rfl⟩
    have hatv : At (evFin F v) yv := by rw [hyv]; exact at_liftV' v _
    have hev : ∀ i, evFin F v (yv i) = evFin F v (y i) := by
      intro i; rw [hyv]; exact GlobalTheory.LatVac.evFin_liftV v _
    have hoff : ∀ i, evFin F v (y' i) = 0 := by
      intro i; rw [hy', Pi.sub_apply, map_sub, hev, sub_self]
    have hsum : y' + yv = y := by rw [hy', sub_add_cancel]
    have hry : r y = r y' := by rw [← hsum]; exact hr.1 y' yv hatv

    have hD : R 0 • tens (evFin F v) φ r - r y' • (fun x => tens (evFin F v) φ R (x + -y')) ∈
        schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) :=
      sub_mem (Submodule.smul_mem _ _ hr.2) (Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem (-y') _ hRφ.2))
    have hvan : ∀ z, At (evFin F v) z →
        (R 0 • tens (evFin F v) φ r - r y' • (fun x => tens (evFin F v) φ R (x + -y'))) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y' := by
        rw [← hsum, add_assoc]; exact hr.1 y' (yv + z) (at_add_divisor v hatv hz)
      have e2 : y + z + -y' = 0 + (yv + z) := by rw [← hsum]; abel
      have e3 : R (y + z + -y') = R 0 := by rw [e2]; exact hRφ.1 0 (yv + z) (at_add_divisor v hatv hz)
      have e4 : (fun i => evFin F v ((y + z + -y') i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp only [Pi.add_apply, Pi.neg_apply, map_add, map_neg, hoff, neg_zero, add_zero]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, tens]
      rw [e1, e3, e4]
      ring
    have hT := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v B.ψ (omd g) hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hTr.base.std)
      (fun Φ hΦ => hW.pres g Φ hΦ) (fun μ hμ Φ hΦ => hW.unit μ hμ g Φ hΦ)
      (fun u hu p q Φ hΦ => comm_off B G dd omd hW v g hg u hu p q Φ hΦ) _ hD y hvan
    have hoff' : ∀ i, evFin F v ((-y') i) = 0 := by
      intro i; rw [Pi.neg_apply, map_neg, hoff, neg_zero]
    rw [map_sub, map_smul, map_smul, htr (-y') hoff' _ hRφ.2] at hT
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hT
    have e5 : y + -y' = yv := by rw [← hsum]; abel
    rw [e5, sub_eq_zero] at hT
    show omd g (tens (evFin F v) φ r) y =
      (R 0)⁻¹ * omd g (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i))) * r y
    rw [← hyv, hry]
    calc omd g (tens (evFin F v) φ r) y = (R 0)⁻¹ * (R 0 * omd g (tens (evFin F v) φ r) y) := by
          rw [inv_mul_cancel_left₀ hR0]
      _ = _ := by rw [hT]; ring

end GlobalTheory.WeilLocalityDbl
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilRepresentation_locality_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ g : UG (cA σ) (dbl (incM F G.W.J)), At (evFin F v) (GlobalTheory.InertDbl.matD g - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), Acts (evFin F v) (omd g) φ φ₁ := by
  atlas_forward_decl GlobalTheory.WeilLocalityDbl.locality
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_twistedVacuumCondition_doubledLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • (G.M'.vac v))) →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))))) := by
  first | exact @GlobalTheory.DblVacLine.dbl_vac_acts | exact GlobalTheory.DblVacLine.dbl_vac_acts | (intros; apply GlobalTheory.DblVacLine.dbl_vac_acts <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacTransport

theorem acts_dblVacCond_of_mem_KAtD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ₁)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ₁))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v dd omd hsp θ hθ g hg φ hφ φ₁ hφ₁ hvac hAct w₁ hw₁ w₂ hw₂ r hr
  have hS := hsp.2.1
  have etens : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [smul_zero, e0]
    funext x
    simp [Darboux.rho, schr]
  have hrφ : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  obtain ⟨δ₁, k₁, δ₂, k₂, he⟩ := GlobalTheory.DblVacLine.fromCols_mul_transpose G.V' G.W v (GlobalTheory.InertDbl.matD g⁻¹)
    (fun z hz => (hg.2 z hz).2) hw₁ hw₂
  have hback : actB (cA σ) g (Matrix.fromCols δ₁ δ₂) = Matrix.fromCols w₁ w₂ := by
    change Matrix.fromCols δ₁ δ₂ * (GlobalTheory.InertDbl.matD g)ᵀ = _
    have e : GlobalTheory.InertDbl.matD g * GlobalTheory.InertDbl.matD g⁻¹ = 1 := Units.mul_inv g.1
    rw [← he, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsym : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
        (Matrix.fromCols δ₁ δ₂) (Matrix.fromCols δ₁ δ₂) =
      symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
        (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂) := by
    rw [← he]
    exact GlobalTheory.InertSph.symp_mul_transpose (cA σ) _ _ _ (GlobalTheory.InertDbl.matD g⁻¹) (g⁻¹).2 _
  have hi := hS.impl g (Matrix.fromCols δ₁ δ₂) _ hrφ.2
  rw [hback] at hi
  rw [← hAct r hrφ, ← hi, hvac δ₁ k₁ δ₂ k₂ r hrφ, hsym, etens, map_smul, hAct r hrφ, etens]

end GlobalTheory.DblVacTransport
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumCondition_stable_latticeStabilizer_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ₁)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ₁))) := by
  atlas_forward_decl GlobalTheory.DblVacTransport.acts_dblVacCond_of_mem_KAtD
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacUniq

theorem dbl_vac_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • (G.M'.vac v))) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → ∃ c : ℂ, φ = c • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin dd hdd θ _ hvac φ hφ hfix
  classical
  set Λ := latAtV G.V' G.W v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hTr.base.std
  have hnl : ∀ t, ‖GlobalTheory.LatVac.psiAt B.ψ v t‖ = 1 := fun t => hn _
  set vac := G.M'.vac v with hvacdef
  have hvacSB : vac ∈ SB _ := (hTr.geo.hM'.vac v).1
  have hvac0 : vac ≠ 0 := (hTr.geo.hM'.vac v).2.1
  let cf1 : Matrix (Fin a') (Fin (a + a')) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ)
  let cf : Matrix (Fin a') (Fin (a + a') ⊕ Fin (a + a')) (AE F E) → ℂ := fun m =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J)) m m)
  have hcf : ∀ γ₁ γ₂, cf (Matrix.fromCols γ₁ γ₂) = cf1 γ₁ * star (cf1 γ₂) := by
    intro γ₁ γ₂
    simp only [cf, cf1, GlobalTheory.DblVacLine.symp_dbl, GlobalTheory.DblVacLine.star_eq_neg B.ψ hn, mul_sub]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]

  have hl1 : ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) vac = cf1 γ • vac := by
    intro γ hγ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v vac _ _ hvacSB fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ hγ) vac r hr).symm.trans (hvac γ hγ r hr)

  have hlφ : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂)) φ =
      cf (Matrix.fromCols γ₁ γ₂) • φ := by
    intro γ₁ h₁ γ₂ h₂
    exact GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ (GlobalTheory.DblVacLine.at_fromCols v (hat _ h₁) (hat _ h₂)) φ r hr).symm.trans
        (hfix γ₁ h₁ γ₂ h₂ r hr)
  have hco : ∀ γ₁ γ₂, GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v γ₁).1 (GlobalTheory.LatVac.locCo G.M'.co v γ₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v γ₁).2 (-(GlobalTheory.LatVac.locCo G.M'.co v γ₂).2)) := by
    intro γ₁ γ₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).2 k)) = _
    rw [hdd]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _
  set φd := boxFun vac (fun x => star (vac x)) with hφd

  have hld : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂)) φd =
      cf (Matrix.fromCols γ₁ γ₂) • φd := by
    intro γ₁ h₁ γ₂ h₂
    rw [hco, hφd, GlobalTheory.DblVacLine.schr_box (GlobalTheory.LatVac.psiAt B.ψ v) hnl, hl1 γ₁ h₁, hl1 γ₂ h₂, hcf]
    funext x
    simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hvac0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show vac t * star (vac t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)

  have hsd := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW v
  have hunr := (hTr.base.inert v w hin).2.2
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat hTr.geo.hW.lat
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo G.M'.co v)) c hc0 (fun x => hunr x) (GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1 i.2.1))
    (fun i => cf (Matrix.fromCols i.1.1 i.2.1)) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ φd
    (fun i => hlφ _ i.1.2 _ i.2.2) (fun i => hld _ i.1.2 _ i.2.2) hφd0
  exact ⟨c', hc'⟩

end GlobalTheory.DblVacUniq

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_doubledVacuumCondition_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • (G.M'.vac v))) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (dbl (incM F G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → ∃ c : ℂ, φ = c • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) := by
  atlas_forward_decl GlobalTheory.DblVacUniq.dbl_vac_unique
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertDblLine

theorem line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw dd omd hdd hsp R hR g hg
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  set φ₀ := boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)) with hφ₀
  set r₀ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ := boxFun R (fun x => star (R x)) with hr₀
  have hΦ : GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) = tens (evFin F v) φ₀ r₀ := by
    funext x
    show (_ * _) * star (_ * _) = (_ * _) * (_ * _)
    rw [star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hstar : (fun x => star (G.M'.vac v x)) ∈ SB (Fin a' × Fin (a + a') → Fv F v) :=
    ⟨hvSB.1.comp star, hvSB.2.comp_left (g := star) (star_zero ℂ)⟩
  have hφ₀SB : φ₀ ∈ SB _ := GlobalTheory.BoxSpan.boxFun_mem_SB' hvSB hstar
  have hRest : Rest (evFin F v) φ₀ r₀ := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hl : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hr : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      simp only [hr₀, boxFun]
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hR.1 _ _ hl, hR.1 _ _ hr]
    · rw [← hΦ]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hR.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ _ hR.2)
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.doubledWeilRepresentation_locality_finitePlace F E σ B a a' G X om om' hTr v dd omd hsp g hg.1 φ₀ hφ₀SB
  have h₀ := GlobalTheory.T.doubledVacuum_twistedVacuumCondition_doubledLattice F E σ B a a' G X om om' hTr v dd hdd θ hθ hvac
  have h₁ := GlobalTheory.T.doubledVacuumCondition_stable_latticeStabilizer_inert F E σ B a a' G X om om' hTr v dd omd hsp θ hθ g hg φ₀ hφ₀SB φ₁ hφ₁ h₀ hact
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_doubledVacuumCondition_unique F E σ B a a' G X om om' hTr v w hw dd hdd θ hθ hvac φ₁ hφ₁ h₁
  refine ⟨c, ?_⟩
  rw [hΦ, hact r₀ hRest, hc]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.InertDblLine
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_doubledUnitary_vacuumTensor_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  atlas_forward_decl GlobalTheory.InertDblLine.line
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparisonCharacter_det_eq_one_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  first | exact @GlobalTheory.InertDetChr.alpha_det_eq_one | exact GlobalTheory.InertDetChr.alpha_det_eq_one | (intros; apply GlobalTheory.InertDetChr.alpha_det_eq_one <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_theta_integral_at_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  first | exact @GlobalTheory.IntegralDetModule.modu_norm_det_triple | exact GlobalTheory.IntegralDetModule.modu_norm_det_triple | (intros; apply GlobalTheory.IntegralDetModule.modu_norm_det_triple <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDblPar

theorem parD_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv p hp
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.star_mem_schA_main _ Ψ hΨ)
  have hV := hTr.geo.hM'.vac v
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hV.2.1 (funext h)
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_doubledUnitary_vacuumTensor_eigen F E σ B a a' G X om om' hTr v w hin dd omd hdc hws R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.T.exists_translationInvariant_doubledForm_conjProduct_ne_zero F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.T.doubledSiegelParabolic_diagonal_action_integral F E σ G.W v p hp t ht
  have ha := GlobalTheory.T.comparisonCharacter_det_eq_one_inertPlace F E σ B a a' G X om om' hTr v w hin hT t htp
  have hb := GlobalTheory.T.local_theta_integral_at_inert_place F E σ B a a' G X om om' hTr v w hin hT t htp
  rw [ha, hb] at hS
  rw [hc, map_smul, smul_eq_mul] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]

end GlobalTheory.InertDblPar

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilRep_fixes_vacuum_tensor_siegelParabolic_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.W v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  atlas_forward_decl GlobalTheory.InertDblPar.parD_fix
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeil_inert_place_vacuum_eigenfunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @GlobalTheory.DblVacLine.dblFun_eigen | exact GlobalTheory.DblVacLine.dblFun_eigen | (intros; apply GlobalTheory.DblVacLine.dblFun_eigen <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertConjSq

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def atV (v : Pl F) (x : Fv F v) : AF F :=
  ((0 : InfiniteAdeleRing F), RestrictedProduct.single (fun w : Pl F => w.adicCompletionIntegers F) v x)

theorem evFin_atV (v : Pl F) (x : Fv F v) : evFin F v (atV v x) = x := by
  show RestrictedProduct.single (fun w : Pl F => w.adicCompletionIntegers F) v x v = x
  exact RestrictedProduct.single_eq_same _ _ _

theorem mul_atV (v : Pl F) (a : AF F) (x : Fv F v) : a * atV v x = atV v (evFin F v a * x) := by
  refine Prod.ext (mul_zero _) ?_
  have key : ∀ f : RestrictedProduct (fun w : Pl F => w.adicCompletion F) (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) Filter.cofinite,
      f * RestrictedProduct.single (fun w : Pl F => w.adicCompletionIntegers F) v x =
        RestrictedProduct.single (fun w : Pl F => w.adicCompletionIntegers F) v (f v * x) := by
    intro f
    apply RestrictedProduct.ext
    intro w
    rw [RestrictedProduct.mul_apply]
    by_cases h : w = v
    · subst h; simp [RestrictedProduct.single_eq_same]
    · simp [RestrictedProduct.single_eq_of_ne _ _ h]
  exact key a.2

theorem atV_add (v : Pl F) (x y : Fv F v) : atV v (x + y) = atV v x + atV v y :=
  Prod.ext (add_zero _).symm (RestrictedProduct.single_add _ _ _ _)

theorem atV_sub (v : Pl F) (x y : Fv F v) : atV v (x - y) = atV v x - atV v y :=
  Prod.ext (sub_zero _).symm (RestrictedProduct.single_sub _ _ _ _)

theorem atV_zero (v : Pl F) : atV v 0 = 0 :=
  Prod.ext rfl (RestrictedProduct.single_zero _ _)

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem scalar_ids (σ : E →ₐ[F] E) (X Y e h bq cq : AF F) (A : AE F E)
    (he : e * e = e) (hX : e * X = X) (hY : e * Y = Y) (hN : X * X - bq * X * Y + cq * Y * Y = h * e)
    (h2 : 2 * h = 1) (hA : A * A + algebraMap (AF F) (AE F E) bq * A + algebraMap (AF F) (AE F E) cq = 0)
    (hcA : cA σ A = -algebraMap (AF F) (AE F E) bq - A) :
    let ι := algebraMap (AF F) (AE F E)
    let Z := ι X + ι Y * A
    let α := 1 - ι e + 3 * ι h * Z
    let β := -(ι h * Z)
    α * cA σ α - β * cA σ β = 1 ∧ α * cA σ β = β * cA σ α ∧ (α - β) - 2 * (α + β) = ι e - 1 := by
  intro ι Z α β
  have cι : ∀ r, cA σ (ι r) = ι r := fun r => (cA σ).commutes r
  have hZ' : cA σ Z = ι X + ι Y * (-ι bq - A) := by
    simp only [Z, map_add, map_mul, cι, hcA]; rfl
  set Z' := cA σ Z with hZ'def
  have hα : cA σ α = 1 - ι e + 3 * ι h * Z' := by
    simp only [α, map_add, map_sub, map_mul, map_one, map_ofNat, cι, Z']
  have hβ : cA σ β = -(ι h * Z') := by
    simp only [β, map_neg, map_mul, cι, Z']
  have hE : ι e * ι e = ι e := by rw [← map_mul, he]
  have hEZ : ι e * Z = Z := by
    simp only [Z]; rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, hX, hY]
  have hEZ' : ι e * Z' = Z' := by
    rw [hZ']; rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, hX, hY]
  have hN' : Z * Z' = ι h * ι e := by
    rw [hZ']
    have := congrArg ι hN
    simp only [map_add, map_sub, map_mul] at this
    simp only [Z]
    linear_combination this - ι Y * ι Y * hA
  have h2' : 2 * ι h = 1 := by
    have := congrArg ι h2
    rw [map_mul, map_ofNat, map_one] at this; exact this
  rw [hα, hβ]
  refine ⟨?_, ?_, ?_⟩
  · simp only [α, β]
    linear_combination hE - 3 * ι h * hEZ - 3 * ι h * hEZ' + 8 * ι h ^ 2 * hN' + ι e * (4 * ι h ^ 2 + 2 * ι h + 1) * h2'
  · simp only [α, β]
    linear_combination ι h * hEZ' - ι h * hEZ
  · simp only [α, β]
    ring

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def blk (d : ℕ) (x y : AE F E) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
  fromBlocks (x • 1) (y • 1) (y • 1) (x • 1)

theorem blk_mul (d : ℕ) (x y x' y' : AE F E) :
    blk d x y * blk d x' y' = blk d (x * x' + y * y') (x * y' + y * x') := by
  simp only [blk, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← add_smul]
  congr 2 <;> ring

theorem blk_one (d : ℕ) : blk d (F := F) (E := E) 1 0 = 1 := by
  simp [blk, fromBlocks_one]

theorem blk_transpose (d : ℕ) (x y : AE F E) : (blk d x y)ᵀ = blk d x y := by
  simp [blk, fromBlocks_transpose]

theorem smul_one_map (d : ℕ) (f : AE F E →ₐ[AF F] AE F E) (x : AE F E) :
    ((x • 1 : Matrix (Fin d) (Fin d) (AE F E))).map f = f x • 1 := by
  ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]; split_ifs <;> simp

theorem blk_map (d : ℕ) (f : AE F E →ₐ[AF F] AE F E) (x y : AE F E) : (blk d x y).map f = blk d (f x) (f y) := by
  simp [blk, fromBlocks_map, smul_one_map]

theorem blk_unitary (d : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin d) (Fin d) (AE F E)) (α β : AE F E)
    (h1 : α * cA σ α - β * cA σ β = 1) (h2 : α * cA σ β = β * cA σ α) :
    (blk d α β)ᵀ * dbl J * (blk d α β).map (cA σ) = dbl J := by
  rw [blk_transpose, blk_map, dbl, blk, blk, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, smul_smul, smul_neg]
  congr 1
  all_goals
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, Matrix.zero_apply]
    first
      | linear_combination (J i j) * h1
      | linear_combination (J i j) * h2
      | linear_combination -(J i j) * h2
      | linear_combination -(J i j) * h1

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem blk_mul_fromRows (d : ℕ) (x y : AE F E) (X Y : Matrix (Fin d) (Fin d) (AE F E)) :
    blk d x y * fromRows X Y = fromRows (x • X + y • Y) (y • X + x • Y) := by
  ext (i | i) j <;> simp [blk, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem blk_diag (d : ℕ) (x y : AE F E) :
    blk d x y * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((x + y) • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
  rw [diagCols, blk_mul_fromRows]
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, add_smul, add_comm]

theorem blk_anti (d : ℕ) (x y : AE F E) :
    blk d x y * (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((x - y) • (1 : Matrix (Fin d) (Fin d) (AE F E))) := by
  rw [antiCols, blk_mul_fromRows]
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, sub_smul] <;> ring

theorem cols_ext (d : ℕ) (X Y : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (h1 : X * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      Y * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)))
    (h2 : X * (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = Y * antiCols (F := F) (E := E) d) : X = Y := by
  set c : AE F E := algebraMap (AF F) (AE F E) (⅟(2 : AF F))
  have hc : c + c = 1 := by
    simp only [c]; rw [← map_add, invOf_two_add_invOf_two, map_one]
  have hP : fromCols (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) (antiCols (F := F) (E := E) d) *
      (c • fromBlocks 1 1 1 (-1)) = 1 := by
    rw [diagCols, antiCols, fromCols_fromRows_eq_fromBlocks, Matrix.mul_smul, fromBlocks_multiply, fromBlocks_smul,
      ← fromBlocks_one]
    simp [← add_smul, hc]
  set D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d)
  set K : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := antiCols (F := F) (E := E) d
  set Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := c • fromBlocks 1 1 1 (-1)
  have eX : X = fromCols (X * D) (X * K) * Q := by
    rw [← Matrix.mul_fromCols, Matrix.mul_assoc, hP, Matrix.mul_one]
  have eY : Y = fromCols (Y * D) (Y * K) * Q := by
    rw [← Matrix.mul_fromCols, Matrix.mul_assoc, hP, Matrix.mul_one]
  rw [eX, h1, h2]
  exact eY.symm

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mkS (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (α β : AE F E) (h1 : α * cA σ α - β * cA σ β = 1)
    (h2 : α * cA σ β = β * cA σ α) : UD σ W :=
  ⟨⟨blk d α β, blk d (cA σ α) (-cA σ β),
    by rw [blk_mul, ← blk_one d]; congr 1 <;> first | linear_combination h1 | linear_combination -h2 | linear_combination h2,
    by rw [blk_mul, ← blk_one d]; congr 1 <;> first | linear_combination h1 | linear_combination -h2 | linear_combination h2⟩,
    blk_unitary d σ (incM F W.J) α β h1 h2⟩

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem antiCols_transpose_mul (d : ℕ) :
    (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ * antiCols (F := F) (E := E) d = (1 : Matrix (Fin d) (Fin d) (AE F E)) + 1 := by
  simp [antiCols, transpose_fromRows, fromCols_mul_fromRows]

theorem at_b {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} (n : UD σ W) (hK : At (evFin F v) (matD n - 1))
    (b : Matrix (Fin d) (Fin d) (AE F E))
    (hb : matD n * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = diagCols (Fin d) + antiCols (F := F) (E := E) d * b) :
    At (evFin F v) b := by
  intro u hu
  have h0 : u • (matD n - 1) = 0 := hK u hu
  have e : b + b = (antiCols (F := F) (E := E) d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ *
      ((matD n - 1) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))) := by
    rw [Matrix.sub_mul, hb, Matrix.one_mul, add_sub_cancel_left, ← Matrix.mul_assoc, antiCols_transpose_mul,
      Matrix.add_mul, Matrix.one_mul]
  have e2 : u • (b + b) = 0 := by
    rw [e, ← Matrix.mul_smul, ← Matrix.smul_mul, h0, Matrix.zero_mul, Matrix.mul_zero]
  set c : AE F E := algebraMap (AF F) (AE F E) (⅟(2 : AF F))
  have hc : c + c = 1 := by
    simp only [c]; rw [← map_add, invOf_two_add_invOf_two, map_one]
  calc u • b = (c + c) • (u • b) := by rw [hc, one_smul]
    _ = c • (u • (b + b)) := by rw [add_smul, ← smul_add, ← smul_add]
    _ = 0 := by rw [e2, smul_zero]

theorem mkS_conj (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) (α β : AE F E)
    (h1 : α * cA σ α - β * cA σ β = 1) (h2 : α * cA σ β = β * cA σ α) (n : UD σ W) (hn : n ∈ NabD σ W v)
    (hkey : ∀ b : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) b → (α - β) • b = (2 * (α + β)) • b) :
    mkS σ W α β h1 h2 * n * (mkS σ W α β h1 h2)⁻¹ = n * n := by
  obtain ⟨hK, hA, b, hb⟩ := hn
  set N := matD n
  set D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d)
  set K : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := antiCols (F := F) (E := E) d
  have hA' : N * K = K := hA
  have hb' : N * D = D + K * b := hb
  have hbAt := at_b n hK.1 b hb'
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext; apply Units.ext
  show blk d α β * N = N * N * blk d α β
  apply cols_ext
  · have eL : blk d α β * N * D = (α + β) • D + (2 * (α + β)) • (K * b) := by
      rw [Matrix.mul_assoc, hb', Matrix.mul_add, blk_diag, ← Matrix.mul_assoc, blk_anti, Matrix.mul_assoc,
        Matrix.smul_mul, Matrix.one_mul, hkey b hbAt, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    have eR : N * N * blk d α β * D = (α + β) • (D + K * b + K * b) := by
      rw [Matrix.mul_assoc, blk_diag, ← Matrix.mul_assoc, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc, hb',
        Matrix.mul_add, hb', ← Matrix.mul_assoc, hA']
    rw [eL, eR]
    simp only [smul_add, two_mul, add_smul]
    abel
  · rw [Matrix.mul_assoc, hA', Matrix.mul_assoc, blk_anti, ← Matrix.mul_assoc, Matrix.mul_assoc N N K, hA', hA']

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem blk_mulVec_inl (d : ℕ) (x y : AE F E) (z : Fin d ⊕ Fin d → AE F E) :
    (fun i => (blk d x y *ᵥ z) (Sum.inl i)) = x • (fun i => z (Sum.inl i)) + y • (fun i => z (Sum.inr i)) := by
  funext i; simp [blk, fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Function.comp_def]

theorem blk_mulVec_inr (d : ℕ) (x y : AE F E) (z : Fin d ⊕ Fin d → AE F E) :
    (fun i => (blk d x y *ᵥ z) (Sum.inr i)) = y • (fun i => z (Sum.inl i)) + x • (fun i => z (Sum.inr i)) := by
  funext i; simp [blk, fromBlocks_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Function.comp_def]

theorem blk_mulVec_mem {d : ℕ} {W : Spc F E d} {v : Pl F} (x y : AE F E)
    (hx : ∀ z ∈ GlobalTheory.InertSph.latAt W v, x • z ∈ GlobalTheory.InertSph.latAt W v)
    (hy : ∀ z ∈ GlobalTheory.InertSph.latAt W v, y • z ∈ GlobalTheory.InertSph.latAt W v) :
    ∀ z ∈ latAtD W v, blk d x y *ᵥ z ∈ latAtD W v := by
  intro z hz
  obtain ⟨h1, h2⟩ := hz
  refine ⟨?_, ?_⟩
  · rw [blk_mulVec_inl]; exact add_mem (hx _ h1) (hy _ h2)
  · rw [blk_mulVec_inr]; exact add_mem (hy _ h1) (hx _ h2)

theorem blk_sub_one (d : ℕ) (x y : AE F E) : blk d x y - 1 = blk d (x - 1) y := by
  ext (i | i) (j | j) <;> simp [blk, Matrix.one_apply] <;> split_ifs <;> simp

theorem smul_blk (d : ℕ) (u : AF F) (x y : AE F E) : u • blk d x y = blk d (u • x) (u • y) := by
  simp [blk, fromBlocks_smul, smul_assoc]

theorem mkS_mem_ParD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) (α β : AE F E)
    (h1 : α * cA σ α - β * cA σ β = 1) (h2 : α * cA σ β = β * cA σ α)
    (hAt : ∀ u : AF F, evFin F v u = 0 → u • (α - 1) = 0 ∧ u • β = 0)
    (hL : ∀ r ∈ ({α, β, cA σ α, -cA σ β} : Set (AE F E)), ∀ z ∈ GlobalTheory.InertSph.latAt W v, r • z ∈ GlobalTheory.InertSph.latAt W v) :
    mkS σ W α β h1 h2 ∈ ParD σ W v := by
  refine ⟨⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · show u • (blk d α β - 1) = 0
    rw [blk_sub_one, smul_blk, (hAt u hu).1, (hAt u hu).2]
    simp [blk, fromBlocks_zero]
  · exact blk_mulVec_mem α β (hL α (by simp)) (hL β (by simp)) z hz
  · exact blk_mulVec_mem (cA σ α) (-cA σ β) (hL _ (by simp)) (hL _ (by simp)) z hz
  · refine ⟨⟨(α + β) • 1, (cA σ α - cA σ β) • 1, ?_, ?_⟩, ?_⟩
    · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
      convert one_smul (AE F E) (1 : Matrix (Fin d) (Fin d) (AE F E)) using 2
      linear_combination h1 - h2
    · rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
      convert one_smul (AE F E) (1 : Matrix (Fin d) (Fin d) (AE F E)) using 2
      linear_combination h1 - h2
    · exact blk_diag d α β

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_latAt {d : ℕ} {W : Spc F E d} {v : Pl F} (p q : AF F)
    (hp : evFin F v p ∈ v.adicCompletionIntegers F) (hq : evFin F v q ∈ v.adicCompletionIntegers F) (a₀ : 𝓞 E) :
    ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      (algebraMap (AF F) (AE F E) p + algebraMap (AF F) (AE F E) q * inclR (F := F) (AF F) (a₀ : E)) • z ∈
        GlobalTheory.InertSph.latAt W v := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    have gen : ∀ (r : AF F) (y' : Fin d → E), At (evFin F v) a → evFin F v r ∈ v.adicCompletionIntegers F →
        y' ∈ W.L → (r * a) • (fun i => inclR (F := F) (AF F) (y' i)) ∈ GlobalTheory.InertSph.latAt W v := by
      intro r y' ha hr hy'
      refine AddSubgroup.subset_closure ⟨r * a, fun u hu => ?_, ?_, y', hy', rfl⟩
      · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
      · rw [map_mul]; exact mul_mem hr hai
    have e : (algebraMap (AF F) (AE F E) p + algebraMap (AF F) (AE F E) q * inclR (F := F) (AF F) (a₀ : E)) •
        (a • fun i => inclR (F := F) (AF F) (y i)) =
        (p * a) • (fun i => inclR (F := F) (AF F) (y i)) +
          (q * a) • (fun i => inclR (F := F) (AF F) ((a₀ • y) i)) := by
      funext i
      show (algebraMap (AF F) (AE F E) p + algebraMap (AF F) (AE F E) q * inclR (F := F) (AF F) (a₀ : E)) *
          (a • inclR (F := F) (AF F) (y i)) =
        (p * a) • inclR (F := F) (AF F) (y i) + (q * a) • inclR (F := F) (AF F) (a₀ • y i)
      rw [Algebra.smul_def (A := E), map_mul]
      simp only [Algebra.smul_def, map_mul]
      have : inclR (F := F) (AF F) (algebraMap (𝓞 E) E a₀) = inclR (F := F) (AF F) (a₀ : E) := rfl
      rw [this]
      ring
    rw [e]
    exact add_mem (gen p y ha hp hy) (gen q _ ha hq (W.L.smul_mem a₀ hy))
  | zero => rw [smul_zero]; exact zero_mem _
  | add z₁ z₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
  | neg z _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl IsDedekindDomain.HeightOneSpectrum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_evFin_half (v : Pl F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    Valued.v (evFin F v (⅟(2 : AF F))) = 1 := by
  have e2 : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2 : v.adicCompletionIntegers F) : Fv F v) = 2 := by
    rw [GlobalTheory.InertUnitNorm.coe_algebraMap_adicCompletionIntegers]
    first | (push_cast; exact map_ofNat _ 2) | (norm_num) | (exact_mod_cast map_ofNat (algebraMap F (Fv F v)) 2) | (simp [map_ofNat])
  have hle : Valued.v (2 : Fv F v) ≤ 1 := by
    rw [← e2]; exact (algebraMap (𝓞 F) (v.adicCompletionIntegers F) 2).2
  have hnlt : ¬ Valued.v (2 : Fv F v) < 1 := by
    rw [← e2, ← GlobalTheory.InertUnitNorm.mem_maximalIdeal_iff_valued_lt_one, GlobalTheory.InertUnitNorm.algebraMap_mem_maximalIdeal_iff]
    exact h2
  have hv2 : Valued.v (2 : Fv F v) = 1 := le_antisymm hle (not_lt.mp hnlt)
  have hm : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have := congrArg Valued.v hm
  rwa [map_mul, hv2, mul_one, map_one] at this

end GlobalTheory.InertConjSq
end

noncomputable section
namespace GlobalTheory.InertConjSq

open Matrix GlobalTheory.InertDbl IsDedekindDomain.HeightOneSpectrum

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem conj_sq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ n ∈ GlobalTheory.InertDbl.NabD σ W v, ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v, s * n * s⁻¹ = n * n := by
  intro F E _ _ _ _ _ σ B hB d W v w hvw n hn
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hvw]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hconj, hroot⟩ := GlobalTheory.InertUnitNorm.exists_integral_gen σ hB.cm v hp
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  have hU : Valued.v (evFin F v (⅟(2 : AF F))) = 1 := valued_evFin_half v h2
  obtain ⟨x, y, hxy⟩ := GlobalTheory.InertUnitNorm.exists_int_sol v b c h2 hroot ⟨_, hU.le⟩ hU
  have hK : (x : Fv F v) ^ 2 - algebraMap F (Fv F v) (b : F) * x * y + algebraMap F (Fv F v) (c : F) * y ^ 2 =
      evFin F v (⅟(2 : AF F)) := by
    have := congrArg (fun t : v.adicCompletionIntegers F => (t : v.adicCompletion F)) hxy
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      GlobalTheory.InertUnitNorm.coe_algebraMap_adicCompletionIntegers] at this
    exact this
  have hev : ∀ t : F, evFin F v (algebraMap F (AF F) t) = algebraMap F (Fv F v) t := fun t => (evFin F v).commutes t
  have he : atV v 1 * atV v 1 = atV v 1 := by rw [mul_atV, evFin_atV, mul_one]
  have hX : atV v 1 * atV v (x : Fv F v) = atV v (x : Fv F v) := by rw [mul_atV, evFin_atV, one_mul]
  have hY : atV v 1 * atV v (y : Fv F v) = atV v (y : Fv F v) := by rw [mul_atV, evFin_atV, one_mul]
  have hN : atV v (x : Fv F v) * atV v (x : Fv F v) - algebraMap F (AF F) (b : F) * atV v (x : Fv F v) * atV v (y : Fv F v) +
      algebraMap F (AF F) (c : F) * atV v (y : Fv F v) * atV v (y : Fv F v) = ⅟(2 : AF F) * atV v 1 := by
    simp only [mul_assoc, mul_atV, evFin_atV, hev]
    rw [← atV_sub, ← atV_add, mul_one, ← hK]
    congr 1
    ring
  have h2' : (2 : AF F) * ⅟2 = 1 := mul_invOf_self 2
  have hιF : ∀ t : F, inclR (F := F) (AF F) (algebraMap F E t) =
      algebraMap (AF F) (AE F E) (algebraMap F (AF F) t) := fun t => by
    show Algebra.TensorProduct.includeRight (algebraMap F E t) = _
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have hA : inclR (F := F) (AF F) (a : E) * inclR (F := F) (AF F) (a : E) +
      algebraMap (AF F) (AE F E) (algebraMap F (AF F) (b : F)) * inclR (F := F) (AF F) (a : E) +
      algebraMap (AF F) (AE F E) (algebraMap F (AF F) (c : F)) = 0 := by
    have := congrArg (inclR (F := F) (AF F)) hq
    simp only [map_add, map_mul, map_pow, map_zero, hιF] at this
    linear_combination this
  have hcA : cA σ (inclR (F := F) (AF F) (a : E)) =
      -algebraMap (AF F) (AE F E) (algebraMap F (AF F) (b : F)) - inclR (F := F) (AF F) (a : E) := by
    have e1 : cA σ (inclR (F := F) (AF F) (a : E)) = inclR (F := F) (AF F) (σ (a : E)) := by
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] (a : E)) = (1 : AF F) ⊗ₜ[F] σ (a : E)
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [e1, hconj, map_sub, map_neg, hιF]
  have R := scalar_ids σ (atV v (x : Fv F v)) (atV v (y : Fv F v)) (atV v 1) (⅟(2 : AF F))
    (algebraMap F (AF F) (b : F)) (algebraMap F (AF F) (c : F)) (inclR (F := F) (AF F) (a : E)) he hX hY hN
    (by rw [mul_comm]; exact invOf_mul_self 2) hA hcA
  obtain ⟨R1, R2, R3⟩ := R
  have hO3 : (3 : Fv F v) ∈ v.adicCompletionIntegers F := by
    have h1 : (1 : Fv F v) ∈ v.adicCompletionIntegers F := one_mem _
    have : (3 : Fv F v) = 1 + 1 + 1 := by norm_num
    rw [this]; exact add_mem (add_mem h1 h1) h1
  have hOU : evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := hU.le
  have hOx : (x : Fv F v) ∈ v.adicCompletionIntegers F := x.2
  have hOy : (y : Fv F v) ∈ v.adicCompletionIntegers F := y.2
  have hOb : algebraMap F (Fv F v) (b : F) ∈ v.adicCompletionIntegers F := by
    rw [← GlobalTheory.InertUnitNorm.coe_algebraMap_adicCompletionIntegers]; exact (algebraMap (𝓞 F) (v.adicCompletionIntegers F) b).2
  have key : ∀ p q : AF F, evFin F v p ∈ v.adicCompletionIntegers F → evFin F v q ∈ v.adicCompletionIntegers F →
      ∀ r, r = algebraMap (AF F) (AE F E) p + algebraMap (AF F) (AE F E) q * inclR (F := F) (AF F) (a : E) →
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, r • z ∈ GlobalTheory.InertSph.latAt W v := by
    rintro p q hp hq r rfl
    exact smul_latAt p q hp hq a
  refine ⟨mkS σ W _ _ R1 R2, mkS_mem_ParD σ W v _ _ R1 R2 ?_ ?_, mkS_conj σ W v _ _ R1 R2 n hn ?_⟩
  · intro u hu
    have hu0 : ∀ t, algebraMap (AF F) (AE F E) u * algebraMap (AF F) (AE F E) (atV v t) = 0 := fun t => by
      rw [← map_mul, mul_atV, hu, zero_mul, atV_zero, map_zero]
    refine ⟨?_, ?_⟩ <;> rw [Algebra.smul_def]
    · linear_combination -(hu0 1) + 3 * algebraMap (AF F) (AE F E) (⅟2) * hu0 (x : Fv F v) +
        3 * algebraMap (AF F) (AE F E) (⅟2) * inclR (F := F) (AF F) (a : E) * hu0 (y : Fv F v)
    · linear_combination -(algebraMap (AF F) (AE F E) (⅟2)) * hu0 (x : Fv F v) -
        algebraMap (AF F) (AE F E) (⅟2) * inclR (F := F) (AF F) (a : E) * hu0 (y : Fv F v)
  · intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine key (1 - atV v 1 + 3 * ⅟2 * atV v (x : Fv F v)) (3 * ⅟2 * atV v (y : Fv F v)) ?_ ?_ _ ?_
      · simp only [map_add, map_sub, map_mul, map_one, map_ofNat, evFin_atV]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_ofNat, evFin_atV]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_ofNat]; ring
    · refine key (-(⅟2 * atV v (x : Fv F v))) (-(⅟2 * atV v (y : Fv F v))) ?_ ?_ _ ?_
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat]; ring
    · refine key (1 - atV v 1 + 3 * ⅟2 * (atV v (x : Fv F v) - atV v (y : Fv F v) * algebraMap F (AF F) (b : F)))
        (-(3 * ⅟2 * atV v (y : Fv F v))) ?_ ?_ _ ?_
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV, hev]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV, hev]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, AlgHom.commutes, hcA]; ring
    · refine key (⅟2 * (atV v (x : Fv F v) - atV v (y : Fv F v) * algebraMap F (AF F) (b : F)))
        (-(⅟2 * atV v (y : Fv F v))) ?_ ?_ _ ?_
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV, hev]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, evFin_atV, hev]
        repeat (first | exact one_mem _ | assumption | apply add_mem | apply sub_mem | apply mul_mem | apply neg_mem)
      · simp only [map_add, map_sub, map_mul, map_one, map_neg, map_ofNat, AlgHom.commutes, hcA]; ring
  · intro b' hb'
    rw [sub_eq_iff_eq_add.mp R3, add_smul]
    have : (algebraMap (AF F) (AE F E) (atV v 1) - 1) • b' = 0 := by
      rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, algebraMap_smul]
      exact hb' _ (by rw [map_sub, evFin_atV, map_one, sub_self])
    rw [this, zero_add]

end GlobalTheory.InertConjSq
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotentRadical_conj_to_square_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ W v, ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v, s * n * s⁻¹ = n * n := by
  atlas_forward_decl GlobalTheory.InertConjSq.conj_sq
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.NabFix

theorem nab_fix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv n hn
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) with hΦdef
  obtain ⟨c, hc⟩ := GlobalTheory.T.doubledWeil_inert_place_vacuum_eigenfunction F E σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv n hn.1
  obtain ⟨s, hs, hsn⟩ := GlobalTheory.T.integralUnipotentRadical_conj_to_square_inertPlace F E σ B hTr.base (a + a') G.W v w hin n hn
  have hs1 : omd s Φ = Φ := GlobalTheory.T.doubledWeilRep_fixes_vacuum_tensor_siegelParabolic_inert F E σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv s hs
  have hs2 : omd s⁻¹ Φ = Φ := by
    conv_lhs => rw [← hs1]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e1 : omd (s * n * s⁻¹) Φ = c • Φ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hs2, hc, map_smul, hs1]
  have e2 : omd (n * n) Φ = (c * c) • Φ := by
    rw [map_mul, Module.End.mul_apply, hc, map_smul, hc, smul_smul]
  rw [hsn, e2] at e1
  by_cases hΦ : Φ = 0
  · rw [hΦ, map_zero]
  have hcc : c * c = c := smul_left_injective ℂ hΦ e1
  have h01 : c = 0 ∨ c = 1 := by
    rcases mul_eq_zero.1 (show c * (c - 1) = 0 by linear_combination hcc) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  rcases h01 with h0 | h1
  · exfalso
    apply hΦ
    have : omd n⁻¹ (omd n Φ) = Φ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hc, h0, zero_smul, map_zero]
  · rw [hc, h1, one_smul]

end GlobalTheory.NabFix
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilRep_fixes_integralUnipotent_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ n ∈ GlobalTheory.InertDbl.NabD σ G.W v, omd n (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  atlas_forward_decl GlobalTheory.NabFix.nab_fix
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_mem_adelicSchwartzSpaceNumberField : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ), Φ ∈ schA F κ → (fun x => star (Φ x)) ∈ schA F κ := by
  first | exact @GlobalTheory.SchAConj.star_mem_schA | exact GlobalTheory.SchAConj.star_mem_schA | (intros; apply GlobalTheory.SchAConj.star_mem_schA <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertScalar

theorem scalar_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin hT k hk c hc
  obtain ⟨-, dd, omd, hdc, hws, hres⟩ := hTr.weil'.1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hV := hTr.geo.hM'.vac v
  have hSB : G.M'.vac v ∈ SB _ := hV.1
  have hne : G.M'.vac v ≠ 0 := hV.2.1
  have hRv := hR _ hSB
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΨ' : (fun x => star (Ψ x)) ∈ schA F _ := GlobalTheory.T.star_mem_adelicSchwartzSpaceNumberField F _ Ψ hΨ

  let H : Subgroup (GlobalTheory.InertDbl.UD σ G.W) :=
    { carrier := {g | omd g (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hgen := GlobalTheory.T.inertPlace_doubledFirstFactor_mem_siegelClosure F E σ B a a' G X om om' hTr v w hin k hk
  have hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact GlobalTheory.T.doubledWeilRep_fixes_vacuum_tensor_siegelParabolic_inert F E σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv g hg
    · exact GlobalTheory.T.doubledWeilRep_fixes_integralUnipotent_inertPlace F E σ B a a' G X om om' hTr v w hin hT dd omd hdc hws R hR0 hRv g hg
  have hfix : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ := hle hgen
  have hact : om' (1, k) Ψ = c • Ψ := by
    rw [hΨdef, hc R hRv]
    funext x
    simp [tens, mul_assoc]
  have hr := hres k (GlobalTheory.InertDbl.inlD σ G.W k) rfl Ψ hΨ (fun x => star (Ψ x)) hΨ'
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hr
  rw [hact] at hr
  have key : c • GlobalTheory.InertDbl.dblFun Ψ = GlobalTheory.InertDbl.dblFun Ψ := by
    have e1 : omd (GlobalTheory.InertDbl.inlD σ G.W k) (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ := by
      unfold GlobalTheory.InertDbl.dblFun
      rw [hr]
      funext x
      simp only [boxFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← e1, hfix]
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hRx : R x = R 0 := by
    have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  have hΨx : Ψ x ≠ 0 := by
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx]
    exact mul_ne_zero hy hR0
  have h2 := congrFun key (Sum.elim x x)
  simp only [GlobalTheory.InertDbl.dblFun, boxFun, Pi.smul_apply, smul_eq_mul] at h2
  have hz : Ψ x * star (Ψ x) ≠ 0 := mul_ne_zero hΨx (star_ne_zero.mpr hΨx)
  have h3 : (Sum.elim x x ∘ Sum.inl : Fin a' × Fin (a + a') → AF F) = x := rfl
  have h4 : (Sum.elim x x ∘ Sum.inr : Fin a' × Fin (a + a') → AF F) = x := rfl
  rw [h3, h4] at h2
  exact (mul_eq_right₀ hz).mp h2

end GlobalTheory.InertScalar
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_scalar_eq_one_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  atlas_forward_decl GlobalTheory.InertScalar.scalar_eq_one
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph

theorem vac_fixed' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (G.M'.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hv k hk
  obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ B a a' G X om om' hTr v k hk.1 _ hSB
  have h1 := GlobalTheory.T.unitaryStabilizer_preserves_vacuumCondition_at_place F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB φ₁ hφ₁ hact hvac
  obtain ⟨c, rfl⟩ := GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul F E σ B a a' G X om om' hTr v w hw θ hθ hvac φ₁ hφ₁ h1
  have hc := GlobalTheory.T.weil_vacuum_scalar_eq_one_inert_place F E σ B a a' G X om om' hTr v w hw hv k hk c hact
  rwa [hc, one_smul] at hact

end GlobalTheory.InertSph
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_latticeStabilizer_fixes_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (G.M'.vac v) := by
  atlas_forward_decl GlobalTheory.InertSph.vac_fixed'
end
