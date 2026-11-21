import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqOfMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNonzeroIntertwiner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactPolynomialBlockTimesConjDetPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvConjTransposeMem
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModeMatrixDetEqAdjointDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointDetOnCompactTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrepAveragesFinDimSmoothOfKTypesAndPolyAverages
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCharFnAndIsPseudoCoeffOfCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoefIrrepHasDerivedAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylFormulaCompactTorusIdentityOfIngredients

section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem highestWeightKernel_lowestType : AlgDatum := by
  intro n ε lam hg M _ _ E hE hU z hz0 hzp hz hcas S hSfd hSk hzS

  have hz' : IsKHWVec ε (fun a b => TensorProduct.map (E a b) LinearMap.id +
      LinearMap.lTensor M (sgE ε cpFock cmFock a b)) (gaW ε lam) z := by
    have e : (diagE ε (eT E) cpT cmT : Fin n → Fin n → Module.End ℂ (TensorProduct ℂ M (Fock n))) =
        fun a b => TensorProduct.map (E a b) LinearMap.id + LinearMap.lTensor M (sgE ε cpFock cmFock a b) := by
      funext a b
      simp only [diagE, eT, sgE_cpT]
    rw [← e]; exact hz
  obtain ⟨s, hy0, hy⟩ := khw_extract ε hg.1 hz' hz0
  set y := tcoef ((fockBasis n).coord s) z with hydef

  have hs : s ⊆ lfPhysModes ε := by
    intro m hm
    by_contra hnm
    apply hy0
    refine tco_physSub_zero hzp hm fun hp => hnm ?_
    obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
    rw [Equiv.symm_apply_apply] at hp
    exact (lf_mem_phys ε x.1 x.2).2 hp
  set Ph := gcPh ε s with hPh
  have hwt : gaW ε lam - fockWt ε s = lowK ε lam - phSum Ph := by
    rw [gc_wt_eq ε hs]
    funext a
    simp only [gaW, lowK, Pi.sub_apply, Pi.add_apply]
    ring
  rw [hwt] at hy
  have hyS : y ∈ S := hzS s
  set V := kLowSpan ε E y with hV
  have hVS : V ≤ S := kLowSpan_le hSk hyS
  haveI : FiniteDimensional ℂ S := hSfd
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVS
  have hVirr : IsKIrrHW ε E (lowK ε lam - phSum Ph) V := kLowSpan_kIrrHW hE hU hy hy0 hVfd

  set T : Submodule ℂ M := LinearMap.ker (casimir E - ((casVal lam : ℝ) : ℂ) • (1 : Module.End ℂ M)) with hT
  have hTk : IsKStableSub ε E T := by
    intro a b _ v hv
    rw [hT, LinearMap.mem_ker] at hv ⊢
    have hc := congrArg (fun X : Module.End ℂ M => X v) (casimir_comm hE a b)
    simp only [Module.End.mul_apply] at hc
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
    rw [hc, sub_eq_zero.1 hv, map_smul, sub_self]
  have hyT : y ∈ T := by
    rw [hT, LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hcas s, sub_self]
  have hVT : V ≤ T := kLowSpan_le hTk hyT
  have hVc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v := by
    intro v hv
    have := hVT hv
    rw [hT, LinearMap.mem_ker] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
    exact sub_eq_zero.1 this

  have hPh0 : Ph = ∅ := by
    by_contra hne
    exact dirac_sharp hg hE hU (gc_isPosNC ε hs) (Finset.nonempty_iff_ne_empty.2 hne) hVirr hVc
  rw [hPh0] at hVirr
  simp only [phSum, Finset.sum_empty, sub_zero] at hVirr
  refine ⟨V, hVirr, ?_, hVc⟩
  intro h0
  apply hy0
  have : y ∈ V := self_mem_kLowSpan y
  rw [h0] at this
  exact (Submodule.mem_bot ℂ).1 this

end GlobalTheory.PsCo.PcEF
end
end

section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem casimirScalar_stableSumSpace : BuildY := by
  intro n ε H _ _ σ D E hσ hD c hc L hLf hLK
  have hE : IsGlRep E := hD.glRep
  have hLk : IsKStableSub ε E L :=
    isKStableSub_of_kStable hσ hD L hLf fun k hk v hv => ⟨sigD hD hk v, hLK k hk v hv, rfl⟩
  set Dop := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hDop
  let Y0 : Submodule ℂ (TensorProduct ℂ D (Fock n)) := tensFock L ⊓ physicalSubspace ε
  have hA : ∀ a b, ε a = ε b → ∀ x ∈ Y0, diagE ε (eT E) cpT cmT a b x ∈ Y0 :=
    fun a b hab x hx => ⟨tensorFock_diagAction_stable ε hLk hab hx.1, (physSub_stable ε E).2.1 a b x hx.2⟩
  have hD2 : ∀ y ∈ Y0, Dop (Dop y) ∈ Y0 := by
    intro y hy
    have h2 := LinearMap.congr_fun (two_D_sq (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε) y
    rw [LinearMap.smul_apply, Module.End.mul_apply] at h2
    have hcas : casimir (eT (n := n) E) y = c • y := by
      rw [TRGap.casimir_eT]
      exact map_eq_smul_of_tensFock (fun v _ => hc v) hy.1
    have hmem : (2 : ℂ) • Dop (Dop y) ∈ Y0 := by
      rw [hDop, h2]
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
        LinearMap.sum_apply]
      rw [hcas]
      refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)) ?_)
        (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hA a a rfl y hy)))
      simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb =>
        hA a b (Finset.mem_filter.1 hb).2.symm _ (hA b a (Finset.mem_filter.1 hb).2 y hy)
    have := Submodule.smul_mem _ (1 / 2 : ℂ) hmem
    rwa [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at this
  have hG0 : ∀ z ∈ Y0, gradT z ∈ Y0 := fun z hz =>
    ⟨tensFock_lTensor_stable _ hz.1, (physSub_stable ε E).2.2.2.2 z hz.2⟩
  have hW0 : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ Y0, wK hD hk y ∈ Y0 :=
    fun k hk y hy => ⟨wK_tensFock hD hk (fun x hx => hLK k hk x hx) hy.1, wK_physSub hD hk hy.2⟩
  have hfd0 : FiniteDimensional ℂ Y0 := by
    haveI := tensorFock_finiteDimensional (n := n) hLf
    exact Submodule.finiteDimensional_of_le inf_le_left
  refine ⟨Y0 ⊔ Y0.map Dop, inferInstance, le_sup_left, sup_le inf_le_right ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact dD_physSub E hy.2
  · intro y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    show Dop (y0 + Dop x) ∈ _
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_right ⟨y0, hy0, rfl⟩) (Submodule.mem_sup_left (hD2 x hx))
  · intro y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, hDop, gradT_D]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hG0 y0 hy0))
      (Submodule.mem_sup_right ⟨-gradT x, Submodule.neg_mem _ (hG0 x hx), by rw [map_neg]⟩)
  · intro k hk y hy
    obtain ⟨y0, hy0, y1, ⟨x, hx, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, hDop, wK_D hσ hD hk]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hW0 k hk y0 hy0))
      (Submodule.mem_sup_right ⟨_, hW0 k hk x hx, rfl⟩)

end GlobalTheory.PsCo.PcEF
end
end

section
noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem casimirValue_highestWeightCoordinates : CasCoord := by
  intro n ε lam M _ _ E hE z hz hD s
  have hE' := eT_isGlRep (n := n) hE
  have h2 := LinearMap.congr_fun (two_D_sq hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) z
  have hK := casimirK_khwVec_compact ε (diagE_compact hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) hz
  have hs : ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε (eT E) cpT cmT a a z =
      ((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z := by
    simp only [hz.1, smul_smul, ← sum_smul]
    congr 1
    unfold dot
    push_cast
    refine sum_congr rfl fun a _ => ?_
    ring
  have h0 : ((2 : ℂ) • ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) * (dOp ε (eT E) cpT + dOp' ε (eT E) cmT))) z = 0 := by
    rw [LinearMap.smul_apply, Module.End.mul_apply]
    have : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0 := hD
    rw [this, map_zero, smul_zero]
  rw [h0] at h2
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hK, hs] at h2
  have hid := khw_real_identity ε (lam - rhoC ε)
  have hg : lam - rhoC ε + rhoHol ε = gaW ε lam := rfl
  have hl : lam - rhoC ε + rhoC ε = lam := sub_add_cancel _ _
  rw [hg, hl] at hid
  have hc : casimir (eT (n := n) E) z = ((casVal lam : ℝ) : ℂ) • z := by
    have e : casimir (eT (n := n) E) z =
        ((nsq (gaW ε lam + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • z -
          (2 : ℂ) • (((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z) := by
      linear_combination (norm := module) h2
    rw [e, casVal, ← hid]
    push_cast
    module
  have := congrArg (tco s) hc
  rw [TRGap.casimir_eT, tco_map_left] at this
  rw [this]
  simp only [tco, map_smul]

end GlobalTheory.PsCo.PcEF
end
end

section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap Matrix
open Formalism.REAL (KG toMK)

namespace GlobalTheory.PsCo.PcEF.PhysicalMatrixDeterminant

variable {n : ℕ} {ε : Fin n → Bool}

def physM (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Matrix {x : Fin n × Fin n // IsPhys ε x} {x : Fin n × Fin n // IsPhys ε x} ℂ :=
  fun x y => k x.1.1 y.1.1 * star (k x.1.2 y.1.2)

theorem physM_eq_adMat (k : Matrix (Fin n) (Fin n) ℂ) (x y : {x : Fin n × Fin n // IsPhys ε x}) :
    physM ε k x y = adMat ε k x.1 y.1 := by
  simp [physM, adMat, x.2, y.2]

theorem physM_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) :
    physM ε (a * b) = physM ε a * physM ε b := by
  ext x y
  rw [physM_eq_adMat, adMat_mul ha hb, Matrix.mul_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype (IsPhys ε)]
  have h0 : ∑ z : {z : Fin n × Fin n // ¬ IsPhys ε z}, adMat ε a x.1 z * adMat ε b z y.1 = 0 :=
    Finset.sum_eq_zero fun z _ => by simp [adMat, x.2, z.2]
  rw [h0, add_zero]
  simp only [physM_eq_adMat]

theorem physM_one : physM ε (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext x y
  rw [physM_eq_adMat, adMat_one]
  by_cases h : x = y
  · subst h; simp
  · have h' : x.1 ≠ y.1 := fun e => h (Subtype.ext e)
    simp [h, h']

theorem physDet_eq (k : Matrix (Fin n) (Fin n) ℂ) : physDet ε k = (1 - physM ε k).det := by
  unfold physDet
  congr 1

theorem physDet_conj (k k' : KG ε) : physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) := by
  have ha : toMK k'⁻¹ ∈ Kset ε := (k'⁻¹).2
  have hb : toMK k ∈ Kset ε := k.2
  have hc : toMK k' ∈ Kset ε := k'.2
  have hab : toMK k'⁻¹ * toMK k ∈ Kset ε := (k'⁻¹ * k).2
  have hac : physM ε (toMK k'⁻¹) * physM ε (toMK k') = 1 := by
    rw [← physM_mul ha hc, show toMK k'⁻¹ * toMK k' = toMK (k'⁻¹ * k') from rfl, inv_mul_cancel]
    exact physM_one
  rw [physDet_eq, physDet_eq, show toMK (k'⁻¹ * k * k') = toMK k'⁻¹ * toMK k * toMK k' from rfl,
    physM_mul hab hc, physM_mul ha hb]
  have e : 1 - physM ε (toMK k'⁻¹) * physM ε (toMK k) * physM ε (toMK k') =
      physM ε (toMK k'⁻¹) * (1 - physM ε (toMK k)) * physM ε (toMK k') := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hac]
  rw [e, det_mul, det_mul, mul_comm (det (physM ε (toMK k'⁻¹))), mul_assoc, ← det_mul, hac, det_one, mul_one]

theorem trK_conj {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (k k' : KG ε) :
    trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k) := by
  have hmul : ∀ a b : KG ε, (T (toMK (a * b)) : W →ₗ[ℂ] W) = (T (toMK a) : W →ₗ[ℂ] W) * (T (toMK b)) := by
    intro a b
    rw [show toMK (a * b) = toMK a * toMK b from rfl, hT.1.2 _ a.2 _ b.2]
    rfl
  have h1 : (T (toMK (1 : KG ε)) : W →ₗ[ℂ] W) = 1 := by
    rw [show toMK (1 : KG ε) = 1 from rfl, hT.1.1]
    rfl
  unfold trK
  rw [hmul, hmul, LinearMap.trace_mul_comm, ← mul_assoc, ← hmul k' k'⁻¹, mul_inv_cancel, h1, one_mul]

end GlobalTheory.PsCo.PcEF.PhysicalMatrixDeterminant

namespace GlobalTheory.PsCo.PcEF

theorem adjointDetTrace_classFunction : ClassFn := by
  intro n ε k k'
  refine ⟨PhysicalMatrixDeterminant.physDet_conj k k', ?_⟩
  intro W _ _ _ T hT
  exact PhysicalMatrixDeterminant.trK_conj T hT k k'

end GlobalTheory.PsCo.PcEF

end
end
end

section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem fockCoordinates_span_finiteDimensional : CoordFD := by
  intro n ε M _ _ E Z hZ hK
  have hle : coordSpan Z ≤ ⨆ s : Finset (Fin (n * n)), Z.map (tcoef (M := M) ((fockBasis n).coord s)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨s, y, hy, rfl⟩
    exact (le_iSup (fun s : Finset (Fin (n * n)) => Z.map (tcoef (M := M) ((fockBasis n).coord s))) s)
      (Submodule.mem_map_of_mem hy)
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  intro a b hab v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, y, hy, rfl⟩ := hx
    have e := tco_diagE (ε := ε) E a b y s
    have e2 := tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a b) y
    have h1 : E a b (tcoef ((fockBasis n).coord s) y) =
        tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a b y) -
          tcoef ((fockBasis n).coord s ∘ₗ sgE ε (cpFock (n := n)) cmFock a b) y := by
      rw [e]; abel
    show E a b (tcoef ((fockBasis n).coord s) y) ∈ coordSpan Z
    rw [h1, e2]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, _, hK a b hab y hy, rfl⟩) ?_
    refine Submodule.sum_mem _ fun s' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s', y, hy, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.PsCo.PcEF
end
end

section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

variable {n : ℕ}

theorem cpt_const {ε : Fin n → Bool} (h : pOf ε = 0 ∨ qOf ε = 0) (a b : Fin n) : ε a = ε b := by
  rcases h with hp | hq
  · have h1 : ∀ c, ε c = false := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]
  · have h1 : ∀ c, ε c = true := fun c => by
      have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ c)
      simpa using this
    rw [h1 a, h1 b]

theorem cpt_Jm_comm {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * M = M * Formalism.REAL.Jm ε := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, hc i j]
  ring

theorem cpt_Kset_eq {ε : Fin n → Bool} (hc : ∀ a b, ε a = ε b) :
    Formalism.REAL.Kset ε = Formalism.MainNotions.S.UJset ε := by
  ext g
  simp only [Formalism.REAL.Kset, Formalism.MainNotions.S.UJset, Formalism.REAL.inUJ, Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  constructor
  · rintro ⟨hu, -⟩
    rw [Matrix.mul_assoc, cpt_Jm_comm hc g, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · intro h
    refine ⟨?_, (cpt_Jm_comm hc g).symm⟩
    have h2 : g.conjTranspose * g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε := by
      rw [Matrix.mul_assoc, ← cpt_Jm_comm hc g, ← Matrix.mul_assoc]
      exact h
    have h3 := congrArg (· * Formalism.REAL.Jm ε) h2
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h3
    exact h3

theorem compactDiscreteSeries_ownType : CptCase := by
  intro n ε lam h
  have hc := cpt_const h
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have : IsEmpty {x : Fin n × Fin n // IsPhys ε x} :=
      ⟨fun x => by
        have h1 := x.2.1
        have h2 := x.2.2
        rw [hc x.1.1 x.1.2] at h1
        rw [h1] at h2
        exact Bool.noConfusion h2⟩
    unfold physDet
    exact Matrix.det_isEmpty
  · unfold sDeg sModes
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2, -⟩
    rw [hc x.1 x.2] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro X _ _ D hD
    obtain ⟨hcs, hnt, hU, hirr, -, ⟨S, hS⟩, -⟩ := hD
    have := hcs
    have hKU := cpt_Kset_eq hc
    have : FiniteDimensional ℂ S := hS.1
    have hclosed : IsClosed (S : Set X) := Submodule.closed_of_finiteDimensional S
    have hstab : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v ∈ S, D g v ∈ S := fun g hg v hv =>
      hS.2.1 g (hKU ▸ hg) v hv
    have htop : S = ⊤ := by
      rcases hirr S hclosed hstab with h0 | h0
      · exfalso
        obtain ⟨v, hv, hv0, -⟩ := hS.2.2.2.1
        rw [h0] at hv
        exact hv0 ((Submodule.mem_bot ℂ).1 hv)
      · exact h0
    subst htop
    have hga : gaW ε lam = Formalism.QuantumDeterminants.lowK ε lam := by
      funext a
      have hN : Formalism.REAL.rhoN ε a = 0 := by
        unfold Formalism.REAL.rhoN
        have e1 : (Finset.univ.filter fun b => a < b ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        have e2 : (Finset.univ.filter fun b => b < a ∧ ε b ≠ ε a) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun b _ hb => hb.2 (hc b a)
        rw [e1, e2]
        simp
      have hH : rhoHol ε a = 0 := by
        unfold rhoHol
        rcases h with hp | hq
        · have ha : ε a = false := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hp) (Finset.mem_univ a)
            simpa using this
          simp [ha, hp]
        · have ha : ε a = true := by
            have := Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 hq) (Finset.mem_univ a)
            simpa using this
          simp [ha, hq]
      simp only [gaW, Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, hN, hH, add_zero]
      rfl
    refine ⟨LinearEquiv.finiteDimensional Submodule.topEquiv, hnt, hKU ▸ hU, ?_⟩
    rw [hga]
    exact hS

end GlobalTheory.PsCo.PcEF
end
end

section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF

theorem eq_discreteSeries_of_lowestKType_casimir : DatumEquiv := by
  intro n ε lam hgap H _ _ _ σ hσ hirr V hV hV0 hc X _ _ D hD
  haveI : CompleteSpace X := hD.1
  have hσD : IsURepOn (UJset ε) D := hD.2.2.1
  have hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v :=
    kStable_of_isKStableSub hσ (isDerivedOn_smE hσ) V hV.1 hV.2.1
  obtain ⟨V', hV', hV0', hVK', hc'⟩ := arb_datum hD (casOnSmooth_of_isDS hD hgap)
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hirr hV0
  have htop' := data_closGen_eq_top hgap hσD (isDerivedOn_smE hσD) hV' hc' hVK' hD.2.2.2.1 hV0'
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ (isDerivedOn_smE hσ) hV hc hVK hV0
    hσD (isDerivedOn_smE hσD) hV' hc' hVK' hV0'
  refine ⟨((LinearIsometryEquiv.ofTop _ _ htop).symm.trans U).trans (LinearIsometryEquiv.ofTop _ _ htop'),
    fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.ofTop_apply]
  apply hU g hg
  simp only [LinearIsometryEquiv.ofTop_symm_apply_coe]

end GlobalTheory.PsCo.PcEF
end
end

section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF.HarishChandraWeightIntegral

variable {n : ℕ}

theorem card_split (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b = ε a).card + 1 =
      (univ.filter fun b => ε b = ε a).card := by
  have h : (univ.filter fun b => ε b = ε a) =
      ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a)) ∪ {a} := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]
    constructor
    · intro h
      rcases lt_trichotomy a b with h1 | h1 | h1
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · exact Or.inr h1.symm
      · exact Or.inl (Or.inr ⟨h1, h⟩)
    · rintro ((⟨_, h⟩ | ⟨_, h⟩) | rfl)
      · exact h
      · exact h
      · rfl
  have d1 : Disjoint (univ.filter fun b => a < b ∧ ε b = ε a) (univ.filter fun b => b < a ∧ ε b = ε a) := by
    rw [disjoint_filter]
    intro x _ h1 h2
    exact lt_asymm h1.1 h2.1
  have d2 : Disjoint ((univ.filter fun b => a < b ∧ ε b = ε a) ∪ (univ.filter fun b => b < a ∧ ε b = ε a))
      {a} := by
    rw [disjoint_singleton_right]
    simp
  rw [h, card_union_of_disjoint d2, card_union_of_disjoint d1, card_singleton]

theorem p_add_q (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => ε a = true)
  simpa using this

theorem gaW_eq (ε : Fin n → Bool) (lam : Fin n → ℝ) (m : Fin n → ℤ)
    (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) (a : Fin n) :
    gaW ε lam a = ((m a - (if ε a then 0 else (pOf ε : ℤ)) - ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε a : ℤ) : ℝ) := by
  have hcR : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) +
      ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) + 1 =
      ((univ.filter fun b => ε b = ε a).card : ℝ) := by exact_mod_cast card_split ε a
  have hpqR : (pOf ε : ℝ) + qOf ε = n := by exact_mod_cast p_add_q ε
  have hma := hm a
  simp only [gaW, Pi.add_apply, Pi.sub_apply, rhoC, rhoHol, ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK]
  by_cases h : ε a = true
  · have hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = pOf ε := by simp [pOf, h]
    rw [if_pos h, if_pos h]
    push_cast
    linarith
  · have hs : ((univ.filter fun b => ε b = ε a).card : ℝ) = qOf ε := by
      simp only [Bool.not_eq_true] at h
      simp [qOf, h]
    rw [if_neg h, if_neg h]
    push_cast
    linarith

end GlobalTheory.PsCo.PcEF.HarishChandraWeightIntegral

namespace GlobalTheory.PsCo.PcEF

theorem harishChandraWeight_integral_dominant : GaInt := by
  intro n ε lam hlam
  obtain ⟨hanti, hz⟩ := hlam
  choose z hz using hz
  let m : Fin n → ℤ := fun a => z a + ((n : ℤ) - 1)
  have hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a := by
    intro a
    have := hz a
    simp only [m]
    push_cast
    linarith
  let Λ : Fin n → ℤ := fun a =>
    m a - (if ε a then 0 else (pOf ε : ℤ)) - ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε a
  have hg : gaW ε lam = fun a => (Λ a : ℝ) := funext fun a => HarishChandraWeightIntegral.gaW_eq ε lam m hm a
  refine ⟨Λ, m, hg, ?_, hm, ?_⟩
  · intro a b hab he
    have hBA : BlockAnti ε lam := by
      intro a b hab _
      have h1 := hanti hab
      have h2 : (m b : ℝ) < m a := by linarith [hm a, hm b]
      have h3 : m b < m a := by exact_mod_cast h2
      have h4 : ((m b : ℤ) : ℝ) + 1 ≤ m a := by exact_mod_cast h3
      linarith [hm a, hm b]
    have h := lf_dom_block hBA a b hab he
    have e : lowK ε lam + (rhoHol ε - rhoN ε) = gaW ε lam := by
      funext x
      simp only [lowK, gaW, Pi.add_apply, Pi.sub_apply]
      ring
    rw [e, hg] at h
    have h' : (Λ b : ℝ) ≤ Λ a := h
    exact_mod_cast h'
  · intro a
    simp only [Λ, Pi.add_apply]
    ring

end GlobalTheory.PsCo.PcEF

end
end
end

section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

namespace GapNumber

theorem chain {r : ℕ} {lam : Fin r → ℤ} {H : ℤ} (hH : 0 ≤ H)
    (hg : ∀ i j : Fin r, (j : ℕ) = i + 1 → H ≤ lam i - lam j) :
    ∀ i j : Fin r, i < j → H ≤ lam i - lam j := by
  suffices h : ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k + 1 → H ≤ lam i - lam j by
    intro i j hij
    have : (i : ℕ) < j := hij
    exact h ((j : ℕ) - i - 1) i j (by omega)
  intro k
  induction k with
  | zero => intro i j h; exact hg i j (by omega)
  | succ k ih =>
    intro i j h
    have hm : (i : ℕ) + k + 1 < r := by have := j.isLt; omega
    have h1 := ih i ⟨(i : ℕ) + k + 1, hm⟩ rfl
    have h2 := hg ⟨(i : ℕ) + k + 1, hm⟩ j (by show (j : ℕ) = (i : ℕ) + k + 1 + 1; omega)
    linarith

end GapNumber

theorem gapConditions_of_largeGaps : GapNum := by
  intro r hr ε lam hg
  obtain ⟨k, hk⟩ := hr
  have hr1 : 1 ≤ r := by omega
  have hH : (0 : ℤ) ≤ 100 * (r : ℤ) ^ 4 := by positivity
  have hc := GapNumber.chain hH hg
  have hcR : ∀ i j : Fin r, i < j → 100 * (r : ℝ) ^ 4 ≤ (lam i : ℝ) - lam j := fun i j h => by
    exact_mod_cast hc i j h
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hpos : (0 : ℝ) < 100 * (r : ℝ) ^ 4 := by positivity
  have hanti : StrictAnti (fun a => (lam a : ℝ)) := fun i j h => by
    have := hcR i j h
    show (lam j : ℝ) < lam i
    linarith
  have hgap : GapAtLeast ε (fun a => (lam a : ℝ)) (100 * (r : ℝ) ^ 4) := by
    intro a b hab
    have hne : a ≠ b := fun h => hab (h ▸ rfl)
    show 100 * (r : ℝ) ^ 4 ≤ |(lam a : ℝ) - lam b|
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hcR a b h).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hcR b a h).trans (le_abs_self _)
  have hp : pOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq : qOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq0 : S7.q0 ε ≤ r := (min_le_left _ _).trans hp
  have hpR : (pOf ε : ℝ) ≤ r := by exact_mod_cast hp
  have hqR : (qOf ε : ℝ) ≤ r := by exact_mod_cast hq
  have hq0R : (S7.q0 ε : ℝ) ≤ r := by exact_mod_cast hq0
  have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hrR
  have h4 : (r : ℝ) ≤ (r : ℝ) ^ 4 := le_self_pow₀ hrR (by norm_num)
  have h2 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have h3 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have hbig : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < 100 * (r : ℝ) ^ 4 := by
    have : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ r * r * r := by gcongr
    nlinarith
  refine ⟨⟨hanti, fun a => ⟨lam a - k, ?_⟩⟩, ⟨hanti, _, hgap, hbig⟩, ⟨hanti, _, hgap, by linarith⟩, _, hgap, ?_⟩
  · have hkR : (r : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    show (lam a : ℝ) - ((r : ℝ) - 1) / 2 = ((lam a - k : ℤ) : ℝ)
    rw [hkR]; push_cast; ring
  · unfold thrStar
    refine max_lt hbig ?_
    have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * r := by
      rw [show (2 : ℝ) * r = Real.sqrt ((2 * r) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hm : (r : ℝ) * (S7.q0 ε : ℝ) ≤ r * r := mul_le_mul_of_nonneg_left hq0R (by positivity)
    nlinarith

end GlobalTheory.PsCo.PcEF

end
end
end

section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.PsCo.Pc1 (Mat)

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem intertwiner_preserves_highestWeight : HWVec := by
  intro n ε H _ _ σ D E hσ hD Z _ hZK γ W _ _ _ T hT Φ hΦ hint
  obtain ⟨-, -, hTy⟩ := hT
  obtain ⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hTy

  have hker : LinearMap.ker Φ = ⊥ := by
    rcases hirr (LinearMap.ker Φ) le_top (fun g hg w hw => by
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hint g hg w, hw, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hΦ
  have hinj : Function.Injective Φ := LinearMap.ker_eq_bot.1 hker
  let ι : W →ₗ[ℂ] TensorProduct ℂ D (Fock n) := tsubVal Z ∘ₗ Φ
  have hιinj : Function.Injective ι := tsubVal_injective.comp hinj
  have hιK : ∀ (k : Mat n) (hk : k ∈ Kset ε) (w : W), wK hD hk (ι w) = ι (T k w) := by
    intro k hk w
    show wK hD hk (tsubVal Z (Φ w)) = tsubVal Z (Φ (T k w))
    rw [hint k (by rw [mir_Kset_eq]; exact hk) w, tOp_apply hD hZK hk]
  let S' : Submodule ℂ (TensorProduct ℂ D (Fock n)) := LinearMap.range ι
  have hS'fin : FiniteDimensional ℂ S' := LinearMap.finiteDimensional_range ι
  have hS'K : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ S', wK hD hk y ∈ S' := by
    rintro k hk _ ⟨w, rfl⟩
    exact ⟨T k w, (hιK k hk w).symm⟩

  have hwt : ∀ (μ : Fin n → ℝ) (w : W), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w →
      ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w := by
    intro μ w hw θ
    rw [hιK _ _ w, hw θ (by rw [mir_Kset_eq]; exact diag_mem_Kset' ε θ), map_smul]
  have hwt' : ∀ (μ : Fin n → ℝ) (w : W),
      (∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (ι w) = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • ι w) →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T μ w := by
    intro μ w hw θ _
    apply hιinj
    rw [map_smul, ← hιK _ (diag_mem_Kset' ε θ) w, hw θ]
  set z := ι v with hz
  have hz0 : z ≠ 0 := fun h => hv0 (hιinj (h.trans (map_zero ι).symm))
  have hzd : ∀ a, diagE ε (eT E) cpT cmT a a z = ((γ a : ℝ) : ℂ) • z :=
    diagE_wt_of_wK hσ hD (hwt γ v hvw)
  refine ⟨z, tsubVal_mem (Φ v), hz0, hzd, fun a b hab hε => ?_⟩
  set y := diagE ε (eT E) cpT cmT a b z with hy
  have hyS : y ∈ S' := diagE_mem_of_wK hσ hD S' hS'fin hS'K hε ⟨v, rfl⟩
  obtain ⟨w', hw'⟩ := hyS
  have hyd : ∀ c, diagE ε (eT E) cpT cmT c c y = (((γ + root a b) c : ℝ) : ℂ) • y := by
    intro c
    have hc := congrArg (fun F => F z)
      (diagAction_commutator (eT_isGlRep hD.glRep) cpT_cmT_isCAR (eT_commutesCAR E) ε c c a b rfl hε)
    simp only [Module.End.mul_apply, LinearMap.sub_apply] at hc
    rw [hzd c, map_smul] at hc
    have e1 : diagE ε (eT E) cpT cmT c c y =
        ((γ c : ℝ) : ℂ) • y + ((if c = a then diagE ε (eT E) cpT cmT c b else 0) -
          (if b = c then diagE ε (eT E) cpT cmT a c else 0)) z := by
      rw [hy, LinearMap.sub_apply, ← hc]; abel
    rw [e1]
    by_cases hca : c = a
    · subst hca
      have hcb : ¬ b = c := fun h => (ne_of_lt hab) h.symm
      simp only [if_neg hcb, sub_zero, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same, ↓reduceIte]
      rw [Pi.single_eq_of_ne (ne_of_lt hab)]
      simp only [sub_zero, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
      rfl
    · by_cases hcb : b = c
      · subst hcb
        simp only [if_neg hca, zero_sub, Pi.add_apply, root, Pi.sub_apply, Pi.single_eq_same,
          LinearMap.neg_apply, ↓reduceIte]
        rw [Pi.single_eq_of_ne hca]
        simp only [zero_sub, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_one, add_smul, neg_smul,
          one_smul]
        rfl
      · simp only [if_neg hca, if_neg hcb, sub_zero, LinearMap.zero_apply, add_zero, Pi.add_apply, root,
          Pi.sub_apply]
        rw [Pi.single_eq_of_ne hca, Pi.single_eq_of_ne (Ne.symm hcb)]
        simp
  have hw'w : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) T (γ + root a b) w' := by
    apply hwt'
    intro θ
    rw [hw']
    exact wK_diag_wt hσ hD hyd θ
  by_contra hne
  have hw'0 : w' ≠ 0 := by
    intro h; apply hne; rw [← hw', h, map_zero]
  exact not_cdom_add_root ε γ hab (hdom _ w' (Submodule.mem_top) hw'0 hw'w)

end GlobalTheory.PsCo.PcEF
end
end

section
section

noncomputable section

namespace GlobalTheory.PsCo.PcEF.MatrixRepresentation

variable {n : ℕ} (ε : Fin n → Bool) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

abbrev mat (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem mat_injective : Function.Injective (mat ε) := fun _ _ h => Subtype.ext (Units.ext h)

def rep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (x : Matrix (Fin n) (Fin n) ℂ) : X →L[ℂ] X := by
  classical exact if h : ∃ g, mat ε g = x then π h.choose else 1

theorem rep_mat (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (g : Formalism.REAL.UJ ε) : rep ε π (mat ε g) = π g := by
  have h : ∃ g', mat ε g' = mat ε g := ⟨g, rfl⟩
  rw [rep, dif_pos h, mat_injective ε h.choose_spec]

theorem range_mat : Set.range (mat ε) = Formalism.MainNotions.S.UJset ε := (Formalism.REAL.isClosedEmbeddingMatrix n ε).2

theorem mat_mem (g : Formalism.REAL.UJ ε) : mat ε g ∈ Formalism.MainNotions.S.UJset ε := range_mat ε ▸ ⟨g, rfl⟩

theorem exists_mat {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ Formalism.MainNotions.S.UJset ε) : ∃ g, mat ε g = x := by
  rw [← range_mat ε] at hx; exact hx

theorem isEmbedding_mat : Topology.IsEmbedding (mat ε) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding

end GlobalTheory.PsCo.PcEF.MatrixRepresentation

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEF.MatrixRepresentation

theorem unitaryRep_upq_matrixFunction : MatRep := by
  intro n ε U _ _ π hπ hi
  refine ⟨rep ε π, ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩, fun S hS hinv => ?_, fun g => rep_mat ε π g⟩
  · have h1 : mat ε 1 = 1 := rfl
    rw [← h1, rep_mat, map_one]
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    obtain ⟨h, rfl⟩ := exists_mat ε hb
    have hm : mat ε g * mat ε h = mat ε (g * h) := rfl
    rw [hm, rep_mat, rep_mat, rep_mat, map_mul]
    rfl
  · obtain ⟨g, rfl⟩ := exists_mat ε ha
    rw [rep_mat]
    exact hπ.norm_apply g v
  · have hr : Formalism.MainNotions.S.UJset ε = Set.range (mat ε) := (range_mat ε).symm
    show ContinuousOn (fun g => rep ε π g v) (Formalism.MainNotions.S.UJset ε)
    rw [hr, continuousOn_iff_continuous_domRestrict]
    let E := (isEmbedding_mat ε).toHomeomorph
    have hE : ∀ y, (fun g => π g v) (E.symm y) = rep ε π (y : Matrix (Fin n) (Fin n) ℂ) v := by
      intro y
      obtain ⟨g, rfl⟩ := E.surjective y
      show π (E.symm (E g)) v = rep ε π (mat ε g) v
      rw [E.symm_apply_apply, rep_mat]
    exact ((hπ.continuous_apply v).comp E.symm.continuous).congr hE
  · exact hi.2 S ⟨hS, fun g v hv => by simpa [rep_mat] using hinv _ (mat_mem ε g) v hv⟩

end GlobalTheory.PsCo.PcEF

end
end
end

section
noncomputable section

open MeasureTheory
open Formalism.REAL (KG toMK muK)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF

theorem norm_irreducibleCharacter_unitaryMaxCompact_eq_one : SchurOne := by
  intro n ε γ W _ _ _ T hT
  obtain ⟨hnt, hU, hK⟩ := hT
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  let π : KG ε →* (W →L[ℂ] W) :=
    { toFun := fun k => T (toMK k)
      map_one' := hU.1.1
      map_mul' := fun a b => hU.1.2 _ a.2 _ b.2 }
  have hπU : GlobalTheory.OpTrace.IsUnitaryRep π :=
    ⟨fun k v => hU.2.1 _ k.2 v, fun v => (hU.2.2 v).comp_continuous hemb.continuous fun k => k.2⟩
  have hπI : GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π := by
    refine ⟨hnt, fun S hS => ?_⟩
    refine hK.2.2.1 S le_top fun g hg v hv => ?_
    have : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [Formalism.REAL.range_toMK]; exact hg
    obtain ⟨k, rfl⟩ := this
    exact hS.2 k v hv
  have h := GlobalTheory.Orb.integral_conj_trace_mul_trace (μ := muK ε) hπU hπI
  have h1 : (muK ε).real Set.univ = 1 := by
    rw [Measure.real, Formalism.REAL.muK, ← TopologicalSpace.PositiveCompacts.coe_top, Measure.haarMeasure_self]
    rfl
  rw [h1] at h
  exact_mod_cast h

end GlobalTheory.PsCo.PcEF
end
end

section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)

namespace GlobalTheory.PsCo.PcEF

theorem StrIdx_proof2 : StrIdx := by
  intro n ε P
  choose Qm hQm using fun s s' : Finset (Fin (n * n)) => ffMat_poly (ε := ε) s s'
  set Q : Poly n := ∑ s ∈ Finset.univ.filter (IsPhysSet ε), ((-1 : ℂ) ^ s.card) • Qm s s with hQdef
  have hQ : ∀ m : Mat n, ev m Q = physDet ε m := by
    intro m
    show MvPolynomial.eval (entVar m) Q = _
    rw [← strPhys_eq_physDet, strPhys, hQdef, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.smul_eval, hQm]
    rfl
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℕ, ∀ s s' : Finset (Fin (n * n)), (P * Qm s s').totalDegree ≤ d2 :=
    ⟨∑ s, ∑ s', (P * Qm s s').totalDegree, fun s s' =>
      le_trans (Finset.single_le_sum (f := fun s' => (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s'))
      (Finset.single_le_sum (f := fun s => ∑ s', (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s))⟩
  refine ⟨max (P * Q).totalDegree d2, ?_⟩
  intro H _ _ _ σ D E hσ hD L _ hLK hLd Y _ hY0Y hYP hG hK B hB
  have hdeg1 : (P * Q).totalDegree ≤ max (P * Q).totalDegree d2 := le_max_left _ _
  have hdeg2 : ∀ s s', (P * Qm s s').totalDegree ≤ max (P * Q).totalDegree d2 := fun s s' =>
    (hd2 s s').trans (le_max_right _ _)
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
  have hφc : Continuous (fun k : KG ε => toMK k) := hemb.continuous
  have hφK : ∀ g : KG ε, toMK g ∈ Kset ε := fun g => g.2
  have hent : ∀ R : Poly n, Continuous fun k : KG ε => ev (toMK k) R := by
    intro R
    refine (MvPolynomial.continuous_eval R).comp (continuous_pi fun p => ?_)
    rcases p with p | p
    · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hφc))
  have hBL : ∀ w, B w ∈ L.map D.subtype := by
    intro w
    rw [hB]
    have := hLd (P * Q) hdeg1 w
    simpa only [map_mul, hQ] using this
  refine ⟨hBL, ?_⟩
  have hAL : ∀ k : KG ε, ∀ x ∈ L.map D.subtype, σ (toMK k) x ∈ L.map D.subtype := by
    rintro k _ ⟨y, hy, rfl⟩
    exact ⟨sigD hD (hφK k) y, hLK _ (hφK k) y hy, rfl⟩
  have hAc : ∀ v, Continuous fun k : KG ε => σ (toMK k) v := fun v =>
    (hσ.2.2 v).comp_continuous hφc fun g => kset_mem_UJset (hφK g)
  have hcont : Continuous fun k : KG ε => ev (toMK k) P * physDet ε (toMK k) := by
    have := hent (P * Q)
    simpa only [map_mul, hQ] using this
  rw [trace_integral_restrict (μ := muK ε) (L.map D.subtype) hcont (fun k => σ (toMK k)) hAc hAL B hB
    (fun x _ => hBL x)]
  have hY0G : ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε, gradT y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε :=
    fun y hy => ⟨tensFock_lTensor_stable _ hy.1, (physSub_stable ε E).2.2.2.2 y hy.2⟩
  have hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε,
      wK hD hk y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε := fun k hk y hy =>
    ⟨wK_tensFock hD hk (hLK k hk) hy.1, wK_physSub hD hk hy.2⟩
  have hpt : ∀ k : KG ε, ev (toMK k) P * physDet ε (toMK k) *
      LinearMap.trace ℂ (L.map D.subtype) (((σ (toMK k) : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict (hAL k)) =
      ev (toMK k) P * LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) := by
    intro k
    rw [trace_map_subtype (sigD hD (hφK k)) (fun x hx => hLK _ (hφK k) x hx) _ _ (fun x => rfl)]
    have := str_tensFock_physSub hD (hφK k) (fun x hx => hLK _ (hφK k) x hx)
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))
    rw [show LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) = _ from this]
    ring
  simp_rw [hpt]
  have hcP := hent P
  have hrange := fun y => btot_range (μ := muK ε) hσ hD hK (L := L) hφc hφK hcP
    (fun s s' u => by
      have h1 := hLd (P * Qm s s') (hdeg2 s s') u
      have h2 : ∫ k : KG ε, (ev (toMK k) P * ffMat ε (toMK k) s s') • σ (toMK k) u ∂(muK ε) =
          ∫ k : KG ε, ev (toMK k) (P * Qm s s') • σ (toMK k) u ∂(muK ε) := by
        congr 1
        funext k
        rw [map_mul, hQm]
        rfl
      rw [h2]
      exact h1) hYP y
  exact (int_str_eq (μ := muK ε) hσ hD hY0Y hK hY0K hG hY0G hφc hφK hcP hrange).symm

end GlobalTheory.PsCo.PcEF

end
end
end

section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.PsCo.Pc1 (Mat)

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

set_option maxHeartbeats 1000000 in
theorem supertrace_carriedBy_diracKernel : StrKer := by
  intro n ε H _ _ σ D E hσ hD Y _ hY hG hK
  classical
  let Z : Submodule ℂ (TensorProduct ℂ D (Fock n)) := Y ⊓ LinearMap.ker (dD ε E)
  have hZY : Z ≤ Y := inf_le_left
  haveI hZf : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le hZY
  have hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z := by
    intro k hk y hy
    refine ⟨hK k hk y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (wK hD hk y) = 0
    rw [← wK_D hσ hD hk, h0, map_zero]
  have hZG : ∀ y ∈ Z, gradT y ∈ Z := by
    intro y hy
    refine ⟨hG y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (gradT y) = 0
    have := gradT_D (ε := ε) E y
    rw [h0, map_zero] at this
    exact neg_eq_zero.1 this.symm
  let Γ : TSub Z →ₗ[ℂ] TSub Z := ((gradT.restrict hZG : Z →ₗ[ℂ] Z) : TSub Z →ₗ[ℂ] TSub Z)
  refine ⟨Z, hZf, hZK, Γ, hZY, fun y hy => hy.2, fun k hk => ?_⟩
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  let Dl : TSub Y →ₗ[ℂ] TSub Y := (((dD ε E).restrict hY : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let Γy : TSub Y →ₗ[ℂ] TSub Y := ((gradT.restrict hG : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let B : TSub Y →ₗ[ℂ] TSub Y := (((wK hD hk).restrict (hK k hk) : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  obtain ⟨hker, htr⟩ := str_eq_str_ker Dl Γy B
    (fun x y => by rw [tsub_inner, tsub_inner]; exact tform_D hU _ _)
    (fun x => Subtype.ext (gradT_D E _)) (fun x => Subtype.ext (wK_D hσ hD hk _))
  have h1 : LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
      LinearMap.trace ℂ (TSub Y) (Γy ∘ₗ B) := rfl
  rw [h1, htr]
  have hmemZ : ∀ x : LinearMap.ker Dl, tsubVal Y (x : TSub Y) ∈ Z := by
    intro x
    have hx : Dl (x : TSub Y) = 0 := x.2
    exact ⟨tsubVal_mem (x : TSub Y), congrArg (tsubVal Y) hx⟩
  let f : LinearMap.ker Dl →ₗ[ℂ] TSub Z :=
    { toFun := fun x => ((⟨tsubVal Y (x : TSub Y), hmemZ x⟩ : Z) : TSub Z)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have : tsubVal Y (x : TSub Y) = tsubVal Y (y : TSub Y) := congrArg (tsubVal Z) hxy
      exact Subtype.ext (tsubVal_injective this)
    · intro z
      have hzY : tsubVal Z z ∈ Y := hZY (tsubVal_mem z)
      let x : TSub Y := ((⟨tsubVal Z z, hzY⟩ : Y) : TSub Y)
      have hx : x ∈ LinearMap.ker Dl := by
        rw [LinearMap.mem_ker]
        apply tsubVal_injective
        rw [map_zero]
        exact (tsubVal_mem z).2
      exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective f hf
  rw [← LinearMap.trace_conj' _ e]
  congr 1
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply_apply]
  apply tsubVal_injective
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [LinearEquiv.symm_apply_apply]
  show tsubVal Z (f ((Γy ∘ₗ B).restrict hker x)) = tsubVal Z (Γ (tOp hD hZK k (f x)))
  have hΓ : ∀ w : TSub Z, tsubVal Z (Γ w) = gradT (tsubVal Z w) := fun w => rfl
  rw [hΓ, tOp_apply hD hZK hk]
  rfl

end GlobalTheory.PsCo.PcEF
end
end

section
noncomputable section

open MvPolynomial
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

def conjPoly (n : ℕ) : Poly n →+* Poly n :=
  (rename (Sum.swap : (Fin n × Fin n) ⊕ (Fin n × Fin n) → _)).toRingHom.comp (map (starRingEnd ℂ))

theorem ev_conjPoly {n : ℕ} (g : Mat n) (P : Poly n) : ev g (conjPoly n P) = conj (ev g P) := by
  have h : (ev g).comp (conjPoly n) = (starRingEnd ℂ).comp (ev g) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [conjPoly, ev]
    · intro i
      rcases i with x | x
      · simp [conjPoly, ev]
      · simp [conjPoly, ev]
  exact congrArg (fun φ : Poly n →+* ℂ => φ P) h

theorem polyOnK_conj {n : ℕ} {ε : Fin n → Bool} {f : Mat n → ℂ} (hf : PolyOnK ε f) :
    PolyOnK ε fun k => conj (f k) := by
  obtain ⟨P, hP⟩ := hf
  exact ⟨conjPoly n P, fun k hk => by dsimp only; rw [ev_conjPoly, hP k hk]⟩

theorem polyOnK_sum {n : ℕ} {ε : Fin n → Bool} {ι : Type} (s : Finset ι) (f : ι → Mat n → ℂ)
    (hf : ∀ i ∈ s, PolyOnK ε (f i)) : PolyOnK ε fun k => ∑ i ∈ s, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun k _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨P, hP⟩ := hf a (Finset.mem_insert_self a s)
    obtain ⟨Q, hQ⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact ⟨P + Q, fun k hk => by dsimp only at hQ ⊢; rw [Finset.sum_insert ha, map_add, hP k hk, hQ k hk]⟩

theorem trPoly : TrPoly := by
  intro n ε W _ _ _ T hT
  apply polyOnK_conj
  have e : trK T = fun k => ∑ i, ⟪(stdOrthonormalBasis ℂ W) i, T k ((stdOrthonormalBasis ℂ W) i)⟫_ℂ := by
    funext k
    simp only [trK, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ W)]
    rfl
  rw [e]
  exact polyOnK_sum _ _ fun i _ => hT _ _

end GlobalTheory.PsCo.PcEF
end
end

section
section
open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc1

theorem maximalCompact_pseudoCoefficientData' : StKData :=
  GlobalTheory.PsCo.PcEF.stKData_of
    GlobalTheory.PsCo.PcEF.maxCompactPolynomial_blockTimesConjDetPower GlobalTheory.PsCo.PcEF.modeMatrixDet_eq_adjointDet GlobalTheory.PsCo.PcEF.coefPoly
    GlobalTheory.PsCo.PcEF.trPoly GlobalTheory.PsCo.PcEF.adjointDetTrace_classFunction GlobalTheory.PsCo.PcEF.harishChandraWeight_integral_dominant
    GlobalTheory.PsCo.PcEF.polyCoefIrrep_hasDerivedAction GlobalTheory.PsCo.PcEF.adjointDet_onCompactTorus GlobalTheory.PsCo.PcEF.torusId_full
    GlobalTheory.PsCo.PcEF.tracePairing_nonzero_intertwiner GlobalTheory.PsCo.PcEF.norm_irreducibleCharacter_unitaryMaxCompact_eq_one GlobalTheory.PsCo.PcEF.rangeFD_closed
    GlobalTheory.PsCo.PcEF.casimirScalar_stableSumSpace GlobalTheory.PsCo.PcEF.supertrace_carriedBy_diracKernel GlobalTheory.PsCo.PcEF.StrIdx_proof2
    GlobalTheory.PsCo.PcEF.intertwiner_preserves_highestWeight GlobalTheory.PsCo.PcEF.fockCoordinates_span_finiteDimensional GlobalTheory.PsCo.PcEF.casimirValue_highestWeightCoordinates
    GlobalTheory.PsCo.PcEF.highestWeightKernel_lowestType GlobalTheory.PsCo.PcEF.eq_discreteSeries_of_lowestKType_casimir GlobalTheory.PsCo.PcEF.compactDiscreteSeries_ownType
    GlobalTheory.PsCo.PcEF.gapConditions_of_largeGaps GlobalTheory.PsCo.PcEF.unitaryRep_upq_matrixFunction GlobalTheory.HcPort.casimirActsByScalar_indefUnitary

end GlobalTheory.PsCo.Pc1
end

open GlobalTheory.PsCo.Pc1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_pseudoCoefficientData : StKData := by
  atlas_forward_decl GlobalTheory.PsCo.Pc1.maximalCompact_pseudoCoefficientData'
end
