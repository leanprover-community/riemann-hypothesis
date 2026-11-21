import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMatMapSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftECompFinOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommOff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocCoLocDarboux
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalUnitaryActionPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicLeviInverseQuotientDetNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweLocal.Fld

open Polynomial
open scoped IntermediateField

theorem isField_tensor_of_isEmpty_algHom {F K E : Type} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] (h2 : Module.finrank F E = 2) (hE : IsEmpty (E →ₐ[F] K)) :
    IsField (K ⊗[F] E) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hne : (⊥ : IntermediateField F E) ≠ ⊤ := by
    intro h
    rw [IntermediateField.bot_eq_top_iff_finrank_eq_one] at h
    omega
  obtain ⟨a, ha⟩ : ∃ a : E, a ∉ (⊥ : IntermediateField F E) := by
    by_contra h
    push_neg at h
    exact hne (eq_top_iff.2 fun z _ => h z)
  have hint : IsIntegral F a := Algebra.IsIntegral.isIntegral a
  have hnot : a ∉ (algebraMap F E).range := fun h => ha (IntermediateField.mem_bot.2 h)
  have hge : 2 ≤ (minpoly F a).natDegree := (minpoly.two_le_natDegree_iff hint).2 hnot
  have hle : (minpoly F a).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le a
  obtain ⟨b, c, hbc⟩ := isMonicOfDegree_two_iff.1
    (⟨by omega, minpoly.monic hint⟩ : IsMonicOfDegree (minpoly F a) 2)
  have hq : a ^ 2 + algebraMap F E b * a + algebraMap F E c = 0 := by
    have := minpoly.aeval F a
    rw [hbc] at this
    simpa [Algebra.smul_def] using this
  refine GlobalTheory.InertField.isField_tensor_of_no_root h2 a (fun x hx => hnot ⟨x, hx⟩) b c hq
    fun x hx => hE.false ?_
  have hroot : aeval x (minpoly F a) = 0 := by
    rw [hbc]
    simpa [Algebra.smul_def] using hx
  have htop : F⟮a⟯ = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [IntermediateField.adjoin.finrank hint, IntermediateField.finrank_top', h2]
    omega
  exact ((IntermediateField.adjoin.powerBasis hint).lift x
      (by rwa [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen])).comp
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).symm.toAlgHom

theorem isField_of_isEmpty : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → IsField (Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ hCM v hv
  exact isField_tensor_of_isEmpty_algHom hCM.2.2.1 hv

end GlobalTheory.HoweLocal.Fld
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem cm_exists_moved (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : (∃ α : E, σ α ≠ α) ∧ ∀ x, σ (σ x) = x := by
  obtain ⟨_, hc, _, hconj⟩ := h
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply w.embedding.injective
    rw [hconj, hconj, star_star]
  refine ⟨?_, hinv⟩
  by_contra hne
  push_neg at hne
  have hw : w.IsComplex := hc.isComplex w
  apply NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  ext x
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hx := hconj w.embedding x
  rw [hne] at hx
  exact hx.symm

theorem quad_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ v : Pl F, ∃ δ : Fv F v ⊗[F] E, IsQuad (GlobalTheory.HoweLocal.cv σ v) δ := by
  intro F E _ _ _ _ _ σ h v
  have hdim : Module.finrank F E = 2 := h.2.2.1
  obtain ⟨⟨α, hα⟩, hinv⟩ := cm_exists_moved F E σ h
  set δ₀ : E := α - σ α with hδ₀
  have hanti : σ δ₀ = -δ₀ := by
    rw [hδ₀, map_sub, hinv]; ring
  have hne : δ₀ ≠ 0 := by
    intro h0; apply hα; rw [hδ₀, sub_eq_zero] at h0; exact h0.symm
  have hli : LinearIndependent F ![(1 : E), δ₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : σ (s • (1 : E) + t • δ₀) = s • (1 : E) - t • δ₀ := by
      simp only [Algebra.smul_def, map_add, map_mul, AlgHom.commutes, map_one, hanti]
      ring
    rw [hst, map_zero] at h2
    have ht : (2 * t) • δ₀ = 0 := by
      have : (s • (1 : E) + t • δ₀) - (s • (1 : E) - t • δ₀) = (2 * t) • δ₀ := by
        rw [mul_smul, two_smul]; abel
      rw [← this, hst, ← h2, sub_zero]
    have ht0 : t = 0 := by
      rcases smul_eq_zero.mp ht with h3 | h3
      · exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
      · exact absurd h3 hne
    refine ⟨?_, ht0⟩
    rw [ht0, zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h3 | h3
    · exact h3
    · exact absurd h3 one_ne_zero
  let b0 : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim])
  have hb0 : ∀ i, b0 i = ![(1 : E), δ₀] i := fun i => by
    simp [b0, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨(1 : Fv F v) ⊗ₜ[F] δ₀, ⟨?_, ?_, ?_⟩⟩
  · have hu : IsUnit δ₀ := hne.isUnit
    have := hu.map (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E)
    simpa [Algebra.TensorProduct.includeRight_apply] using this
  · simp [GlobalTheory.HoweLocal.cv, Algebra.TensorProduct.map_tmul, hanti, TensorProduct.tmul_neg]
  · refine ⟨Algebra.TensorProduct.basis (Fv F v) b0, ?_, ?_⟩
    · rw [Algebra.TensorProduct.basis_apply, hb0]; rfl
    · rw [Algebra.TensorProduct.basis_apply, hb0]; rfl

end GlobalTheory.HoweLocal
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem continuous_liftV {F : Type} [Field F] [NumberField F] (v : Pl F) :
    Continuous (GlobalTheory.LatVac.liftV v) := by
  change Continuous (fun a : Fv F v => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a))
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_liftE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) : Continuous (liftE (E := E) v) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let bA := Algebra.TensorProduct.basis (Fv F v) b
  have hsum : ∀ z : Fv F v ⊗[F] E,
      liftE v z = ∑ i, GlobalTheory.LatVac.liftV v (bA.repr z i) • ((1 : AF F) ⊗ₜ[F] b i) := by
    intro z
    conv_lhs => rw [← bA.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [liftE, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  have hfun : (liftE (E := E) v : Fv F v ⊗[F] E → AE F E) =
      fun z => ∑ i, GlobalTheory.LatVac.liftV v (bA.repr z i) • ((1 : AF F) ⊗ₜ[F] b i) := funext hsum
  rw [hfun]
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  refine continuous_finset_sum _ fun i _ => ?_
  have hl : Continuous ((Finsupp.lapply i).comp bA.repr.toLinearMap : Fv F v ⊗[F] E →ₗ[Fv F v] Fv F v) :=
    IsModuleTopology.continuous_of_linearMap _
  exact Continuous.smul ((continuous_liftV v).comp hl)
    (continuous_const : Continuous fun _ : Fv F v ⊗[F] E => ((1 : AF F) ⊗ₜ[F] b i : AE F E))

theorem continuous_liftU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) :
    Continuous (GlobalTheory.HoweLocal.liftU (F := F) (E := E) v) := by
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) := IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  rw [Units.continuous_iff]
  constructor
  · change Continuous (fun z : (Fv F v ⊗[F] E)ˣ => 1 + liftE v ((z : Fv F v ⊗[F] E) - 1))
    exact continuous_const.add ((continuous_liftE v).comp (Units.continuous_val.sub continuous_const))
  · change Continuous (fun z : (Fv F v ⊗[F] E)ˣ => 1 + liftE v (((z⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) - 1))
    exact continuous_const.add ((continuous_liftE v).comp (Units.continuous_coe_inv.sub continuous_const))

end GlobalTheory.HoweLocal
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.NormLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adele_ext {a b : AF F} (hf : ∀ u, evFin F u a = evFin F u b) (hi : ∀ w, evInf F w a = evInf F w b) :
    a = b :=
  Prod.ext (funext fun w => hi w) (GlobalTheory.AdelicU.af_ext fun u => hf u)

theorem evFin_liftV_ne {u v : Pl F} (h : u ≠ v) (b : Fv F v) : evFin F u (GlobalTheory.LatVac.liftV v b) = 0 :=
  GlobalTheory.AdelicU.evalV_singleFin_ne h b

theorem evInf_liftV (w : InfinitePlace F) (v : Pl F) (b : Fv F v) : evInf F w (GlobalTheory.LatVac.liftV v b) = 0 := rfl

theorem map_liftE_eq_zero {B : Type} [CommRing B] [Algebra F B] (f : AF F →ₐ[F] B) (v : Pl F)
    (hf : ∀ b, f (GlobalTheory.LatVac.liftV v b) = 0) (y : Fv F v ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (GlobalTheory.HoweLocal.liftE v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul a e =>
    simp only [GlobalTheory.HoweLocal.liftE, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
    rw [Algebra.TensorProduct.map_tmul, hf, TensorProduct.zero_tmul]

theorem comp_away {B : Type} [CommRing B] [Algebra F B] (f : AF F →ₐ[F] B) (v : Pl F)
    (hf : ∀ b, f (GlobalTheory.LatVac.liftV v b) = 0) (y : Fv F v ⊗[F] E) (a : Fv F v) :
    f (Algebra.norm (AF F) (1 + GlobalTheory.HoweLocal.liftE v y : AF F ⊗[F] E)) = f (1 + GlobalTheory.LatVac.liftV v a) := by
  rw [← GlobalTheory.HoweLocal.norm_map_tensor, map_add (Algebra.TensorProduct.map f (AlgHom.id F E)),
    map_liftE_eq_zero f v hf, add_zero, map_one, map_one, map_add f, hf, add_zero, map_one]

theorem norm_liftU (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (z : (Fv F v ⊗[F] E)ˣ) :
    Units.map (Algebra.norm (AF F) : AE F E →* AF F) (GlobalTheory.HoweLocal.liftU v z) =
      GlobalTheory.HoweLocal.liftUF v (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) z) := by
  refine Units.ext ?_
  rw [Units.coe_map, GlobalTheory.HoweLocal.liftU_val, GlobalTheory.HoweLocal.liftUF_val, Units.coe_map]
  refine adele_ext (fun u => ?_) (fun w => comp_away _ v (evInf_liftV w v) _ _)
  by_cases h : u = v
  · subst h
    have h1 := GlobalTheory.HoweLocal.norm_map_tensor (evFin F u)
      (1 + GlobalTheory.HoweLocal.liftE u ((z : Fv F u ⊗[F] E) - 1) : AF F ⊗[F] E)
    have h2 : Algebra.TensorProduct.map (evFin F u) (AlgHom.id F E)
        (GlobalTheory.HoweLocal.liftE u ((z : Fv F u ⊗[F] E) - 1)) = (z : Fv F u ⊗[F] E) - 1 :=
      GlobalTheory.HoweLocal.LocCoords.compFin_liftE u _
    rw [map_add, map_one, h2, add_sub_cancel] at h1
    rw [map_add (evFin F u), map_one, GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
    exact h1.symm
  · exact comp_away _ v (evFin_liftV_ne h) _ _

end GlobalTheory.HoweLocal.NormLift
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweLocal

theorem map_div_mem_normGroup {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (x : Aˣ) (t : Fˣ) (z : (A ⊗[F] E)ˣ)
    (h : x = Units.map (algebraMap F A).toMonoidHom t * Units.map (Algebra.norm A : A ⊗[F] E →* A) z)
    (y : Bˣ) (hy : f (x : A) = y) :
    (GlobalTheory.QuadSymbol.toUnits F B t)⁻¹ * y ∈ GlobalTheory.QuadSymbol.normGroup F E B := by
  refine ⟨Units.map (Algebra.TensorProduct.map f (AlgHom.id F E) : A ⊗[F] E →* B ⊗[F] E) z, ?_⟩
  rw [eq_inv_mul_iff_mul_eq]
  ext
  rw [← hy, h]
  change algebraMap F B t * Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id F E) (z : A ⊗[F] E)) =
    f (algebraMap F A t * Algebra.norm A (z : A ⊗[F] E))
  rw [norm_map_tensor, map_mul, AlgHom.commutes]

theorem mem_localNorms_of_liftUF_eq (hC : GlobalTheory.Published.QuadraticClassFieldTheory)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (h2 : Module.finrank F E = 2)
    (v : Pl F) (a : (Fv F v)ˣ) (t : Fˣ) (z : (AE F E)ˣ)
    (h : GlobalTheory.HoweLocal.liftUF v a =
      Units.map (algebraMap F (AF F)).toMonoidHom t * Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) :
    a ∈ (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v)).range := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hP := ((hC.1 F E).2.2.2 t).2
  have hfin : ∀ u : Pl F, u ≠ v →
      GlobalTheory.QuadSymbol.eta F E (u.adicCompletion F) (GlobalTheory.QuadSymbol.finDiag F t u) = 1 := by
    intro u hu
    have := map_div_mem_normGroup (evFin F u) _ t z h 1 (by
      rw [liftUF_val, map_add, map_one,
        show evFin F u (GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1)) = 0 from evalV_singleFin_ne hu _, add_zero]
      rfl)
    rw [mul_one, inv_mem_iff] at this
    exact GlobalTheory.QuadSymbol.eta_eq_one_iff.2 this
  have hinf : ∀ w : InfinitePlace F,
      GlobalTheory.QuadSymbol.eta F E w.Completion (GlobalTheory.QuadSymbol.infDiag F t w) = 1 := by
    intro w
    have := map_div_mem_normGroup (evInf F w) _ t z h 1 (by
      rw [liftUF_val, map_add, map_one,
        show evInf F w (GlobalTheory.LatVac.liftV v ((a : Fv F v) - 1)) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), add_zero]
      rfl)
    rw [mul_one, inv_mem_iff] at this
    exact GlobalTheory.QuadSymbol.eta_eq_one_iff.2 this
  unfold GlobalTheory.QuadSymbol.etaProd at hP
  rw [Finset.prod_eq_one fun w _ => hinf w, mul_one, finprod_eq_single _ v hfin] at hP
  have ht := GlobalTheory.QuadSymbol.eta_eq_one_iff.1 hP
  have hv := map_div_mem_normGroup (evFin F v) _ t z h a (by
    rw [liftUF_val, map_add, map_one, GlobalTheory.LatVac.evFin_liftV, add_sub_cancel])
  have := mul_mem ht hv
  rw [show GlobalTheory.QuadSymbol.finDiag F t v = GlobalTheory.QuadSymbol.toUnits F (Fv F v) t from rfl, mul_inv_cancel_left] at this
  exact this

end GlobalTheory.HoweLocal
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem locChr_exists (hC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F), Continuous (GlobalTheory.HoweLocal.liftU (F := F) (E := E) v)) (hN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (z : (Fv F v ⊗[F] E)ˣ), Units.map (Algebra.norm (AF F) : AE F E →* AF F) (GlobalTheory.HoweLocal.liftU v z) = GlobalTheory.HoweLocal.liftUF v (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) z)) (hQ : GlobalTheory.Published.QuadraticClassFieldTheory → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (v : Pl F) (a : (Fv F v)ˣ) (t : Fˣ) (z : (AE F E)ˣ), GlobalTheory.HoweLocal.liftUF v a = Units.map (algebraMap F (AF F)).toMonoidHom t * Units.map (Algebra.norm (AF F) : AE F E →* AF F) z → a ∈ (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v)).range) : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (m : ℕ) (χ : Chr F E), IsHecke F E χ →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
        ∃ χv : (Fv F v ⊗[F] E)ˣ →* Circle, Continuous χv ∧ ResEtaPow (R := Fv F v) ⊥ χv m ∧ GlobalTheory.HoweLocal.IsLocChr χ v χv := by
  intro hP F E _ _ _ _ _ σ hcm m χ hχ hres v _
  refine ⟨locChr χ v, hχ.1.comp (hC F E v), ?_, ?_⟩
  · intro a
    change ((χ (liftU v (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E) : Fv F v →* Fv F v ⊗[F] E) a)) : Circle) : ℂ) = _
    rw [liftU_algebraMap]
    have h := hres (liftUF v a)
    simp only [RingHom.toMonoidHom_eq_coe] at h ⊢
    rw [h]
    congr 1
    apply propext
    rw [bot_sup_eq]
    constructor
    · intro hm
      obtain ⟨y, hy, n, hn, hyn⟩ := Subgroup.mem_sup.1 hm
      obtain ⟨t, rfl⟩ := hy
      obtain ⟨z, rfl⟩ := hn
      exact hQ hP.quadraticClassFieldTheory F E hcm.2.2.1 v a t z hyn.symm
    · rintro ⟨z, rfl⟩
      exact Subgroup.mem_sup_right ⟨liftU v z, hN F E v z⟩
  · intro a ha
    change χ (liftU v _) = χ a
    rw [liftU_compFin_of_at v a ha]

theorem exists_locChr_of_resEtaPow : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (m : ℕ) (χ : Chr F E), IsHecke F E χ →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
        ∃ χv : (Fv F v ⊗[F] E)ˣ →* Circle, Continuous χv ∧ ResEtaPow (R := Fv F v) ⊥ χv m ∧ GlobalTheory.HoweLocal.IsLocChr χ v χv :=
  locChr_exists GlobalTheory.HoweLocal.continuous_liftU GlobalTheory.HoweLocal.NormLift.norm_liftU GlobalTheory.HoweLocal.mem_localNorms_of_liftUF_eq

end GlobalTheory.HoweLocal
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweLocal.Psi

theorem psiAt_cont_norm_nontriv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    Continuous (GlobalTheory.LatVac.psiAt ψ v) ∧ (∀ t, ‖GlobalTheory.LatVac.psiAt ψ v t‖ = 1) ∧ GlobalTheory.LatVac.psiAt ψ v ≠ 1 := by
  intro F _ _ ψ hψ v
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
    show Continuous (fun x => ψ (GlobalTheory.LatVac.liftV v x))
    exact hψ.1.comp (continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v))

  have hle : ∀ t, ‖GlobalTheory.LatVac.psiAt ψ v t‖ ≤ 1 := by
    intro t
    haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
    have hcf : Continuous fun y : v.adicCompletionIntegers F => ‖GlobalTheory.LatVac.psiAt ψ v (t * (y : Fv F v))‖ :=
      (hc.comp (continuous_const.mul continuous_subtype_val)).norm
    obtain ⟨M, hM⟩ := (isCompact_range hcf).isBounded.bddAbove
    have hpow : ∀ n : ℕ, ‖GlobalTheory.LatVac.psiAt ψ v t‖ ^ n ≤ M := by
      intro n
      have hn : ((n : Fv F v)) ∈ v.adicCompletionIntegers F := by
        exact natCast_mem _ n
      have := hM ⟨⟨(n : Fv F v), hn⟩, rfl⟩
      simp only at this
      rw [← norm_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]
      exact this
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    exact absurd (hpow n) (not_le.mpr hn)
  refine ⟨hc, fun t => ?_, ?_⟩
  · have h1 := hle t
    have h2 := hle (-t)
    have hmul : GlobalTheory.LatVac.psiAt ψ v t * GlobalTheory.LatVac.psiAt ψ v (-t) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    have hn : ‖GlobalTheory.LatVac.psiAt ψ v t‖ * ‖GlobalTheory.LatVac.psiAt ψ v (-t)‖ = 1 := by
      rw [← norm_mul, hmul, norm_one]
    nlinarith [norm_nonneg (GlobalTheory.LatVac.psiAt ψ v t), norm_nonneg (GlobalTheory.LatVac.psiAt ψ v (-t))]
  · intro h
    obtain ⟨t, ht⟩ := GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one ψ hψ v
    exact ht (by rw [h, AddChar.one_apply])

end GlobalTheory.HoweLocal.Psi
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.HoweTransport

open GlobalTheory.Published GlobalTheory.PRep

section Sub

variable {H H' T : Type} [Group H] [Group H'] [AddCommGroup T] [Module ℂ T]

def subIso (e : H ≃* H') (ρ : Representation ℂ H' T) :
    Subrepresentation (ρ.comp e.toMonoidHom : Representation ℂ H T) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (e.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (e g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem irr_comp (e : H ≃* H') {ρ : Representation ℂ H' T} (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom : Representation ℂ H T) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact (subIso e ρ).isSimpleOrder

theorem coatom_comp (e : H ≃* H') {ρ : Representation ℂ H' T}
    (h : ∀ N N' : Subrepresentation ρ, IsCoatom N → IsCoatom N' → N = N') :
    ∀ N N' : Subrepresentation (ρ.comp e.toMonoidHom : Representation ℂ H T), IsCoatom N → IsCoatom N' → N = N' := by
  intro N N' hN hN'
  apply (subIso e ρ).injective
  exact h _ _ (((subIso e ρ).isCoatom_iff N).2 hN) (((subIso e ρ).isCoatom_iff N').2 hN')

def modIso (e : H ≃* H') (ρ : Representation ℂ H' T) :
    Submodule (MonoidAlgebra ℂ H) (Representation.asModule (ρ.comp e.toMonoidHom : Representation ℂ H T)) ≃o
      Submodule (MonoidAlgebra ℂ H') ρ.asModule :=
  (Subrepresentation.subrepresentationSubmoduleOrderIso.symm.trans (subIso e ρ)).trans
    Subrepresentation.subrepresentationSubmoduleOrderIso

theorem finLen_comp (e : H ≃* H') {ρ : Representation ℂ H' T}
    (h : IsFiniteLength (MonoidAlgebra ℂ H') ρ.asModule) :
    IsFiniteLength (MonoidAlgebra ℂ H) (Representation.asModule (ρ.comp e.toMonoidHom : Representation ℂ H T)) := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
  obtain ⟨h1, h2⟩ := h
  rw [isNoetherian_iff'] at h1 ⊢
  refine ⟨(modIso e ρ).strictMono.wellFoundedGT, ?_⟩
  haveI := h2
  exact (modIso e ρ).strictMono.wellFoundedLT

end Sub

section Top

variable {G G' V : Type} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [AddCommGroup V] [Module ℂ V]

theorem smooth_comp (e : G' →* G) (he : Continuous e) {π : Representation ℂ G V} (h : IsSmooth π) :
    IsSmooth (π.comp e : Representation ℂ G' V) := fun v => (h v).preimage he

theorem fixed_comp (e : G' ≃* G) (π : Representation ℂ G V) (K : Subgroup G') :
    fixed (π.comp e.toMonoidHom : Representation ℂ G' V) K = fixed π (K.comap e.symm.toMonoidHom) := by
  ext v
  simp only [fixed, eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro hv k
    have := hv ⟨e.symm k, k.2⟩
    simpa using this
  · intro hv k
    have := hv ⟨e k, by simp [Subgroup.mem_comap]⟩
    simpa using this

theorem admissible_comp_eval (e : G' ≃* G) (he : Continuous e) (he' : Continuous e.symm) {π : Representation ℂ G V}
    (h : IsAdmissible π) : IsAdmissible (π.comp e.toMonoidHom : Representation ℂ G' V) := by
  refine ⟨smooth_comp e.toMonoidHom he h.1, fun K hKo hKc => ?_⟩
  rw [fixed_comp]
  refine h.2 _ ?_ ?_
  · have : ((K.comap e.symm.toMonoidHom : Subgroup G) : Set G) = e.symm ⁻¹' (K : Set G') := rfl
    rw [this]
    exact hKo.preimage he'
  · have : ((K.comap e.symm.toMonoidHom : Subgroup G) : Set G) = e '' (K : Set G') := by
      ext x
      simp only [Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe, Set.mem_image, MulEquiv.coe_toMonoidHom]
      exact ⟨fun hx => ⟨e.symm x, hx, by simp⟩, fun ⟨y, hy, hyx⟩ => by rw [← hyx]; simpa using hy⟩
    rw [this]
    exact hKc.image he

end Top

end GlobalTheory.HoweLocal.HoweTransport

namespace GlobalTheory.HoweLocal.HoweTransport

open GlobalTheory.Published GlobalTheory.PRep

section HoweDuality

variable {G G' H H' Y V T : Type} [Group G] [Group G'] [Group H] [Group H'] [TopologicalSpace Y]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℂ T]

theorem left_iff (eG : G ≃* G') (eH : H ≃* H') (om : G' × H' →* Module.End ℂ (Y → ℂ))
    (π : Representation ℂ G V) (f : SB Y →ₗ[ℂ] V) :
    IsLeftHom (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) π f ↔
      IsLeftHom om (π.comp eG.symm.toMonoidHom) f := by
  constructor
  · intro h g φ φ₁ hφ
    have := h (eG.symm g) φ φ₁ (by simpa using hφ)
    simpa using this
  · intro h g φ φ₁ hφ
    have := h (eG g) φ φ₁ (by simpa using hφ)
    simpa using this

theorem pair_to (eG : G ≃* G') (eH : H ≃* H') (om : G' × H' →* Module.End ℂ (Y → ℂ))
    (π : Representation ℂ G V) (τ : Representation ℂ H T) (f : SB Y →ₗ[ℂ] V ⊗[ℂ] T)
    (h : IsPairHom (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) π τ f) :
    IsPairHom om (π.comp eG.symm.toMonoidHom) (τ.comp eH.symm.toMonoidHom) f := by
  intro g k φ φ₁ hφ
  have := h (eG.symm g) (eH.symm k) φ φ₁ (by simpa using hφ)
  simpa using this

theorem pair_from (eG : G ≃* G') (eH : H ≃* H') (om : G' × H' →* Module.End ℂ (Y → ℂ))
    (π : Representation ℂ G V) (τ : Representation ℂ H' T) (f : SB Y →ₗ[ℂ] V ⊗[ℂ] T)
    (h : IsPairHom om (π.comp eG.symm.toMonoidHom) τ f) :
    IsPairHom (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) π (τ.comp eH.toMonoidHom) f := by
  intro g k φ φ₁ hφ
  have := h (eG g) (eH k) φ φ₁ (by simpa using hφ)
  simpa using this

theorem equiv_back {V' : Type} [AddCommGroup V'] [Module ℂ V'] (eG : G ≃* G') {π : Representation ℂ G V}
    {π' : Representation ℂ G V'}
    (e : Representation.Equiv (π.comp eG.symm.toMonoidHom : Representation ℂ G' V)
      (π'.comp eG.symm.toMonoidHom : Representation ℂ G' V')) :
    Nonempty (π.Equiv π') := by
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (eG g) v
  simp only [LinearMap.comp_apply]
  change e.toIntertwiningMap (π g v) = π' g (e.toIntertwiningMap v)
  simpa using h1

end HoweDuality

end GlobalTheory.HoweLocal.HoweTransport

namespace GlobalTheory.HoweLocal.HoweTransport

open GlobalTheory.Published GlobalTheory.PRep

theorem howeDualityFor_transport : ∀ {G G' H H' Y : Type} [Group G] [Group G'] [Group H] [Group H'] [TopologicalSpace G] [TopologicalSpace G']
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace Y] (eG : G ≃* G') (eH : H ≃* H'),
    Continuous eG → Continuous eG.symm → Continuous eH → Continuous eH.symm →
    ∀ om : G' × H' →* Module.End ℂ (Y → ℂ), GlobalTheory.Published.HoweDualityFor om →
      GlobalTheory.Published.HoweDualityFor (om.comp (eG.toMonoidHom.prodMap eH.toMonoidHom)) := by
  intro G G' H H' Y _ _ _ _ _ _ _ _ _ eG eH hG hG' hH hH' om hom
  have hGs : Continuous eG.symm.symm := by simpa using hG
  intro V _ _ π hπ hA
  obtain ⟨⟨T, iT1, iT2, Θ, p, ⟨hP, hSur, hK⟩, hS, hF, hC⟩, h2⟩ :=
    hom V (π.comp eG.symm.toMonoidHom) (irr_comp eG.symm hπ) (admissible_comp_eval eG.symm hG' hGs hA)
  refine ⟨⟨T, iT1, iT2, Θ.comp eH.toMonoidHom, p, ⟨pair_from eG eH om π Θ p hP, hSur, fun φ => ?_⟩,
    smooth_comp eH.toMonoidHom hH hS, finLen_comp eH hF, coatom_comp eH hC⟩, ?_⟩
  · rw [hK φ]
    simp only [left_iff]
  · intro T _ _ τ hτ hτs f hf hf0
    obtain ⟨h2a, h2b⟩ := h2 T (τ.comp eH.symm.toMonoidHom) (irr_comp eH.symm hτ)
      (smooth_comp eH.symm.toMonoidHom hH' hτs) f (pair_to eG eH om π τ f hf) hf0
    refine ⟨fun f' hf' => h2a f' (pair_to eG eH om π τ f' hf'), fun V' _ _ π₂ hπ₂ hA₂ f' hf' hf'0 => ?_⟩
    obtain ⟨e⟩ := h2b V' (π₂.comp eG.symm.toMonoidHom) (irr_comp eG.symm hπ₂) (admissible_comp_eval eG.symm hG' hGs hA₂) f'
      (pair_to eG eH om π₂ τ f' hf') hf'0
    exact equiv_back eG e

end GlobalTheory.HoweLocal.HoweTransport

end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweLocal

theorem isContOn_locOps_nonsplit : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) →
      ∀ (eX : UAtGrp σ X (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J)),
        GlobalTheory.HoweLocal.IsCompIso σ X v eX →
      ∀ (eW : UAtGrp σ W (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v W.J)),
        GlobalTheory.HoweLocal.IsCompIso σ W v eW →
      ∀ (co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J))
        (Fin n × Fin d)), GlobalTheory.HoweLocal.IsLocCo σ M v co →
      ∀ χXv χWv : (Fv F v ⊗[F] E)ˣ →* Circle, GlobalTheory.HoweLocal.IsLocChr χX v χXv → GlobalTheory.HoweLocal.IsLocChr χW v χWv →
      IsContOn (sbClass (Fv F v)) (om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)) := by
  intro _ F E _ _ _ _ _ σ _ n d X W M ψ χX χW om _ _ _ _ _ _ _ _ _ hWeil v _ _ om' hom' eX heX eW heW _ _ χXv χWv _ _
  refine IsContOn.comp ?_ (f := eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom) (heX.2.2.prodMap heW.2.2)
  intro l _ φ hφ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin n × Fin d) v
  let lift : (Fin n × Fin d → Fv F v) → (Fin n × Fin d → AF F) := fun t i => GlobalTheory.LatVac.liftV v (t i)
  let L : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := (R 0)⁻¹ • l.comp (LinearMap.funLeft ℂ ℂ lift)
  have hL : L ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨((R 0)⁻¹ * l (fun t => g (fun i => (lift t i).2))) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : (fun t => pureA F f g (lift t)) = f 0 • fun t => g (fun i => (lift t i).2) := by
      funext t
      have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (lift t i).1) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      simp only [pureA, h0, Pi.smul_apply, smul_eq_mul]
    show (R 0)⁻¹ • l (fun t => pureA F f g (lift t)) = _
    rw [e, map_smul]
    simp [smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]
  have hc0 : IsContOn (adeleClass F) om := hWeil.2.2
  have hc := (hc0 L hL _ (hR φ hφ).2).comp ((continuous_subtype_val (p := (· ∈ UAtGrp σ X (evFin F v)))).prodMap
    (continuous_subtype_val (p := (· ∈ UAtGrp σ W (evFin F v)))))
  refine hc.congr fun q => ?_
  simp only [Function.comp_apply, Prod.map]
  rw [(hom' q.1 q.2 φ hφ).2 R (hR φ hφ)]
  have e : (fun t => tens (evFin F v) (om' q φ) R (lift t)) = R 0 • om' q φ := by
    funext t
    have hz : At (evFin F v) (lift t) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have hrz : R (lift t) = R 0 := by simpa using (hR φ hφ).1 0 _ hz
    simp only [tens, lift, GlobalTheory.LatVac.evFin_liftV, Pi.smul_apply, smul_eq_mul]
    rw [show (fun i => GlobalTheory.LatVac.liftV v (t i)) = lift t from rfl, hrz, mul_comm]
  show (R 0)⁻¹ • l (fun t => tens (evFin F v) (om' q φ) R (lift t)) = _
  rw [e, map_smul, smul_smul, inv_mul_cancel₀ hR0, one_smul]

end GlobalTheory.HoweLocal
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.WeilImpl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftE_mul_eq (v : Pl F) (z : Fv F v ⊗[F] E) (M : AE F E) :
    liftE v z * M = liftE v (z * compFin F E v M) := by
  have h1 : GlobalTheory.LatVac.liftV v 1 • liftE (E := E) v z = liftE v z := by
    rw [GlobalTheory.HoweLocal.LocCoords.liftV_one_smul, GlobalTheory.HoweLocal.LocCoords.compFin_liftE]
  rw [← h1, smul_mul_assoc, GlobalTheory.HoweLocal.LocCoords.liftV_one_smul, map_mul,
    GlobalTheory.HoweLocal.LocCoords.compFin_liftE]

theorem at_liftE (v : Pl F) (z : Fv F v ⊗[F] E) : At (evFin F v) (liftE (E := E) v z) := by
  intro u hu
  have h1 : GlobalTheory.LatVac.liftV v 1 • liftE (E := E) v z = liftE v z := by
    rw [GlobalTheory.HoweLocal.LocCoords.liftV_one_smul, GlobalTheory.HoweLocal.LocCoords.compFin_liftE]
  rw [← h1, smul_smul, mul_comm, GlobalTheory.HoweLocal.LocCoords.liftV_mul, hu, mul_zero, map_zero, zero_smul]

end GlobalTheory.HoweLocal.WeilImpl

namespace GlobalTheory.HoweLocal.WeilImpl

theorem impl_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a b : ℕ)
    (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → IsUSplitting (adeleClass F) ψ dA (actB (cA σ)) omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    ∀ g w, ∀ φ ∈ SB (κ → Fv F v), omL g (co.rho (GlobalTheory.LatVac.psiAt ψ v) w φ) =
      co.rho (GlobalTheory.LatVac.psiAt ψ v) (actB (GlobalTheory.HoweLocal.cv σ v) g w) (omL g φ) := by
  intro F E _ _ _ _ _ σ a b JA B κ _ dA ψ omB hstd hW v _hv inst2 eB hcomp omL hL co hco g w φ hφ
  classical
  have hat : ∀ x : Matrix (Fin a) (Fin b) (Fv F v ⊗[F] E), At (evFin F v) (x.map (liftE v)) := by
    intro x u hu; funext i j; exact at_liftE v (x i j) u hu
  have hrho : ∀ (x : Matrix (Fin a) (Fin b) (Fv F v ⊗[F] E)) (φ₀ : (κ → Fv F v) → ℂ),
      Acts (evFin F v) (dA.rho ψ (x.map (liftE v))) φ₀ (co.rho (GlobalTheory.LatVac.psiAt ψ v) x φ₀) := by
    intro x φ₀
    have h := GlobalTheory.VacBridge.rho_acts_locCo dA ψ v _ (hat x) φ₀
    rw [← hco x] at h
    convert h using 2
    simp only [Darboux.rho]
    first | rfl | (congr 1; exact Subsingleton.elim _ _) | congr
  have hSB : ∀ x, ∀ φ₀ ∈ SB (κ → Fv F v), co.rho (GlobalTheory.LatVac.psiAt ψ v) x φ₀ ∈ SB (κ → Fv F v) := by
    intro x φ₀ h0
    have := GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 v (co.e x) φ₀ h0
    convert this using 2
    simp only [Darboux.rho]
    first | rfl | (congr 1; exact Subsingleton.elim _ _) | congr
  have hpresR : ∀ x, ∀ Φ ∈ schA F κ, dA.rho ψ x Φ ∈ schA F κ := by
    intro x Φ hΦ
    exact GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hstd κ _ Φ hΦ
  have hm : (((g : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)) : GL (Fin b) (Fv F v ⊗[F] E)) : Matrix (Fin b) (Fin b) (Fv F v ⊗[F] E)) = (mat ((eB.symm g : UAtGrp σ B (evFin F v)) : UA σ B.J)).map (compFin F E v) := by
    have := hcomp.1 (eB.symm g)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hact : actB (cA σ) (eB.symm g).1 (w.map (liftE v)) = (actB (GlobalTheory.HoweLocal.cv σ v) g w).map (liftE v) := by
    funext i j
    simp only [actB, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, map_sum, hm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [liftE_mul_eq]; rfl
  have h1 := GlobalTheory.ThK.LocalOps.acts_comp v (hpresR (w.map (liftE v))) (hrho w φ) (hL g _ (hSB w φ hφ)).2
  have h2 := GlobalTheory.ThK.LocalOps.acts_comp v (fun Φ hΦ => hW.pres (eB.symm g).1 Φ hΦ) (hL g φ hφ).2
    (hrho (actB (GlobalTheory.HoweLocal.cv σ v) g w) (omL g φ))
  have h2' : Acts (evFin F v) (omB (eB.symm g).1 ∘ dA.rho ψ (w.map (liftE v))) φ
      (co.rho (GlobalTheory.LatVac.psiAt ψ v) (actB (GlobalTheory.HoweLocal.cv σ v) g w) (omL g φ)) := by
    intro r hr
    have := h2 r hr
    simp only [Function.comp_apply] at this ⊢
    rw [hW.impl (eB.symm g).1 (w.map (liftE v)) _ hr.2, hact]
    exact this
  exact GlobalTheory.HoweLocal.LocOpsW.acts_uniq v _ hφ h1 h2'

end GlobalTheory.HoweLocal.WeilImpl
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweLocal

theorem isContOn_locOps_member_nonsplit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a b : ℕ)
    (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → IsUSplitting (adeleClass F) ψ dA (actB (cA σ)) omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    IsContOn (sbClass (Fv F v)) omL := by
  intro F E _ _ _ _ _ σ a b JA B κ _ dA ψ omB _ hsp v _ _ eB heB omL hom _ _
  have hcomp : omL = (omL.comp eB.toMonoidHom).comp eB.symm.toMonoidHom := by
    ext g : 1
    simp
  rw [hcomp]
  refine IsContOn.comp ?_ heB.2.2
  intro l _ φ hφ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  let lift : (κ → Fv F v) → (κ → AF F) := fun t i => GlobalTheory.LatVac.liftV v (t i)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (R 0)⁻¹ • l.comp (LinearMap.funLeft ℂ ℂ lift)
  have hL : L ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨((R 0)⁻¹ * l (fun t => g (fun i => (lift t i).2))) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : (fun t => pureA F f g (lift t)) = f 0 • fun t => g (fun i => (lift t i).2) := by
      funext t
      have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (lift t i).1) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      simp only [pureA, h0, Pi.smul_apply, smul_eq_mul]
    show (R 0)⁻¹ • l (fun t => pureA F f g (lift t)) = _
    rw [e, map_smul]
    simp [smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]
  have hc0 : IsContOn (adeleClass F) omB := hsp.cont
  have hc := (hc0 L hL _ (hR φ hφ).2).comp
    (continuous_subtype_val (p := (· ∈ UAtGrp σ B (evFin F v))))
  refine hc.congr fun q => ?_
  have hq := (hom (eB q) φ hφ).2 R (hR φ hφ)
  rw [MulEquiv.symm_apply_apply] at hq
  simp only [Function.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hq]
  have e : (fun t => tens (evFin F v) (omL (eB q) φ) R (lift t)) = R 0 • omL (eB q) φ := by
    funext t
    have hz : At (evFin F v) (lift t) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have hrz : R (lift t) = R 0 := by simpa using (hR φ hφ).1 0 _ hz
    simp only [tens, lift, GlobalTheory.LatVac.evFin_liftV, Pi.smul_apply, smul_eq_mul]
    rw [show (fun i => GlobalTheory.LatVac.liftV v (t i)) = lift t from rfl, hrz, mul_comm]
  show (R 0)⁻¹ • l (fun t => tens (evFin F v) (omL (eB q) φ) R (lift t)) = _
  rw [e, map_smul, smul_smul, inv_mul_cancel₀ hR0, one_smul]

end GlobalTheory.HoweLocal
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.DblLocal

open MeasureTheory GlobalTheory.HoweLocal GlobalTheory.LatVac

section Uniq

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {κ : Type}

theorem diag_eq_mul_integral [Invertible (2 : k)] [Fintype κ] (ψ : AddChar k ℂ) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (l : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ x y : κ → k, ∀ φ ∈ SB (κ ⊕ κ → k), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ)
    (μ : @Measure (κ → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ c : ℂ, ∀ φ ∈ SB (κ ⊕ κ → k), l φ = c * ∫ x, φ (Sum.elim x x) ∂μ := by
  classical
  letI : MeasurableSpace (κ → k) := borel _
  haveI : BorelSpace (κ → k) := ⟨rfl⟩
  have := SplitWeil.t2Space k
  have := nonarch_pi k κ
  have hz : ∀ φ ∈ SB (κ ⊕ κ → k), ∀ φ' ∈ SB (κ ⊕ κ → k), (∀ x, φ' (Sum.elim x x) = φ (Sum.elim x x)) → l φ' = l φ := by
    intro φ hφ φ' hφ' h
    have := diag_invariant_comp ψ hψ hψ1 l hl 1 hφ hφ' (fun x => by simpa using h x)
    simpa using this
  let K : Set (κ → k) := Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => SplitWeil.isCompact_int k
  have hK : IsClopen K := ⟨hKc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => SplitWeil.isOpen_int k⟩
  let e : (κ → k) → ℂ := K.indicator 1
  have he : IsLocallyConstant e := (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant
  have he0 : e 0 = 1 := Set.indicator_of_mem (show (0 : κ → k) ∈ K from fun _ _ => zero_mem _) _
  let ext : ((κ → k) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    { toFun := fun f u => f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl)
      map_add' := fun f f' => by funext u; simp [add_mul]
      map_smul' := fun a f => by funext u; simp [mul_assoc] }
  have hext : ∀ f u, ext f u = f (u ∘ Sum.inl) * e (u ∘ Sum.inr - u ∘ Sum.inl) := fun _ _ => rfl
  have c1 : Continuous fun u : κ ⊕ κ → k => u ∘ Sum.inl := continuous_pi fun k => continuous_apply _
  have c2 : Continuous fun u : κ ⊕ κ → k => u ∘ Sum.inr := continuous_pi fun k => continuous_apply _
  have hSB : ∀ f ∈ SB (κ → k), ext f ∈ SB (κ ⊕ κ → k) := by
    intro f hf
    have c3 : Continuous fun p : (κ → k) × (κ → k) => (Sum.elim p.1 (p.2 + p.1) : κ ⊕ κ → k) :=
      continuous_pi (by rintro (k | k) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply] <;> fun_prop)
    refine ⟨(hf.1.comp_continuous c1).mul (he.comp_continuous (c2.sub c1)),
      HasCompactSupport.intro ((IsCompact.prod hf.2 hKc).image c3) fun u hu => ?_⟩
    by_contra h
    rw [hext] at h
    refine hu ⟨(u ∘ Sum.inl, u ∘ Sum.inr - u ∘ Sum.inl),
      ⟨subset_tsupport _ (left_ne_zero_of_mul h), Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩, ?_⟩
    simp
  have hres : ∀ φ ∈ SB (κ ⊕ κ → k), l φ = (l ∘ₗ ext) fun x => φ (Sum.elim x x) := by
    intro φ hφ
    rw [LinearMap.comp_apply]
    refine hz _ (hSB _ (diag_mem_SB hφ)) _ hφ fun x => ?_
    simp [hext, he0]
  have hinv : ∀ f ∈ SB (κ → k), ∀ a, (l ∘ₗ ext) (fun x => f (x + a)) = (l ∘ₗ ext) f := by
    intro f hf a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hl a 0 _ (hSB f hf)]
    congr 1
    funext u
    have e1 : (u + Sum.elim a a) ∘ Sum.inl = u ∘ Sum.inl + a := rfl
    have e2 : (u + Sum.elim a a) ∘ Sum.inr = u ∘ Sum.inr + a := rfl
    simp [schr, hext, e1, e2]
  obtain ⟨c, hc⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (κ → k) μ _ hinv
  exact ⟨c, fun φ hφ => by rw [hres φ hφ, hc _ (diag_mem_SB hφ)]⟩

end Uniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Lift

theorem liftE_eq (v : Pl F) (y : Fv F v ⊗[F] E) : liftE v y = Supp.singleTens E v y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_liftE_mul (v : Pl F) {a b c : Type} [Fintype b] (x : Matrix a b (Fv F v ⊗[F] E)) (P : Matrix b c (AE F E)) :
    x.map (liftE v) * P = (x * P.map (compFin F E v)).map (liftE v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, liftE_eq, Supp.singleTens_mul]

theorem mul_map_liftE (v : Pl F) {a b c : Type} [Fintype b] (P : Matrix a b (AE F E)) (x : Matrix b c (Fv F v ⊗[F] E)) :
    P * x.map (liftE v) = (P.map (compFin F E v) * x).map (liftE v) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, liftE_eq]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm, Supp.singleTens_mul, mul_comm]

theorem map_liftE_map (v : Pl F) {a b : Type} (x : Matrix a b (Fv F v ⊗[F] E)) :
    (x.map (liftE v)).map (compFin F E v) = x := by
  ext i j
  simp only [Matrix.map_apply, liftE_eq, Supp.compFin_singleTens_self]

theorem at_map_liftE (v : Pl F) {a b : Type} (x : Matrix a b (Fv F v ⊗[F] E)) : At (evFin F v) (x.map (liftE v)) := by
  intro u hu
  ext i j
  rw [Matrix.smul_apply, Matrix.map_apply, liftE_eq, Algebra.smul_def, mul_comm, Supp.singleTens_mul]
  have e : compFin F E v (algebraMap (AF F) (AE F E) u) = 0 := by
    show evFin F v u ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [e, mul_zero, map_zero]
  rfl

theorem map_liftE_cA (σ : E →ₐ[F] E) (v : Pl F) {a b : Type} (x : Matrix a b (Fv F v ⊗[F] E)) :
    (x.map (liftE v)).map (cA σ) = (x.map (cv σ v)).map (liftE v) := by
  ext i j
  simp only [Matrix.map_apply]
  induction x i j using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {β : Type} [Fintype β] [DecidableEq β]

def liftM (v : Pl F) (β : Type) [Fintype β] [DecidableEq β] : Matrix β β (Fv F v ⊗[F] E) →* Matrix β β (AE F E) where
  toFun h := 1 + (h - 1).map (liftE v)
  map_one' := by simp
  map_mul' a b := by
    have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    have e2 : ((a - 1) * (b - 1)).map (liftE v) = (a - 1).map (liftE v) * (b - 1).map (liftE v) := by
      rw [map_liftE_mul, map_liftE_map]
    rw [e, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), e2]
    noncomm_ring

theorem liftM_apply (v : Pl F) (h : Matrix β β (Fv F v ⊗[F] E)) : liftM v β h = 1 + (h - 1).map (liftE v) := rfl

theorem liftM_map (v : Pl F) (h : Matrix β β (Fv F v ⊗[F] E)) : (liftM v β h).map (compFin F E v) = h := by
  rw [liftM_apply, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), map_liftE_map]
  abel

theorem liftM_at (v : Pl F) (h : Matrix β β (Fv F v ⊗[F] E)) : At (evFin F v) (liftM v β h - 1) := by
  rw [liftM_apply, add_sub_cancel_left]
  exact at_map_liftE v _

theorem liftM_comp (v : Pl F) (g : Matrix β β (AE F E)) (hg : At (evFin F v) (g - 1)) :
    liftM v β (g.map (compFin F E v)) = g := by
  have e : g.map (compFin F E v) - 1 = (g - 1).map (compFin F E v) := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [liftM_apply, e, Matrix.map_map]
  ext i j
  have hz : At (evFin F v) ((g - 1) i j) := fun u hu => by
    have := congrArg (fun M => M i j) (hg u hu)
    simp only [Matrix.smul_apply, Matrix.zero_apply] at this
    exact this
  rw [Matrix.add_apply, Matrix.map_apply, Function.comp_apply, liftE_eq, CompIso.lift_comp v _ hz, Matrix.sub_apply]
  abel

theorem liftM_mem (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) (h : UG (cv σ v) JL) : Units.map (liftM v β) h.1 ∈ UG (cA σ) J := by
  have hh : (h.1 : Matrix β β (Fv F v ⊗[F] E))ᵀ * JL * (h.1 : Matrix β β (Fv F v ⊗[F] E)).map (cv σ v) = JL := h.2
  show (liftM v β h.1.1)ᵀ * J * (liftM v β h.1.1).map (cA σ) = J
  obtain ⟨a, ha⟩ : ∃ a, (h.1 : Matrix β β (Fv F v ⊗[F] E)) = 1 + a := ⟨h.1.1 - 1, by abel⟩
  rw [ha] at hh
  rw [ha, liftM_apply, add_sub_cancel_left]
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add,
    Matrix.transpose_one] at hh ⊢
  rw [map_liftE_cA, ← Matrix.transpose_map]
  set c := a.map (cv σ v)
  have h0 : aᵀ * JL + JL * c + aᵀ * JL * c = 0 := by
    rw [← sub_eq_zero] at hh
    rw [← hh]; noncomm_ring
  have e1 : aᵀ.map (liftE v) * J = (aᵀ * JL).map (liftE v) := by rw [map_liftE_mul, hJ]
  have e2 : J * c.map (liftE v) = (JL * c).map (liftE v) := by rw [mul_map_liftE, hJ]
  have e3 : aᵀ.map (liftE v) * J * c.map (liftE v) = (aᵀ * JL * c).map (liftE v) := by
    rw [e1, map_liftE_mul, map_liftE_map]
  have h1 : aᵀ.map (liftE v) * J + J * c.map (liftE v) + aᵀ.map (liftE v) * J * c.map (liftE v) = 0 := by
    rw [e3, e1, e2, ← Matrix.map_add _ (map_add _), ← Matrix.map_add _ (map_add _), h0, Matrix.map_zero _ (map_zero _)]
  rw [← sub_eq_zero, ← h1]
  noncomm_ring

def liftU (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) : UG (cv σ v) JL →* UG (cA σ) J :=
  ((Units.map (liftM v β)).comp (UG (cv σ v) JL).subtype).codRestrict _ (liftM_mem σ v hJ)

theorem liftU_val (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) (h : UG (cv σ v) JL) :
    ((liftU σ v hJ h : GL β (AE F E)) : Matrix β β (AE F E)) = liftM v β (h : GL β (Fv F v ⊗[F] E)) := rfl

theorem continuous_liftU (σ : E →ₐ[F] E) (v : Pl F) {J : Matrix β β (AE F E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) : Continuous (liftU σ v hJ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have hst : Continuous (Supp.singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ (Continuous.prodMk continuous_const (continuous_singleFin v))
  have hst' : Continuous (liftE (E := E) v) := hst.congr fun y => (liftE_eq v y).symm
  refine Continuous.subtype_mk ?_ _
  exact (Continuous.units_map _ (continuous_const.add ((continuous_id.sub continuous_const).matrix_map hst'))).comp
    continuous_subtype_val

theorem liftM_mul_of {ν : Type} [Fintype ν] [DecidableEq ν] (v : Pl F) (D : Matrix β ν (AE F E))
    (p : Matrix β β (Fv F v ⊗[F] E)) (t : Matrix ν ν (Fv F v ⊗[F] E))
    (hp : p * D.map (compFin F E v) = D.map (compFin F E v) * t) : liftM v β p * D = D * liftM v ν t := by
  rw [liftM_apply, liftM_apply, Matrix.add_mul, Matrix.mul_add, map_liftE_mul, mul_map_liftE, Matrix.sub_mul,
    Matrix.mul_sub, hp, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

theorem liftM_fromBlocks (v : Pl F) (g : Matrix β β (Fv F v ⊗[F] E)) :
    liftM v (β ⊕ β) (Matrix.fromBlocks g 0 0 1) = Matrix.fromBlocks (liftM v β g) 0 0 1 := by
  rw [liftM_apply, liftM_apply]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

end Lift

section Split

open scoped GlobalTheory.VacAny

variable {κ : Type} [Fintype κ]

theorem lintegral_eq_of_acts (v : Pl F) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (hU : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ schA F κ, ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ)
    {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) (hφ₁ : φ₁ ∈ SB (κ → Fv F v)) (hA : Acts (evFin F v) T φ φ₁)
    (μ : @Measure (κ → Fv F v) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  obtain ⟨r, hr, hS, h0⟩ := GlobalTheory.LocalUnitaryL2.exists_r (κ := κ) v
  let μA : Measure (κ → AF F) := Measure.addHaar
  obtain ⟨c, hc0, hct, hc⟩ := GlobalTheory.LocalUnitaryL2.exists_const v r hr hS μA ⟨0, h0⟩ μ
  have h := hU μA inferInstance (tens (evFin F v) φ r) (hS φ hφ)
  rw [hA r ⟨hr, hS φ hφ⟩, hc φ₁ hφ₁, hc φ hφ] at h
  exact (ENNReal.mul_right_inj hc0 hct).1 h

open scoped Classical in

theorem isContOn_of_acts (v : Pl F) {G : Type} [Group G] [TopologicalSpace G]
    (Ω : G →* Module.End ℂ ((κ → AF F) → ℂ)) (hc0 : IsContOn (adeleClass F) Ω)
    (om : G →* Module.End ℂ ((κ → Fv F v) → ℂ))
    (hom : ∀ g, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) (Ω g) φ (om g φ)) : IsContOn (sbClass (Fv F v)) om := by
  intro l _ φ hφ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  let lift : (κ → Fv F v) → (κ → AF F) := fun t i => liftV v (t i)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (R 0)⁻¹ • l.comp (LinearMap.funLeft ℂ ℂ lift)
  have hL : L ∈ (adeleClass F).adm κ := by
    intro g _
    refine ⟨((R 0)⁻¹ * l (fun t => g (fun i => (lift t i).2))) •
      ((BoundedContinuousFunction.evalCLM ℂ 0).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    have e : (fun t => pureA F f g (lift t)) = f 0 • fun t => g (fun i => (lift t i).2) := by
      funext t
      have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (lift t i).1) = 0 := by
        funext i
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      simp only [pureA, h0, Pi.smul_apply, smul_eq_mul]
    show (R 0)⁻¹ • l (fun t => pureA F f g (lift t)) = _
    rw [e, map_smul]
    simp [smul_eq_mul, mul_comm, mul_assoc, mul_left_comm]
  refine (hc0 L hL _ (hR φ hφ).2).congr fun q => ?_
  rw [hom q φ hφ R (hR φ hφ)]
  have e : (fun t => tens (evFin F v) (om q φ) R (lift t)) = R 0 • om q φ := by
    funext t
    have hz : At (evFin F v) (lift t) := fun u hu => funext fun i => at_liftV v _ u hu
    have hrz : R (lift t) = R 0 := by simpa using (hR φ hφ).1 0 _ hz
    simp only [tens, lift, evFin_liftV, Pi.smul_apply, smul_eq_mul]
    rw [show (fun i => liftV v (t i)) = lift t from rfl, hrz, mul_comm]
  show (R 0)⁻¹ • l (fun t => tens (evFin F v) (om q φ) R (lift t)) = _
  rw [e, map_smul, smul_smul, inv_mul_cancel₀ hR0, one_smul]

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem exists_loc_splitting (σ : E →ₐ[F] E) (v : Pl F) {ξ : AE F E} {JA : Matrix α α (AE F E)} {J : Matrix β β (AE F E)}
    {ξL : Fv F v ⊗[F] E} {JAL : Matrix α α (Fv F v ⊗[F] E)} {JL : Matrix β β (Fv F v ⊗[F] E)}
    (hJ : J.map (compFin F E v) = JL) (d : Darboux (symp (R := AF F) (cA σ) ξ JA J) κ) {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) {om : UG (cA σ) J →* Module.End ℂ ((κ → AF F) → ℂ)}
    (hS : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (co : Darboux (symp (R := Fv F v) (cv σ v) ξL JAL JL) κ) (hco : ∀ x, co.e x = locCo d v (x.map (liftE v))) :
    ∃ omL : UG (cv σ v) JL →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) (om (liftU σ v hJ g)) φ (omL g φ)) ∧
      IsUSplitting (sbClass (Fv F v)) (psiAt ψ v) co (actB (cv σ v)) omL := by
  have hex : ∀ g, ∀ φ ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om (liftU σ v hJ g)) φ φ₁ := by
    intro g φ hφ
    refine GlobalTheory.DblActs.acts_of_comm v ψ hψ _ (fun Φ hΦ => hS.pres _ Φ hΦ) (fun μ hμ Φ hΦ => hS.unit μ hμ _ Φ hΦ) ?_ φ hφ
    intro u hu x y Φ hΦ
    set w := d.e.symm (x, y) with hw
    have he : d.e (u • w) = (u • x, u • y) := by
      rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := liftM_at v ((g : GL β (Fv F v ⊗[F] E)) : Matrix β β (Fv F v ⊗[F] E)) u hu
    have e2 : actB (cA σ) (liftU σ v hJ g) (u • w) = u • w := by
      rw [actB, liftU_val]
      set P := liftM v β ((g : GL β (Fv F v ⊗[F] E)) : Matrix β β (Fv F v ⊗[F] E))
      have : (u • w) * Pᵀ - u • w = w * (u • (P - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      exact this
    have h3 := hS.impl (liftU σ v hJ g) (u • w) Φ hΦ
    simp only [Darboux.rho, he, e2] at h3
    exact h3
  obtain ⟨T, hT⟩ := GlobalTheory.HoweLocal.LocOpsW.loc_hom v (om.comp (liftU σ v hJ)) (fun x Φ hΦ => hS.pres _ Φ hΦ) hex
  obtain ⟨omL, homL⟩ := GlobalTheory.HoweLocal.LocOpsW.extend_hom (SB (κ → Fv F v)) T
  have hpres : ∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) := fun g φ hφ => by
    rw [show omL g φ = _ from homL g ⟨φ, hφ⟩]; exact (T g ⟨φ, hφ⟩).2
  have hact : ∀ g, ∀ φ ∈ SB (κ → Fv F v), Acts (evFin F v) (om (liftU σ v hJ g)) φ (omL g φ) := fun g φ hφ => by
    rw [show omL g φ = _ from homL g ⟨φ, hφ⟩]; exact hT g ⟨φ, hφ⟩
  refine ⟨omL, hact, ⟨hpres, fun g w φ hφ => ?_, fun _ _ _ => Set.mem_univ _⟩, fun μ hμ g φ hφ => ?_, ?_⟩
  · obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
    have hrho : ∀ x, ∀ f ∈ SB (κ → Fv F v), d.rho ψ (x.map (liftE v)) (tens (evFin F v) f R) =
        tens (evFin F v) (co.rho (psiAt ψ v) x f) R := fun x f hf => by
      rw [GlobalTheory.VacBridge.rho_acts_locCo d ψ v _ (at_map_liftE v x) f R (hR f hf), Darboux.rho, hco]
    have hm : co.rho (psiAt ψ v) w φ ∈ SB (κ → Fv F v) := GlobalTheory.SchrSB.schr_mem_SB ψ hψ.1 v _ φ hφ
    have e : actB (cA σ) (liftU σ v hJ g) (w.map (liftE v)) = (actB (cv σ v) g w).map (liftE v) := by
      rw [actB, actB, liftU_val, map_liftE_mul, Matrix.transpose_map, liftM_map]
    refine GlobalTheory.DblSwap.eq_of_tens_ne v (hR φ hφ).1 hR0 ?_
    rw [← hact g _ hm R (hR _ hm), ← hrho w φ hφ, hS.impl _ _ _ (hR φ hφ).2, e, hact g φ hφ R (hR φ hφ),
      hrho _ _ (hpres g φ hφ)]
  · exact lintegral_eq_of_acts v _ (fun μ hμ Φ hΦ => hS.unit μ hμ _ Φ hΦ) hφ (hpres g φ hφ) (hact g φ hφ) μ hμ
  · exact isContOn_of_acts v (om.comp (liftU σ v hJ)) (hS.cont.comp (continuous_liftU σ v hJ)) omL hact

end Split

theorem dbl_map (v : Pl F) {b : ℕ} (J : Matrix (Fin b) (Fin b) E) :
    (dbl (incM F J)).map (compFin F E v) = dbl (Jv v J) := by
  rw [dbl, dbl, Matrix.fromBlocks_map, Matrix.map_neg _ (map_neg _), CompIso.incM_map, Matrix.map_zero _ (map_zero _)]

theorem diag_mul {R : Type} [CommRing R] {α β : Type} [Fintype β] [DecidableEq β] (z : Matrix α β R) :
    z * (diagCols β : Matrix (β ⊕ β) β R)ᵀ = Matrix.fromCols z z := by
  rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]

theorem scalar_eq (χ : Chr F E) (v : Pl F) (χv : (Fv F v ⊗[F] E)ˣ →* Circle) (hχ : IsLocChr χ v χv) (z : (AE F E)ˣ)
    (zv : (Fv F v ⊗[F] E)ˣ) (hz : compFin F E v z = zv) (h1 : At (evFin F v) ((z : AE F E) - 1))
    (h2 : At (evFin F v) (Algebra.norm (AF F) (z : AE F E) - 1)) :
    χ z = χv zv ∧ ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) : ℝ) =
      (sbClass (Fv F v)).modu (Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) zv) := by
  refine ⟨?_, ?_⟩
  · rw [← hχ z h1]
    congr 1
    exact Units.ext hz
  · have h := GlobalTheory.ModuLocal.distribHaarChar_eq_nabs_of_at F v (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) h2
    rw [show Units.map (evFin F v : AF F →* Fv F v) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) z) =
      Units.map (Algebra.norm (Fv F v) : Fv F v ⊗[F] E →* Fv F v) zv from
        Units.ext ((GlobalTheory.NormAtPlace.evFin_norm_eq F E v z).trans (congrArg _ hz))] at h
    exact h

theorem exists_dbl_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ) (χ : Chr F E)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → JA.det ≠ 0 → B.J.det ≠ 0 →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ a → IsHecke F E χ →
    IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F B.J) dA χ omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    ∀ χv : (Fv F v ⊗[F] E)ˣ →* Circle, GlobalTheory.HoweLocal.IsLocChr χ v χv →
    ∃ (dd : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (dbl (GlobalTheory.HoweLocal.Jv v B.J))) (κ ⊕ κ))
      (omd : UG (GlobalTheory.HoweLocal.cv σ v) (dbl (GlobalTheory.HoweLocal.Jv v B.J)) →* Module.End ℂ ((κ ⊕ κ → Fv F v) → ℂ)),
      IsDblCoord (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA) (GlobalTheory.HoweLocal.Jv v B.J) co dd ∧
      IsUWeilSplit (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (dbl (GlobalTheory.HoweLocal.Jv v B.J)) dd χv (diagCols (Fin b)) omd ∧
      ∀ (g : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J))
        (gd : UG (GlobalTheory.HoweLocal.cv σ v) (dbl (GlobalTheory.HoweLocal.Jv v B.J))),
        ((gd : GL (Fin b ⊕ Fin b) (Fv F v ⊗[F] E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (Fv F v ⊗[F] E)) =
          Matrix.fromBlocks ((g : GL (Fin b) (Fv F v ⊗[F] E)) : Matrix (Fin b) (Fin b) (Fv F v ⊗[F] E)) 0 0 1 →
        ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), omd gd (boxFun φ₁ φ₂) = boxFun (omL g φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ hσ a b JA B κ _ dA ψ χ omB hψ _ hB _ _ hW v _ inst eB heB omL homL co hco χv hχv
  obtain rfl : inst = GlobalTheory.VacAny.invTwoV v := Subsingleton.elim _ _
  letI := GlobalTheory.VacAny.invTwoV v
  obtain ⟨-, ddA, omdA, hdd, ⟨-, hS, hSieg⟩, hbox⟩ := hW
  have hD := GlobalTheory.DblSchr.isDblCoord_dblD (cv σ v) co
  set dd := GlobalTheory.DblSchr.dblD (cv σ v) co
  have hcod : ∀ x, dd.e x = locCo ddA v (x.map (liftE v)) := fun x => by
    rw [← Matrix.fromCols_toCols x, hD, Matrix.fromCols_map, hco, hco]
    ext (k | k) <;> simp [locCo, hdd _ _]
  obtain ⟨omd, hact, hspl⟩ := exists_loc_splitting σ v (dbl_map v B.J) ddA hψ hS dd hcod
  refine ⟨dd, omd, hD, ⟨isLagr_diagCols _ _, hspl, ?_⟩, ?_⟩
  · intro l _ hl p t hp φ hφ
    obtain ⟨r, hr, c₀, hc₀, μ, hμ, hint, -⟩ := GlobalTheory.DiagLocal.exists_local (ι := κ) v
    obtain ⟨c, hc⟩ := diag_eq_mul_integral (psiAt ψ v) (GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v)
      (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) l (fun x y f hf => by
        have := hl (co.e.symm (x, y)) f hf
        rwa [Darboux.rho, diag_mul, hD, LinearEquiv.apply_symm_apply] at this) μ hμ
    let tA : GL (Fin b) (AE F E) := Units.map (liftM v (Fin b)) t
    have hDm : (diagCols (Fin b) : Matrix (Fin b ⊕ Fin b) (Fin b) (AE F E)).map (compFin F E v) = diagCols (Fin b) := by
      rw [diagCols, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
    have hpA : ((liftU σ v (dbl_map v B.J) p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) * diagCols (Fin b) =
        diagCols (Fin b) * (tA : Matrix (Fin b) (Fin b) (AE F E)) :=
      liftM_mul_of v _ _ _ (by rw [hDm]; exact hp)
    obtain ⟨h1, h2, -⟩ := GlobalTheory.InertLagLevi.levi_det F E σ hσ b B.J hB v _ tA (liftM_at v _) hpA
    obtain ⟨s1, s2⟩ := scalar_eq χ v χv hχv (Matrix.GeneralLinearGroup.det tA) (Matrix.GeneralLinearGroup.det t)
      (((compFin F E v).map_det _).trans (congrArg Matrix.det (liftM_map v _))) h1 h2
    have key := hSieg _ GlobalTheory.DiagForm.lDiag_adm (fun z Φ hΦ => by
      rw [diag_mul, Darboux.rho, hdd z z]
      exact GlobalTheory.DiagForm.lDiag_schr ψ _ _ hΦ) _ tA hpA _ (hr φ hφ).2
    rw [hact p φ hφ r (hr φ hφ), hint _ (hspl.pres p φ hφ), hint φ hφ, s1, s2, mul_left_comm] at key
    rw [hc _ (hspl.pres p φ hφ), hc φ hφ, mul_left_cancel₀ hc₀ key, mul_left_comm]
  · intro g gd hg φ₁ h₁ φ₂ h₂
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
    have hg1 : liftM v (Fin b) (g : GL (Fin b) (Fv F v ⊗[F] E)) = mat (eB.symm g).1 := by
      have := heB.1 (eB.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]
      exact liftM_comp v _ (eB.symm g).2
    have hgA : ((liftU σ v (dbl_map v B.J) gd : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix (Fin b ⊕ Fin b) (Fin b ⊕ Fin b) (AE F E)) =
        Matrix.fromBlocks (mat (eB.symm g).1) 0 0 1 := by
      rw [liftU_val, hg, ← hg1, liftM_fromBlocks]
    have hrb := GlobalTheory.DblSwap.rest_box v (hR φ₁ h₁) (hR φ₂ h₂)
    refine GlobalTheory.DblSwap.eq_of_tens_ne v hrb.1 (x₀ := 0) (mul_ne_zero hR0 hR0) ?_
    rw [← hact gd _ (GlobalTheory.DblSwap.box_mem_SB h₁ h₂) _ hrb, GlobalTheory.DblSwap.tens_box, GlobalTheory.DblSwap.tens_box,
      hbox _ _ hgA _ (hR φ₁ h₁).2 _ (hR φ₂ h₂).2]
    exact congrArg (boxFun · _) ((homL g φ₁ h₁).2 R (hR φ₁ h₁))

end GlobalTheory.HoweLocal.DblLocal
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal

theorem hTens_transpose {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JB JA xᵀ yᵀ = hTens c JA JB x y := by
  simp only [hTens, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_transpose {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    symp c ξ JB JA xᵀ yᵀ = symp c ξ JA JB x y := by
  simp only [symp, hTens_transpose]

def dTr {R E : Type} [CommRing R] [Invertible (2 : R)] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (co : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans co.e
  form w w' := by
    rw [← symp_transpose c ξ JB JA w w', co.form]
    rfl

theorem dTr_e {R E : Type} [CommRing R] [Invertible (2 : R)] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (ξ : E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) {κ : Type} [Fintype κ]
    (co : Darboux (symp c ξ JA JB) κ) (y : Matrix β α E) : (dTr c ξ JA JB co).e y = co.e yᵀ := rfl

theorem weilX : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) →
      ∀ (eX : UAtGrp σ X (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J)),
        GlobalTheory.HoweLocal.IsCompIso σ X v eX →
      ∀ (eW : UAtGrp σ W (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v W.J)),
        GlobalTheory.HoweLocal.IsCompIso σ W v eW →
      ∀ (co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J))
        (Fin n × Fin d)), GlobalTheory.HoweLocal.IsLocCo σ M v co →
      ∀ χXv χWv : (Fv F v ⊗[F] E)ˣ →* Circle, GlobalTheory.HoweLocal.IsLocChr χX v χXv → GlobalTheory.HoweLocal.IsLocChr χW v χWv →
      ∃ d' : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v W.J) (GlobalTheory.HoweLocal.Jv v X.J))
        (Fin n × Fin d), (∀ x : Matrix (Fin n) (Fin d) (Fv F v ⊗[F] E), d'.e xᵀ = co.e x) ∧
        IsUWeilB (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1) (GlobalTheory.HoweLocal.Jv v W.J)
          (GlobalTheory.HoweLocal.Jv v X.J) d' χWv ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inl _ _)) := by
  intro hP F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hhX hhW hweil v hv _ om' hom' eX heX eW heW
    co hco χXv χWv hlX hlW
  obtain ⟨-, ⟨dA, hdA, hB⟩, -⟩ := hweil
  refine ⟨dTr _ _ _ _ co, fun x => by rw [dTr_e, Matrix.transpose_transpose], ?_⟩
  have hL : ∀ g, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inl _ _)) g φ ∈ SB _ ∧
      Acts (evFin F v) ((om.comp (MonoidHom.inl _ _)) (eX.symm g).1) φ
        (((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inl _ _)) g φ) := by
    intro g φ hφ
    have h := hom' (eX.symm g) 1 φ hφ
    simpa using h
  have hc : ∀ y, (dTr _ _ _ _ co).e y = GlobalTheory.LatVac.locCo dA v (y.map (GlobalTheory.HoweLocal.liftE v)) := by
    intro y
    rw [dTr_e, hco]
    have := hdA (yᵀ.map (GlobalTheory.HoweLocal.liftE v))
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [← this]
    rfl
  have hS := hB.1
  obtain ⟨dd, omd, h1, h2, h3⟩ := GlobalTheory.HoweLocal.DblLocal.exists_dbl_local F E σ hcm d n W.J X (Fin n × Fin d) dA ψ χW (om.comp (MonoidHom.inl _ _)) hstd hWd hXd
    hrW hhW hB v hv eX heX _ hL _ hc χWv hlW
  exact ⟨⟨⟨fun g φ hφ => (hL g φ hφ).1,
    GlobalTheory.HoweLocal.WeilImpl.impl_local F E σ d n W.J X (Fin n × Fin d) dA ψ (om.comp (MonoidHom.inl _ _)) hstd hS v hv eX heX _ hL _ hc,
    fun _ _ _ => Set.mem_univ _⟩,
    GlobalTheory.HoweLocal.LocUnitNonsplit.isUnitaryOn_local F E σ d n W.J X (Fin n × Fin d) dA ψ (om.comp (MonoidHom.inl _ _)) hstd hS v hv eX heX _ hL _ hc,
    GlobalTheory.HoweLocal.isContOn_locOps_member_nonsplit F E σ d n W.J X (Fin n × Fin d) dA ψ (om.comp (MonoidHom.inl _ _)) hstd hS v hv eX heX _ hL _ hc⟩,
    dd, omd, h1, h2, h3⟩

theorem weilW : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) →
      ∀ (eX : UAtGrp σ X (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J)),
        GlobalTheory.HoweLocal.IsCompIso σ X v eX →
      ∀ (eW : UAtGrp σ W (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v W.J)),
        GlobalTheory.HoweLocal.IsCompIso σ W v eW →
      ∀ (co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J))
        (Fin n × Fin d)), GlobalTheory.HoweLocal.IsLocCo σ M v co →
      ∀ χXv χWv : (Fv F v ⊗[F] E)ˣ →* Circle, GlobalTheory.HoweLocal.IsLocChr χX v χXv → GlobalTheory.HoweLocal.IsLocChr χW v χWv →
      IsUWeilB (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1) (GlobalTheory.HoweLocal.Jv v X.J)
        (GlobalTheory.HoweLocal.Jv v W.J) co χXv ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inr _ _)) := by
  intro hP F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hhX hhW hweil v hv _ om' hom' eX heX eW heW
    co hco χXv χWv hlX hlW
  obtain ⟨hB, -, -⟩ := hweil
  have hL : ∀ g, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inr _ _)) g φ ∈ SB _ ∧
      Acts (evFin F v) ((om.comp (MonoidHom.inr _ _)) (eW.symm g).1) φ
        (((om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (MonoidHom.inr _ _)) g φ) := by
    intro g φ hφ
    have h := hom' 1 (eW.symm g) φ hφ
    simpa using h
  have hS := hB.1
  obtain ⟨dd, omd, h1, h2, h3⟩ := GlobalTheory.HoweLocal.DblLocal.exists_dbl_local F E σ hcm n d X.J W (Fin n × Fin d) M.co ψ χX (om.comp (MonoidHom.inr _ _)) hstd
    hXd hWd hrX hhX hB v hv eW heW _ hL _ hco χXv hlX
  exact ⟨⟨⟨fun g φ hφ => (hL g φ hφ).1,
    GlobalTheory.HoweLocal.WeilImpl.impl_local F E σ n d X.J W (Fin n × Fin d) M.co ψ (om.comp (MonoidHom.inr _ _)) hstd hS v hv eW heW _ hL _ hco,
    fun _ _ _ => Set.mem_univ _⟩,
    GlobalTheory.HoweLocal.LocUnitNonsplit.isUnitaryOn_local F E σ n d X.J W (Fin n × Fin d) M.co ψ (om.comp (MonoidHom.inr _ _)) hstd hS v hv eW heW _ hL _ hco,
    GlobalTheory.HoweLocal.isContOn_locOps_member_nonsplit F E σ n d X.J W (Fin n × Fin d) M.co ψ (om.comp (MonoidHom.inr _ _)) hstd hS v hv eW heW _ hL _ hco⟩,
    dd, omd, h1, h2, h3⟩

theorem howeDualityFor_locOps : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) → GlobalTheory.Published.HoweDualityFor om' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom'
  have hinj : Function.Injective (algebraMap F (Fv F v)) := (algebraMap F (Fv F v)).injective
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap hinj
  letI : Invertible (2 : Fv F v) := invertibleOfNonzero two_ne_zero
  letI : Field (Fv F v ⊗[F] E) := (GlobalTheory.HoweLocal.Fld.isField_of_isEmpty F E σ hCM v hv).toField
  obtain ⟨δ, hδ⟩ := GlobalTheory.HoweLocal.quad_exists F E σ hCM v
  obtain ⟨eX, heX⟩ := GlobalTheory.HoweLocal.compIso_exists F E σ hCM n X v
  obtain ⟨eW, heW⟩ := GlobalTheory.HoweLocal.compIso_exists F E σ hCM d W v
  obtain ⟨co, hco⟩ := GlobalTheory.HoweLocal.exists_isLocCo F E σ hCM n d X W M v
  obtain ⟨χXv, hcX, hrXv, hlX⟩ := GlobalTheory.HoweLocal.exists_locChr_of_resEtaPow hP F E σ hCM n χX hhX hrX v hv
  obtain ⟨χWv, hcW, hrWv, hlW⟩ := GlobalTheory.HoweLocal.exists_locChr_of_resEtaPow hP F E σ hCM d χW hhW hrW v hv
  obtain ⟨hψc, hψn, hψ1⟩ := GlobalTheory.HoweLocal.Psi.psiAt_cont_norm_nontriv F ψ hψ v
  have hcv : ∀ x : E, GlobalTheory.HoweLocal.cv σ v (Algebra.TensorProduct.includeRight x) =
      Algebra.TensorProduct.includeRight (σ x) := fun x => by
    simp [GlobalTheory.HoweLocal.cv]
  have hdet : ∀ {m : ℕ} (J : Matrix (Fin m) (Fin m) E), (GlobalTheory.HoweLocal.Jv v J).det =
      Algebra.TensorProduct.includeRight (R := F) (A := Fv F v) J.det := fun J => by
    simp only [GlobalTheory.HoweLocal.Jv]
    exact (AlgHom.map_det _ J).symm
  have hiR : Function.Injective (Algebra.TensorProduct.includeRight (R := F) (A := Fv F v) (B := E)) :=
    Algebra.TensorProduct.includeRight_injective hinj
  have hHX : IsHerm (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v X.J) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [GlobalTheory.HoweLocal.Jv, Matrix.map_apply, hcv, hX]
    · rw [hdet]; exact (isUnit_iff_ne_zero.mpr hXd).map _
  have hWs : ∀ i j, GlobalTheory.HoweLocal.cv σ v ((-1) * GlobalTheory.HoweLocal.Jv v W.J j i) =
      -((-1) * GlobalTheory.HoweLocal.Jv v W.J i j) := fun i j => by
    simp only [GlobalTheory.HoweLocal.Jv, Matrix.map_apply, map_mul, map_neg, map_one, hcv, hW]
    ring
  have hWd' : (GlobalTheory.HoweLocal.Jv v W.J).det ≠ 0 := by
    rw [hdet]; intro h; exact hWd (hiR (h.trans (map_zero _).symm))
  have hWeil : IsUWeilPair (GlobalTheory.HoweLocal.cv σ v) (sbClass (Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) (-1)
      (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J) co χXv χWv
      (om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)) :=
    ⟨weilW hP F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom' eX heX eW heW co hco
        χXv χWv hlX hlW,
      weilX hP F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom' eX heX eW heW co hco
        χXv χWv hlX hlW,
      GlobalTheory.HoweLocal.isContOn_locOps_nonsplit hP F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv om' hom' eX heX eW heW co hco
        χXv χWv hlX hlW⟩
  have hHD' := (hHD (Fv F v) (Fv F v ⊗[F] E) (GlobalTheory.HoweLocal.cv σ v) δ hδ (GlobalTheory.LatVac.psiAt ψ v) hψc hψn hψ1 n d (-1)
    (GlobalTheory.HoweLocal.Jv v X.J) (GlobalTheory.HoweLocal.Jv v W.J) hHX (neg_ne_zero.mpr one_ne_zero) hWs hWd' χXv χWv hcX hcW
    hrXv hrWv (Fin n × Fin d) co _ hWeil).1
  have e : (om'.comp (eX.symm.toMonoidHom.prodMap eW.symm.toMonoidHom)).comp (eX.toMonoidHom.prodMap eW.toMonoidHom) = om' := by
    ext ⟨a, b⟩ : 1
    simp
  have := GlobalTheory.HoweLocal.HoweTransport.howeDualityFor_transport eX eW heX.2.1 heX.2.2 heW.2.1 heW.2.2 _ hHD'
  rwa [e] at this

theorem howeDualityFor_closure : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ om' : Subgroup.closure (UAt σ X (evFin F v)) × Subgroup.closure (UAt σ W (evFin F v)) →*
          Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) → GlobalTheory.Published.HoweDualityFor om' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  have key := howeDualityFor_locOps hP hHD F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  rw [closure_UAt σ X (evFin F v), closure_UAt σ W (evFin F v)]
  exact key

end GlobalTheory.HoweLocal
end
end
