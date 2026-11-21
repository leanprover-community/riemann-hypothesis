import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceSeesawWScalarFrame

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertPsi

open Formalism.UG GlobalTheory.LFun.InertChart GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_tmul (R : Type) [CommRing R] [Algebra F R] [Module.Free F E] [Module.Finite F E] (c : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (c ⊗ₜ[F] x) = c * algebraMap F R (Algebra.trace F E x) := by
  have h1 : c ⊗ₜ[F] x = c • ((1 : R) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, LinearMap.map_smul, smul_eq_mul]
  congr 1
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem trace_singleTens (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    Algebra.trace (AF F) (AF F ⊗[F] E) (Supp.singleTens E v y) =
      GlobalTheory.EmbChart.atPlace v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [show Supp.singleTens E v (a ⊗ₜ[F] x) = GlobalTheory.EmbChart.atPlace v a ⊗ₜ[F] x from
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ a x, trace_tmul, trace_tmul, mul_comm a, ← Algebra.smul_def,
      LinearMap.map_smul, Algebra.smul_def, mul_comm]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem trace_mem {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y ∈ v.adicCompletionIntegers F := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine intLoc_induction (p := fun y => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y ∈ v.adicCompletionIntegers F)
    (fun a ha x => ?_) (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
    (fun y hy => by rw [map_neg]; exact neg_mem hy) hy
  rw [trace_tmul]
  refine mul_mem ha ?_
  have hint : IsIntegral ℤ (Algebra.trace F E (x : E)) := Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe x)
  have := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v (⟨_, hint⟩ : 𝓞 F)
  convert this using 1
  first | rfl | simp | (exact (IsScalarTower.algebraMap_apply (𝓞 F) F (Fv F v) (⟨_, hint⟩ : 𝓞 F)))

theorem odd_absNorm {v : HeightOneSpectrum (𝓞 F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : Odd (Ideal.absNorm v.asIdeal) := by
  have hc : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ h0)
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  by_contra hodd
  have h1 : ringChar (𝓞 F ⧸ v.asIdeal) = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hc]
    exact Nat.even_iff.1 (Nat.not_odd_iff_even.1 hodd)
  have h3 : ((2 : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := (ringChar.spec _ 2).2 (by rw [h1])
  apply h2
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_ofNat]
  simpa using h3

end GlobalTheory.InertPsi

namespace GlobalTheory.InertPsi

open Formalism.UG GlobalTheory.LFun.InertChart GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {σ : E →ₐ[F] E}
  {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E}

theorem exists_unif (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) :
    ∃ s : F, IsUnramInv (complMap h (algebraMap F (Fv F v) s)) c (qV F v) := by
  have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  obtain ⟨s, hs, hs2⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.map_le_iff_le_comap.2 (not_map_le_sq hw))
  have hs1 : algebraMap (𝓞 F) (𝓞 E) s ∈ w.asIdeal := hw ▸ Ideal.mem_map_of_mem _ hs
  refine ⟨(s : F), ?_⟩
  have hϖ : complMap h (algebraMap F (Fv F v) (s : F)) =
      algebraMap E (w.adicCompletion E) (algebraMap (𝓞 F) (𝓞 E) s : E) := by
    rw [complMap_algebraMap]; rfl
  rw [hϖ]
  set ϖ : w.adicCompletion E := algebraMap E _ (algebraMap (𝓞 F) (𝓞 E) s : E) with hϖ'
  have h1 : c ϖ = ϖ := (conj_algebraMap hc _).trans (congrArg _ (σ.commutes (s : F)))
  have h2 : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [hϖ', hval, HeightOneSpectrum.valuation_of_algebraMap]
    have a := (w.intValuation_le_pow_iff_mem _ 1).2 (by rwa [pow_one])
    have b := not_le.1 (mt (w.intValuation_le_pow_iff_mem _ 2).1 hs2)
    have h0 : w.intValuation (algebraMap (𝓞 F) (𝓞 E) s) ≠ 0 := b.ne_bot
    rw [← WithZero.exp_log h0] at a b ⊢
    rw [WithZero.exp_le_exp] at a
    rw [WithZero.exp_lt_exp] at b
    congr 1
    omega
  have h3 : ∀ u, Valued.v u = 1 → Valued.v (c u) = 1 := fun u hu => by
    have a : Valued.v (c u) ≤ 1 := conj_mem hw hc hu.le
    have b : Valued.v (c u⁻¹) ≤ 1 := conj_mem hw hc (show Valued.v u⁻¹ ≤ 1 by rw [map_inv₀, hu, inv_one])
    have h0 : u ≠ 0 := fun h0 => by simp [h0] at hu
    rw [map_inv₀, map_inv₀, inv_le_one₀ (by simpa [pos_iff_ne_zero] using h0)] at b
    exact le_antisymm a b
  refine ⟨fun x => ?_, fun x => ?_, h1, h2, ?_, one_lt_absNorm v, ?_⟩
  · obtain ⟨y, rfl⟩ := toCompl_surjective h x
    rw [hc, hc]
    congr 1
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (conj_conj hσ x)
    | add x y hx hy => simp only [map_add, hx, hy]
  · by_cases h0 : x = 0
    · simp [h0]
    have h0' : Valued.v x ≠ 0 := by simpa using h0
    have a : Valued.v (x * ϖ ^ WithZero.log (Valued.v x)) = 1 := by
      rw [map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, ← WithZero.exp_log h0', ← WithZero.exp_add]
      simp
    have b := h3 _ a
    rw [map_mul, map_zpow₀, h1, ← a, map_mul, map_mul] at b
    exact mul_right_cancel₀ (by rw [map_zpow₀, h2]; exact zpow_ne_zero _ WithZero.exp_ne_zero) b
  · obtain ⟨x, hx⟩ := exists_conj_sub_unit hσ hw
    exact ⟨algebraMap E _ (x : E), GlobalTheory.AdeleBaseChange.algebraMap_int_mem x w, by
      rw [conj_algebraMap hc, ← map_sub, hval, hx]⟩
  · exact (P.tjcosets_card_residue w).trans (absNorm_eq hσ.2.2.1 hw)

end GlobalTheory.InertPsi

open GlobalTheory.InertPsi in
theorem GlobalTheory.InertPsi.exists_field_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v),
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (ψL : AddChar (w.adicCompletion E) ℂ),
      IsConjAt σ h σL ∧ Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
      (∀ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z → ψL z = 1) ∧
      (∃ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
      ∀ z, ψL ((z + σL z) / 2) = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (-1 * ptAt hw h z)) := by
  intro F E _ _ _ _ _ σ B hB v w hw h
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨c, hc, -⟩ := InertChart.existsUnique_isConjAt σ hw h
  obtain ⟨s, hU⟩ := exists_unif hB.cm hw hc
  obtain ⟨h2, -, hψ⟩ := hB.inert v w hw
  set k := evFin F v (⅟(2 : AF F)) with hk'
  have hk2 : k * 2 = 1 := by
    rw [hk', ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv2 : Valued.v (2 : Fv F v) = 1 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : F)).trans ?_
    rw [← map_ofNat (algebraMap (𝓞 F) F) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
  have hk : k ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have := congrArg Valued.v hk2
    rw [map_mul, hv2, mul_one, map_one] at this
    exact this.le
  have hO : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v y = 1 := fun y hy => by
    simpa using (hψ 1).2 (one_mem _) y hy
  let ψL : AddChar (w.adicCompletion E) ℂ :=
    { toFun := fun z => B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (-1 * ptAt hw h z))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by
        simp only [map_add, mul_add, AddChar.map_add_eq_mul] }
  have hval : ∀ z, ψL z = psiLoc B.ψ v
      (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((InertChart.complEquiv hw h).symm (-z)) * k) := fun z => by
    show B.ψ _ = _
    rw [neg_one_mul, ← map_neg (ptAt hw h), ptAt_apply, trace_singleTens, mul_comm,
      GlobalTheory.EmbChart.atPlace_mul_right]
    rfl
  have hcm : ∀ a : Fv F v, (InertChart.complEquiv hw h).symm (complMap h a) = a ⊗ₜ[F] (1 : E) := fun a =>
    (InertChart.complEquiv hw h).symm_apply_eq.2 (by
      show complMap h a = toCompl h (a ⊗ₜ[F] (1 : E))
      rw [toCompl_tmul, map_one, mul_one])
  have htr1 : algebraMap F (Fv F v) (Algebra.trace F E 1) = 2 := by
    rw [show (1 : E) = algebraMap F E 1 from (map_one _).symm, Algebra.trace_algebraMap, hB.cm.2.2.1]
    first | simp [map_ofNat] | (simp; exact map_ofNat _ 2) | (rw [nsmul_eq_mul, mul_one, Nat.cast_ofNat, map_ofNat])
  have hvalc : ∀ a, ψL (complMap h a) = psiLoc B.ψ v (-a) := fun a => by
    rw [hval, ← map_neg, hcm, trace_tmul, htr1, mul_assoc, mul_comm 2 k, hk2, mul_one]
  refine ⟨complMap h (algebraMap F (Fv F v) s), c, Formalism.UG.qV F v, ψL, hc, hU, odd_absNorm h2, ?_, ?_, ?_⟩
  · intro z hz _
    rw [hval]
    refine hO _ (mul_mem (trace_mem ((InertChart.mem_intLoc_iff hw h _).2 ?_)) hk)
    rw [show toCompl h ((InertChart.complEquiv hw h).symm (-z)) = -z from
      (InertChart.complEquiv hw h).apply_symm_apply (-z)]
    exact neg_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hz)
  · have hs : (algebraMap F (Fv F v) s)⁻¹ ∉ v.adicCompletionIntegers F := fun hm => by
      have h4 := complMap_mem h hm
      have h5 : Valued.v (complMap h (algebraMap F (Fv F v) s))⁻¹ ≤ 1 := by
        rw [← map_inv₀]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h4
      rw [map_inv₀, hU.2.2.2.1] at h5
      exact absurd h5 (by decide)
    obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F,
        psiLoc B.ψ v ((algebraMap F (Fv F v) s)⁻¹ * y) ≠ 1 := by
      have := mt (hψ _).1 hs
      push_neg at this
      exact this
    have ht : ∀ a, toCompl h (a ⊗ₜ[F] (1 : E)) = complMap h a := fun a => by
      rw [toCompl_tmul, map_one, mul_one]
    refine ⟨complMap h (-y), (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (complMap_mem h (neg_mem hy)),
      ?_, ?_⟩
    · rw [← ht, hc]
      congr 1
      show (-y) ⊗ₜ[F] σ 1 = _
      rw [map_one]
    · rw [← map_inv₀, ← map_mul, hvalc]
      convert hne using 2
      ring
  · intro z
    show B.ψ _ = B.ψ _
    have hcc : ∀ x, cA σ (cA σ x) = x := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (InertChart.conj_conj hB.cm x)
      | add x y hx hy => simp only [map_add, hx, hy]
    let cE : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
    have hT : ∀ x, Algebra.trace (AF F) (AE F E) (cA σ x) = Algebra.trace (AF F) (AE F E) x := fun x =>
      Algebra.trace_eq_of_algEquiv cE x
    haveI : NeZero (2 : w.adicCompletion E) := ⟨fun h0 => two_ne_zero ((map_eq_zero_iff _ (algebraMap E (w.adicCompletion E)).injective).1 ((map_ofNat _ 2).trans h0))⟩
    set y := (z + c z) / 2
    have hy : y + y = z + c z := add_halves _
    have key : Algebra.trace (AF F) (AE F E) (ptAt hw h y) = Algebra.trace (AF F) (AE F E) (ptAt hw h z) := by
      have e1 : Algebra.trace (AF F) (AE F E) (ptAt hw h y) + Algebra.trace (AF F) (AE F E) (ptAt hw h y) =
          Algebra.trace (AF F) (AE F E) (ptAt hw h z) + Algebra.trace (AF F) (AE F E) (ptAt hw h z) := by
        rw [← map_add, ← map_add (ptAt hw h), hy, map_add, map_add, ← cA_ptAt hw h σ hc, hT]
      have e2 : ∀ t : AF F, t = ⅟(2 : AF F) * (t + t) := fun t => by
        rw [← two_mul, ← mul_assoc, invOf_mul_self, one_mul]
      rw [e2 (Algebra.trace _ _ (ptAt hw h y)), e1, ← e2]
    rw [neg_one_mul, neg_one_mul, map_neg, map_neg, key]
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_localField_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v),
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (ψL : AddChar (w.adicCompletion E) ℂ),
      IsConjAt σ h σL ∧ Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
      (∀ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z → ψL z = 1) ∧
      (∃ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
      ∀ z, ψL ((z + σL z) / 2) = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (-1 * ptAt hw h z)) := by
  atlas_forward_decl GlobalTheory.InertPsi.exists_field_data
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertUnitFrame

theorem exists_frame_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ A : GL (Fin a') (w.adicCompletion E), IsFrameAt w G.V'.L A ∧
      (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ * G.V'.J.map (algebraMap E (w.adicCompletion E)) *
        (A : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := by
  intro F E _ _ _ _ _ σ B a a' G hB hG v w hw h σL hc
  have hX := hG.hV'
  have hd : (G.V'.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  have hJ : IsHermND σ G.V'.Jᵀ :=
    ⟨fun i j => by simp only [Matrix.transpose_apply]; exact hX.herm j i, hd⟩
  have hs : IsSelfDualAt σ G.V'.Jᵀ G.V'.L v :=
    GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B a' G.V' _ _ hB hX v
  obtain ⟨f, hf, ef⟩ := InertChart.exists_frame_antiJ hB.cm hJ hX.lat.fg hX.lat.span_eq_top hw hc hs
  obtain ⟨ϖ, hU⟩ := InertChart.exists_isUnramInv hB.cm hw hc
  obtain ⟨k, hk, ek⟩ := InertChart.exists_congr_antiJ hU (B := 1) (one_mem _) (by exact Formalism.UG.cT_one _)
  refine ⟨f * k⁻¹, (InertChart.isFrameAt_mul hf (inv_mem hk)).1, ?_⟩
  have key : Formalism.UG.cT σL (f * k⁻¹).1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * (f * k⁻¹).1 = 1 := by
    rw [Units.val_mul, Formalism.UG.cT_mul, Units.val_one, Matrix.mul_one] at *
    calc Formalism.UG.cT σL (k⁻¹).1 * Formalism.UG.cT σL f.1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * (f.1 * (k⁻¹).1)
        = Formalism.UG.cT σL (k⁻¹).1 * (Formalism.UG.cT σL f.1 * (G.V'.Jᵀ).map (algebraMap E (w.adicCompletion E)) * f.1) * (k⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σL (k⁻¹).1 * Formalism.UG.cT σL k.1 * (k.1 * (k⁻¹).1) := by
          rw [ef, ← ek]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [← Formalism.UG.cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Formalism.UG.cT_one, Matrix.one_mul]
  have := congrArg Matrix.transpose key
  simpa [Formalism.UG.cT, Matrix.transpose_mul, Matrix.transpose_map, Matrix.mul_assoc] using this

end GlobalTheory.InertUnitFrame
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_orthonormal_selfDual_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ A : GL (Fin a') (w.adicCompletion E), IsFrameAt w G.V'.L A ∧
      (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ * G.V'.J.map (algebraMap E (w.adicCompletion E)) *
        (A : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := by
  atlas_forward_decl GlobalTheory.InertUnitFrame.exists_frame_one
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_conjTranspose_mul_eq_smul_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v) (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∃ (δ : w.adicCompletion E) (Bm : GL (Fin (a + a')) (w.adicCompletion E)), Valued.v δ = 1 ∧ σL δ = -δ ∧
      IsFrameAt w G.W.L Bm ∧
      (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E))ᵀ * G.W.J.map (algebraMap E (w.adicCompletion E)) *
        (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)).map σL = δ • 1 := by
  first | exact @GlobalTheory.SkewFrameInert.exists_inertPlace_seesawW_scalar_frame | exact GlobalTheory.SkewFrameInert.exists_inertPlace_seesawW_scalar_frame | (intros; apply GlobalTheory.SkewFrameInert.exists_inertPlace_seesawW_scalar_frame <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.InertTens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem quadruple_sum_eq_trace_transpose_mul {L : Type} [CommRing L] {m n : ℕ} (P : Matrix (Fin m) (Fin n) L) (J : Matrix (Fin m) (Fin m) L)
    (K : Matrix (Fin n) (Fin n) L) (Q : Matrix (Fin m) (Fin n) L) :
    ∑ i, ∑ j, ∑ k, ∑ l, P i j * J i k * K j l * Q k l = (Pᵀ * J * Q * Kᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem trace_orth {L : Type} [Field L] (σL : L →+* L) {m n : ℕ} (J : Matrix (Fin m) (Fin m) L) (K : Matrix (Fin n) (Fin n) L)
    (A : Matrix (Fin m) (Fin m) L) (Bm : Matrix (Fin n) (Fin n) L) (δ : L)
    (hA : Aᵀ * J * A.map σL = 1) (hB : Bmᵀ * K * Bm.map σL = δ • 1) (x y : Matrix (Fin n) (Fin m) L) :
    ((A * xᵀ * Bmᵀ)ᵀ * J * (A * yᵀ * Bmᵀ).map σL * Kᵀ).trace = δ * ((y.map σL)ᵀ * x).trace := by
  have e1 : (A * yᵀ * Bmᵀ).map σL = A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
  have e2 : (Bm.map σL)ᵀ * Kᵀ * Bm = δ • 1 := by
    have := congrArg Matrix.transpose hB
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [e1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have e3 : Bm * (x * Aᵀ) * J * (A.map σL * (y.map σL)ᵀ * (Bm.map σL)ᵀ) * Kᵀ
      = Bm * (x * (Aᵀ * J * A.map σL) * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ)) := by
    simp only [Matrix.mul_assoc]
  rw [e3, hA, Matrix.trace_mul_comm, Matrix.mul_one]
  have e4 : x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ) * Bm = x * (y.map σL)ᵀ * ((Bm.map σL)ᵀ * Kᵀ * Bm) := by
    simp only [Matrix.mul_assoc]
  rw [e4, e2, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem hTens_kap (σ : E →ₐ[F] E) {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (h : w.under (𝓞 F) = v) {σL : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h σL)
    {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (x y : Matrix (Fin n) (Fin m) (w.adicCompletion E)) :
    hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
      ptAt hw h (∑ i, ∑ j, ∑ k, ∑ l, (A * xᵀ * Bmᵀ) i j * JA.map (algebraMap E (w.adicCompletion E)) i k *
        JB.map (algebraMap E (w.adicCompletion E)) j l * (A * yᵀ * Bmᵀ).map σL k l) := by
  have hr : ∀ (a : E) (z : w.adicCompletion E),
      ptAt hw h z * inclR (F := F) (AF F) a = ptAt hw h (z * algebraMap E (w.adicCompletion E) a) := by
    intro a z
    rw [mul_comm, inclR_mul_ptAt, mul_comm]
  simp only [hTens, incM, kap_apply, Matrix.map_apply, cA_ptAt hw h σ hc, hr, ← map_mul, map_sum]

end GlobalTheory.InertTens

namespace GlobalTheory.InertTens

theorem hTens_kap_eq_locH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin m) (Fin m) (w.adicCompletion E))
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      Aᵀ * JA.map (algebraMap E (w.adicCompletion E)) * A.map σL = 1 →
      Bmᵀ * JB.map (algebraMap E (w.adicCompletion E)) * Bm.map σL = δ • 1 →
      ∀ x y, hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
        ptAt hw h (GlobalTheory.Hk3.locH σL δ (1 : GL (Fin m) (w.adicCompletion E)) (1 : GL (Fin n) (w.adicCompletion E)) x y) := by
  intro F E _ _ _ _ _ σ v w hw h σL hc m n JA JB A Bm δ hA hB x y
  rw [hTens_kap σ hw h hc, quadruple_sum_eq_trace_transpose_mul, trace_orth σL _ _ A Bm δ hA hB x y]
  congr 1
  simp [GlobalTheory.Hk3.locH]

end GlobalTheory.InertTens
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorHermitianForm_inertPoint_eq_localForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin m) (Fin m) (w.adicCompletion E))
      (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      Aᵀ * JA.map (algebraMap E (w.adicCompletion E)) * A.map σL = 1 →
      Bmᵀ * JB.map (algebraMap E (w.adicCompletion E)) * Bm.map σL = δ • 1 →
      ∀ x y, hTens (cA σ) (incM F JA) (incM F JB) (kap hw h A Bm x) (kap hw h A Bm y) =
        ptAt hw h (GlobalTheory.Hk3.locH σL δ (1 : GL (Fin m) (w.adicCompletion E)) (1 : GL (Fin n) (w.adicCompletion E)) x y) := by
  atlas_forward_decl GlobalTheory.InertTens.hTens_kap_eq_locH
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoord

theorem kap_at_and_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (AE F E), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  intro F E _ _ _ _ _ v w hw h m n A Bm
  refine ⟨fun x u hu => ?_, fun γ hγ => ?_⟩
  · ext i j
    rw [Matrix.smul_apply, kap_apply, Matrix.map_apply, Matrix.zero_apply]
    exact at_ptAt hw h _ u hu
  · refine ⟨(((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ))ᵀ, ?_⟩
    rw [kap_apply, Matrix.transpose_transpose]
    have e : (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *
        (((A⁻¹ : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) * γ.map (locW h) *
        ((((Bm⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ)) *
        (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = γ.map (locW h) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    rw [e]
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply]
    refine ptAt_locW hw h fun u hu => ?_
    have := congrFun (congrFun (hγ u hu) i) j
    rwa [Matrix.smul_apply, Matrix.zero_apply] at this

end GlobalTheory.InertCoord
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlacePoint_supported_and_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {m n : ℕ}
    (A : GL (Fin m) (w.adicCompletion E)) (Bm : GL (Fin n) (w.adicCompletion E)),
    (∀ x, At (evFin F v) (kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x)) ∧
    ∀ γ : Matrix (Fin m) (Fin n) (AE F E), At (evFin F v) γ →
      ∃ x, kap hw h (A : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (Bm : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x = γ := by
  atlas_forward_decl GlobalTheory.InertCoord.kap_at_and_onto
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem ptAt_complMap (b : Fv F v) : ptAt hw h (complMap h b) = GlobalTheory.LatVac.liftV v b • (1 : AE F E) := by
  have hat : At (evFin F v) (GlobalTheory.LatVac.liftV v b • (1 : AE F E)) := by
    intro u hu
    rw [smul_smul, ← smul_eq_mul, GlobalTheory.LatVac.at_liftV v b u hu, zero_smul]
  rw [← ptAt_locW hw h hat]
  congr 1
  change complMap h b = toCompl h (compFin F E v (GlobalTheory.LatVac.liftV v b • (1 : AE F E)))
  rw [GlobalTheory.ThK.compFin_smul, map_one, GlobalTheory.LatVac.evFin_liftV, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul',
    toCompl_tmul, smul_eq_mul, mul_one, map_one, mul_one]

theorem locW_smul_inclR (a : AF F) (e : E) :
    locW h (a • inclR (F := F) (AF F) e) = complMap h (evFin F v a) * algebraMap E _ e := by
  change toCompl h (compFin F E v (a • ((1 : AF F) ⊗ₜ[F] e))) = _
  rw [GlobalTheory.ThK.compFin_smul, GlobalTheory.AdelicU.Supp.compFin_one_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, toCompl_tmul]

theorem mul_vecMulVec_mul {R : Type} [CommRing R] {m k : ℕ} (M : Matrix (Fin m) (Fin m) R) (N : Matrix (Fin k) (Fin k) R)
    (p : Fin m → R) (q : Fin k → R) : M * Matrix.vecMulVec p q * Nᵀ = Matrix.vecMulVec (M *ᵥ p) (N *ᵥ q) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mul_transpose_mul_eq_sum {R : Type} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin k) (Fin k) R) (x : Matrix (Fin k) (Fin m) R) :
    A * xᵀ * Bᵀ = ∑ i, ∑ j, x j i • Matrix.vecMulVec (Aᵀ i) (Bᵀ j) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)

theorem smul_mem_latAtV {t : w.adicCompletion E} (ht : t ∈ Formalism.UG.Ov E w) {γ : Matrix (Fin n) (Fin d) (AE F E)}
    (hγ : γ ∈ latAtV X Y v) : ptAt hw h t • γ ∈ latAtV X Y v := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective h t
  have hy := (InertChart.mem_intLoc_iff hw h y).2 ht
  refine intLoc_induction (p := fun y => ∀ γ ∈ latAtV X Y v, ptAt hw h (toCompl h y) • γ ∈ latAtV X Y v)
    ?_ ?_ ?_ ?_ hy γ hγ
  · intro a ha o γ hγ
    rw [toCompl_tmul, mul_comm, ← inclR_mul_ptAt, ptAt_complMap]
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a', ha', hv, x, hx, y, hy, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * a', ?_, ?_, (o • x), X.L.smul_mem o hx, y, hy, ?_⟩
      · intro u hu
        rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a', ha' u hu, mul_zero]
      · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
        exact mul_mem ha hv
      · ext k l
        simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        rw [show algebraMap (𝓞 E) E o = (o : E) from rfl]
        ring
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro γ hγ; rw [map_zero, map_zero, zero_smul]; exact zero_mem _
  · intro y z hy hz γ hγ; rw [map_add, map_add, add_smul]; exact add_mem (hy γ hγ) (hz γ hγ)
  · intro y hy γ hγ; rw [map_neg, map_neg, neg_smul]; exact neg_mem (hy γ hγ)

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
  {n d : ℕ} (X : Spc F E n) (Y : Spc F E d)

theorem ptAt_algebraMap (e : E) :
    ptAt hw h (algebraMap E (w.adicCompletion E) e) = GlobalTheory.LatVac.liftV v 1 • inclR (F := F) (AF F) e := by
  have := inclR_mul_ptAt hw h e 1
  rw [mul_one, ← (complMap h).map_one, ptAt_complMap, mul_smul_comm, mul_one] at this
  exact this.symm

theorem vecMulVec_mem {p : Fin n → w.adicCompletion E} (hp : p ∈ latAt w X.L) {q : Fin d → w.adicCompletion E}
    (hq : q ∈ latAt w Y.L) : (Matrix.vecMulVec p q).map (ptAt hw h) ∈ latAtV X Y v := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨x, hx, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨y, hy, rfl⟩ := hq
      refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1, GlobalTheory.LatVac.at_liftV v 1, ?_, x, hx, y, hy, ?_⟩
      · rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _
      · ext k l
        simp only [incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, ← map_mul, ptAt_algebraMap]
    | zero =>
      convert zero_mem (latAtV X Y v) using 1
      ext k l; simp [Matrix.vecMulVec_apply]
    | add q q' _ _ h1 h2 =>
      convert add_mem h1 h2 using 1
      ext k l; simp [Matrix.vecMulVec_apply, mul_add]
    | smul t q _ h1 =>
      convert smul_mem_latAtV hw h X Y t.2 h1 using 1
      ext k l
      simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]
      congr 1
      rw [Subring.smul_def, smul_eq_mul]
      ring
  | zero =>
    convert zero_mem (latAtV X Y v) using 1
    ext k l; simp [Matrix.vecMulVec_apply]
  | add p p' _ _ h1 h2 =>
    convert add_mem h1 h2 using 1
    ext k l; simp [Matrix.vecMulVec_apply, add_mul]
  | smul t p _ h1 =>
    convert smul_mem_latAtV hw h X Y t.2 h1 using 1
    ext k l
    simp only [Matrix.map_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, ← map_mul]
    congr 1
    rw [Subring.smul_def, smul_eq_mul]
    ring

end GlobalTheory.InertLat

namespace GlobalTheory.InertLat

open GlobalTheory.InertCoord in

theorem kap_mem_latAtV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E)),
    IsFrameAt w X.L A → IsFrameAt w Y.L Bm → ∀ x,
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion E)) ↔
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x ∈ latAtV X Y v := by
  intro F E _ _ _ _ _ v w hw h n d X Y A Bm hA hB x
  have col : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)},
      IsFrameAt w L C → ∀ i, (C : Matrix (Fin m) (Fin m) (w.adicCompletion E))ᵀ i ∈ latAt w L := by
    intro m L C hC i
    have := (hC (Pi.single i 1)).1 fun k => by
      by_cases e : k = i
      · subst e; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne e]; exact zero_mem _
    rwa [Matrix.mulVec_single_one] at this
  have inv : ∀ {m : ℕ} {L : Submodule (𝓞 E) (Fin m → E)} {C : GL (Fin m) (w.adicCompletion E)},
      IsFrameAt w L C → ∀ z ∈ L, ∀ k, ((↑C⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ
        fun i => algebraMap E (w.adicCompletion E) (z i)) k ∈ Formalism.UG.Ov E w := by
    intro m L C hC z hz
    refine (hC _).2 ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  constructor
  · intro hx
    rw [kap_apply, mul_transpose_mul_eq_sum]
    change _ ∈ (latAtV X Y v).comap (AddMonoidHom.mapMatrix (ptAt hw h).toAddMonoidHom)
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    change (x j i • Matrix.vecMulVec _ _).map (ptAt hw h) ∈ latAtV X Y v
    convert smul_mem_latAtV hw h X Y (hx j i) (vecMulVec_mem hw h X Y (col hA i) (col hB j)) using 1
    ext k l
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  · intro hk i j
    let Ψ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (w.adicCompletion E) := fun γ =>
      (↑A⁻¹ : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * AddMonoidHom.mapMatrix (locW h).toAddMonoidHom γ *
        (↑Bm⁻¹ : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ
    have hΨ : ∀ γ ∈ latAtV X Y v, ∀ k l, Ψ γ k l ∈ Formalism.UG.Ov E w := by
      intro γ hγ
      induction hγ using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, -, ha, p, hp, q, hq, rfl⟩ := hz
        have e1 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (a • incM F (Matrix.vecMulVec p q)) =
            complMap h (evFin F v a) • Matrix.vecMulVec (fun i => algebraMap E (w.adicCompletion E) (p i))
              (fun i => algebraMap E (w.adicCompletion E) (q i)) := by
          refine Matrix.ext fun k l => ?_
          change locW h (a • inclR (F := F) (AF F) (p k * q l)) = _
          rw [locW_smul_inclR, map_mul]
          simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
        intro k l
        simp only [Ψ, e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul, Matrix.smul_apply,
          Matrix.vecMulVec_apply, smul_eq_mul]
        exact mul_mem (complMap_mem h ha) (mul_mem (inv hA p hp k) (inv hB q hq l))
      | zero => intro k l; simp [Ψ]
      | add x y _ _ hx hy =>
        intro k l
        simp only [Ψ, map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        exact add_mem (hx k l) (hy k l)
      | neg x _ hx =>
        intro k l
        simp only [Ψ, map_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
        exact neg_mem (hx k l)
    have e : Ψ (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) = xᵀ := by
      have e2 : AddMonoidHom.mapMatrix (locW h).toAddMonoidHom (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
          (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
          (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ := by
        refine Matrix.ext fun k l => ?_
        simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, kap_apply, RingHom.toAddMonoidHom_eq_coe,
          AddMonoidHom.coe_coe, locW_ptAt]
      simp only [Ψ, e2]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    have := hΨ _ hk j i
    rw [e] at this
    exact this

end GlobalTheory.InertLat
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPoint_mem_tensorLattice_iff_integral_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E)),
    IsFrameAt w X.L A → IsFrameAt w Y.L Bm → ∀ x,
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion E)) ↔
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x ∈ latAtV X Y v := by
  atlas_forward_decl GlobalTheory.InertLat.kap_mem_latAtV_iff
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCoordAct

theorem at_mul_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (a : AE F E) {z : AE F E} (hz : At (evFin F v) z) : At (evFin F v) (a * z) := fun u hu => by
  rw [← mul_smul_comm, hz u hu, mul_zero]

theorem at_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (a : AE F E) {z : AE F E} (hz : At (evFin F v) z) : At (evFin F v) (z * a) := fun u hu => by
  rw [← smul_mul_assoc, hz u hu, zero_mul]

theorem at_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    {ι : Type} (s : Finset ι) (f : ι → AE F E) (hf : ∀ i, At (evFin F v) (f i)) :
    At (evFin F v) (∑ i ∈ s, f i) := fun u hu => by
  rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun i _ => hf i u hu

theorem act_kap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  intro F E _ _ _ _ _ σ v w hw h n d X Y A Bm g₁ g₂ _ _ x
  set P : Matrix (Fin n) (Fin d) (w.adicCompletion E) := (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * xᵀ * (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))ᵀ with hP
  have hK : kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x = P.map (ptAt hw h) := kap_apply hw h _ _ x
  have hmm : (P.map (ptAt hw h)).map (locW h) = P := by
    rw [Matrix.map_map]; exact Matrix.ext fun i j => locW_ptAt hw h _
  rw [hK, kap_apply]
  simp only [actAB]
  change mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ = _
  have hat : ∀ i j, At (evFin F v) ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ) i j) := fun i j => by
    simp only [Matrix.mul_apply]
    refine at_sum _ _ fun k => at_mul_right _ (at_sum _ _ fun l => at_mul_left _ (at_ptAt hw h _))
  have e1 : mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ =
      ((mat g₁ * P.map (ptAt hw h) * (mat g₂)ᵀ).map (locW h)).map (ptAt hw h) := by
    exact Matrix.ext fun i j => (ptAt_locW hw h (hat i j)).symm
  rw [e1]
  congr 1
  rw [Matrix.map_mul, Matrix.map_mul, hmm, Matrix.transpose_map, hP]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hB : (((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ *
      ((Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)))ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have hA : (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hB, Matrix.mul_one, ← Matrix.mul_assoc (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)), hA, Matrix.one_mul]

end GlobalTheory.InertCoordAct
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_action_on_tensorCoords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E))
    (g₁ : UA σ X.J) (g₂ : UA σ Y.J), g₁ ∈ UAt σ X (evFin F v) → g₂ ∈ UAt σ Y (evFin F v) → ∀ x,
      actAB (cA σ) (g₁, g₂) (kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x) =
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))
          ((((Bm⁻¹ : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) * (mat g₂).map (locW h) *
              (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E))) * x *
            (((A⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (mat g₁).map (locW h) *
              (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)))ᵀ) := by
  atlas_forward_decl GlobalTheory.InertCoordAct.act_kap
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem map_mul_nu {R S : Type} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S)
    {l m k : ℕ} (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin k) R) :
    (A * B).map f = A.map f * B.map f := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

def blow {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (AE F E) :=
  1 + (A - 1).map (ptAt hw h)

theorem blow_one {n : ℕ} : blow hw h (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := by
  simp [blow, Matrix.map_zero _ (map_zero (ptAt hw h))]

theorem blow_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    blow hw h (A * B) = blow hw h A * blow hw h B := by
  have e : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  simp only [blow, e, Matrix.map_add _ (map_add (ptAt hw h)), map_mul_nu]
  noncomm_ring

def blowHom (n : ℕ) : Matrix (Fin n) (Fin n) (w.adicCompletion E) →* Matrix (Fin n) (Fin n) (AE F E) where
  toFun := blow hw h
  map_one' := blow_one hw h
  map_mul' := blow_mul hw h

theorem blow_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    (blow hw h A)ᵀ = blow hw h Aᵀ := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [blow]
  · simp [blow, Matrix.one_apply, hij, Ne.symm hij]

theorem blow_map_cA (σ : E →ₐ[F] E) {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : (blow hw h A).map (cA σ) = blow hw h (A.map c) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [blow, cA_ptAt hw h σ hc]
  · simp [blow, Matrix.one_apply, hij, cA_ptAt hw h σ hc]

theorem map_pt_mul_incM {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (J : Matrix (Fin n) (Fin n) E) :
    A.map (ptAt hw h) * incM F J = (A * J.map (algebraMap E _)).map (ptAt hw h) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, incM, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, inclR_mul_ptAt, mul_comm]

theorem incM_mul_map_pt {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (J : Matrix (Fin n) (Fin n) E) :
    incM F J * A.map (ptAt hw h) = (J.map (algebraMap E _) * A).map (ptAt hw h) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, incM, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inclR_mul_ptAt]

theorem blow_form {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (A B : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hAB : Aᵀ * J.map (algebraMap E _) * B = J.map (algebraMap E _)) :
    (blow hw h A)ᵀ * incM F J * blow hw h B = incM F J := by
  rw [blow_transpose]
  set Ja := J.map (algebraMap E (w.adicCompletion E))
  have e : (Aᵀ - 1) * Ja + Ja * (B - 1) + (Aᵀ - 1) * Ja * (B - 1) = 0 := by
    have : (Aᵀ - 1) * Ja + Ja * (B - 1) + (Aᵀ - 1) * Ja * (B - 1) = Aᵀ * Ja * B - Ja := by noncomm_ring
    rw [this, hAB, sub_self]
  have e2 : (blow hw h Aᵀ) * incM F J * blow hw h B = incM F J +
      (((Aᵀ - 1) * Ja + Ja * (B - 1) + (Aᵀ - 1) * Ja * (B - 1)).map (ptAt hw h)) := by
    rw [Matrix.map_add _ (map_add (ptAt hw h)), Matrix.map_add _ (map_add (ptAt hw h)), map_mul_nu _ ((Aᵀ - 1) * Ja),
      ← map_pt_mul_incM, ← incM_mul_map_pt]
    simp only [blow]
    noncomm_ring
  rw [e2, e, Matrix.map_zero _ (map_zero (ptAt hw h)), add_zero]

theorem blow_mulVec_pt {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (ζ : Fin n → w.adicCompletion E) :
    blow hw h A *ᵥ (fun i => ptAt hw h (ζ i)) = fun i => ptAt hw h ((A *ᵥ ζ) i) := by
  have e1 : (A - 1).map (ptAt hw h) *ᵥ (fun i => ptAt hw h (ζ i)) = fun i => ptAt hw h (((A - 1) *ᵥ ζ) i) := by
    ext i; simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  rw [blow, Matrix.add_mulVec, Matrix.one_mulVec, e1]
  ext i
  rw [Pi.add_apply, ← map_add, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, add_sub_cancel]

theorem pt_mem_latAt {n : ℕ} (X : Spc F E n) {x : Fin n → w.adicCompletion E} (hx : x ∈ GlobalTheory.LFun.latAt w X.L) :
    (fun i => ptAt hw h (x i)) ∈ GlobalTheory.InertSph.latAt X v := by
  suffices H : ∀ c : Formalism.UG.Ov E w, (fun i => ptAt hw h ((c • x) i)) ∈ GlobalTheory.InertSph.latAt X v by
    simpa using H 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro c
    obtain ⟨t, ht⟩ := (InertChart.complEquiv hw h).surjective (c : w.adicCompletion E)
    have htI : t ∈ intLoc F E v := (InertChart.mem_intLoc_iff hw h t).2 (by
      rw [show toCompl h t = c from ht]; exact c.2)
    have key : ∀ t ∈ intLoc F E v,
        (fun i => ptAt hw h (toCompl h t * algebraMap E (w.adicCompletion E) (y i))) ∈ GlobalTheory.InertSph.latAt X v := by
      intro s hs
      have hs' : s ∈ AddSubgroup.closure
          {z | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, z = a ⊗ₜ[F] (x : E)} := hs
      clear hs
      induction hs' using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, e, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a,
          by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, e • y, X.L.smul_mem e hy, ?_⟩
        funext i
        rw [Pi.smul_apply, ptAt_apply]
        have e2 : toCompl h (a ⊗ₜ[F] (e : E)) * algebraMap E (w.adicCompletion E) (y i) =
            toCompl h (a ⊗ₜ[F] ((e : E) * y i)) := by
          rw [toCompl_tmul, toCompl_tmul, map_mul, mul_assoc]
        rw [e2, show toCompl h (a ⊗ₜ[F] ((e : E) * y i)) = InertChart.complEquiv hw h (a ⊗ₜ[F] ((e : E) * y i)) from rfl,
          RingEquiv.symm_apply_apply]
        show _ = GlobalTheory.LatVac.liftV v a • ((1 : AF F) ⊗ₜ[F] _)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rfl
      | zero => simp only [map_zero, zero_mul]; exact zero_mem _
      | add a b _ _ ha hb =>
        have e3 : (fun i => ptAt hw h (toCompl h (a + b) * algebraMap E (w.adicCompletion E) (y i))) =
            (fun i => ptAt hw h (toCompl h a * algebraMap E (w.adicCompletion E) (y i))) +
              (fun i => ptAt hw h (toCompl h b * algebraMap E (w.adicCompletion E) (y i))) := by
          funext i; simp [add_mul]
        rw [e3]; exact add_mem ha hb
      | neg a _ ha =>
        have e3 : (fun i => ptAt hw h (toCompl h (-a) * algebraMap E (w.adicCompletion E) (y i))) =
            -(fun i => ptAt hw h (toCompl h a * algebraMap E (w.adicCompletion E) (y i))) := by
          funext i; simp [neg_mul]
        rw [e3]; exact neg_mem ha
    convert key t htI using 2 with i
    show ptAt hw h ((c : w.adicCompletion E) * _) = _
    rw [← ht]; rfl
  | zero => intro c; simp only [smul_zero, Pi.zero_apply, map_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    intro c
    convert add_mem (hx c) (hy c) using 1
    funext i; simp [smul_add]
  | smul a x _ hx =>
    intro c
    convert hx (c * a) using 1
    funext i; rw [mul_smul]

theorem blow_mulVec_mem {n : ℕ} (X : Spc F E n) (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hA : ∀ x ∈ GlobalTheory.LFun.latAt w X.L, A *ᵥ x ∈ GlobalTheory.LFun.latAt w X.L) :
    ∀ z ∈ GlobalTheory.InertSph.latAt X v, blow hw h A *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
    have hat : ∀ i, At (evFin F v) ((a • fun i => inclR (F := F) (AF F) (y i)) i) := fun i u hu => by
      rw [Pi.smul_apply, smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
    have hz : (a • fun i => inclR (F := F) (AF F) (y i)) =
        fun i => ptAt hw h (locW h ((a • fun i => inclR (F := F) (AF F) (y i)) i)) :=
      funext fun i => (ptAt_locW hw h (hat i)).symm
    have hloc : (fun i => locW h ((a • fun i => inclR (F := F) (AF F) (y i)) i)) ∈ GlobalTheory.LFun.latAt w X.L := by
      have e : (fun i => locW h ((a • fun i => inclR (F := F) (AF F) (y i)) i)) =
          (⟨complMap h (evFin F v a), complMap_mem h hav⟩ : Formalism.UG.Ov E w) •
            fun i => algebraMap E (w.adicCompletion E) (y i) := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply]
        show toCompl h (compFin F E v (a • ((1 : AF F) ⊗ₜ[F] y i))) = complMap h (evFin F v a) * _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rfl
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
    rw [hz, blow_mulVec_pt]
    exact pt_mem_latAt hw h X (hA _ hloc)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem conj_preserves {n : ℕ} (X : Spc F E n) (P : GL (Fin n) (w.adicCompletion E)) (hP : IsFrameAt w X.L P)
    (k : GL (Fin n) (w.adicCompletion E)) (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (w.adicCompletion E))) :
    ∀ x ∈ GlobalTheory.LFun.latAt w X.L,
      ((P * k * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ x ∈
        GlobalTheory.LFun.latAt w X.L := by
  intro x hx
  obtain ⟨k', rfl⟩ := hk
  have hy := (hP (((P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) _) *ᵥ x)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]; exact hx)
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine (hP _).1 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hy j)
  exact (k'.1 i j).2

theorem conj_form {K : Type} [CommRing K] {n : ℕ} (c : K →+* K) (Ja p q m : Matrix (Fin n) (Fin n) K) (δ : K)
    (hpq : p * q = 1) (hP : pᵀ * Ja * p.map c = δ • 1) (hk : mᵀ * m.map c = 1) :
    (p * m * q)ᵀ * Ja * (p * m * q).map c = Ja := by
  have hpqc : p.map c * q.map c = 1 := by rw [← Matrix.map_mul, hpq, Matrix.map_one _ (map_zero c) (map_one c)]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.map_mul]
  calc qᵀ * (mᵀ * pᵀ) * Ja * (p.map c * m.map c * q.map c)
      = qᵀ * mᵀ * (pᵀ * Ja * p.map c) * m.map c * q.map c := by simp only [Matrix.mul_assoc]
    _ = δ • (qᵀ * (mᵀ * m.map c) * q.map c) := by
        rw [hP]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = δ • (qᵀ * q.map c) := by rw [hk, Matrix.mul_one]
    _ = qᵀ * (pᵀ * Ja * p.map c) * q.map c := by rw [hP]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    _ = (p * q)ᵀ * Ja * (p.map c * q.map c) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = Ja := by rw [hpq, hpqc]; simp

variable {Γ : Type} [Group Γ]

def embHom {n : ℕ} (P : GL (Fin n) (w.adicCompletion E)) (φ : Γ →* GL (Fin n) (w.adicCompletion E)) :
    Γ →* GL (Fin n) (AE F E) :=
  (Units.map (blowHom hw h n)).comp ((MulAut.conj P).toMonoidHom.comp φ)

theorem embHom_val {n : ℕ} (P : GL (Fin n) (w.adicCompletion E)) (φ : Γ →* GL (Fin n) (w.adicCompletion E)) (g : Γ) :
    ((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) =
      blow hw h ((P * φ g * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl

end GlobalTheory.InertPlace

open GlobalTheory.InertPlace in
theorem GlobalTheory.InertPlace.exists_hom_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {n : ℕ} (X : Spc F E n) (P : GL (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) *
        (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = δ • 1 →
      ∀ {Γ : Type} [Group Γ] (φ : Γ →* GL (Fin n) (w.adicCompletion E)),
        (∀ g, (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = 1) →
        ∃ ι : Γ →* UA σ X.J, (∀ g, ι g ∈ UAt σ X (evFin F v)) ∧
          (∀ g, (mat (ι g)).map (locW h) = ((P * φ g * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
          (IsFrameAt w X.L P → ∀ g, φ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (w.adicCompletion E)) → ι g ∈ GlobalTheory.InertSph.KAt σ X v) := by
  intro F E _ _ _ _ _ σ v w hw h σL hc n X P δ hPJ Γ _ φ hφ
  have hmem : ∀ g, embHom hw h P φ g ∈ UG (cA σ) (incM F X.J) := fun g => by
    show ((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F X.J *
      ((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F X.J
    rw [embHom_val, blow_map_cA hw h σ hc]
    refine blow_form hw h X.J _ _ ?_
    rw [Units.val_mul, Units.val_mul]
    exact conj_form σL _ _ _ _ δ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hPJ (hφ g)
  have hAt : ∀ g, (embHom hw h P φ).codRestrict (UG (cA σ) (incM F X.J)) hmem g ∈ UAt σ X (evFin F v) := fun g => by
    show At (evFin F v) (((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) - 1)
    rw [embHom_val, blow, add_sub_cancel_left]
    intro u hu
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
    exact at_ptAt hw h _ u hu
  refine ⟨(embHom hw h P φ).codRestrict (UG (cA σ) (incM F X.J)) hmem, hAt, fun g => ?_, fun hF g hg => ?_⟩
  · show (((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))).map (locW h) = _
    rw [embHom_val]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [blow, locW_ptAt]
    · simp [blow, Matrix.one_apply, hij, locW_ptAt]
  · refine ⟨hAt g, fun z hz => ⟨?_, ?_⟩⟩
    · show ((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ _
      rw [embHom_val]
      exact blow_mulVec_mem hw h X _ (conj_preserves X P hF (φ g) hg) z hz
    · rw [← map_inv]
      show ((embHom hw h P φ g⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ _
      rw [embHom_val]
      exact blow_mulVec_mem hw h X _ (conj_preserves X P hF (φ g⁻¹) (by rw [map_inv]; exact inv_mem hg)) z hz
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_unitary_adelicHom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {n : ℕ} (X : Spc F E n) (P : GL (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) *
        (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = δ • 1 →
      ∀ {Γ : Type} [Group Γ] (φ : Γ →* GL (Fin n) (w.adicCompletion E)),
        (∀ g, (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = 1) →
        ∃ ι : Γ →* UA σ X.J, (∀ g, ι g ∈ UAt σ X (evFin F v)) ∧
          (∀ g, (mat (ι g)).map (locW h) = ((P * φ g * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
          (IsFrameAt w X.L P → ∀ g, φ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (w.adicCompletion E)) → ι g ∈ GlobalTheory.InertSph.KAt σ X v) := by
  atlas_forward_decl GlobalTheory.InertPlace.exists_hom_inert
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

open GlobalTheory.InertCoord

theorem exists_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (δ : w.adicCompletion E)
      (JS : GL (Fin a') (w.adicCompletion E)) (JT : GL (Fin (a + a')) (w.adicCompletion E)) (ψL : AddChar (w.adicCompletion E) ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') (w.adicCompletion E) →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw _
  have h : w.under (𝓞 F) = v := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨ϖ, σL, q, ψL, hc, hU, hodd, hpi, hpn, hψ⟩ := GlobalTheory.T.exists_inertPlace_localField_data F E σ B hTr.base v w hw h
  obtain ⟨A, hAf, hA⟩ := GlobalTheory.T.exists_inertPlace_orthonormal_selfDual_frame F E σ B a a' G hTr.base hTr.geo v w hw h σL hc
  obtain ⟨δ, Bm, hδ1, hδ2, hBf, hB⟩ := GlobalTheory.T.exists_frame_conjTranspose_mul_eq_smul_one F E σ B a a' G hTr.base hTr.geo v w hw h σL hc
  have hσσ : ∀ x, σL (σL x) = x := hU.1
  have hmapσσ : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) (w.adicCompletion E)), (M.map σL).map σL = M := fun M =>
    Matrix.ext fun i j => hσσ _
  have hS : ∀ {k : ℕ} (g : Formalism.UG.UJ σL ((1 : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))),
      (((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)).map σL)ᵀ *
        ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = 1 := fun {k} g => by
    have := g.2
    change Formalism.UG.cT σL ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
      (1 : Matrix (Fin k) (Fin k) (w.adicCompletion E)) * ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = 1 at this
    rwa [Matrix.mul_one] at this
  have hS' : ∀ {k : ℕ} (g : Formalism.UG.UJ σL ((1 : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))),
      ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E))ᵀ *
        ((g : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)).map σL = 1 := fun g => by
    have h2 := congrArg (fun M => M.map σL) (hS g)
    simp only [Matrix.map_mul (f := σL), Matrix.transpose_map, hmapσσ] at h2
    rw [Matrix.map_one _ (map_zero σL) (map_one σL)] at h2
    exact h2
  let φS : Formalism.UG.UJ σL ((1 : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →*
      GL (Fin a') (w.adicCompletion E) := (Formalism.UG.bc σL).comp (Subgroup.subtype _)
  have hφS : ∀ g, ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) =
      ((g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL := fun g => rfl
  have hφSu : ∀ g, ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E))ᵀ *
      ((φS g : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL = 1 := fun g => by
    rw [hφS, hmapσσ]; exact hS g
  obtain ⟨ιS, hSat, hSmat, hSK⟩ := GlobalTheory.T.exists_inertPlace_unitary_adelicHom F E σ v w hw h σL hc G.V' A 1 (by rw [hA, one_smul]) φS hφSu
  obtain ⟨ιT, hTat, hTmat, hTK⟩ := GlobalTheory.T.exists_inertPlace_unitary_adelicHom F E σ v w hw h σL hc G.W Bm δ hB (Subgroup.subtype _) (fun g => hS' g)
  have hgrp : ∀ {k : ℕ} (P M : GL (Fin k) (w.adicCompletion E)),
      ((P⁻¹ : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
        ((P * M * P⁻¹ : GL (Fin k) (w.adicCompletion E)) : Matrix (Fin k) (Fin k) (w.adicCompletion E)) *
        (P : Matrix (Fin k) (Fin k) (w.adicCompletion E)) = (M : Matrix (Fin k) (Fin k) (w.adicCompletion E)) := fun P M => by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  refine ⟨ϖ, σL, q, δ, 1, 1, ψL, kap hw h (A : Matrix (Fin a') (Fin a') (w.adicCompletion E))
    (Bm : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)), ιS, ιT, hU, hodd, one_mem _, one_mem _, ?_, ?_,
    ⟨hδ1, hδ2⟩, hpi, hpn, (GlobalTheory.T.inertPlacePoint_supported_and_surjective F E v w hw h A Bm).1, (GlobalTheory.T.inertPlacePoint_supported_and_surjective F E v w hw h A Bm).2,
    GlobalTheory.T.inertPoint_mem_tensorLattice_iff_integral_coords F E v w hw h G.V' G.W A Bm hAf hBf, ?_, ?_, fun g => hSat g, fun g => hTat g, ?_, ?_⟩
  · intro i j
    simp only [Units.val_one, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  · intro i j
    simp only [Units.val_one, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  · intro x y
    show _ = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (-1 * hTens (cA σ) (incM F G.V'.J) (incM F G.W.J) _ _))
    rw [GlobalTheory.T.tensorHermitianForm_inertPoint_eq_localForm F E σ v w hw h σL hc G.V'.J G.W.J _ _ δ hA hB x y]
    exact hψ _
  · intro g k x
    rw [GlobalTheory.T.inertPlace_action_on_tensorCoords F E σ v w hw h G.V' G.W A Bm (ιS g) (ιT k) (hSat g) (hTat k) x, hSmat, hTmat, hgrp, hgrp, hφS]
    congr 1
    have key : ∀ M : GL (Fin a') (w.adicCompletion E),
        ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ * (M : Matrix (Fin a') (Fin a') (w.adicCompletion E)) = 1 →
        ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ = ((M⁻¹ : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E)) := by
      intro M e
      calc _ = ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)).map σL)ᵀ *
            ((M : Matrix (Fin a') (Fin a') (w.adicCompletion E)) * ((M⁻¹ : GL (Fin a') (w.adicCompletion E)) : Matrix (Fin a') (Fin a') (w.adicCompletion E))) := by
              rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
    rw [key _ (hS g)]
    rfl
  · intro g hg
    refine hSK hAf g ?_
    obtain ⟨k, hk⟩ := hg
    let σO : Formalism.UG.intL (w.adicCompletion E) →+* Formalism.UG.intL (w.adicCompletion E) :=
      σL.restrict _ _ fun x hx => by
        change Valued.v (σL x) ≤ 1
        rw [hU.2.1 x]; exact hx
    refine ⟨Formalism.UG.bc σO k, Units.ext (Matrix.ext fun i j => ?_)⟩
    rw [hφS, ← hk]
    rfl
  · intro g hg
    exact hTK hBf g hg

end GlobalTheory.InertBridge

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localChart_inertPlace_unitaryPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (δ : w.adicCompletion E)
      (JS : GL (Fin a') (w.adicCompletion E)) (JT : GL (Fin (a + a')) (w.adicCompletion E)) (ψL : AddChar (w.adicCompletion E) ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') (w.adicCompletion E) →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') (w.adicCompletion E)) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) (w.adicCompletion E)) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT := by
  atlas_forward_decl GlobalTheory.InertBridge.exists_chart
end
