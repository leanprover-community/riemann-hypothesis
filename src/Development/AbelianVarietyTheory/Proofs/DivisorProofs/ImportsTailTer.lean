import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLocAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryFixingPlaneComplementMemClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMemSUAdelic
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTwistByHeckeCharactersTrivialBase

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open Filter Topology

namespace GlobalTheory.SUTrunc

section Mat

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {e : R}

theorem idempotentTruncation_preserves_form (he : e * e = e) {A B J : Matrix n n R} (h : A * J * B = J) :
    (1 + e • (A - 1)) * J * (1 + e • (B - 1)) = J := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_sub, smul_smul, he, h]
  abel

theorem trunc_mul (he : e * e = e) {A B : Matrix n n R} (h : A * B = 1) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 := by
  have := idempotentTruncation_preserves_form he (A := A) (B := B) (J := 1) (by rw [Matrix.mul_one, h])
  rwa [Matrix.mul_one] at this

theorem cT_trunc (c : R →+* R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, hc]
  · simp [Formalism.UG.cT, hc, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem det_trunc (he : e * e = e) {A : Matrix n n R} (h : A.det = 1) : (1 + e • (A - 1)).det = 1 := by
  have key : ∀ (a : R) (B : Matrix n n R), B.det = 1 → (∀ i j, a ∣ (1 + e • (A - 1)) i j - B i j) →
      a ∣ (1 + e • (A - 1)).det - 1 := by
    intro a B hB hd
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, ← hB, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hd i j
  obtain ⟨x, hx⟩ := key e 1 Matrix.det_one fun i j => ⟨(A - 1) i j, by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring⟩
  obtain ⟨y, hy⟩ := key (1 - e) A h fun i j => ⟨-((A - 1) i j), by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]; ring⟩
  linear_combination (1 - e) * hx + e * hy + (-x - y) * he

end Mat

variable {F : Type} [Field F] [NumberField F]

theorem idem_mul_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {η : AF F}
    (h : IsPlacesIdem S₁ S₂ η) : η * η = η := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · change fstA F η w * fstA F η w = fstA F η w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, mul_one]
    · rw [h2 w hw, mul_zero]
  · change evalV F v (sndA F η) * evalV F v (sndA F η) = evalV F v (sndA F η)
    by_cases hw : v ∈ S₂
    · rw [h3 v hw, mul_one]
    · rw [h4 v hw, mul_zero]

theorem tendsto_idem (η : Finset (HeightOneSpectrum (𝓞 F)) → AF F)
    (hη : ∀ T, IsPlacesIdem Finset.univ T (η T)) : Tendsto η atTop (𝓝 1) := by
  classical
  let y : Finset (HeightOneSpectrum (𝓞 F)) → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F :=
    fun T v => if v ∈ T then 1 else 0
  have hy : Tendsto y atTop (𝓝 1) := by
    rw [tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {v}] with T hT
    exact (if_pos (hT (Finset.mem_singleton_self v))).symm
  let s : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → Af F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : Continuous fun z => pairA F 1 (s z) := continuous_const.prodMk hs
  have h1 : pairA F 1 (s 1) = 1 := rfl
  have h2 : η = fun T => pairA F 1 (s (y T)) := by
    funext T
    obtain ⟨h1, -, h3, h4⟩ := hη T
    refine Prod.ext (funext fun w => h1 w (Finset.mem_univ w)) (RestrictedProduct.ext _ _ fun v => ?_)
    change evalV F v (sndA F (η T)) = ((y T v : v.adicCompletionIntegers F) : v.adicCompletion F)
    by_cases hv : v ∈ T
    · rw [h3 v hv]; simp [y, hv]
    · rw [h4 v hv]; simp [y, hv]
  rw [h2, ← h1]
  exact (hp.tendsto 1).comp hy

theorem mem_closure_supp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η ∧ x ∈ SUSupp σ J η} := by
  intro F E _ _ _ _ _ σ _ M J _ g hg
  choose η hη using fun T : Finset (HeightOneSpectrum (𝓞 F)) => StrongApprox.exists_isPlacesIdem Finset.univ T
  have hlim := tendsto_idem η hη
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  have he : ∀ T, ι (η T) * ι (η T) = ι (η T) := fun T => by rw [← map_mul, idem_mul_self (hη T)]
  let u : Finset (HeightOneSpectrum (𝓞 F)) → GL (Fin M) (AF F ⊗[F] E) := fun T =>
    ⟨1 + ι (η T) • (SUSuppSub.mv σ J g - 1), 1 + ι (η T) • (SUSuppSub.mv σ J g⁻¹ - 1),
      trunc_mul (he T) (SUSuppSub.mv_mul_inv σ J g), trunc_mul (he T) (SUSuppSub.mv_inv_mul σ J g)⟩
  have hu : ∀ T, u T ∈ HR (AF F) σ J := by
    intro T
    change Formalism.UG.cT (sigR (AF F) σ) (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) * JR (AF F) J *
      (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) = JR (AF F) J
    rw [cT_trunc _ (StrongApprox.sigR_algebraMap σ _)]
    exact idempotentTruncation_preserves_form (he T) (g : HR (AF F) σ J).2
  let x : Finset (HeightOneSpectrum (𝓞 F)) → HA (AF F) σ J := fun T => (⟨u T, hu T⟩ : HR (AF F) σ J)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hmat : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      Tendsto (fun T => 1 + ι (η T) • (A - 1)) atTop (𝓝 A) := by
    intro A
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h := (hlim.smul_const ((A - 1) i j)).const_add ((1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j)
    rw [one_smul, Matrix.sub_apply, add_sub_cancel] at h
    refine h.congr fun T => ?_
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Algebra.smul_def]
  have hx : Tendsto x atTop (𝓝 g) := by
    refine (tendsto_subtype_rng (p := fun a => a ∈ HR (AF F) σ J)).2 ?_
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    exact (hmat (SUSuppSub.mv σ J g)).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp (hmat (SUSuppSub.mv σ J g⁻¹)))
  refine mem_closure_of_tendsto hx (Eventually.of_forall fun T => ⟨Finset.univ, T, η T, hη T, ?_⟩)
  rw [SUSuppSub.mem_SUSupp_iff]
  refine ⟨StrongApprox.mem_SUAdelic.2 (det_trunc (he T) (StrongApprox.mem_SUAdelic.1 hg)), ?_⟩
  change ι (η T) • (1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1) = 1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1
  rw [add_sub_cancel_left, smul_smul, he]

end GlobalTheory.SUTrunc

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η ∧ x ∈ SUSupp σ J η} := by
  atlas_forward_decl GlobalTheory.SUTrunc.mem_closure_supp
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUWeakApprox

section Abstract

open Formalism.UG Matrix

theorem exists_aniso {K : Type} [Field K] (c : K →+* K) (hne : ∃ z, c z ≠ z) {n : ℕ} (hn : 0 < n)
    (J : Matrix (Fin n) (Fin n) K) (hdet : J.det ≠ 0) :
    ∃ x : Fin n → K, (c ∘ x) ⬝ᵥ (J *ᵥ x) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨z, hz⟩ := hne
  have hs : ∀ (i : Fin n) (t : K), c ∘ (Pi.single i t : Fin n → K) = Pi.single i (c t) := by
    intro i t
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  have hd : ∀ i, J i i = 0 := by
    intro i
    have := h (Pi.single i 1)
    simpa [hs] using this
  have ho : ∀ i j t, J i j * t + c t * J j i = 0 := by
    intro i j t
    have := h (Pi.single i 1 + Pi.single j t)
    have e : c ∘ (Pi.single i 1 + Pi.single j t : Fin n → K) = Pi.single i 1 + Pi.single j (c t) := by
      have e1 := hs i 1
      rw [map_one] at e1
      calc _ = c ∘ (Pi.single i 1 : Fin n → K) + c ∘ (Pi.single j t : Fin n → K) := funext fun k => map_add c _ _
        _ = _ := by rw [e1, hs]
    rw [e] at this
    simp only [mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct, mulVec_single, Pi.smul_apply, col_apply, hd] at this
    simpa [add_comm] using this
  have hJ : J = 0 := by
    ext i j
    have h1 := ho i j 1
    have h2 := ho i j z
    rw [map_one] at h1
    have : (z - c z) * J i j = 0 := by linear_combination h2 - c z * h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hz.symm)
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact hdet (by rw [hJ, det_zero])

theorem exists_proj {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) {n : ℕ}
    (hn : 0 < n) (J : Matrix (Fin n) (Fin n) K) (hJ : cT c J = J) (hdet : J.det ≠ 0) :
    ∃ P : Matrix (Fin n) (Fin n) K, P * P = P ∧ cT c P * J = J * P ∧ ∀ a : K, (1 + a • P).det = 1 + a := by
  obtain ⟨x, hx⟩ := exists_aniso c hne hn J hdet
  have hJ' : ∀ i j, c (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j
  set d := (c ∘ x) ⬝ᵥ (J *ᵥ x) with hd
  set y : Fin n → K := (c ∘ x) ᵥ* J with hy
  have hyx : y ⬝ᵥ x = d := by rw [hd, dotProduct_mulVec]
  have hcy : c ∘ y = J *ᵥ x := by
    funext i
    simp [hy, vecMul, mulVec, dotProduct, map_sum, hc, hJ', mul_comm]
  have hcd : c d = d := by
    conv_lhs => rw [← hyx]
    rw [hd, ← hcy]
    simp [dotProduct, map_sum, mul_comm]
  refine ⟨d⁻¹ • vecMulVec x y, ?_, ?_, fun a => ?_⟩
  · rw [smul_mul_assoc, mul_smul_comm, vecMulVec_mul_vecMulVec, hyx, vecMulVec_smul, smul_smul d⁻¹ d,
      inv_mul_cancel₀ hx, one_smul]
  · have e : cT c (d⁻¹ • vecMulVec x y) = d⁻¹ • vecMulVec (c ∘ y) (c ∘ x) := by
      ext i j
      simp [cT, vecMulVec_apply, hcd, mul_comm]
    rw [e, smul_mul_assoc, mul_smul_comm, vecMulVec_mul, mul_vecMulVec, hcy]
  · rw [smul_smul, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
      dotProduct_smul, hyx, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]

theorem mem_closure_su {K R : Type} [Field K] [CharZero K] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsArtinianRing R] (ι : K →+* R) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hne : ∃ z, c z ≠ z) (hσ : ∀ x, σ (σ x) = x)
    (hσc : Continuous σ) (hd : DenseRange ι) (h1 : IsOpen {x : R | IsUnit x})
    (h2 : ∀ x : R, IsUnit x → ContinuousAt Ring.inverse x) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) K) (hJ : cT c J = J) (hdet : J.det ≠ 0)
    (g : Matrix (Fin n) (Fin n) R) (hg : cT σ g * J.map ι * g = J.map ι) (hg1 : g.det = 1) :
    g ∈ closure {m | ∃ γ : Matrix (Fin n) (Fin n) K, cT c γ * J * γ = J ∧ γ.det = 1 ∧ m = γ.map ι} := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact subset_closure ⟨1, by rw [cT_one, Matrix.one_mul, Matrix.mul_one], det_one, Subsingleton.elim _ _⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact subset_closure ⟨1, by rw [cT_one, Matrix.one_mul, Matrix.mul_one], det_one, Subsingleton.elim _ _⟩
  obtain ⟨P, hPP, hPJ, hPd⟩ := exists_proj c hc hne hn J hJ hdet
  have h := GlobalTheory.RealApprox.mem_closure_unitary ι c σ hσι hc hne hσ hσc hd h1 h2 Jᵀ
    (by rw [Matrix.transpose_map]; exact congrArg Matrix.transpose hJ) (by rwa [Matrix.det_transpose]) g
    (by rw [Matrix.transpose_map]; exact (GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).1 hg)
  let Ψ : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R := fun m => m * (1 + (σ m.det - 1) • P.map ι)
  have hΨ : Continuous Ψ :=
    continuous_id.matrix_mul (continuous_const.add
      (((hσc.comp continuous_id.matrix_det).sub continuous_const).smul continuous_const))
  have hΨg : Ψ g = g := by simp [Ψ, hg1]
  rw [← hΨg]
  refine hΨ.continuousWithinAt.mem_closure h ?_
  rintro _ ⟨γ, hγ, rfl⟩
  have hγ' : cT c γ * J * γ = J := (GlobalTheory.Mass.OnePlace.unitary_transpose _ _ _).2 hγ
  have hN : c γ.det * γ.det = 1 := by
    have := congrArg Matrix.det hγ'
    rw [det_mul, det_mul, cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    apply mul_right_cancel₀ hdet
    linear_combination this
  refine ⟨γ * (1 + (c γ.det - 1) • P), ?_, ?_, ?_⟩
  · have e : cT c (1 + (c γ.det - 1) • P) = 1 + (γ.det - 1) • cT c P := by
      ext i j
      simp [cT, hc, one_apply, eq_comm]
    rw [cT_mul, e, Matrix.mul_assoc _ _ J, Matrix.mul_assoc, ← Matrix.mul_assoc _ γ, hγ', ← Matrix.mul_assoc]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hPJ,
      Matrix.mul_assoc, hPP, smul_add, smul_smul]
    rw [add_assoc, ← add_smul, ← add_smul,
      show γ.det - 1 + (c γ.det - 1 + (c γ.det - 1) * (γ.det - 1)) = 0 by linear_combination hN, zero_smul, add_zero]
  · rw [det_mul, hPd]
    linear_combination hN
  · simp only [Ψ]
    rw [Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hσι, Matrix.map_add _ (map_add ι),
      Matrix.map_one _ (map_zero ι) (map_one ι), GlobalTheory.UnRep.WeakApprox.map_smul'', map_sub, map_one]

end Abstract

section Transfer

open Matrix
open Formalism.UG hiding sigR

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := by
  simp [sigR, inclR]

theorem sigR_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hc : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [sigR, hc]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem continuous_sigR (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem denseRange_inclR (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [FiniteDimensional F E] (hd : DenseRange (algebraMap F R)) : DenseRange (inclR (F := F) (E := E) R) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  intro y
  let S : AddSubgroup (R ⊗[F] E) := (inclR (F := F) (E := E) R).toAddMonoidHom.range.topologicalClosure
  have hS : IsClosed (S : Set (R ⊗[F] E)) := AddSubgroup.isClosed_topologicalClosure _
  show y ∈ S
  induction y using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | add a b ha hb => exact S.add_mem ha hb
  | tmul a x =>
    have hc : Continuous fun a : R => a ⊗ₜ[F] x := by
      have : (fun a : R => a ⊗ₜ[F] x) = fun a : R => a • ((1 : R) ⊗ₜ[F] x) := by
        funext a
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Continuous.smul (f := fun a : R => a) (g := fun _ : R => ((1 : R) ⊗ₜ[F] x : R ⊗[F] E))
        continuous_id continuous_const
    refine DenseRange.induction_on hd a (p := fun a => a ⊗ₜ[F] x ∈ S) (hS.preimage hc) fun f => ?_
    refine AddSubgroup.le_topologicalClosure _ ⟨f • x, ?_⟩
    show (1 : R) ⊗ₜ[F] (f • x) = algebraMap F _ f ⊗ₜ[F] x
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem mem_closure_trunc [CharZero E] [FiniteDimensional F E] (A B : Type) [CommRing A] [Algebra F A]
    [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] [Algebra F B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsArtinianRing B] (π : A →ₐ[F] B) (s : B → A) (hs : Continuous s) (η : A) (hη : ∀ a, s (π a) = η * a)
    (hd : DenseRange (algebraMap F B)) (h1 : IsOpen {x : B | IsUnit x})
    (h2 : ∀ x : B, IsUnit x → ContinuousAt Ring.inverse x)
    (σ : E →ₐ[F] E) (hc : ∀ x, σ (σ x) = x) (hne : ∃ z, σ z ≠ z) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0)
    (g : Matrix (Fin n) (Fin n) (A ⊗[F] E)) (hg : cT (sigR A σ) g * JR A J * g = JR A J) (hg1 : g.det = 1)
    (hgη : algebraMap A (A ⊗[F] E) η • (g - 1) = g - 1) :
    g ∈ closure {m | ∃ γ : Matrix (Fin n) (Fin n) E, cT (σ : E →+* E) γ * J * γ = J ∧ γ.det = 1 ∧
      m = 1 + algebraMap A (A ⊗[F] E) η • (γ.map (inclR (F := F) A) - 1)} := by
  classical
  haveI : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (A ⊗[F] E) := IsModuleTopology.isTopologicalRing A _
  haveI : IsModuleTopology B (B ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (B ⊗[F] E) := IsModuleTopology.isTopologicalRing B _
  haveI : IsArtinianRing (B ⊗[F] E) := IsArtinianRing.of_finite B _
  let b := Module.finBasis F E
  let bA := Algebra.TensorProduct.basis A b
  let bB := Algebra.TensorProduct.basis B b
  obtain ⟨u1, u2⟩ := GlobalTheory.RealApprox.units_of_free (A := B) (R := B ⊗[F] E) bB h1 h2
  let p : A ⊗[F] E →+* B ⊗[F] E := (Algebra.TensorProduct.map π (AlgHom.id F E)).toRingHom
  have hp : ∀ a x, p (a ⊗ₜ[F] x) = π a ⊗ₜ[F] x := fun a x => rfl
  have hpι : ∀ x, p (inclR (F := F) A x) = inclR (F := F) B x := fun x =>
    (hp 1 x).trans (by rw [map_one]; rfl)
  have hpσ : ∀ y, sigR B σ (p y) = p (sigR A σ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hrepr : ∀ y i, bB.repr (p y) i = π (bA.repr y i) := by
    intro y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [hp, bA, bB, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  let S : B ⊗[F] E → A ⊗[F] E := fun y => ∑ i, s (bB.repr y i) • bA i
  have hS : Continuous S := continuous_finsetSum _ fun i _ =>
    (hs.comp (IsModuleTopology.continuous_of_linearMap (bB.coord i))).smul continuous_const
  have hSp : ∀ y, S (p y) = algebraMap A (A ⊗[F] E) η * y := by
    intro y
    simp only [S, hrepr, hη, mul_smul]
    rw [← Finset.smul_sum, bA.sum_repr, Algebra.smul_def]
  have hmap : ∀ γ : Matrix (Fin n) (Fin n) E, (γ.map (inclR (F := F) A)).map p = γ.map (inclR (F := F) B) := by
    intro γ
    ext i j
    exact hpι _
  have h := mem_closure_su (inclR (F := F) B) (σ : E →+* E) (sigR B σ) (sigR_inclR B σ) hc hne (sigR_sigR B σ hc)
    (continuous_sigR B σ) (denseRange_inclR B hd) u1 u2 J hJ hdet (g.map p)
    (by
      have e : cT (sigR B σ) (g.map p) = (cT (sigR A σ) g).map p := by
        ext i j
        exact hpσ _
      rw [e, ← hmap, ← Matrix.map_mul, ← Matrix.map_mul]
      exact congrArg (·.map p) hg)
    (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hg1, map_one])
  let Ψ : Matrix (Fin n) (Fin n) (B ⊗[F] E) → Matrix (Fin n) (Fin n) (A ⊗[F] E) := fun m => 1 + (m - 1).map S
  have hΨ : Continuous Ψ := continuous_const.add ((continuous_id.sub continuous_const).matrix_map hS)
  have hΨp : ∀ m : Matrix (Fin n) (Fin n) (A ⊗[F] E), Ψ (m.map p) = 1 + algebraMap A (A ⊗[F] E) η • (m - 1) := by
    intro m
    simp only [Ψ]
    rw [← Matrix.map_one p (map_zero p) (map_one p), ← Matrix.map_sub _ (map_sub p)]
    congr 1
    ext i j
    exact hSp _
  have hΨg : Ψ (g.map p) = g := by rw [hΨp, hgη, add_sub_cancel]
  rw [← hΨg]
  refine hΨ.continuousWithinAt.mem_closure h ?_
  rintro _ ⟨γ, hγ, hγ1, rfl⟩
  exact ⟨γ, hγ, hγ1, by rw [← hmap, hΨp]⟩

end Transfer

section Main

open Matrix
open Formalism.UG hiding sigR evalV

theorem isInducing_val {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (σ : R →+* R)
    (hσ : Continuous σ) {n : ℕ} (J K : Matrix (Fin n) (Fin n) R) (hK : K * J = 1) :
    Topology.IsInducing fun u : UJ σ J => (u.1 : Matrix (Fin n) (Fin n) R) := by
  have hφ : Continuous fun m : Matrix (Fin n) (Fin n) R => (m, MulOpposite.op (K * cT σ m * J)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul (continuous_id.matrix_map hσ).matrix_transpose).matrix_mul continuous_const))
  refine Topology.IsInducing.of_comp (Units.continuous_val.comp continuous_subtype_val) hφ ?_
  have he := (Units.isInducing_embedProduct (M := Matrix (Fin n) (Fin n) R)).comp
    (Topology.IsInducing.subtypeVal (t := (UJ σ J : Set (GL (Fin n) R))))
  suffices e : ((fun m : Matrix (Fin n) (Fin n) R => (m, MulOpposite.op (K * cT σ m * J))) ∘
      fun u : UJ σ J => (u.1 : Matrix (Fin n) (Fin n) R)) =
      fun u : UJ σ J => Units.embedProduct (Matrix (Fin n) (Fin n) R) u.1 by
    rw [e]
    exact he
  funext u
  refine Prod.ext rfl (congrArg MulOpposite.op ?_)
  have hu : cT σ u.1.1 * J * u.1.1 = J := u.2
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  rw [Matrix.mul_assoc K, Matrix.mul_assoc K, hu, hK]

theorem unitary_trunc {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (J u : Matrix (Fin n) (Fin n) R) (e : R)
    (he : e * e = e) (hσ : σ e = e) (hu : cT σ u * J * u = J) :
    cT σ (1 + e • (u - 1)) * J * (1 + e • (u - 1)) = J := by
  have e1 : cT σ (1 + e • (u - 1)) = 1 + e • (cT σ u - 1) := by
    ext i j
    simp [cT, hσ, one_apply, eq_comm]
  rw [e1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub, smul_smul, he, hu]
  abel

theorem weak_approx_SU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ h ∈ SUSupp σ J η, h ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j)} := by
  intro F E _ _ _ _ _ σ hCM M J hJ T₁ T₂ η hη h hh
  classical
  obtain ⟨-, hE, -, hτ⟩ := hCM
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  have hne : ∃ z, σ z ≠ z := by
    by_contra hn
    push Not at hn
    refine IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    have := hτ τ x
    rw [hn] at this
    exact this.symm
  let B : Type := ((v : T₂) → Fv F v.1) × ((w : T₁) → w.1.Completion)
  let π : AF F →ₐ[F] B :=
    AlgHom.prod (AlgHom.pi fun v : T₂ => (evalV F v.1).comp (sndA F))
      (AlgHom.pi fun w : T₁ => (Pi.evalAlgHom F (fun u : InfinitePlace F => u.Completion) w.1).comp (fstA F))
  have hπ : ∀ a, GlobalTheory.PlaceApprox.locAdele T₁ T₂ (π a) = η * a := fun a =>
    (GlobalTheory.PlaceApprox.mul_eq_locAdele hη a).symm
  have hηη : η * η = η := by
    have e : π η = π 1 := by
      refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
      · exact (hη.2.2.1 v.1 v.2).trans (map_one ((evalV F v.1).comp (sndA F))).symm
      · exact (hη.1 w.1 w.2).trans (by rw [map_one]; rfl)
    rw [← hπ, e, hπ, mul_one]
  have a1 : IsOpen {x : B | IsUnit x} := Units.isOpen
  have a2 : ∀ x : B, IsUnit x → ContinuousAt Ring.inverse x := by
    rintro _ ⟨x, rfl⟩
    exact NormedRing.inverse_continuousAt x
  have hJ' : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  obtain ⟨hh1, hh2⟩ := (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).1 hh
  have key := mem_closure_trunc (AF F) B π _ (GlobalTheory.PlaceApprox.continuous_locAdele T₁ T₂) η hπ
    (GroundTheory.Global.denseRange_algebraMap_prod_pi (K := F) T₂ T₁) a1 a2 σ hc hne J hJ' hJ.2
    (GlobalTheory.SUSuppSub.mv σ J h) (show HR (AF F) σ J from h).2 (StrongApprox.mem_SUAdelic.1 hh1) hh2
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hu : IsUnit (JR (F := F) (AF F) J).det := by
    unfold JR
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hind : Topology.IsInducing (GlobalTheory.SUSuppSub.mv σ J) :=
    isInducing_val (sigR (AF F) σ) (continuous_sigR _ σ) _ _ (Matrix.nonsing_inv_mul _ hu)
  rw [hind.closure_eq_preimage_closure_image]
  refine closure_mono ?_ key
  rintro _ ⟨γ, hγ, hγ1, rfl⟩
  have hγA : cT (sigR (AF F) σ) (γ.map (inclR (F := F) (AF F))) * JR (F := F) (AF F) J *
      γ.map (inclR (F := F) (AF F)) = JR (F := F) (AF F) J := by
    have e : cT (sigR (AF F) σ) (γ.map (inclR (F := F) (AF F))) =
        (cT (σ : E →+* E) γ).map (inclR (F := F) (AF F)) := by
      ext i j
      exact sigR_inclR _ σ _
    unfold JR
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hγ]
  have hx := unitary_trunc _ _ _ (algebraMap (AF F) (AF F ⊗[F] E) η) (by rw [← map_mul, hηη])
    (StrongApprox.sigR_algebraMap σ η) hγA
  have hxu : IsUnit (1 + algebraMap (AF F) (AF F ⊗[F] E) η • (γ.map (inclR (F := F) (AF F)) - 1)).det := by
    have := hu
    rw [← hx, det_mul] at this
    exact isUnit_of_mul_isUnit_right this
  let γ₀ : GL (Fin M) E := Matrix.GeneralLinearGroup.mkOfDetNeZero γ (by rw [hγ1]; exact one_ne_zero)
  let γA : HA (AF F) σ J := (⟨bc (inclR (F := F) (AF F)) γ₀, hγA⟩ : HR (AF F) σ J)
  let x : HA (AF F) σ J := (⟨Matrix.GeneralLinearGroup.mk'' _ hxu, hx⟩ : HR (AF F) σ J)
  refine ⟨x, ⟨γA, ⟨StrongApprox.mem_SUAdelic.2 ?_, ⟨γ₀, hγ, rfl⟩⟩, fun i j => rfl⟩, rfl⟩
  change (γ.map (inclR (F := F) (AF F))).det = 1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hγ1, map_one]

end Main

end GlobalTheory.SUWeakApprox

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_rational_points_unitary_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ h ∈ SUSupp σ J η, h ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j)} := by
  atlas_forward_decl GlobalTheory.SUWeakApprox.weak_approx_SU
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SUGenPairs

open GlobalTheory.UnRep Matrix

section Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

theorem refl_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E) :
    k * refl c G x u = refl c G (k *ᵥ x) u * k := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ReflLaws.refl_mulVec, ReflLaws.refl_mulVec, hk, hk, Matrix.mulVec_add, Matrix.mulVec_smul]

theorem refl_conj' {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (x : Fin n → E) (u : E)
    (X : Matrix (Fin n) (Fin n) E) : k * (refl c G x u * X) = refl c G (k *ᵥ x) u * (k * X) := by
  rw [← mul_assoc, refl_conj hk, mul_assoc]

theorem det_refl (x : Fin n → E) (u : E) (hx : hermE c G x x ≠ 0) : (refl c G x u).det = u := by
  rw [GlobalTheory.UnRep.refl, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    smul_eq_mul, ← ReflLaws.hermE_eq_dot, div_mul_cancel₀ _ hx]
  ring

theorem det_prod (l : List ((Fin n → E) × E)) (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0) :
    (l.map fun p => refl c G p.1 p.2).prod.det = (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.det_mul]
    rw [det_refl _ _ (hl p List.mem_cons_self), ih fun q hq => hl q (List.mem_cons_of_mem _ hq)]

theorem prod_conj {k : Matrix (Fin n) (Fin n) E} (hk : IsUnE c G k) (P : List ((Fin n → E) × (Fin n → E) × E)) :
    k * (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod =
      ((P.map fun p => (k *ᵥ p.1, k *ᵥ p.2.1, p.2.2)).map
        fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * k := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.map_cons, List.prod_cons, mul_assoc, refl_conj' hk, ih]

theorem tele (hG : IsHermForm c G) (x₀ : Fin n → E) (h₀ : hermE c G x₀ x₀ ≠ 0) :
    ∀ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
    ∃ P : List ((Fin n → E) × (Fin n → E) × E),
      (∀ p ∈ P, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * c p.2.2 = 1) ∧
      (l.map fun p => refl c G p.1 p.2).prod =
        (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod * refl c G x₀ (l.map Prod.snd).prod := by
  have L := ReflLaws.refl_laws F E c n G hG x₀ h₀
  intro l
  induction l with
  | nil => intro _; exact ⟨[], by simp, by simp [L.2.1]⟩
  | cons q l ih =>
    intro hl
    obtain ⟨P, hP, e⟩ := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
    obtain ⟨hq1, hq2⟩ := hl q List.mem_cons_self
    have hk : IsUnE c G (refl c G x₀ q.2) := L.2.2.2 q.2 hq2
    refine ⟨(q.1, x₀, q.2) :: P.map (fun p => (refl c G x₀ q.2 *ᵥ p.1, refl c G x₀ q.2 *ᵥ p.2.1, p.2.2)), ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hq1, h₀, hq2⟩
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
        obtain ⟨a1, a2, a3⟩ := hP p' hp'
        exact ⟨by rw [hk]; exact a1, by rw [hk]; exact a2, a3⟩
    · have hcu : refl c G x₀ (c q.2) * refl c G x₀ q.2 = 1 := by
        rw [L.2.2.1, mul_comm, hq2, L.2.1]
      have hc := prod_conj hk P
      simp only [List.map_cons, List.prod_cons]
      rw [e, ← L.2.2.1 q.2]
      calc refl c G q.1 q.2 * ((P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod *
              refl c G x₀ (l.map Prod.snd).prod)
          = refl c G q.1 q.2 * ((refl c G x₀ (c q.2) * refl c G x₀ q.2) *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by rw [hcu, one_mul, mul_assoc]
        _ = refl c G q.1 q.2 * refl c G x₀ (c q.2) * (refl c G x₀ q.2 *
              (P.map fun p => refl c G p.1 p.2.2 * refl c G p.2.1 (c p.2.2)).prod) *
              refl c G x₀ (l.map Prod.snd).prod := by simp only [mul_assoc]
        _ = _ := by rw [hc]; simp only [mul_assoc]

end Refl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conjE_apply (hcm : IsCMExt F E σ) (x : E) : GlobalTheory.WeilTwistF.conjE hcm x = σ x := rfl

theorem hermE_transpose (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = (fun b => σ (y b)) ⬝ᵥ J *ᵥ x := by
  simp only [hermE, conjE_apply, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hermE_eq_hE (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x y = hE σ J y x := by
  rw [hermE_transpose]
  simp only [hE, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rfl

theorem isUnE_of (hcm : IsCMExt F E σ) {n : ℕ} (J m : Matrix (Fin n) (Fin n) E) (h : (m.map σ)ᵀ * J * m = J) :
    IsUnE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ m := by
  have e1 : ∀ y : Fin n → E, (fun b => σ ((m *ᵥ y) b)) = m.map σ *ᵥ (fun b => σ (y b)) := fun y => by
    funext i
    simp [mulVec, dotProduct, map_sum, map_mul]
  intro x y
  have e : (fun b => σ ((m *ᵥ y) b)) ⬝ᵥ J *ᵥ (m *ᵥ x) = (fun b => σ (y b)) ⬝ᵥ ((m.map σ)ᵀ * J * m) *ᵥ x := by
    rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, dotProduct_comm,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  rw [hermE_transpose, hermE_transpose, e, h]

theorem qr_eq_refl (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) :
    GlobalTheory.SUAssemble.qr σ J x u = GlobalTheory.UnRep.refl (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x u := by
  rw [GlobalTheory.SUAssemble.qr, GlobalTheory.UnRep.refl, hermE_eq_hE, Matrix.mulVec_transpose]
  rfl

end GlobalTheory.SUGenPairs

open GlobalTheory.UnRep GlobalTheory.SUGenPairs in

theorem GlobalTheory.SUGenPairs.eq_prod_pairs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ Formalism.UG.UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E).det = 1 → ∃ l : List ((Fin M → E) × (Fin M → E) × E), (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) ∧ (g : Matrix (Fin M) (Fin M) E) = (l.map fun p => GlobalTheory.SUAssemble.qr σ J p.1 p.2.2 * GlobalTheory.SUAssemble.qr σ J p.2.1 (σ p.2.2)).prod := by
  intro F E _ _ _ _ _ σ hcm M J hJ g hg hdet
  have hG : IsHermForm (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ :=
    ⟨fun x => (GlobalTheory.WeilTwistF.conjE hcm).apply_symm_apply x, GlobalTheory.WeilTwistF.conjE_ne hcm, fun a b => hJ.1 a b,
      by rw [Matrix.det_transpose]; exact hJ.2⟩
  have hu : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  obtain ⟨l, hl, hgl⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl F E _ M Jᵀ hG _ (isUnE_of hcm J _ hu)
  have hne : ∀ x : Fin M → E, hermE (GlobalTheory.WeilTwistF.conjE hcm) Jᵀ x x ≠ 0 → hE σ J x x ≠ 0 := fun x hx => by
    rwa [← hermE_eq_hE hcm]
  cases l with
  | nil => exact ⟨[], by simp, by simpa using hgl⟩
  | cons q l' =>
    obtain ⟨P, hP, e⟩ := tele hG q.1 (hl q List.mem_cons_self).1 (q :: l') hl
    have ha : ((q :: l').map Prod.snd).prod = 1 := by
      rw [← det_prod _ (fun p hp => (hl p hp).1), ← hgl, hdet]
    rw [ha, (ReflLaws.refl_laws F E _ M Jᵀ hG q.1 (hl q List.mem_cons_self).1).2.1, mul_one] at e
    refine ⟨P, fun p hp => ⟨hne _ (hP p hp).1, hne _ (hP p hp).2.1, (hP p hp).2.2⟩, ?_⟩
    rw [hgl, e]
    congr 2
    funext p
    rw [qr_eq_refl hcm, qr_eq_refl hcm]
    rfl
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialUnitary_eq_prod_quasiReflectionPairs : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ Formalism.UG.UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E).det = 1 → ∃ l : List ((Fin M → E) × (Fin M → E) × E), (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) ∧ (g : Matrix (Fin M) (Fin M) E) = (l.map fun p => GlobalTheory.SUAssemble.qr σ J p.1 p.2.2 * GlobalTheory.SUAssemble.qr σ J p.2.1 (σ p.2.2)).prod := by
  atlas_forward_decl GlobalTheory.SUGenPairs.eq_prod_pairs
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.SUPair
open Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def wv (x : Fin M → E) : Fin M → E := Matrix.vecMul (fun i => σ (x i)) J

theorem hE_eq (x v : Fin M → E) : hE σ J x v = wv σ J x ⬝ᵥ v := by
  simp only [hE, Formalism.UG.hform, wv, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem qr_eq (x : Fin M → E) (u : E) :
    GlobalTheory.SUAssemble.qr σ J x u = 1 + ((u - 1) / hE σ J x x) • Matrix.vecMulVec x (wv σ J x) := rfl

theorem qr_mulVec (x : Fin M → E) (u : E) (v : Fin M → E) :
    GlobalTheory.SUAssemble.qr σ J x u *ᵥ v = v + ((u - 1) / hE σ J x x * hE σ J x v) • x := by
  rw [qr_eq, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp only [hE_eq, op_smul_eq_smul, smul_smul]

theorem hE_sub_left (a b v : Fin M → E) : hE σ J (a - b) v = hE σ J a v - hE σ J b v := by
  simp [hE, Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]
theorem hE_smul_left (t : E) (a v : Fin M → E) : hE σ J (t • a) v = σ t * hE σ J a v := by
  simp [hE, Formalism.UG.hform, Finset.mul_sum, mul_assoc]
theorem hE_sub_right (a b v : Fin M → E) : hE σ J v (a - b) = hE σ J v a - hE σ J v b := by
  simp [hE, Formalism.UG.hform, mul_sub, Finset.sum_sub_distrib]
theorem hE_smul_right (t : E) (a v : Fin M → E) : hE σ J v (t • a) = t * hE σ J v a := by
  simp [hE, Formalism.UG.hform, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem Q_mul_Q (x : Fin M → E) :
    Matrix.vecMulVec x (wv σ J x) * Matrix.vecMulVec x (wv σ J x) = hE σ J x x • Matrix.vecMulVec x (wv σ J x) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hE_eq, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => by ring

theorem cT_Q_mul (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) :
    Formalism.UG.cT (σ : E →+* E) (Matrix.vecMulVec x (wv σ J x)) * J = J * Matrix.vecMulVec x (wv σ J x) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply, wv,
    Matrix.vecMul, dotProduct, map_mul, map_sum, AlgHom.coe_toRingHom, hσ, hJ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.SUPair

namespace GlobalTheory.SUPair
open Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_self (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem qr_one (x : Fin M → E) : GlobalTheory.SUAssemble.qr σ J x 1 = 1 := by
  rw [qr_eq, sub_self, zero_div, zero_smul, add_zero]

theorem qr_mul_qr (x : Fin M → E) (hx : hE σ J x x ≠ 0) (a b : E) :
    GlobalTheory.SUAssemble.qr σ J x a * GlobalTheory.SUAssemble.qr σ J x b = GlobalTheory.SUAssemble.qr σ J x (a * b) := by
  rw [qr_eq, qr_eq, qr_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Q_mul_Q, smul_add]
  have : (a * b - 1) / hE σ J x x = (a - 1) / hE σ J x x + (b - 1) / hE σ J x x +
      (a - 1) / hE σ J x x * ((b - 1) / hE σ J x x * hE σ J x x) := by
    field_simp; ring
  rw [this]
  module

theorem cT_qr (x : Fin M → E) (u : E) :
    Formalism.UG.cT (σ : E →+* E) (GlobalTheory.SUAssemble.qr σ J x u) =
      1 + σ ((u - 1) / hE σ J x x) • Formalism.UG.cT (σ : E →+* E) (Matrix.vecMulVec x (wv σ J x)) := by
  rw [qr_eq]
  ext i j
  simp [Formalism.UG.cT, Matrix.one_apply, eq_comm]

theorem qr_unitary (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E)
    (hx : hE σ J x x ≠ 0) (u : E) (hu : u * σ u = 1) :
    Formalism.UG.cT (σ : E →+* E) (GlobalTheory.SUAssemble.qr σ J x u) * J * GlobalTheory.SUAssemble.qr σ J x u = J := by
  rw [cT_qr]
  rw [qr_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, cT_Q_mul σ J hσ hJ, Matrix.mul_assoc, Q_mul_Q, smul_add]
  have hs : σ ((u - 1) / hE σ J x x) = (σ u - 1) / hE σ J x x := by
    rw [map_div₀, map_sub, map_one, hE_self σ J hσ hJ]
  rw [hs]
  have : (u - 1) / hE σ J x x * ((σ u - 1) / hE σ J x x * hE σ J x x) =
      -((σ u - 1) / hE σ J x x) - (u - 1) / hE σ J x x := by
    field_simp; linear_combination hu
  rw [this]
  module

theorem det_qr (x : Fin M → E) (hx : hE σ J x x ≠ 0) (u : E) : (GlobalTheory.SUAssemble.qr σ J x u).det = u := by
  rw [qr_eq, ← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq (ι := Unit),
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, ← hE_eq, smul_eq_mul, div_mul_cancel₀ _ hx]
  ring

end GlobalTheory.SUPair

namespace GlobalTheory.SUPair
open Matrix

section Grp
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def qrU (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) (hx : hE σ J x x ≠ 0)
    (u : E) (hu : u * σ u = 1) : Formalism.UG.UJ (σ : E →+* E) J :=
  ⟨⟨GlobalTheory.SUAssemble.qr σ J x u, GlobalTheory.SUAssemble.qr σ J x (σ u),
    by rw [qr_mul_qr σ J x hx, hu, qr_one], by rw [qr_mul_qr σ J x hx, mul_comm, hu, qr_one]⟩,
    qr_unitary σ J hσ hJ x hx u hu⟩

end Grp

section Fix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem trunc_fix (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J) (v : Fin M → E)
    (hv : (g.1 : Matrix (Fin M) (Fin M) E) *ᵥ v = v) :
    ((HA.mat (AF F) σ J (GlobalTheory.SUAssemble.trunc σ J η hη g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *ᵥ
      (fun i => inclR (AF F) (v i)) = fun i => inclR (AF F) (v i) := by
  rw [GlobalTheory.SUAssemble.mv_trunc]
  have h : GlobalTheory.SUAssemble.rmat (F := F) g.1 *ᵥ (fun i => inclR (AF F) (v i)) = fun i => inclR (AF F) (v i) := by
    funext i
    conv_rhs => rw [← hv]
    simp [GlobalTheory.SUAssemble.rmat, Matrix.mulVec, dotProduct, map_sum]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, h, Matrix.one_mulVec, sub_self,
    smul_zero, add_zero]

end Fix

theorem trunc_pair_mem : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (η : AF F) (hη : η * η = η) (x y z : Fin M → E) (u : E), u * σ u = 1 → hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → hE σ J z z ≠ 0 → (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) → (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) → ∃ p : Formalism.UG.UJ (σ : E →+* E) J, (p.1 : Matrix (Fin M) (Fin M) E) = GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J y (σ u) ∧ GlobalTheory.SUAssemble.trunc σ J η hη p ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro H F E _ _ _ _ _ σ hcm M J hJ S₁ S₂ ε hε hne η hη x y z u hu hx hy hz ⟨hz'n, t₁, ht₁⟩ ⟨hy'n, t₂, ht₂⟩
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hJ' : ∀ i j, σ (J j i) = J i j := hJ.1
  have hu' : σ u * σ (σ u) = 1 := by rw [hσ, mul_comm, hu]
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have h1 : (1 : HA (AF F) σ J) ∈ closure S := subset_closure ⟨1, (SURat σ J).one_mem, 1,
    (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by rw [GlobalTheory.SUSuppSub.mv_one, sub_self, smul_zero]⟩,
    by simp⟩
  have hmul : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b ∈ closure S := by
    intro a ha b hb
    have hbi : b⁻¹ ∈ closure S := by
      simpa using GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε 1 h1 b hb
    simpa using GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε a ha b⁻¹ hbi
  let A := qrU σ J hσ hJ' x hx u hu
  let B := qrU σ J hσ hJ' y hy (σ u) hu'
  let C := qrU σ J hσ hJ' z hz (σ u) hu'
  let D := qrU σ J hσ hJ' z hz u hu
  refine ⟨A * B, rfl, ?_⟩
  have hCD : C * D = 1 := Subtype.ext (Units.ext (by
    show GlobalTheory.SUAssemble.qr σ J z (σ u) * GlobalTheory.SUAssemble.qr σ J z u = 1
    rw [qr_mul_qr σ J z hz, mul_comm, hu, qr_one]))
  have hAB : A * B = (A * C) * (D * B) := by
    rw [mul_assoc, ← mul_assoc C, hCD, one_mul]
  rw [hAB, map_mul]

  have hzv : ∀ v : Fin M → E, hE σ J x v = 0 →
      hE σ J (z - (hE σ J x z / hE σ J x x) • x) v = 0 → hE σ J z v = 0 := by
    intro v h1 h2
    rwa [hE_sub_left, hE_smul_left, h1, mul_zero, sub_zero] at h2
  have hyv : ∀ v : Fin M → E, hE σ J z v = 0 →
      hE σ J (y - (hE σ J z y / hE σ J z z) • z) v = 0 → hE σ J y v = 0 := by
    intro v h1 h2
    rwa [hE_sub_left, hE_smul_left, h1, mul_zero, sub_zero] at h2
  apply hmul
  · refine H F E σ hcm M J hJ S₁ S₂ ε hε hne x (z - (hE σ J x z / hE σ J x x) • x) ?_ hx hz'n ⟨t₁, ht₁⟩ _ ?_ ?_
    · rw [hE_sub_right, hE_smul_right, div_mul_cancel₀ _ hx, sub_self]
    · refine GlobalTheory.SUAssemble.trunc_mem_SUAdelic σ J η hη _ ?_
      show (GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J z (σ u)).det = 1
      rw [Matrix.det_mul, det_qr σ J x hx, det_qr σ J z hz, hu]
    · intro v h1 h2
      refine trunc_fix σ J η hη _ v ?_
      show (GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J z (σ u)) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec, qr_mulVec σ J z, hzv v h1 h2, mul_zero, zero_smul, add_zero, qr_mulVec σ J x, h1, mul_zero,
        zero_smul, add_zero]
  · refine H F E σ hcm M J hJ S₁ S₂ ε hε hne z (y - (hE σ J z y / hE σ J z z) • z) ?_ hz hy'n ⟨t₂, ht₂⟩ _ ?_ ?_
    · rw [hE_sub_right, hE_smul_right, div_mul_cancel₀ _ hz, sub_self]
    · refine GlobalTheory.SUAssemble.trunc_mem_SUAdelic σ J η hη _ ?_
      show (GlobalTheory.SUAssemble.qr σ J z u * GlobalTheory.SUAssemble.qr σ J y (σ u)).det = 1
      rw [Matrix.det_mul, det_qr σ J z hz, det_qr σ J y hy, hu]
    · intro v h1 h2
      refine trunc_fix σ J η hη _ v ?_
      show (GlobalTheory.SUAssemble.qr σ J z u * GlobalTheory.SUAssemble.qr σ J y (σ u)) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec, qr_mulVec σ J y, hyv v h1 h2, mul_zero, zero_smul, add_zero, qr_mulVec σ J z, h1, mul_zero,
        zero_smul, add_zero]

end GlobalTheory.SUPair
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiReflectionPair_truncation_mem_closure : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (η : AF F) (hη : η * η = η) (x y z : Fin M → E) (u : E), u * σ u = 1 → hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → hE σ J z z ≠ 0 → (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) → (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) → ∃ p : Formalism.UG.UJ (σ : E →+* E) J, (p.1 : Matrix (Fin M) (Fin M) E) = GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J y (σ u) ∧ GlobalTheory.SUAssemble.trunc σ J η hη p ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  atlas_forward_decl GlobalTheory.SUPair.trunc_pair_mem
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.SUAssemble

open GlobalTheory.SUAssemble in

theorem assemble : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ γ ∈ SURat σ J, ∀ x : HA (AF F) σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j) → x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro H1 H2 F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc T₁ T₂ η hη γ hγ x hx
  obtain ⟨S₁', S₂', ε', hs1, hs2, hne, hε', hz⟩ := H2 F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  have hηη : η * η = η := idem_sq hη
  have hεε : ε * ε' = ε' := idem_mul_of_sub hε hε' hs1 hs2
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have hdiv := GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε
  have h1 : (1 : HA (AF F) σ J) ∈ closure S := subset_closure ⟨1, (SURat σ J).one_mem, 1,
    (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by
      rw [GlobalTheory.SUSuppSub.mv_one, sub_self, smul_zero]⟩, by simp⟩
  let Cg : Subgroup (HA (AF F) σ J) := Subgroup.ofDiv (closure S) ⟨1, h1⟩ hdiv
  have hmono : closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε', x = γ * h} ⊆ closure S :=
    closure_mono (by
      rintro _ ⟨g, hg, h, hh, rfl⟩
      exact ⟨g, hg, h, SUSupp_mono σ J hεε hh, rfl⟩)
  let K := Cg.comap (trunc σ J η hηη)
  have hlist : ∀ l : List ((Fin M → E) × (Fin M → E) × E),
      (∀ p ∈ l, hE σ J p.1 p.1 ≠ 0 ∧ hE σ J p.2.1 p.2.1 ≠ 0 ∧ p.2.2 * σ p.2.2 = 1) →
      ∃ p ∈ K, (p.1 : Matrix (Fin M) (Fin M) E) =
        (l.map fun p => qr σ J p.1 p.2.2 * qr σ J p.2.1 (σ p.2.2)).prod := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨1, K.one_mem, by simp⟩
    | cons q l ih =>
      intro hl
      obtain ⟨p₂, hp₂, e₂⟩ := ih (fun p hp => hl p (List.mem_cons_of_mem _ hp))
      obtain ⟨hx, hy, hu⟩ := hl q List.mem_cons_self
      obtain ⟨z, hzz, c1, c2⟩ := hz q.1 q.2.1 hx hy
      obtain ⟨p₁, e₁, hp₁⟩ := GlobalTheory.T.quasiReflectionPair_truncation_mem_closure H1 F E σ hcm M J hJ S₁' S₂' ε' hε' hne η hηη q.1 q.2.1 z q.2.2 hu hx hy
        hzz c1 c2
      refine ⟨p₁ * p₂, K.mul_mem (hmono hp₁) hp₂, ?_⟩
      rw [List.map_cons, List.prod_cons, ← e₁, ← e₂]
      rfl
  obtain ⟨hγa, hγr⟩ := hγ
  change HA.mat (AF F) σ J γ ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) at hγr
  obtain ⟨g0, hg0, hg0e⟩ := Subgroup.mem_map.1 hγr
  have hmat : ((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      RingHom.mapMatrix (inclR (AF F)) (g0 : Matrix (Fin M) (Fin M) E) := by
    rw [← hg0e]
    rfl
  have hdet : (g0 : Matrix (Fin M) (Fin M) E).det = 1 := by
    have h := StrongApprox.mem_SUAdelic.1 hγa
    rw [hmat, ← RingHom.map_det] at h
    haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
    have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective
    exact hinj (h.trans (map_one _).symm)
  obtain ⟨l, hl, hle⟩ := GlobalTheory.T.specialUnitary_eq_prod_quasiReflectionPairs F E σ hcm M J hJ g0 hg0 hdet
  obtain ⟨p, hp, hpe⟩ := hlist l hl
  have hpg : p = ⟨g0, hg0⟩ := Subtype.ext (Units.ext (hpe.trans hle.symm))
  have hxe : x = trunc σ J η hηη ⟨g0, hg0⟩ := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    refine (hx i j).trans ?_
    change _ = (1 + algebraMap (AF F) (AF F ⊗[F] E) η • (rmat (F := F) g0 - 1)) i j
    rw [hmat]
    simp [rmat]
  rw [hxe, ← hpg]
  exact hp

end GlobalTheory.SUAssemble

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_specialUnitary_mem_closure_strongApprox : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0)) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ γ ∈ SURat σ J, ∀ x : HA (AF F) σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j) → x ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  atlas_forward_decl GlobalTheory.SUAssemble.assemble
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.StrongApproxSUProof

theorem strongApproxSU : StrongApproxSU := by
  intro F E _ _ _ _ _ σ hcm M J hM hJ S₁ S₂ ε hε hnc g hg
  have h3 := GlobalTheory.T.truncation_specialUnitary_mem_closure_strongApprox GlobalTheory.T.specialUnitary_fixing_plane_complement_mem_closure GlobalTheory.T.exists_isotropic_places_alt F E σ hcm M J hM hJ S₁ S₂ ε hε hnc
  refine closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces F E σ hcm M J hJ g hg)
  rintro x ⟨T₁, T₂, η, hη, hx⟩
  refine closure_minimal ?_ isClosed_closure (GlobalTheory.T.mem_closure_rational_points_unitary_group F E σ hcm M J hJ T₁ T₂ η hη x hx)
  rintro y ⟨γ, hγ, hy⟩
  exact h3 T₁ T₂ η hη γ hγ y hy

end GlobalTheory.StrongApproxSUProof
end
