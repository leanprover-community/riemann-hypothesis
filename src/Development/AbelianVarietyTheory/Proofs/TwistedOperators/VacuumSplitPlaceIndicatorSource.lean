import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumEigenvalueEqOneSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzTensorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemAdelicSchwartzSpaceNumberFieldOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMemStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCellStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBloc
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairIsUnitDetBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBigCellExistsAdmissibleInverse
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall

section
section
open Matrix

namespace GlobalTheory.BlockInvertibleLocal

theorem exists_linearMap_injective_add_comp {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (a c : V →ₗ[k] V) (h : LinearMap.ker a ⊓ LinearMap.ker c = ⊥) :
    ∃ x : V →ₗ[k] V, Function.Injective (a + x ∘ₗ c) := by
  set W := LinearMap.range (c ∘ₗ (LinearMap.ker a).subtype) with hWdef
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl (LinearMap.range a)
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl W
  have hinjK : Function.Injective (c ∘ₗ (LinearMap.ker a).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hu' : (u : V) ∈ LinearMap.ker a ⊓ LinearMap.ker c :=
      Submodule.mem_inf.2 ⟨u.2, by simpa using hu⟩
    rw [h, Submodule.mem_bot] at hu'
    exact Subtype.ext hu'
  have h1 := LinearMap.finrank_range_of_inj hinjK
  have h2 := Submodule.finrank_add_eq_of_isCompl hR
  have h3 := LinearMap.finrank_range_add_finrank_ker a
  have hdim : Module.finrank k W = Module.finrank k R := by rw [hWdef, h1]; omega
  let e : W ≃ₗ[k] R := LinearEquiv.ofFinrankEq W R hdim
  let x : V →ₗ[k] V := LinearMap.ofIsCompl hW (R.subtype ∘ₗ e.toLinearMap) 0
  refine ⟨x, ?_⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨w, hw, w', hw', hsum⟩ := Submodule.mem_sup.1 (hW.sup_eq_top ▸ Submodule.mem_top : c v ∈ W ⊔ W')
  have hxw : x (c v) = ((e ⟨w, hw⟩ : R) : V) := by
    rw [← hsum, map_add]
    have hl := LinearMap.ofIsCompl_left_apply (φ := R.subtype ∘ₗ e.toLinearMap) (ψ := (0 : W' →ₗ[k] V)) hW ⟨w, hw⟩
    have hr := LinearMap.ofIsCompl_right_apply (φ := R.subtype ∘ₗ e.toLinearMap) (ψ := (0 : W' →ₗ[k] V)) hW ⟨w', hw'⟩
    simp only at hl hr
    rw [hl, hr]; simp
  have hv' : a v + ((e ⟨w, hw⟩ : R) : V) = 0 := by
    rw [← hxw]; simpa using hv
  have hav : a v = 0 := by
    refine Submodule.disjoint_def.1 hR.disjoint (a v) (LinearMap.mem_range_self a v) ?_
    rw [eq_neg_of_add_eq_zero_left hv']
    exact R.neg_mem (e ⟨w, hw⟩).2
  have he0 : ((e ⟨w, hw⟩ : R) : V) = 0 := by simpa [hav] using hv'
  have hw0 : w = 0 := by
    have : e ⟨w, hw⟩ = 0 := Subtype.ext he0
    have : (⟨w, hw⟩ : W) = 0 := by simpa using this
    simpa using congrArg Subtype.val this
  have hcvW : c v ∈ W := ⟨⟨v, hav⟩, rfl⟩
  have hcvW' : c v ∈ W' := by rw [← hsum, hw0, zero_add]; exact hw'
  have hcv : c v = 0 := Submodule.disjoint_def.1 hW.disjoint _ hcvW hcvW'
  have hmem : v ∈ LinearMap.ker a ⊓ LinearMap.ker c := Submodule.mem_inf.2 ⟨hav, hcv⟩
  rw [h, Submodule.mem_bot] at hmem
  exact hmem

theorem exists_isUnit_det_add_mul_of_field {k : Type} [Field k] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) k) (h : IsUnit (fromBlocks A B C D).det) :
    ∃ X : Matrix (Fin n) (Fin n) k, IsUnit (A + X * C).det := by
  have hinj : Function.Injective (fromBlocks A B C D).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 h)
  have hker : LinearMap.ker (toLin' A) ⊓ LinearMap.ker (toLin' C) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, toLin'_apply, toLin'_apply] at hv
    have hz : (fromBlocks A B C D) *ᵥ (Sum.elim v 0) = (fromBlocks A B C D) *ᵥ 0 := by
      rw [fromBlocks_mulVec, mulVec_zero]
      ext i <;> cases i <;> simp [hv.1, hv.2]
    have h2 := hinj hz
    rw [Submodule.mem_bot]
    funext i
    exact congrFun h2 (Sum.inl i)
  obtain ⟨x, hx⟩ := exists_linearMap_injective_add_comp _ _ hker
  refine ⟨LinearMap.toMatrix' x, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  convert hx using 1
  funext v
  simp [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]

theorem exists_isUnit_det_add_mul : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  intro O _ _ n A B C D h
  have h' : IsUnit (fromBlocks (A.map (IsLocalRing.residue O)) (B.map (IsLocalRing.residue O))
      (C.map (IsLocalRing.residue O)) (D.map (IsLocalRing.residue O))).det := by
    rw [← fromBlocks_map]
    have := h.map (IsLocalRing.residue O)
    rwa [RingHom.map_det] at this
  obtain ⟨Y, hY⟩ := exists_isUnit_det_add_mul_of_field _ _ _ _ h'
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) O, X.map (IsLocalRing.residue O) = Y :=
    ⟨Y.map (Function.surjInv IsLocalRing.residue_surjective), by
      ext i j; simp [Function.surjInv_eq]⟩
  refine ⟨X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add _), Matrix.map_mul, hX]
  exact hY.ne_zero

end GlobalTheory.BlockInvertibleLocal
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_det_add_mul_of_fromBlocks_localRing : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  atlas_forward_decl GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitDictHerm

open GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tensAt_compFin (v : Pl F) (z : AE F E) : tensAt E v (compFin F E v z) = atPlace v 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a x =>
    show atPlace v (evFin F v a) ⊗ₜ[F] x = atPlace v 1 • (a ⊗ₜ[F] x)
    rw [TensorProduct.smul_tmul', smul_eq_mul, atPlace_mul_right, one_mul]

theorem at_atPlace (v : Pl F) (c : Fv F v) : At (evFin F v) (atPlace v c) := fun u hu => by
  rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]

theorem at_tensAt (v : Pl F) (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := fun u hu => by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
  | tmul a x =>
    rw [tensAt_tmul, TensorProduct.smul_tmul', at_atPlace v a u hu, TensorProduct.zero_tmul]

theorem eq_tensAt_of_at {v : Pl F} {z : AE F E} (hz : At (evFin F v) z) : z = tensAt E v (compFin F E v z) := by
  rw [tensAt_compFin]
  have h1 : (1 - atPlace v 1) • z = 0 := hz _ (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (z : AE F E) :
    compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem piW_apply {v : Pl F} (τ : E →ₐ[F] Fv F v) (z : AE F E) : piW τ z = splitProj τ (compFin F E v z) := rfl

theorem piW_inclR {v : Pl F} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (AF F) x) = τ x := by
  show splitProj τ (evFin F v 1 ⊗ₜ[F] x) = τ x
  rw [map_one, splitProj_tmul, one_mul]

theorem piW_algebraMap {v : Pl F} (τ : E →ₐ[F] Fv F v) (a : AF F) :
    piW τ (algebraMap (AF F) (AE F E) a) = evFin F v a := by
  show splitProj τ (evFin F v a ⊗ₜ[F] 1) = evFin F v a
  rw [splitProj_tmul, map_one, mul_one]

theorem compFin_smul_inclR (v : Pl F) (a : AF F) (x : E) :
    compFin F E v (a • inclR (AF F) x) = evFin F v a ⊗ₜ[F] x := by
  show compFin F E v (a • ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem mem_latAt_iff {d : ℕ} (W : Spc F E d) (v : Pl F) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧ (fun j => compFin F E v (z j)) ∈ latLoc F W.L v := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      · convert tmul_mem_latLoc hav hy using 1
        funext j
        exact compFin_smul_inclR v a (y j)
    | zero => exact ⟨fun u _ => smul_zero u, by convert zero_mem (latLoc F W.L v) using 1; funext j; simp⟩
    | add x y _ _ hx hy =>
      refine ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], ?_⟩
      convert add_mem hx.2 hy.2 using 1
      funext j; simp
    | neg x _ hx =>
      refine ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], ?_⟩
      convert neg_mem hx.2 using 1
      funext j; simp
  · rintro ⟨hz, hl⟩
    have e : z = fun j => tensAt E v (compFin F E v (z j)) := funext fun j => eq_tensAt_of_at (fun u hu => by
      have := congrFun (hz u hu) j
      simpa using this)
    rw [e]
    refine latLoc_induction (p := fun Y => (fun j => tensAt E v (Y j)) ∈ GlobalTheory.InertSph.latAt W v)
      (fun c hc x hx => ?_) (by convert zero_mem (GlobalTheory.InertSph.latAt W v) using 1; funext j; simp) (fun Y Y' hY hY' => ?_)
      (fun Y hY => ?_) hl
    · refine AddSubgroup.subset_closure ⟨atPlace v c, at_atPlace v c, by rwa [evFin_atPlace], x, hx, ?_⟩
      funext j
      rw [tensAt_tmul]
      show _ = atPlace v c • ((1 : AF F) ⊗ₜ[F] x j)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · convert add_mem hY hY' using 1
      funext j; simp
    · convert neg_mem hY using 1
      funext j; simp

theorem mem_latAt_iff_bases {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {d : ℕ} (W : Spc F E d) {v : Pl F}
    (τ : E →ₐ[F] Fv F v) {b₁ b₂ : GL (Fin d) (Fv F v)} (hb₁ : IsSplitBasis τ W.L b₁)
    (hb₂ : IsSplitBasis (τ.comp σ) W.L b₂) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => piW τ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => piW (τ.comp σ) (z j)) i ∈
          v.adicCompletionIntegers F) := by
  have key : ∀ {ρ : E →ₐ[F] Fv F v} {b : GL (Fin d) (Fv F v)}, IsSplitBasis ρ W.L b → ∀ u : Fin d → Fv F v,
      (∀ i, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ u) i ∈ v.adicCompletionIntegers F) ↔
        u ∈ splitLat ρ W.L := by
    intro ρ b hb u
    rw [hb, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_latAt_iff, mem_latLoc_iff_split τ h, key hb₁, key hb₂]
  exact Iff.rfl

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    (by intro a b c; ring : ∀ a b c : E, a * b * c = c * (b * a)) _ _ _

theorem split_dict_herm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt V v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F V.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  intro F E _ _ _ _ _ σ B d V r s hB hV v hv _
  have h := hB.cm
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  obtain ⟨τ, -⟩ := (existsUnique_splitPrime_eq h hPQ (HeightOneSpectrum.ext hP) (HeightOneSpectrum.ext hQ)).exists
  haveI := hV.lat
  obtain ⟨b₁, hb₁⟩ := exists_isSplitBasis τ V.L h
  have hdet : V.J.det ≠ 0 := by
    intro h0
    obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ _ _ (hV.sig u)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hdetT : V.Jᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hJ : IsHermND σ V.Jᵀ := ⟨fun i j => hV.herm j i, hdetT⟩
  have hL : IsSelfDualAt σ V.Jᵀ V.L v := by
    refine (SelfDual.forall_isSelfDualAt_iff hdetT hV.lat).2 (fun y => ?_) v
    rw [hV.dual y]
    refine forall₂_congr fun x _ => ?_
    rw [hE_transpose]
    exact ⟨fun hi => ⟨⟨_, hi⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c⟩
  have hb₂ := IsSplitBasis.dual h hJ hL hb₁
  refine ⟨piW τ, piW (τ.comp σ), b₁, dualConj 1 (splitGram hJ τ * b₁), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, 1, by simp, ?_⟩
  · intro z; rw [piW_apply, piW_apply, compFin_cA, splitProj_comp]
  · intro z; rw [piW_apply, piW_apply, compFin_cA, splitProj_comp_sigR h]
  · exact piW_algebraMap τ
  · exact piW_algebraMap _
  · intro z hz h1 h2
    have e : compFin F E v z = 0 := split_ext h τ (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
    rw [eq_tensAt_of_at hz, e, map_zero]
  · intro x₁ x₂
    refine ⟨tensAt E v ((splitAlgEquiv h τ).symm (x₁, x₂)), at_tensAt v _, ?_, ?_⟩
    · rw [piW_apply, compFin_tensAt, splitProj_symm]
    · rw [piW_apply, compFin_tensAt, splitProj_comp_symm]
  · exact mem_latAt_iff_bases h V τ hb₁ hb₂
  · have eJ : (incM F V.J).map (piW τ) = V.J.map τ := by
      exact Matrix.ext fun i j => piW_inclR τ (V.J i j)
    have eT : V.J.map τ = ((splitGram hJ τ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ := by
      exact Matrix.ext fun i j => rfl
    have eG : V.J.map τ * (((splitGram hJ τ)⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ = 1 := by
      rw [eT, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
    rw [Matrix.map_one _ (by simp) (by simp), eJ, dualConj_one_val, mul_inv_rev, Units.val_mul, Matrix.transpose_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ (V.J.map τ), eG, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.transpose_one]

end GlobalTheory.SplitDictHerm
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_selfDual_lattice_split_place_dictionary : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt V v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F V.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  first | exact @GlobalTheory.SplitDictHerm.split_dict_herm | exact GlobalTheory.SplitDictHerm.split_dict_herm | (intros; apply GlobalTheory.SplitDictHerm.split_dict_herm <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CMSkewUnit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cm_sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cm_exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  haveI : IsTotallyComplex E := h.2.1
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex w)
  by_contra hne
  push_neg at hne
  apply hc
  ext x
  have hx := h.2.2.2 w.embedding x
  rw [hne x] at hx
  simpa [ComplexEmbedding.conjugate_coe_eq] using hx.symm

theorem cm_exists_skew (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨x, hx⟩ := cm_exists_moved σ h
  refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  rw [map_sub, cm_sigma_sigma σ h]; ring

end GlobalTheory.CMSkewUnit

namespace GlobalTheory.CMSkewUnit

theorem exists_unit_of_val_eq_one {F : Type} [Field F] [NumberField F] {v : Pl F} {x : Fv F v} (hx : Valued.v x = 1) :
    ∃ u : (v.adicCompletionIntegers F)ˣ, ((u : v.adicCompletionIntegers F) : Fv F v) = x := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hx; exact zero_ne_one hx
  have hmem : x ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_eq hx)
  have hmem' : x⁻¹ ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hx, inv_one])
  refine ⟨⟨⟨x, hmem⟩, ⟨x⁻¹, hmem'⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

end GlobalTheory.CMSkewUnit

namespace GlobalTheory.CMSkewUnit

theorem exists_skew_unit_at : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F) (π : AE F E →+* Fv F v),
    (∀ a : AF F, π (algebraMap (AF F) (AE F E) a) = evFin F v a) →
    ∃ δ : E, σ δ = -δ ∧ ∃ u : (v.adicCompletionIntegers F)ˣ,
      ((u : v.adicCompletionIntegers F) : Fv F v) = π (inclR (F := F) (AF F) δ) := by
  intro F E _ _ _ _ _ σ h v π hπ
  obtain ⟨δ₀, h0, hs⟩ := cm_exists_skew σ h
  have ht : π (inclR (F := F) (AF F) δ₀) ≠ 0 :=
    (map_ne_zero_iff (π.comp (inclR (F := F) (AF F))) (RingHom.injective _)).2 h0
  have hF : ∀ f : F, π (inclR (F := F) (AF F) (algebraMap F E f)) = algebraMap F (Fv F v) f := by
    intro f
    have e1 : inclR (F := F) (AF F) (algebraMap F E f) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) f) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes f
    rw [e1, hπ, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
  set t := π (inclR (F := F) (AF F) δ₀) with ht_def
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
  refine ⟨algebraMap F E (ϖ ^ WithZero.log (Valued.v t)) * δ₀, ?_, ?_⟩
  · rw [map_mul, AlgHom.commutes, hs]; ring
  · apply exists_unit_of_val_eq_one
    rw [map_mul, map_mul, hF, ← ht_def, map_mul]
    have e2 : Valued.v (algebraMap F (Fv F v) (ϖ ^ WithZero.log (Valued.v t))) =
        v.valuation F (ϖ ^ WithZero.log (Valued.v t)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [e2, map_zpow₀, hϖ]
    conv_lhs => rw [← WithZero.exp_log hvt]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp

end GlobalTheory.CMSkewUnit
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmSkew_element_unit_at_finitePlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl F) (π : AE F E →+* Fv F v),
    (∀ a : AF F, π (algebraMap (AF F) (AE F E) a) = evFin F v a) →
    ∃ δ : E, σ δ = -δ ∧ ∃ u : (v.adicCompletionIntegers F)ˣ,
      ((u : v.adicCompletionIntegers F) : Fv F v) = π (inclR (F := F) (AF F) δ) := by
  atlas_forward_decl GlobalTheory.CMSkewUnit.exists_skew_unit_at
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitChooseHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def scaleSpc {d : ℕ} (V : Spc F E d) (δ : E) : Spc F E d where
  J := δ • V.J
  L := V.L
  θ := V.θ
  bas := V.bas

theorem incM_smul {d : ℕ} (δ : E) (J : Matrix (Fin d) (Fin d) E) :
    incM F (δ • J) = inclR (F := F) (AF F) δ • incM F J := by
  ext i j
  simp [incM, Matrix.map_apply, Matrix.smul_apply, map_mul]

theorem dbl_smul {d : ℕ} (c : AE F E) (X : Matrix (Fin d) (Fin d) (AE F E)) : dbl (c • X) = c • dbl X := by
  simp [dbl, Matrix.fromBlocks_smul, smul_neg]

end GlobalTheory.SplitChooseHerm

namespace GlobalTheory.SplitChooseHerm

theorem exists_admissible_unipotent_split_place_hermitian : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  intro _ F E _ _ _ _ _ σ B d V r s hB hV v hv hψ h2 g hg
  obtain ⟨π₁, π₂, b₁, b₂, hP, S, hS, hSe⟩ := GlobalTheory.T.hermitian_selfDual_lattice_split_place_dictionary σ B V r s hB hV v hv hψ
  obtain ⟨δ, hδ, u, hu⟩ := GlobalTheory.T.exists_cmSkew_element_unit_at_finitePlace σ hB.cm v π₁ hP.2.2.1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have h0 : ((u : v.adicCompletionIntegers F) : Fv F v) = 0 := by rw [hu, map_zero, map_zero]
    exact u.ne_zero (Subtype.ext h0)
  have hcu : inclR (F := F) (AF F) δ⁻¹ * inclR (F := F) (AF F) δ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ0, map_one]
  have h2' : IsUnit (2 : v.adicCompletionIntegers F) := by
    have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h2
    rwa [map_ofNat] at this
  let W' : Spc F E d := scaleSpc V δ
  have hskew : ∀ i j, σ (W'.J j i) = -W'.J i j := by
    intro i j
    show σ (δ * V.J j i) = -(δ * V.J i j)
    rw [map_mul, hδ, hV.herm]
    ring
  have hS' : ∃ S' : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S'.det ∧
      S'.map (fun x => (x : Fv F v)) =
        (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W'.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
    refine ⟨(u : v.adicCompletionIntegers F) • S, ?_, ?_⟩
    · rw [Matrix.det_smul]
      exact (u.isUnit.pow _).mul hS
    · have e1 : (incM F W'.J).map π₁ = π₁ (inclR (F := F) (AF F) δ) • (incM F V.J).map π₁ := by
        show (incM F (δ • V.J)).map π₁ = _
        rw [incM_smul]
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply]
      rw [e1, Matrix.mul_smul, Matrix.smul_mul, ← hSe, ← hu]
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply]
  let g' : GlobalTheory.DblVac.UD σ W' := ⟨g.1, by
    have h := g.2
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F V.J) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F V.J) at h
    change ((g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)))ᵀ * dbl (incM F (δ • V.J)) *
      (g.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F (δ • V.J))
    rw [incM_smul, dbl_smul, Matrix.mul_smul, Matrix.smul_mul, h]⟩
  have hg' : g' ∈ GlobalTheory.DblVac.KD σ W' v := hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ :=
    GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt GlobalTheory.T.exists_dual_pair_isUnit_det_blocks' σ W' v hskew h2' π₁ π₂ b₁ b₂ hP hS' g' hg'
  refine ⟨Y, hYat, hYlat, ?_, M, hM, hMlat⟩
  change Yᵀ * incM F (δ • V.J) + incM F (δ • V.J) * Y.map (cA σ) = 0 at hYadm
  rw [incM_smul, Matrix.mul_smul, Matrix.smul_mul, ← smul_add] at hYadm
  have h3 := congrArg (fun X => inclR (F := F) (AF F) δ⁻¹ • X) hYadm
  simp only [smul_smul, hcu, one_smul, smul_zero] at h3
  exact h3

end GlobalTheory.SplitChooseHerm
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_unipotent_at_split_place : (∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ V v,
      ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt V v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt V v) ∧
        Yᵀ * incM F V.J + incM F V.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt V v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt V v := by
  atlas_forward_decl GlobalTheory.SplitChooseHerm.exists_admissible_unipotent_split_place_hermitian
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

theorem gen_diag_anti_split_herm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ H : Subgroup (GlobalTheory.DblVac.UD σ V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PDiag σ V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PAnti σ V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ V v, g ∈ H := by
  intro F E _ _ _ _ _ σ B d V r s hB hV v hv hψ h2 H hD hA g hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ := GlobalTheory.T.exists_admissible_unipotent_at_split_place GlobalTheory.T.exists_isUnit_det_add_mul_of_fromBlocks_localRing σ B V r s hB hV v hv hψ h2 g hg
  obtain ⟨p, hpK, hpD, hp⟩ := GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock σ V v h2 Y hYat hYlat hYadm
  obtain ⟨hpgK, hpg⟩ := hp g hg
  have hbig : GlobalTheory.DblVac.BigCell V v (p * g) := ⟨M, by rw [hpg]; exact hM, hMlat⟩
  obtain ⟨q, hqK, hqA, p', hp'K, hp'D, he⟩ := GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell σ V v h2 (p * g) hpgK hbig
  have hg' : g = p⁻¹ * (q * p') := by rw [← he]; group
  rw [hg']
  exact H.mul_mem (H.inv_mem (hD p hpK hpD)) (H.mul_mem (hA q hqK hqA) (hD p' hp'K hp'D))

end GlobalTheory.DblVac
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_diagonal_stabilizer_generated_hermitian_doubling : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ H : Subgroup (GlobalTheory.DblVac.UD σ V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PDiag σ V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PAnti σ V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ V v, g ∈ H := by
  atlas_forward_decl GlobalTheory.DblVac.gen_diag_anti_split_herm
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitVacV
open GlobalTheory.DblVacSiegel

theorem siegel_eigen_eq_one_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv d' dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (t : Matrix (Fin a) (Fin a) (AE F E)) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin a) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.V) (s : Matrix (Fin a) (Fin a) (AE F E)),
      GlobalTheory.DblVac.matD g * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin a → AE F E, (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * ((t⁻¹ : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E)) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (t : Matrix (Fin a) (Fin a) (AE F E))) *
          ((t⁻¹ : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hunr : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt (X.β / X.α) P := fun P hP => by
    have hPT : P ∉ above E (X.T : Set (Pl F)) := fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl F))))
    rw [div_eq_mul_inv]
    exact (hT.chars.unrβ P hPT).mul (hT.chars.unrα P hPT).inv
  have hβ : (X.β / X.α) (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any (v := v) G.V hT.geo.hV.lat hunr t (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) =
          (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * ((t : Matrix (Fin a) (Fin a) (AE F E)) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (u • ((t : Matrix (Fin a) (Fin a) (AE F E)) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  rw [hμ, map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl hrule
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

theorem eigen_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩ := hT.weil.2.1
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.V) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.vacuum_split_place_indicator_base hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr p hp
    have h1 := siegel_eigen_eq_one_any F E σ B a a' G X om om' hT v hv d' dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.V v, q ∈ GlobalTheory.DblVac.PAnti σ G.V → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.V v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.vacuum_split_place_indicator_base hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk
  have hfix : omd gd S = S :=
    GlobalTheory.T.split_place_diagonal_stabilizer_generated_hermitian_doubling σ B G.V _ _ hT.base hT.geo.hV v hsp₀ hψ htwo H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)

end GlobalTheory.SplitVacV

end
end
