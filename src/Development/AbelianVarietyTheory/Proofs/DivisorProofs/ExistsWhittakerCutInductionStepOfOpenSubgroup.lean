import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
import BuildAid.ForwardExisting

section
section
open Matrix Topology

noncomputable section

namespace GlobalTheory.JSW.KirFin

theorem exists_charSum_eq_on_compact : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 →
    ∀ {ι : Type} [Fintype ι] (K : Set (ι → F)), IsCompact K → ∀ Φ : (ι → F) → ℂ, IsLocallyConstant Φ →
    ∃ T : (ι → F) →₀ ℂ, ∀ r ∈ K, (T.sum fun v c => c * ψ (r ⬝ᵥ v)) = Φ r := by
  intro F _ ψ hψ hψ1 ι _ K hK Φ hΦ
  classical
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ1 (AddChar.ext _ _ h)
  let χ : (ι → F) → (ι → F) → ℂ := fun v r => ψ (r ⬝ᵥ v)
  let S : Set ((ι → F) → ℂ) := Set.range χ
  have hχmul : ∀ v w, χ v * χ w = χ (v + w) := by
    intro v w; funext r; simp [χ, dotProduct_add, AddChar.map_add_eq_mul]
  have hχ0 : χ 0 = 1 := by funext r; simp [χ]
  have hlc : ∀ v, IsLocallyConstant (χ v) := fun v =>
    hψ.comp_continuous (continuous_id.dotProduct continuous_const)
  let L : Subalgebra ℂ ((ι → F) → ℂ) :=
    { carrier := {a | IsLocallyConstant a}
      mul_mem' := fun ha hb => IsLocallyConstant.mul ha hb
      add_mem' := fun ha hb => IsLocallyConstant.add ha hb
      algebraMap_mem' := fun c => IsLocallyConstant.const _ }
  let A := Algebra.adjoin ℂ S
  have hAL : A ≤ L := Algebra.adjoin_le (by rintro _ ⟨v, rfl⟩; exact hlc v)
  have hAspan : ∀ a ∈ A, a ∈ Submodule.span ℂ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span hx
    | algebraMap c =>
      have : algebraMap ℂ ((ι → F) → ℂ) c = c • χ 0 := by
        rw [hχ0, Algebra.algebraMap_eq_smul_one]
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
      exact ⟨v + w, (hχmul v w).symm⟩
  let ρ : ((ι → F) → ℂ) →ₐ[ℂ] (K → ℂ) :=
    { toFun := fun a x => a x.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨a, ha, e⟩ := mem_of_separates (A.map ρ)
    (by rintro _ ⟨a, ha, rfl⟩; exact (hAL ha).comp_continuous continuous_subtype_val)
    (by
      intro x y hxy
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (Subtype.coe_ne_coe.2 hxy)
      refine ⟨ρ (χ (Pi.single i (t / (x.1 i - y.1 i)))), ⟨_, Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩,
        fun h => ht ?_⟩
      change ψ (x.1 ⬝ᵥ _) = ψ (y.1 ⬝ᵥ _) at h
      rw [dotProduct_single, dotProduct_single] at h
      have h2 : x.1 i * (t / (x.1 i - y.1 i)) = t + y.1 i * (t / (x.1 i - y.1 i)) := by
        have := sub_ne_zero.2 hi
        field_simp
        ring
      rw [h2, AddChar.map_add_eq_mul] at h
      exact (mul_eq_right₀ (ψ.val_isUnit _).ne_zero).1 h)
    (hΦ.comp_continuous continuous_subtype_val)
  obtain ⟨T, hT⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hAspan a ha)
  refine ⟨T, fun r hr => ?_⟩
  have h1 := congrFun e ⟨r, hr⟩
  change a r = Φ r at h1
  rw [← h1, ← hT]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, χ]

end GlobalTheory.JSW.KirFin
end
end

open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_characterSum_eq_locallyConstant_on_compact : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ {ι : Type} [Fintype ι] (K : Set (ι → F)), IsCompact K → ∀ Φ : (ι → F) → ℂ, IsLocallyConstant Φ → ∃ T : (ι → F) →₀ ℂ, ∀ r ∈ K, (T.sum fun v c => c * ψ (r ⬝ᵥ v)) = Φ r := by
  atlas_forward_decl GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact
end

section
open Matrix Topology

namespace GlobalTheory.JSW

theorem isCompact_charAnnihilator_of_mem_nhds_zero {F : Type} [NormedField F] [ProperSpace F] (ψ : AddChar F ℂ)
    (hlc : IsLocallyConstant ψ) (hψ : ψ ≠ 1) {ι : Type} [Fintype ι] (L : Set (ι → F))
    (hL : L ∈ nhds (0 : ι → F)) :
    IsCompact {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} := by
  classical
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 hψ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hL
  have hcont : Continuous (fun x : F => ψ x) := hlc.continuous
  have hclosed : IsClosed {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} := by
    have : {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} = ⋂ y ∈ L, {r : ι → F | ψ (r ⬝ᵥ y) = 1} := by
      ext r; simp
    rw [this]
    refine isClosed_biInter fun y _ => isClosed_eq ?_ continuous_const
    refine hcont.comp ?_
    simp only [dotProduct]
    fun_prop
  have hR : 0 ≤ ‖t‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hsub : {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} ⊆ Metric.closedBall 0 (‖t‖ / ε) := by
    intro r hr
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    intro i
    by_contra hlt
    push_neg at hlt
    have hri : r i ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hlt; linarith
    have hpos : 0 < ‖r i‖ := norm_pos_iff.2 hri
    have hy : Pi.single i (t / r i) ∈ L := by
      apply hball
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same, norm_div, div_lt_iff₀ hpos]
        rw [div_lt_iff₀ hε] at hlt
        linarith
      · rw [Pi.single_eq_of_ne hj, norm_zero]; exact hε
    have := hr _ hy
    rw [dotProduct_single, mul_div_cancel₀ _ hri] at this
    exact ht this
  exact (isCompact_closedBall 0 (‖t‖ / ε)).of_isClosed_subset hclosed hsub

end GlobalTheory.JSW
end

section
section
noncomputable section

open Matrix Topology

namespace GlobalTheory.JSW.Orbit

theorem isClopen_orbit : ∀ {F : Type} [NormedField F] {n : ℕ} (B : Subgroup (GL (Fin n) F)),
    IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B : Set (GL (Fin n) F)) → ∀ r₀ : Fin n → F, r₀ ≠ 0 →
    IsClopen {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} := by
  intro F _ n B hBc hBo r₀ hr₀
  classical
  have hset : {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} =
      (fun b : GL (Fin n) F => r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)) '' (B : Set (GL (Fin n) F)) := by
    ext r
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact (hBc.image (continuous_const.matrix_vecMul Units.continuous_val)).isClosed
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨b, hb, rfl⟩
    set r := r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F) with hr
    have hr0 : r ≠ 0 := by
      intro h
      apply hr₀
      have : r ᵥ* ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = r₀ := by
        rw [hr, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
      rw [← this, h, zero_vecMul]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hr0
    let c : Fin n → F := Pi.single i (r i)⁻¹
    have hc : r ⬝ᵥ c = 1 := by
      simp only [c, dotProduct_single]
      exact mul_inv_cancel₀ hi
    obtain ⟨O, hO, hOB⟩ := GlobalTheory.JSW.KirFin.isEmbedding_coe.isInducing.isOpen_iff.1 hBo
    let s : (Fin n → F) → Matrix (Fin n) (Fin n) F := fun y => 1 + vecMulVec c (y - r)
    have hs : Continuous s :=
      continuous_const.add (continuous_const.matrix_vecMulVec (continuous_id.sub continuous_const))
    have hs1 : s r = 1 := by simp [s]
    have h1O : (1 : Matrix (Fin n) (Fin n) F) ∈ O := by
      have : (1 : GL (Fin n) F) ∈ (B : Set (GL (Fin n) F)) := B.one_mem
      rw [← hOB] at this
      exact this
    have e1 : ∀ᶠ y in 𝓝 r, s y ∈ O := hs.continuousAt.eventually_mem (hO.mem_nhds (by rw [hs1]; exact h1O))
    have e2 : ∀ᶠ y in 𝓝 r, (s y).det ≠ 0 := hs.matrix_det.continuousAt.eventually_ne (by simp [hs1])
    filter_upwards [e1, e2] with y hy1 hy2
    let u : GL (Fin n) F := GeneralLinearGroup.mkOfDetNeZero _ hy2
    have hu : u ∈ B := by
      have : u ∈ (fun g : GL (Fin n) F => g.val) ⁻¹' O := hy1
      rw [hOB] at this
      exact this
    refine ⟨b * u, B.mul_mem hb hu, ?_⟩
    change y = r₀ ᵥ* ((b : Matrix (Fin n) (Fin n) F) * s y)
    rw [← vecMul_vecMul, ← hr]
    change y = r ᵥ* (1 + vecMulVec c (y - r))
    rw [vecMul_add, vecMul_one, vecMul_vecMulVec, hc]
    simp

end GlobalTheory.JSW.Orbit
end
end

open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_rowVector_orbit_compactOpen_GL : ∀ {F : Type} [NormedField F] {n : ℕ} (B : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B : Set (GL (Fin n) F)) → ∀ r₀ : Fin n → F, r₀ ≠ 0 → IsClopen {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} := by
  atlas_forward_decl GlobalTheory.JSW.Orbit.isClopen_orbit
end

section
open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

theorem eqv_cor_mul_col {F : Type} [NormedField F] {ψ : AddChar F ℂ} {m : ℕ} {W : GL (Fin (m + 2)) F → ℂ}
    (hW : Eqv ψ W) (h : GL (Fin (m + 1)) F) (x : Fin (m + 1) → F) :
    W (cor h * mir 1 x) = ψ (lr h ⬝ᵥ x) * W (cor h) := by
  change W (mir h 0 * mir 1 x) = _
  rw [mir_mul, hW.apply_mir, mul_one, add_zero]
  rfl

theorem eqv_act {F : Type} [NormedField F] {ψ : AddChar F ℂ} {n : ℕ} {W : GL (Fin n) F → ℂ}
    (hW : Eqv ψ W) (T : GL (Fin n) F →₀ ℂ) : Eqv ψ (act T W) := fun u hu g => by
  unfold act
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [mul_assoc u, hW u hu]
  ring

theorem lr_ne_zero {F : Type} [NormedField F] {m : ℕ} (h : GL (Fin (m + 1)) F) : lr h ≠ 0 := fun h0 => by
  have h1 : lr (h * h⁻¹) = 0 := by rw [lr_mul, h0, zero_vecMul]
  rw [mul_inv_cancel] at h1
  have := congrFun h1 (Fin.last m)
  simp [lr] at this

end GlobalTheory.JSW.Cut
end

section
section
open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

theorem exists_mul_lr {F : Type} [NormedField F] [ProperSpace F] {ψ : AddChar F ℂ} (hψ : IsLocallyConstant ψ)
    (hψ1 : ψ ≠ 1) {m : ℕ} {L : Set (Fin (m + 1) → F)} (hL : L ∈ nhds (0 : Fin (m + 1) → F))
    (T' : GL (Fin (m + 1)) F →₀ ℂ) (κ : GL (Fin (m + 1)) F → GL (Fin (m + 1)) F) (Φ : (Fin (m + 1) → F) → ℂ)
    (hΦ : IsLocallyConstant Φ) :
    ∃ M₂ : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f →
      (∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F,
      act (comp M₂ (T'.sum fun k c => Finsupp.single (cor (κ k)) c)) f (cor h) =
        Φ (lr h) * act (T'.sum fun k c => Finsupp.single (cor (κ k)) c) f (cor h) := by
  classical
  have hK := GlobalTheory.JSW.isCompact_charAnnihilator_of_mem_nhds_zero ψ hψ hψ1 L hL
  set K := {r : Fin (m + 1) → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} with hKdef
  let K' : Set (Fin (m + 1) → F) := ⋃ k ∈ T'.support, (fun r => r ᵥ* ((κ k)⁻¹).val) '' K
  have hK' : IsCompact K' := T'.support.isCompact_biUnion fun k _ =>
    hK.image (continuous_id.matrix_vecMul continuous_const)
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_finite_characterSum_eq_locallyConstant_on_compact ψ hψ hψ1 K' hK' Φ hΦ
  set T₂ : GL (Fin (m + 2)) F →₀ ℂ := T'.sum fun k c => Finsupp.single (cor (κ k)) c with hT₂def
  let M₂ : GL (Fin (m + 2)) F →₀ ℂ := M.sum fun v c => Finsupp.single (mir 1 v) c
  refine ⟨M₂, fun f hf hfL h => ?_⟩
  have hT₂ : act T₂ f (cor h) = T'.sum fun k c => c * f (cor (h * κ k)) := by
    simp only [T₂, act_finsupp_sum, act_single, map_mul]
  rw [act_comp]
  simp only [M₂, act_finsupp_sum, act_single, eqv_cor_mul_col (eqv_act hf T₂), ← mul_assoc]
  rw [← Finsupp.sum_mul]
  by_cases h0 : act T₂ f (cor h) = 0
  · rw [h0, mul_zero, mul_zero]
  · rw [hM]
    rw [hT₂] at h0
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    have hk1 := right_ne_zero_of_mul hk0
    refine Set.mem_iUnion₂.2 ⟨k, hk, lr (h * κ k), fun y hy => ?_, ?_⟩
    · have := hfL y hy (cor (h * κ k))
      rw [eqv_cor_mul_col hf] at this
      exact (mul_eq_right₀ hk1).1 this
    · simp only
      rw [← lr_mul, mul_inv_cancel_right]

theorem exists_cut_cor_of_sub : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ U : Subgroup (GL (Fin (m + 1)) F), IsCompact (U : Set (GL (Fin (m + 1)) F)) → IsOpen (U : Set (GL (Fin (m + 1)) F)) → ∀ z : GL (Fin (m + 1)) F, ∃ U₁ : Subgroup (GL (Fin (m + 1)) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin (m + 1)) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 1)) F))) {g | ∃ p : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1 ∧ ∃ u ∈ U₁, g = p * u}) → ∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h := by
  intro F _ _ _ ψ hψ hψ1 m H B hBc hBo L hL h₀
  classical
  let U : Subgroup (GL (Fin (m + 1)) F) := B.map (MulAut.conj h₀).toMonoidHom
  have hUe : (U : Set (GL (Fin (m + 1)) F)) = (fun b => h₀ * b * h₀⁻¹) '' B := by
    ext x; simp [U]
  have hUm : ∀ b ∈ B, h₀ * b * h₀⁻¹ ∈ U := fun b hb => ⟨b, hb, rfl⟩
  have hUB : ∀ u ∈ U, h₀⁻¹ * u * h₀ ∈ B := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [mul_assoc] using hb
  have hUc : IsCompact (U : Set (GL (Fin (m + 1)) F)) := by
    rw [hUe]; exact hBc.image (by fun_prop)
  have hUo : IsOpen (U : Set (GL (Fin (m + 1)) F)) := by
    rw [hUe]; exact ((isOpenMap_mul_right h₀⁻¹).comp (isOpenMap_mul_left h₀)) _ hBo
  obtain ⟨U₁, hU₁U, hU₁o, T', hT'⟩ := H U hUc hUo 1
  have hU₁c : IsCompact (U₁ : Set (GL (Fin (m + 1)) F)) :=
    hUc.of_isClosed_subset (U₁.isClosed_of_isOpen hU₁o) hU₁U
  have hOe := GlobalTheory.T.isClopen_rowVector_orbit_compactOpen_GL U₁ hU₁c hU₁o (lr 1) (lr_ne_zero 1)
  let R : GL (Fin (m + 1)) F → Set (Fin (m + 1) → F) := fun a =>
    (fun r => r ᵥ* ((a * h₀)⁻¹).val) ⁻¹' {r | ∃ b ∈ U₁, r = lr 1 ᵥ* (b : Matrix (Fin (m + 1)) (Fin (m + 1)) F)}
  have hR : ∀ a, IsClopen (R a) := fun a => hOe.preimage (continuous_id.matrix_vecMul continuous_const)

  have hC : ∀ a ∈ U, ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * cor b) = f g) →
      ∀ h, lr h ∈ R a → act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        (cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (cor h)) h := by
    intro a ha f hf hfB h hRa
    obtain ⟨v, hv, e⟩ := hRa
    have e' : lr (h * h₀⁻¹ * a⁻¹) = lr (1 * v) := by
      rw [show h * h₀⁻¹ * a⁻¹ = h * (a * h₀)⁻¹ by group]
      exact e
    have hmem : h * h₀⁻¹ * a⁻¹ ∈ {g | ∃ p : GL (Fin (m + 1)) F, lr p = lr 1 ∧ ∃ u ∈ U₁, g = p * u} :=
      ⟨h * h₀⁻¹ * a⁻¹ * v⁻¹, by rw [lr_mul_congr e' v⁻¹, one_mul, mul_inv_cancel], v, hv, by group⟩
    have h2 := hT' (fun g => f (cor (g * h₀)))
      (fun u hu g => by simp only [mul_assoc]; exact hf.res u hu _)
      (fun u hu g => by
        rw [show g * u * h₀ = g * h₀ * (h₀⁻¹ * u * h₀) by group, map_mul]
        exact hfB _ (hUB u hu) _)
      (h * h₀⁻¹ * a⁻¹) hmem
    have hT₂ : act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        T'.sum fun k c => c * f (cor (h * (h₀⁻¹ * a⁻¹ * k * h₀))) := by
      simp only [act_finsupp_sum, act_single, map_mul]
    have h3 : act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        act T' (fun g => f (cor (g * h₀))) (h * h₀⁻¹ * a⁻¹) := by
      rw [hT₂]
      simp only [act, mul_assoc]
    rw [h3, h2]
    have h4 : h * h₀⁻¹ * a⁻¹ ∈ cell 1 (U : Set (GL (Fin (m + 1)) F)) ↔
        h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
      constructor
      · rintro ⟨u, hu, c, hc, e⟩
        refine ⟨u, hu, h₀⁻¹ * (c * a) * h₀, hUB _ (U.mul_mem hc ha), ?_⟩
        rw [show h = h * h₀⁻¹ * a⁻¹ * (a * h₀) by group, e]
        group
      · rintro ⟨u, hu, c, hc, rfl⟩
        exact ⟨u, hu, h₀ * c * h₀⁻¹ * a⁻¹, U.mul_mem (hUm c hc) (U.inv_mem ha), by group⟩
    by_cases h5 : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
    · rw [Set.indicator_of_mem h5, Set.indicator_of_mem (h4.2 h5)]
      rw [show h * h₀⁻¹ * a⁻¹ * h₀ = h * (h₀⁻¹ * a⁻¹ * h₀) by group, map_mul]
      exact hfB _ (by simpa using hUB _ (U.inv_mem ha)) _
    · rw [Set.indicator_of_notMem h5, Set.indicator_of_notMem (fun h6 => h5 (h4.1 h6))]

  have key : ∀ A : Finset (GL (Fin (m + 1)) F), (∀ a ∈ A, a ∈ U) → ∃ S : GL (Fin (m + 2)) F →₀ ℂ,
      ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * cor b) = f g) →
      (∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F,
      act S f (cor h) = (⋃ a ∈ A, R a).indicator 1 (lr h) *
        (cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (cor h)) h := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro _; exact ⟨0, fun f _ _ _ h => by simp⟩
    | insert a A haA ih =>
      intro hA
      obtain ⟨S, hS⟩ := ih (fun b hb => hA b (Finset.mem_insert_of_mem hb))
      have ha : a ∈ U := hA a (Finset.mem_insert_self a A)
      have hcl : IsClopen (R a \ ⋃ b ∈ A, R b) := (hR a).diff (isClopen_biUnion_finset fun b _ => hR b)
      obtain ⟨M₂, hM₂⟩ := exists_mul_lr hψ hψ1 hL T' (fun k => h₀⁻¹ * a⁻¹ * k * h₀)
        ((R a \ ⋃ b ∈ A, R b).indicator 1) (LocallyConstant.charFn ℂ hcl).isLocallyConstant
      refine ⟨S + comp M₂ (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c),
        fun f hf hfB hfL h => ?_⟩
      rw [act_add, hS f hf hfB hfL h, hM₂ f hf hfL h]
      by_cases h1 : lr h ∈ ⋃ b ∈ A, R b
      · have h2 : lr h ∈ ⋃ b ∈ insert a A, R b := by
          rw [Finset.set_biUnion_insert]; exact Or.inr h1
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_notMem (s := R a \ ⋃ b ∈ A, R b) (fun h3 => h3.2 h1)]
        simp
      · by_cases h3 : lr h ∈ R a
        · have h2 : lr h ∈ ⋃ b ∈ insert a A, R b := by
            rw [Finset.set_biUnion_insert]; exact Or.inl h3
          rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_mem (s := R a \ ⋃ b ∈ A, R b) ⟨h3, h1⟩,
            hC a ha f hf hfB h h3]
          simp
        · have h2 : lr h ∉ ⋃ b ∈ insert a A, R b := by
            rw [Finset.set_biUnion_insert]; exact fun h4 => h4.elim h3 h1
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
            Set.indicator_of_notMem (s := R a \ ⋃ b ∈ A, R b) (fun h4 => h3 h4.1)]
          simp
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover
    (fun a : U => (fun x => x * (a : GL (Fin (m + 1)) F)⁻¹) ⁻¹' (U₁ : Set (GL (Fin (m + 1)) F)))
    (fun a => hU₁o.preimage (continuous_mul_right _))
    (fun u hu => Set.mem_iUnion.2 ⟨⟨u, hu⟩, by simp [U₁.one_mem]⟩)
  obtain ⟨S, hS⟩ := key (t.image Subtype.val) (fun a ha => by
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 ha
    exact b.2)
  refine ⟨S, fun f hf hfB hfL h => ?_⟩
  rw [hS f hf hfB hfL h]
  by_cases hh : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
  · have hmem : lr h ∈ ⋃ a ∈ t.image Subtype.val, R a := by
      obtain ⟨u, hu, c, hc, rfl⟩ := hh
      obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.1 (ht (hUm c hc))
      refine Set.mem_iUnion₂.2 ⟨i.1, Finset.mem_image_of_mem _ hi, h₀ * c * h₀⁻¹ * (i : GL (Fin (m + 1)) F)⁻¹, hw, ?_⟩
      show lr (u * h₀ * c) ᵥ* _ = _
      rw [← lr_mul, show u * h₀ * c * ((i : GL (Fin (m + 1)) F) * h₀)⁻¹ =
        u * (h₀ * c * h₀⁻¹ * (i : GL (Fin (m + 1)) F)⁻¹) by group, lr_mul_congr (lr_of_mem hu), one_mul, ← lr_mul, one_mul]
    rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem hh, mul_zero]

end GlobalTheory.JSW.Cut
end

open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_whittakerCut_inductionStep_of_open_subgroup : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ U : Subgroup (GL (Fin (m + 1)) F), IsCompact (U : Set (GL (Fin (m + 1)) F)) → IsOpen (U : Set (GL (Fin (m + 1)) F)) → ∀ z : GL (Fin (m + 1)) F, ∃ U₁ : Subgroup (GL (Fin (m + 1)) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin (m + 1)) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 1)) F))) {g | ∃ p : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1 ∧ ∃ u ∈ U₁, g = p * u}) → ∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h := by
  atlas_forward_decl GlobalTheory.JSW.Cut.exists_cut_cor_of_sub
end
