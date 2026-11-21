import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import CompanionTheory.AutomorphicTheory.HarishChandraMultiplicity.HCMult
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX

section
open Matrix
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

section

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mem_of_forall_orthogonalComplement_inner_eq_zero (T : Submodule ℂ H) [FiniteDimensional ℂ T] {x : H} (h : ∀ y ∈ Tᗮ, ⟪y, x⟫_ℂ = 0) : x ∈ T := by
  rw [← Submodule.orthogonal_orthogonal T]
  exact (Submodule.mem_orthogonal' _ _).2 fun y hy => by rw [← inner_conj_symm, h y hy, map_zero]

theorem exists_sub_B (hK : KFSm) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) {v : smD ε σ} (hv : v ∈ KF ε σ) :
    ∃ S : Submodule ℂ (smD ε σ), FiniteDimensional ℂ S ∧ v ∈ S ∧ (S : Set (smD ε σ)) ⊆ KF ε σ ∧
      IsKStableSub ε (smE ε σ) S ∧ ∀ k ∈ Kset ε, ∀ w ∈ S, ∃ w' ∈ S, (w' : H) = σ k w := by
  obtain ⟨S, hSf, hvS, hSK⟩ := hv
  let S' : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hmap : S'.map (smD ε σ).subtype ≤ S := Submodule.map_comap_le _ _
  have hS'f : FiniteDimensional ℂ S' := by
    have e := Submodule.equivMapOfInjective (smD ε σ).subtype Subtype.val_injective S'
    have : FiniteDimensional ℂ (S'.map (smD ε σ).subtype) := Submodule.finiteDimensional_of_le hmap
    exact LinearEquiv.finiteDimensional e.symm
  have hKF : (S' : Set (smD ε σ)) ⊆ KF ε σ := fun w hw => ⟨S, hSf, hw, hSK⟩
  have hS'K : ∀ k ∈ Kset ε, ∀ w ∈ S', ∃ w' ∈ S', (w' : H) = σ k w := by
    intro k hk w hw
    have h1 : σ k w ∈ S := hSK k hk w hw
    have h2 : σ k w ∈ smD ε σ := (hK _ ε H σ hσ hirr).1 _ ⟨S, hSf, h1, hSK⟩
    exact ⟨⟨_, h2⟩, h1, rfl⟩
  exact ⟨S', hS'f, hvS, hKF, isKStableSub_of_kStable hσ (isDerivedOn_smE hσ) S' hS'f hS'K, hS'K⟩

theorem kavg_mem_B (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {e : Formalism.REAL.KG ε → ℂ} (he : Continuous e)
    (T : Submodule ℂ H) [FiniteDimensional ℂ T] {x : H} (hx : ∀ k : Formalism.REAL.KG ε, σ (Formalism.REAL.toMK k) x ∈ T) :
    Formalism.MainNotions.BridgeCPX.kavg hσ he x ∈ T := by
  refine mem_of_forall_orthogonalComplement_inner_eq_zero T fun y hy => ?_
  rw [show Formalism.MainNotions.BridgeCPX.kavg hσ he x = _ from Formalism.MainNotions.BridgeCPX.kavg_apply hσ he x, ← integral_inner (Formalism.MainNotions.BridgeCPX.kavg_integrable hσ he x)]
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right, Pi.zero_apply]
  rw [Submodule.inner_left_of_mem_orthogonal (hx k) hy, mul_zero]

end

theorem uIrr_of (hK : KFSm) (hC : CasScal) : UIrr := by
  intro n ε H _ _ _ σ hσ hirr N hNK hNst
  have hD := isDerivedOn_smE hσ
  obtain ⟨c, hc⟩ := hC n ε H σ hσ hirr
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
  obtain ⟨S, hSf, hvS, -, hSst, -⟩ := exists_sub_B hK hσ hirr (hNK hvN)
  let V := N ⊓ S
  have hVf : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_right
  have hVK : IsKStableSub ε (smE ε σ) V := fun a b hab w hw => ⟨hNst a b w hw.1, hSst a b hab w hw.2⟩
  have hgen : genSub (smE ε σ) V ≤ N := sInf_le ⟨inf_le_left, fun a b w hw => hNst a b w hw⟩
  set C := ((genSub (smE ε σ) V).map (smD ε σ).subtype).topologicalClosure with hCdef
  have hvC : (v : H) ∈ C := Submodule.le_topologicalClosure _
    (Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun T hT => hT.1 ⟨hvN, hvS⟩))
  have hCtop : C = ⊤ := by
    rcases hirr C (Submodule.isClosed_topologicalClosure _)
      (closure_genSub_stable hσ hD hVf hVK fun w _ => hc w) with h | h
    · exfalso
      rw [h, Submodule.mem_bot] at hvC
      exact hv0 (Subtype.ext hvC)
    · exact h
  refine Set.Subset.antisymm hNK fun u hu => ?_
  obtain ⟨e, T, he, hTf, hrange, hfix⟩ :=
    Formalism.MainNotions.BridgeCPX.HCAdm_of_mult CompanionTheory.HCMult.harish_chandra_multiplicity n ε H σ hσ hirr (u : H) hu
  set P := Formalism.MainNotions.BridgeCPX.kavg hσ he
  let NT : Submodule ℂ H := N.map (smD ε σ).subtype ⊓ T
  have : FiniteDimensional ℂ NT := Submodule.finiteDimensional_of_le inf_le_right
  have hPN : ∀ w ∈ N, P w ∈ NT := by
    intro w hw
    obtain ⟨S₁, hS₁f, hwS₁, -, hS₁st, -⟩ := exists_sub_B hK hσ hirr (hNK hw)
    let V₁ := N ⊓ S₁
    have hV₁f : FiniteDimensional ℂ V₁ := Submodule.finiteDimensional_of_le inf_le_right
    have hV₁K : IsKStableSub ε (smE ε σ) V₁ := fun a b hab x hx => ⟨hNst a b x hx.1, hS₁st a b hab x hx.2⟩
    have hKst := kStable_of_isKStableSub hσ hD V₁ hV₁f hV₁K
    let W₁ : Submodule ℂ H := V₁.map (smD ε σ).subtype
    have : FiniteDimensional ℂ W₁ := Module.Finite.map V₁ _
    have h1 : P w ∈ W₁ := kavg_mem_B hσ he W₁ fun k => by
      obtain ⟨x, hx, hxe⟩ := hKst _ k.2 w ⟨hw, hwS₁⟩
      exact ⟨x, hx, hxe⟩
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 h1
    refine ⟨Submodule.mem_map.2 ⟨x, hx.1, hxe⟩, ?_⟩
    exact hrange w
  have hclosed : IsClosed (NT : Set H) := Submodule.closed_of_finiteDimensional NT
  have hsub : (P '' ((genSub (smE ε σ) V).map (smD ε σ).subtype : Set H)) ⊆ NT := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact hPN w (hgen hw)
  have huC : (u : H) ∈ closure ((genSub (smE ε σ) V).map (smD ε σ).subtype : Set H) := by
    rw [← Submodule.topologicalClosure_coe, ← hCdef, hCtop]; trivial
  have h1 : P u ∈ NT := (hclosed.closure_subset_iff.2 hsub) (image_closure_subset_closure_image P.continuous
    ⟨_, huC, rfl⟩)
  have hPu : P u = u := hfix
  rw [hPu] at h1
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 h1.1
  have : x = u := Subtype.ext hxe
  exact this ▸ hx

end CompanionTheory.D.gk.HC
end
end

section
open Matrix
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

section

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def resB (W : Submodule ℂ (smD ε σ)) (hW : IsKStableSub ε (smE ε σ) W) (a b : Fin n) : Module.End ℂ W :=
  if h : ε a = ε b then (smE ε σ a b).restrict (fun x hx => hW a b h x hx) else 0

theorem resB_apply {W : Submodule ℂ (smD ε σ)} (hW : IsKStableSub ε (smE ε σ) W) {a b : Fin n} (h : ε a = ε b)
    (x : W) : ((resB W hW a b x : W) : smD ε σ) = smE ε σ a b x := by
  simp [resB, dif_pos h]

theorem kRel_resB (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {W : Submodule ℂ (smD ε σ)}
    (hW : IsKStableSub ε (smE ε σ) W) : Formalism.REAL.KRel ε (resB W hW) := by
  intro a b c d hab hcd
  have hG := (isDerivedOn_smE hσ).glRep a b c d
  refine LinearMap.ext fun x => Subtype.ext ?_
  have h1 := congrArg (fun T : Module.End ℂ (smD ε σ) => T x) hG
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, resB_apply hW hab, resB_apply hW hcd]
  rw [h1]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc; subst hda
    simp [resB_apply hW (rfl : ε d = ε d), resB_apply hW (rfl : ε b = ε b)]
  · subst hbc
    simp [hda, resB_apply hW (hab.trans hcd)]
  · subst hda
    simp [hbc, resB_apply hW (hcd.trans hab)]
  · simp [hbc, hda]

theorem kUnit_resB (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {W : Submodule ℂ (smD ε σ)}
    (hW : IsKStableSub ε (smE ε σ) W) : Formalism.REAL.KUnit ε (resB W hW) := by
  intro a b hab x y
  have hU := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ) a b (x : smD ε σ) (y : smD ε σ)
  rw [adjSign, if_pos hab, one_mul] at hU
  simp only [Submodule.coe_inner, resB_apply hW hab, resB_apply hW hab.symm]
  exact hU

theorem hasSum_actM_pow_div_factorial (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {W : Submodule ℂ (smD ε σ)}
    [FiniteDimensional ℂ W] (hW : IsKStableSub ε (smE ε σ) W) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z)
    {x : smD ε σ} (hx : x ∈ W) :
    HasSum (fun m : ℕ => (((1 : ℝ) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) • ((((actM (smE ε σ) Z) ^ m) x : smD ε σ) : H))
      (σ (NormedSpace.exp Z) (x : H)) := by
  have hD := isDerivedOn_smE hσ
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_isKStableSub hW inferInstance hZ
  have hs : Summable fun m : ℕ => C ^ m * ‖x‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_right ‖x‖
    refine this.congr fun m => ?_
    simp
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 x (fun m => C ^ m * ‖x‖) (fun m => hC x hx m) 0 1 hs
  rw [exp_zero_smul, hσ.1.1] at hsum
  simpa only [Complex.ofReal_one, one_smul, ContinuousLinearMap.one_apply, sub_zero] using hsum

theorem intertwiner_actM_pow_comm {W W' : Submodule ℂ (smD ε σ)} (hW : IsKStableSub ε (smE ε σ) W)
    (hW' : IsKStableSub ε (smE ε σ) W') (φ : W →ₗ[ℂ] W')
    (hφ : ∀ a b, ε a = ε b → ∀ x : W, φ (resB W hW a b x) = resB W' hW' a b (φ x))
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (m : ℕ) (x : W) :
    ((φ ⟨((actM (smE ε σ) Z) ^ m) x, actM_pow_mem_of_isKStableSub_inK hW hZ x.2 m⟩ : W') : smD ε σ) =
      ((actM (smE ε σ) Z) ^ m) (φ x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    have e1 : (⟨((actM (smE ε σ) Z) ^ (m + 1)) x, actM_pow_mem_of_isKStableSub_inK hW hZ x.2 (m + 1)⟩ : W) =
        ∑ a, ∑ b, Z a b • resB W hW a b
          ⟨((actM (smE ε σ) Z) ^ m) x, actM_pow_mem_of_isKStableSub_inK hW hZ x.2 m⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      show ((actM (smE ε σ) Z) ^ (m + 1)) (x : smD ε σ) = _
      rw [pow_succ', Module.End.mul_apply]
      simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : ε a = ε b
      · rw [resB_apply hW hab]
      · rw [inK_apply_eq_zero hZ hab, zero_smul, zero_smul]
    rw [e1, map_sum]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
    rw [pow_succ', Module.End.mul_apply, ← ih x]
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : ε a = ε b
    · rw [hφ a b hab, resB_apply hW' hab]
    · rw [inK_apply_eq_zero hZ hab, zero_smul, zero_smul]

theorem intertwiner_comm_kset (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {W W' : Submodule ℂ (smD ε σ)}
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ W'] (hW : IsKStableSub ε (smE ε σ) W)
    (hW' : IsKStableSub ε (smE ε σ) W') (φ : W →ₗ[ℂ] W')
    (hφ : ∀ a b, ε a = ε b → ∀ x : W, φ (resB W hW a b x) = resB W' hW' a b (φ x))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) (x y : W)
    (hxy : ((y : smD ε σ) : H) = σ g ((x : smD ε σ) : H)) :
    (((φ y : W') : smD ε σ) : H) = σ g (((φ x : W') : smD ε σ) : H) := by
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hg
  let Wh : Submodule ℂ H := W.map (smD ε σ).subtype
  have : FiniteDimensional ℂ Wh := Module.Finite.map W _
  let e : W ≃ₗ[ℂ] Wh := Submodule.equivMapOfInjective _ Subtype.val_injective W
  let Φ : H →L[ℂ] H := ((smD ε σ).subtypeL.comp W'.subtypeL).comp
    ((LinearMap.toContinuousLinearMap φ).comp
      ((LinearMap.toContinuousLinearMap (e.symm : Wh →ₗ[ℂ] W)).comp Wh.orthogonalProjection))
  have hΦ : ∀ z : W, Φ ((z : smD ε σ) : H) = (((φ z : W') : smD ε σ) : H) := by
    intro z
    have hz : ((z : smD ε σ) : H) ∈ Wh := Submodule.mem_map_of_mem z.2
    have h1 : Wh.orthogonalProjection ((z : smD ε σ) : H) = ⟨_, hz⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨_, hz⟩ : Wh)
    have h2 : e.symm ⟨_, hz⟩ = z := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [Φ, ContinuousLinearMap.comp_apply, h1, LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe, h2]
    rfl
  have hs := (hasSum_actM_pow_div_factorial hσ hW hZ x.2).map Φ Φ.continuous
  have hs' := hasSum_actM_pow_div_factorial hσ hW' hZ (φ x).2
  rw [Function.comp_def] at hs
  simp only [map_smul] at hs
  have e3 : ∀ m : ℕ, Φ ((((actM (smE ε σ) Z) ^ m) x : smD ε σ) : H) =
      ((((actM (smE ε σ) Z) ^ m) (φ x) : smD ε σ) : H) := by
    intro m
    have := hΦ ⟨_, actM_pow_mem_of_isKStableSub_inK hW hZ x.2 m⟩
    rw [this, intertwiner_actM_pow_comm hW hW' φ hφ hZ m x]
  simp only [e3] at hs
  rw [← hxy, hΦ] at hs
  exact hs.unique hs'

end

end CompanionTheory.D.gk.HC
end
end

section
open Matrix
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

section

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kSpan_top_B {x : smD ε σ} (hW : IsKStableSub ε (smE ε σ) (Formalism.REAL.kSpan ε (smE ε σ) x))
    (x' : Formalism.REAL.kSpan ε (smE ε σ) x) {c : ℂ} (hc : c ≠ 0) (hx' : (x' : smD ε σ) = c • x) :
    Formalism.REAL.kSpan ε (resB _ hW) x' = ⊤ := by
  let M : Submodule ℂ (smD ε σ) := (Formalism.REAL.kSpan ε (resB _ hW) x').map (Formalism.REAL.kSpan ε (smE ε σ) x).subtype
  have hM : Formalism.REAL.KStable ε (smE ε σ) M := by
    rintro a b hab _ ⟨z, hz, rfl⟩
    refine ⟨resB _ hW a b z, Formalism.REAL.compact_span_stable x' a b hab z hz, ?_⟩
    simp [resB_apply hW hab]
  have hxM : x ∈ M := by
    have h1 : (x' : smD ε σ) ∈ M := ⟨x', Formalism.REAL.mem_compact_span_self x', rfl⟩
    have h2 := M.smul_mem c⁻¹ h1
    rwa [hx', smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  have hle : Formalism.REAL.kSpan ε (smE ε σ) x ≤ M := Formalism.REAL.compact_span_le_stable hxM hM
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨z', hz', he⟩ := hle z.2
  have : z' = z := Subtype.ext he
  exact this ▸ hz'

theorem kSpan_fin_B (hK : KFSm) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) {v : smD ε σ} (hv : v ∈ KF ε σ) :
    FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) v) ∧
      IsKStableSub ε (smE ε σ) (Formalism.REAL.kSpan ε (smE ε σ) v) := by
  obtain ⟨S, hSf, hvS, -, hSst, -⟩ := exists_sub_B hK hσ hirr hv
  exact ⟨Submodule.finiteDimensional_of_le (Formalism.REAL.compact_span_le_stable hvS hSst), Formalism.REAL.compact_span_stable v⟩

end

theorem uAdm_of (hK : KFSm) : UAdm := by
  classical
  intro n ε H _ _ _ σ hσ hirr μ
  have hD := isDerivedOn_smE hσ
  set A := {v : smD ε σ | v ∈ KF ε σ ∧ IsKHWVec ε (smE ε σ) μ v} with hA
  by_cases h0 : ∀ v ∈ A, v = 0
  · have : Submodule.span ℂ A = ⊥ := Submodule.span_eq_bot.2 h0
    rw [this]; infer_instance
  push_neg at h0
  obtain ⟨v₀, hv₀A, hv₀0⟩ := h0

  have key : ∀ v ∈ A, v ≠ 0 → ∃ (hf : FiniteDimensional ℂ (Formalism.REAL.kSpan ε (smE ε σ) v))
      (hst : IsKStableSub ε (smE ε σ) (Formalism.REAL.kSpan ε (smE ε σ) v)) (w : Formalism.REAL.kSpan ε (smE ε σ) v),
      ((w : smD ε σ) = ((‖v‖⁻¹ : ℝ) : ℂ) • v) ∧ ‖w‖ = 1 ∧ Formalism.REAL.KHighest ε (resB _ hst) μ w ∧
      Formalism.REAL.kSpan ε (resB _ hst) w = ⊤ := by
    intro v hvA hv0
    obtain ⟨hf, hst⟩ := kSpan_fin_B hK hσ hirr hvA.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    let w : Formalism.REAL.kSpan ε (smE ε σ) v :=
      ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, Submodule.smul_mem _ _ (Formalism.REAL.mem_compact_span_self v)⟩
    refine ⟨hf, hst, w, rfl, ?_, ⟨fun a => ?_, fun a b hab he => ?_⟩, kSpan_top_B hst w ?_ rfl⟩
    · show ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
    · apply Subtype.ext
      rw [resB_apply hst rfl]
      show smE ε σ a a (((‖v‖⁻¹ : ℝ) : ℂ) • v) = _
      rw [map_smul, hvA.2.1 a, smul_comm]
      rfl
    · apply Subtype.ext
      rw [resB_apply hst he]
      show smE ε σ a b (((‖v‖⁻¹ : ℝ) : ℂ) • v) = _
      rw [map_smul, hvA.2.2 a b hab he, smul_zero]
      rfl
    · exact_mod_cast inv_ne_zero hn
  obtain ⟨hf₀, hst₀, w₀, hw₀, hw₀1, hw₀h, hw₀T⟩ := key v₀ hv₀A hv₀0
  let Sh : Submodule ℂ H := (Formalism.REAL.kSpan ε (smE ε σ) v₀).map (smD ε σ).subtype
  have hShf : FiniteDimensional ℂ Sh := Module.Finite.map (Formalism.REAL.kSpan ε (smE ε σ) v₀) _
  have hShK : Formalism.MainNotions.S.IsKStableOn ε σ Sh := by
    rintro g hg _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hye⟩ := kStable_of_isKStableSub hσ hD (Formalism.REAL.kSpan ε (smE ε σ) v₀) hf₀ hst₀ g hg x hx
    exact ⟨y, hy, hye⟩
  have hM : Formalism.MainNotions.BridgeCPX.HCMult := CompanionTheory.HCMult.harish_chandra_multiplicity
  have hfin := hM n ε H σ hσ hirr Sh hShf hShK
  set Q := Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) Sh
  let e₀ : (Formalism.REAL.kSpan ε (smE ε σ) v₀) ≃ₗ[ℂ] Sh := Submodule.equivMapOfInjective _ Subtype.val_injective (Formalism.REAL.kSpan ε (smE ε σ) v₀)
  have hmem : ∀ v ∈ A, (v : H) ∈ Q := by
    intro v hvA
    by_cases hv0 : v = 0
    · rw [hv0]; exact Q.zero_mem
    obtain ⟨hf, hst, w, hw, hw1, hwh, hwT⟩ := key v hvA hv0
    obtain ⟨φ, hφ, hφw⟩ := ReciprocityTheory.ChartRestriction.DS.HW.uq_exists_isometry ε (resB (Formalism.REAL.kSpan ε (smE ε σ) v₀) hst₀) (resB _ hst) μ w₀ w
      (kRel_resB hσ hst₀) (kRel_resB hσ hst) (kUnit_resB hσ hst₀) (kUnit_resB hσ hst) hw₀h hwh hw₀1 hw1 hw₀T hwT
    let Θ : Sh →ₗ[ℂ] H := (smD ε σ).subtype ∘ₗ (Formalism.REAL.kSpan ε (smE ε σ) v).subtype ∘ₗ
      (φ.toLinearEquiv : (Formalism.REAL.kSpan ε (smE ε σ) v₀) →ₗ[ℂ] _) ∘ₗ (e₀.symm : Sh →ₗ[ℂ] (Formalism.REAL.kSpan ε (smE ε σ) v₀))
    have hΘ : ∀ (a : Formalism.REAL.KG ε) (x y : Sh), (y : H) = σ (Formalism.REAL.toMK a) x →
        Θ y = σ (Formalism.REAL.toMK a) (Θ x) := by
      intro a x y hxy
      have hx : ((e₀.symm x : (Formalism.REAL.kSpan ε (smE ε σ) v₀)) : smD ε σ) = (x : H) := by
        obtain ⟨x', rfl⟩ := e₀.surjective x; simp; rfl
      have hy : ((e₀.symm y : (Formalism.REAL.kSpan ε (smE ε σ) v₀)) : smD ε σ) = (y : H) := by
        obtain ⟨y', rfl⟩ := e₀.surjective y; simp; rfl
      have := intertwiner_comm_kset (W' := Formalism.REAL.kSpan ε (smE ε σ) v) hσ hst₀ hst φ.toLinearEquiv.toLinearMap
        (fun a b hab z => hφ a b hab z) a.2 (e₀.symm x) (e₀.symm y) (by rw [hx, hy]; exact hxy)
      exact this
    have hrange : LinearMap.range Θ ≤ Q := le_sSup ⟨Θ, hΘ, rfl⟩
    refine hrange ⟨((‖v‖ : ℝ) : ℂ) • e₀ w₀, ?_⟩
    rw [map_smul]
    have h1 : Θ (e₀ w₀) = (((φ w₀ : Formalism.REAL.kSpan ε (smE ε σ) v) : smD ε σ) : H) := by
      show ((smD ε σ).subtype ((Formalism.REAL.kSpan ε (smE ε σ) v).subtype
        (φ.toLinearEquiv (e₀.symm (e₀ w₀))))) = _
      rw [LinearEquiv.symm_apply_apply]
      rfl
    rw [h1, hφw, hw]
    simp only [Submodule.coe_smul]
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv0), Complex.ofReal_one, one_smul]
  have hle : Submodule.span ℂ A ≤ Q.comap (smD ε σ).subtype := Submodule.span_le.2 fun v hv => hmem v hv
  have hcf : FiniteDimensional ℂ (Q.comap (smD ε σ).subtype) := by
    have e := Submodule.equivMapOfInjective (smD ε σ).subtype Subtype.val_injective (Q.comap (smD ε σ).subtype)
    have : FiniteDimensional ℂ ((Q.comap (smD ε σ).subtype).map (smD ε σ).subtype) :=
      Submodule.finiteDimensional_of_le (Submodule.map_comap_le _ _)
    exact LinearEquiv.finiteDimensional e.symm
  exact Submodule.finiteDimensional_of_le hle

end CompanionTheory.D.gk.HC
end
end
