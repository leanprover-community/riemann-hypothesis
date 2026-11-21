import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HermXGen

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section iso2

variable {k r : ℕ}

lemma part_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h m : B.Mat k r} (hh : h ∈ UWset k r z)
    (hm : m ∈ Nset k r) (hX : ∀ a : Fin r, (h * m) *ᵥ bvec (eI k r a) = bvec (eI k r a))
    {w w' x x' : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (hw' : inWb k r w') (hx : x ∈ Xsp k r)
    (hx' : x' ∈ Xsp k r) (e : (h * m) *ᵥ (w + x) = w' + x') : h *ᵥ w = w' := by
  rw [mulVec_add, fix_X hX hx, ← mulVec_mulVec] at e
  have hmw := N_wb hm hw
  have e2 : m *ᵥ w = w + (m *ᵥ w - w) := by abel
  rw [e2, mulVec_add, uw_X hz hh hmw] at e
  have hd : h *ᵥ w - w' = x' - x - (m *ᵥ w - w) := by
    calc h *ᵥ w - w' = (h *ᵥ w + (m *ᵥ w - w) + x) - w' - (m *ᵥ w - w) - x := by abel
      _ = (w' + x') - w' - (m *ᵥ w - w) - x := by rw [e]
      _ = x' - x - (m *ᵥ w - w) := by abel
  have hX0 : h *ᵥ w - w' ∈ Xsp k r := by
    rw [hd]; exact Submodule.sub_mem _ (Submodule.sub_mem _ hx' hx) hmw
  have hW0 : inWb k r (h *ᵥ w - w') := by
    intro i hi; simp [uw_inWb hz hh hw i hi, hw' i hi]
  exact sub_eq_zero.1 (X_wb_zero hX0 hW0)

lemma fixes_e {s : B.Mat k r} {z : Fin (2 * r + k + 1) → ℂ} (hs : ∀ a, s *ᵥ fvec k r z a = fvec k r z a) :
    ∀ a : Fin r, s *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  intro a
  have := hs ⟨a.val, by omega⟩
  rwa [fvec_lt] at this

theorem isoCore : IsoCore := by
  intro k r z z' hk hr hz hz' D0 y hy α hα β hβ hν hν' hαβ
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  have hyG := hy.1
  have hG := hy.2.1
  have hyu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hyG
  have hαu := Wz.unit α hα
  have hβu := Wz'.unit β hβ
  have hβν : β *ᵥ D0.nu' = D0.nu' := by
    conv_lhs => rw [← hν']
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hβu, one_mulVec]
  have hU0W : ∀ u ∈ D0.U0, inWb k r u := fun u hu => ((D0.isotropic_subspace_eq u).1 hu).1.1
  have hU0z : ∀ u ∈ D0.U0, herm (Hpk k r) u z = 0 := fun u hu => ((D0.isotropic_subspace_eq u).1 hu).1.2
  have hU0z' : ∀ u ∈ D0.U0, herm (Hpk k r) u z' = 0 := fun u hu => ((D0.isotropic_subspace_eq_primed u).1 hu).1.2
  have hβU : ∀ u ∈ D0.U0, β *ᵥ u ∈ D0.U0 := by
    intro u hu
    obtain ⟨⟨huW, huz'⟩, huν'⟩ := (D0.isotropic_subspace_eq_primed u).1 hu
    refine (D0.isotropic_subspace_eq_primed _).2 ⟨⟨uw_inWb hz'.1 hβ huW, ?_⟩, ?_⟩
    · conv_lhs => rw [← hβ.2.2]
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hβ.1]; exact huz'
    · conv_lhs => rw [← hβν]
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hβ.1]; exact huν'
  have hαU : ∀ u ∈ D0.U0, α *ᵥ u ∈ D0.U0 := by
    intro u hu
    obtain ⟨⟨huW, huz⟩, huν⟩ := (D0.isotropic_subspace_eq u).1 hu
    refine (D0.isotropic_subspace_eq _).2 ⟨⟨uw_inWb hz.1 hα huW, ?_⟩, ?_⟩
    · conv_lhs => rw [← hα.2.2]
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1]; exact huz
    · conv_lhs => rw [← hν]
      rw [Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hα.1]; exact huν

  let S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
    { carrier := D0.U0
      add_mem' := by
        intro a b (ha : a ∈ D0.U0) (hb : b ∈ D0.U0)
        show a + b ∈ D0.U0
        rw [D0.isotropic_subspace_eq] at ha hb ⊢
        refine ⟨⟨fun i hi => by simp [ha.1.1 i hi, hb.1.1 i hi], ?_⟩, ?_⟩
        · rw [hm_add_l, ha.1.2, hb.1.2, add_zero]
        · rw [hm_add_l, ha.2, hb.2, add_zero]
      zero_mem' := by
        show (0 : Fin (2 * r + k + 1) → ℂ) ∈ D0.U0
        rw [D0.isotropic_subspace_eq]
        exact ⟨⟨fun i _ => rfl, by simp [herm]⟩, by simp [herm]⟩
      smul_mem' := by
        intro c a (ha : a ∈ D0.U0)
        show c • a ∈ D0.U0
        rw [D0.isotropic_subspace_eq] at ha ⊢
        refine ⟨⟨fun i hi => by simp [ha.1.1 i hi], ?_⟩, ?_⟩
        · rw [hm_smul_l, ha.1.2, mul_zero]
        · rw [hm_smul_l, ha.2, mul_zero] }
  have hSmem : ∀ u, u ∈ S ↔ u ∈ D0.U0 := fun u => Iff.rfl
  let b := Module.finBasis ℂ S
  let bv : Fin (Module.finrank ℂ S) → Fin (2 * r + k + 1) → ℂ := fun i => (b i : Fin (2 * r + k + 1) → ℂ)
  have hbU : ∀ i, bv i ∈ D0.U0 := fun i => (b i).2
  have hbspan : ∀ u (hu : u ∈ D0.U0), u = ∑ i, (b.repr ⟨u, (hSmem u).2 hu⟩ i) • bv i := by
    intro u hu
    have := congrArg Subtype.val (b.sum_repr ⟨u, (hSmem u).2 hu⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm

  choose! Vf hVf V'f hV'f hq using hy.2.2.2.2
  let q : (Fin (2 * r + k + 1) → ℂ) → Fin (2 * r + k + 1) → ℂ := fun u => u + Vf u
  have hqy : ∀ u ∈ D0.U0, y *ᵥ (u + V'f u) = q u := hq
  have hesI : ∀ a : Fin r, r + k < (esI k r a).val := fun a => by simp [esI]; omega
  have hq_f : ∀ u ∈ D0.U0, ∀ a, herm (Hpk k r) (q u) (fvec k r z a) = 0 := by
    intro u hu a
    show herm (Hpk k r) (u + Vf u) _ = 0
    rw [hm_add_l]
    unfold fvec
    split_ifs with ha
    · rw [herm_bvec_eI, herm_bvec_eI, hU0W u hu _ (Or.inr (hesI _)), X_hi (hVf u hu) _ (hesI _), add_zero]
    · rw [hU0z u hu, herm_X_wb (hVf u hu) hz.1, add_zero]
  have hq_yf : ∀ u ∈ D0.U0, ∀ c, herm (Hpk k r) (q u) (y *ᵥ fvec k r z' c) = 0 := by
    intro u hu c
    rw [← hqy u hu, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hyG, hm_add_l]
    unfold fvec
    split_ifs with hc
    · rw [herm_bvec_eI, herm_bvec_eI, hU0W u hu _ (Or.inr (hesI _)), X_hi (hV'f u hu) _ (hesI _), add_zero]
    · rw [hU0z' u hu, herm_X_wb (hV'f u hu) hz'.1, add_zero]
  have hq_gv : ∀ u ∈ D0.U0, ∀ i, herm (Hpk k r) (q u) (gramVec k r z z' y i) = 0 := by
    intro u hu i
    cases i with
    | inl a => exact hq_f u hu a
    | inr c => exact hq_yf u hu c
  have hgv_q : ∀ u ∈ D0.U0, ∀ i, herm (Hpk k r) (gramVec k r z z' y i) (q u) = 0 := by
    intro u hu i
    rw [hm_symm _ (Formalism.QuantumDeterminants.hpkFacts k r).1, hq_gv u hu i, star_zero]
  have hq_q : ∀ u ∈ D0.U0, ∀ u' ∈ D0.U0, herm (Hpk k r) (q u) (q u') = herm (Hpk k r) u u' := by
    intro u hu u' hu'
    show herm (Hpk k r) (u + Vf u) (u' + Vf u') = _
    rw [hm_add_l, hm_add_r, hm_add_r, herm_X_gen (hVf u hu) (wb_hi (hU0W u' hu')),
      herm_X_gen (hVf u hu) (X_hi (hVf u' hu')), herm_wb_X (hVf u' hu') (wb_hi (hU0W u hu))]
    ring

  have key0 : ∀ c : Fin (Module.finrank ℂ S) → Fin (2 * r + k + 1) → ℂ, (∀ i, c i ∈ D0.U0) →
      LinearIndependent ℂ c → ∀ g : Fin (Module.finrank ℂ S) → ℂ,
      (∀ u ∈ D0.U0, herm (Hpk k r) (∑ i, g i • q (c i)) (q u) = 0) → g = 0 := by
    intro c hc hli g hg
    set u₀ := ∑ i, g i • c i with hu₀d
    have hu₀ : u₀ ∈ D0.U0 := (hSmem u₀).1 (S.sum_mem fun i _ => S.smul_mem (g i) ((hSmem _).2 (hc i)))
    have h0 : herm (Hpk k r) u₀ u₀ = 0 := by
      have := hg u₀ hu₀
      rw [hm_sum_l] at this
      rw [hu₀d, hm_sum_l, ← this]
      exact Finset.sum_congr rfl fun i _ => by rw [hq_q _ (hc i) _ hu₀]
    have hz0 : u₀ = 0 := by
      by_contra hne
      have := posV hz (hU0W u₀ hu₀) (hU0z u₀ hu₀) hne
      rw [h0] at this; simp at this
    funext i
    exact (Fintype.linearIndependent_iff.1 hli) g hz0 i
  have hlib : LinearIndependent ℂ bv := b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hlibβ : LinearIndependent ℂ (fun i => β *ᵥ bv i) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have : ∑ i, g i • bv i = 0 := by
      have h2 := congrArg (fun v => β⁻¹ *ᵥ v) hg
      simp only [mv_sum, mulVec_smul, mulVec_mulVec, Matrix.nonsing_inv_mul _ hβu, one_mulVec, mulVec_zero] at h2
      exact h2
    exact (Fintype.linearIndependent_iff.1 hlib) g this
  have liq : ∀ c : Fin (Module.finrank ℂ S) → Fin (2 * r + k + 1) → ℂ, (∀ i, c i ∈ D0.U0) →
      LinearIndependent ℂ c → LinearIndependent ℂ (fun i => q (c i)) := by
    intro c hc hli
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have := key0 c hc hli g (fun u _ => by rw [hg]; simp [herm])
    intro i; rw [this]; rfl
  have hgvli := (Formalism.FourierDecayAlt.P.gram_independent_signature' k r z z' y ⟨hk, hz, hz'⟩ ⟨hyG, hG⟩).1
  have famli : ∀ c : Fin (Module.finrank ℂ S) → Fin (2 * r + k + 1) → ℂ, (∀ i, c i ∈ D0.U0) →
      LinearIndependent ℂ c → LinearIndependent ℂ (Sum.elim (gramVec k r z z' y) (fun i => q (c i))) := by
    intro c hc hli
    refine hgvli.sum_type (liq c hc hli) ?_
    rw [Submodule.disjoint_def]
    intro v hv1 hv2
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv2
    obtain ⟨g1, hg1⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv1
    have := key0 c hc hli g (fun u hu => by
      rw [← hg1, hm_sum_l]
      exact Finset.sum_eq_zero fun j _ => by rw [hgv_q u hu j, mul_zero])
    rw [this]; simp
  have hβbU : ∀ i, β *ᵥ bv i ∈ D0.U0 := fun i => hβU _ (hbU i)

  obtain ⟨s, hsG, hs⟩ := PI.UnitaryGroupMassFormula.DLm.Lifts.wittHpk k r
    (Sum.elim (gramVec k r z z' y) (fun i => q (β *ᵥ bv i)))
    (Sum.elim (gramVec k r z z' y) (fun i => q (bv i)))
    (famli _ hβbU hlibβ) (famli _ hbU hlib) (by
      intro i j
      cases i with
      | inl a =>
        cases j with
        | inl c => rfl
        | inr c => simp only [Sum.elim_inl, Sum.elim_inr]; rw [hgv_q _ (hβbU c), hgv_q _ (hbU c)]
      | inr a =>
        cases j with
        | inl c => simp only [Sum.elim_inl, Sum.elim_inr]; rw [hq_gv _ (hβbU a), hq_gv _ (hbU a)]
        | inr c =>
          simp only [Sum.elim_inr]
          rw [hq_q _ (hβbU a) _ (hβbU c), hq_q _ (hbU a) _ (hbU c), Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hβ.1])
  have hsf : ∀ a, s *ᵥ fvec k r z a = fvec k r z a := fun a => hs (Sum.inl (Sum.inl a))
  have hsyf : ∀ c, s *ᵥ (y *ᵥ fvec k r z' c) = y *ᵥ fvec k r z' c := fun c => hs (Sum.inl (Sum.inr c))
  have hsq : ∀ i, s *ᵥ q (β *ᵥ bv i) = q (bv i) := fun i => hs (Sum.inr i)
  have hsu : IsUnit s.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hsG
  have hsS : s ∈ C2.CurvatureSupportSet k r z := by
    rw [← Formalism.FourierDecayAlt.P.fixed_frame_property k r z hz]; exact ⟨hsG, hsf⟩
  obtain ⟨h, hh, m, hm, hsd⟩ := parabolic_levi_unipotent_decomp hz hsS
  set s' := y⁻¹ * s⁻¹ * y with hs'd
  have hsinv : ∀ v, s *ᵥ v = v → s⁻¹ *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hsu, one_mulVec]
  have hs'f : ∀ c, s' *ᵥ fvec k r z' c = fvec k r z' c := by
    intro c
    rw [hs'd, ← mulVec_mulVec, ← mulVec_mulVec, hsinv _ (hsyf c), mulVec_mulVec, Matrix.nonsing_inv_mul _ hyu,
      one_mulVec]
  have hs'G : s' ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hyG) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hsG)) hyG
  have hs'S : s' ∈ C2.CurvatureSupportSet k r z' := by
    rw [← Formalism.FourierDecayAlt.P.fixed_frame_property k r z' hz']; exact ⟨hs'G, hs'f⟩
  obtain ⟨h', hh', m', hm', hs'd2⟩ := parabolic_levi_unipotent_decomp hz' hs'S

  have hhβ : ∀ i, h *ᵥ (β *ᵥ bv i) = bv i := by
    intro i
    have e := hsq i
    rw [hsd] at e
    exact part_eq hz.1 hh hm.1 (by rw [← hsd]; exact fixes_e hsf) (hU0W _ (hβbU i)) (hU0W _ (hbU i))
      (hVf _ (hβbU i)) (hVf _ (hbU i)) e
  have hhβ' : ∀ u ∈ D0.U0, h *ᵥ (β *ᵥ u) = u := by
    intro u hu
    rw [hbspan u hu, mv_sum, mv_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mulVec_smul, mulVec_smul, hhβ i]
  have hβα : ∀ u ∈ D0.U0, β *ᵥ (α *ᵥ u) = u := by
    intro u hu
    have e := hαβ (α *ᵥ u) (hαU u hu)
    have inj : ∀ v v' : Fin (2 * r + k + 1) → ℂ, α *ᵥ v = α *ᵥ v' → v = v' := by
      intro v v' hvv
      have := congrArg (fun t => α⁻¹ *ᵥ t) hvv
      simpa [mulVec_mulVec, Matrix.nonsing_inv_mul _ hαu] using this
    exact inj _ _ e
  have hxs : s *ᵥ xcof k r z z' y = xcof k r z z' y := by
    unfold xcof; rw [mv_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [mulVec_smul, hsyf c]
  have hhom : h *ᵥ omW k r z z' y = omW k r z z' y := by
    unfold omW
    calc h *ᵥ prW k r z (xcof k r z z' y) = h *ᵥ prW k r z (m *ᵥ xcof k r z z' y) := by
          rw [prW_N hm.1 (xcof_esI z z' y)]
      _ = prW k r z (h *ᵥ (m *ᵥ xcof k r z z' y)) := by rw [prW_UW hz hh]
      _ = prW k r z (s *ᵥ xcof k r z z' y) := by rw [hsd, mulVec_mulVec]
      _ = prW k r z (xcof k r z z' y) := by rw [hxs]
  have hα_eq : h = α := by
    refine uw_eq hz D0.nu_mem D0.nu_unit D0.isotropic_subspace_eq hh hα (fun u hu => ?_) ?_
    · conv_lhs => rw [← hβα u hu]
      rw [hhβ' _ (hαU u hu)]
    · rw [hν]
      obtain ⟨t, ht, hom⟩ := hy.2.2.1
      rw [hom, mulVec_smul] at hhom
      exact smul_right_injective _ (Complex.ofReal_ne_zero.2 ht.ne') hhom

  have hs'X : ∀ a : Fin r, (h' * m') *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
    rw [← hs'd2]; exact fixes_e hs'f
  have hh'b : ∀ i, h' *ᵥ bv i = β *ᵥ bv i := by
    intro i
    have e : s' *ᵥ (bv i + V'f (bv i)) = β *ᵥ bv i + V'f (β *ᵥ bv i) := by
      rw [hs'd, ← mulVec_mulVec, ← mulVec_mulVec, hqy _ (hbU i)]
      have : s⁻¹ *ᵥ q (bv i) = q (β *ᵥ bv i) := by
        rw [← hsq i, mulVec_mulVec, Matrix.nonsing_inv_mul _ hsu, one_mulVec]
      rw [this, ← hqy _ (hβbU i), mulVec_mulVec, Matrix.nonsing_inv_mul _ hyu, one_mulVec]
    rw [hs'd2] at e
    exact part_eq hz'.1 hh' hm'.1 hs'X (hU0W _ (hbU i)) (hU0W _ (hβbU i)) (hV'f _ (hbU i)) (hV'f _ (hβbU i)) e
  have hh'U : ∀ u ∈ D0.U0, h' *ᵥ u = β *ᵥ u := by
    intro u hu
    rw [hbspan u hu, mv_sum, mv_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mulVec_smul, mulVec_smul, hh'b i]
  have hxs' : s' *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y) = y⁻¹ *ᵥ xcofL k r z z' y := by
    have hfix : s⁻¹ *ᵥ xcofL k r z z' y = xcofL k r z z' y := by
      apply hsinv
      unfold xcofL; rw [mv_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [mulVec_smul, hsf a]
    rw [hs'd, ← mulVec_mulVec, ← mulVec_mulVec,
      show y *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y) = xcofL k r z z' y by
        rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hyu, one_mulVec], hfix]
  have hhom' : h' *ᵥ omW' k r z z' y = omW' k r z z' y := by
    unfold omW'
    calc h' *ᵥ prW k r z' (y⁻¹ *ᵥ xcofL k r z z' y) = h' *ᵥ prW k r z' (m' *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y)) := by
          rw [prW_N hm'.1 (ginv_xcofL_esI z z' hyG)]
      _ = prW k r z' (h' *ᵥ (m' *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y))) := by rw [prW_UW hz' hh']
      _ = prW k r z' (s' *ᵥ (y⁻¹ *ᵥ xcofL k r z z' y)) := by rw [hs'd2, mulVec_mulVec]
      _ = prW k r z' (y⁻¹ *ᵥ xcofL k r z z' y) := by rw [hxs']
  have hβ_eq : h' = β := by
    refine uw_eq hz' D0.nu'_mem D0.nu'_unit D0.isotropic_subspace_eq_primed hh' hβ hh'U ?_
    rw [hβν]
    obtain ⟨t, ht, hom⟩ := hy.2.2.2.1
    rw [hom, mulVec_smul] at hhom'
    exact smul_right_injective _ (Complex.ofReal_ne_zero.2 ht.ne') hhom'

  have hmu := Gz.unit m hm
  have hsys : s * y * s' = y := by
    rw [hs'd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc s y, Matrix.mul_nonsing_inv _ hyu,
      Matrix.mul_one, Matrix.mul_nonsing_inv _ hsu, Matrix.one_mul]
  rw [hsd, hs'd2, hα_eq, hβ_eq] at hsys
  refine ⟨m⁻¹, Gz.inv_mem m hm, β * m' * β⁻¹, unipotent_normal_unitary hz' hβ hm', ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv m hmu]
  calc α * (m * y * (β * m' * β⁻¹)) * β = α * m * y * (β * m') := by
        simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hβu, Matrix.mul_one]
    _ = y := hsys


end iso2

end PI.UnitaryGroupMassFormula.GsFr
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram


end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

def LocB : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ →
      ∃ (O : Set (B.Mat k r)) (bf : B.Mat k r → B.Mat k r),
        IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bf O ∧
        ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
          bf g ∈ UWset k r z' ∧ ∃ t : ℝ, 0 < t ∧ omW' k r z z' (g * bf g) = (t : ℂ) • D0.nu'

def LocA : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ →
      ∀ (O : Set (B.Mat k r)) (bf : B.Mat k r → B.Mat k r), IsOpen O → g₀ ∈ O →
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bf O →
        (∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
          bf g ∈ UWset k r z' ∧ ∃ t : ℝ, 0 < t ∧ omW' k r z z' (g * bf g) = (t : ℂ) • D0.nu') →
        ∃ (O' : Set (B.Mat k r)) (af : B.Mat k r → B.Mat k r),
          O' ⊆ O ∧ IsOpen O' ∧ g₀ ∈ O' ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) af O' ∧
          ∀ g ∈ O', g ∈ B.GV k r → 0 < Gf k r z z' g →
            af g ∈ UWset k r z ∧ af g * g * bf g ∈ gfSig D0



end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section qrefl

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

def qr (u : Fin m → ℂ) (c : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - c⁻¹ • vecMulVec u (star u ᵥ* H)

lemma vmv_mulVec (u v : Fin m → ℂ) :
    vecMulVec u (star u ᵥ* H) *ᵥ v = herm H v u • u := by
  have e : herm H v u = (star u ᵥ* H) ⬝ᵥ v := by unfold herm; rw [dotProduct_mulVec]
  rw [e]
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma qr_mulVec (u : Fin m → ℂ) (c : ℂ) (v : Fin m → ℂ) :
    qr H u c *ᵥ v = v - (herm H v u / c) • u := by
  rw [qr, sub_mulVec, one_mulVec, smul_mulVec, vmv_mulVec, smul_smul, div_eq_inv_mul]

lemma qr_fix {u v : Fin m → ℂ} (c : ℂ) (h : herm H v u = 0) : qr H u c *ᵥ v = v := by
  rw [qr_mulVec, h, zero_div, zero_smul, sub_zero]

lemma uh_of_herm {g : Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ x y : Fin m → ℂ, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) : g ∈ UH H := by
  show gᴴ * H * g = H
  have key : ∀ x y : Fin m → ℂ, herm (gᴴ * H * g) x y = herm H x y := by
    intro x y
    rw [← h x y]
    unfold herm
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  ext i j
  have := key (Pi.single j 1) (Pi.single i 1)
  simpa [herm, dotProduct, mulVec, Pi.single_apply] using this

lemma qr_herm (hH : Hᴴ = H) (u : Fin m → ℂ) {c : ℂ} (hc0 : c ≠ 0) (hc : c + star c = herm H u u)
    (x y : Fin m → ℂ) : herm H (qr H u c *ᵥ x) (qr H u c *ᵥ y) = herm H x y := by
  rw [qr_mulVec, qr_mulVec]
  simp only [hm_sub_l, hm_sub_r, hm_smul_l, hm_smul_r]
  rw [hm_symm H hH y u, ← hc, star_div₀]
  have hc1 : star c ≠ 0 := star_ne_zero.2 hc0
  field_simp
  ring

lemma qr_uh (hH : Hᴴ = H) (u : Fin m → ℂ) {c : ℂ} (hc0 : c ≠ 0) (hc : c + star c = herm H u u) :
    qr H u c ∈ UH H := uh_of_herm H (qr_herm H hH u hc0 hc)

lemma uh_mul {g h : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (hh : h ∈ UH H) : g * h ∈ UH H := by
  have hg' : gᴴ * H * g = H := hg
  have hh' : hᴴ * H * h = H := hh
  show (g * h)ᴴ * H * (g * h) = H
  calc (g * h)ᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = H := by rw [hg', hh']

end qrefl

section hpk

variable {k r : ℕ}

lemma hH_ct : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1

lemma hH_sq : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1

lemma herm_out_wb {v u : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → v i = 0) (hu : inWb k r u) :
    herm (Hpk k r) v u = 0 := by
  unfold herm
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun l _ => ?_)
    by_cases hl : r ≤ l.val ∧ l.val ≤ r + k
    · rw [hv l hl.1 hl.2, mul_zero]
    · have h0 : Hpk k r j l = 0 := by
        simp only [Hpk]
        split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega) | (exfalso; apply hl; rw [← h3.2.2]; exact hj)
      rw [h0, zero_mul]
  · rw [hu j (by omega), star_zero, zero_mul]

lemma herm_wb_out {u v : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u)
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → v i = 0) :
    herm (Hpk k r) u v = 0 := by
  rw [hm_symm _ hH_ct v u, herm_out_wb hv hu, star_zero]

lemma bvec_eI_mid (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → bvec (eI k r a) i = 0 := by
  intro i h1 _
  simp only [bvec, Pi.single_apply]
  rw [if_neg]
  rintro rfl
  have := a.isLt
  simp only [eI, Fin.val_mk] at h1
  omega

lemma bvec_esI_mid (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → bvec (esI k r a) i = 0 := by
  intro i _ h2
  simp only [bvec, Pi.single_apply]
  rw [if_neg]
  rintro rfl
  have := a.isLt
  simp only [esI, Fin.val_mk] at h2
  omega

lemma wbPart_mid (v : Fin (2 * r + k + 1) → ℂ) :
    ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → (v - wbPart k r v) i = 0 := by
  intro i h1 h2
  simp only [Pi.sub_apply, wbPart]
  rw [if_pos ⟨h1, h2⟩, sub_self]

lemma wbPart_inWb (v : Fin (2 * r + k + 1) → ℂ) : inWb k r (wbPart k r v) := by
  intro i hi
  simp only [wbPart]
  rw [if_neg (by omega)]

lemma Tz_ne {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : (Tz k r z : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 hz.2.ne'

lemma prW_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    prW k r z v ∈ Wsp k r z := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have h0 : wbPart k r v i = 0 := wbPart_inWb v i hi
    simp only [prW, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, hz.1 i hi, mul_zero, add_zero]
  · simp only [prW]
    rw [hm_add_l, hm_smul_l, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, mul_neg, div_mul_cancel₀ _ (Tz_ne hz),
      add_neg_cancel]

lemma herm_prW_r {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) q (prW k r z v) = herm (Hpk k r) q v := by
  have e1 : herm (Hpk k r) q (v - wbPart k r v) = 0 := herm_wb_out hq.1 (wbPart_mid v)
  have e2 : herm (Hpk k r) q z = 0 := hq.2
  simp only [prW]
  rw [hm_add_r, hm_smul_r, e2, mul_zero, add_zero]
  rw [hm_sub_r, sub_eq_zero] at e1
  exact e1.symm

lemma herm_prW_l {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (prW k r z v) q = herm (Hpk k r) v q := by
  rw [hm_symm _ hH_ct q (prW k r z v), herm_prW_r hq]
  exact (hm_symm _ hH_ct q v).symm

lemma esI_hi {ξ : Fin (2 * r + k + 1) → ℂ} (hX : ∀ a : Fin r, ξ (esI k r a) = 0) :
    ∀ i : Fin (2 * r + k + 1), r + k < i.val → ξ i = 0 := by
  intro i hi
  have := i.isLt
  have e : esI k r ⟨2 * r + k - i.val, by omega⟩ = i := Fin.ext (by simp only [esI, Fin.val_mk]; omega)
  rw [← e]
  exact hX _

lemma sub_wbPart_X {ξ : Fin (2 * r + k + 1) → ℂ} (hX : ∀ a : Fin r, ξ (esI k r a) = 0) :
    ξ - wbPart k r ξ ∈ Xsp k r := by
  rw [mem_Xsp_iff]
  intro i hi
  by_cases h2 : i.val ≤ r + k
  · exact wbPart_mid ξ i hi h2
  · simp only [Pi.sub_apply, wbPart]
    rw [if_neg (by omega), sub_zero]
    exact esI_hi hX i (by omega)

lemma herm_add_X {p q x x' : Fin (2 * r + k + 1) → ℂ} (hp : inWb k r p) (hq : inWb k r q)
    (hx : x ∈ Xsp k r) (hx' : x' ∈ Xsp k r) :
    herm (Hpk k r) (p + x) (q + x') = herm (Hpk k r) p q := by
  rw [hm_add_l, hm_add_r, hm_add_r, herm_wb_X hx' (wb_hi hp), herm_X_gen hx (wb_hi hq),
    herm_X_gen hx (X_hi hx')]
  simp

lemma fv_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by simp [fvec]

lemma fv_X (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) (hb : b ≠ Fin.last r) : fvec k r z b ∈ Xsp k r := by
  have hb' : b.val < r := by
    have h1 := b.isLt
    have h2 : b.val ≠ r := fun h => hb (Fin.ext (by rw [h, Fin.val_last]))
    omega
  rw [fvec, dif_pos hb']
  exact Submodule.subset_span ⟨⟨b.val, hb'⟩, rfl⟩

lemma fv_hi {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (b : Fin (r + 1)) :
    ∀ i : Fin (2 * r + k + 1), r + k < i.val → fvec k r z b i = 0 := by
  by_cases hb : b = Fin.last r
  · subst hb; rw [fv_last]; exact wb_hi hz
  · exact X_hi (fv_X z b hb)

lemma key_pr {z ξ : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hX : ∀ a : Fin r, ξ (esI k r a) = 0)
    (h0 : prW k r z ξ = 0) :
    herm (Hpk k r) ξ ξ * herm (Hpk k r) z z = herm (Hpk k r) ξ z * star (herm (Hpk k r) ξ z) := by
  have h0' := h0
  unfold prW at h0'
  have hw : wbPart k r ξ = (-(herm (Hpk k r) (wbPart k r ξ) z / (Tz k r z : ℂ))) • z := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0'
  set c := -(herm (Hpk k r) (wbPart k r ξ) z / (Tz k r z : ℂ))
  have hx := sub_wbPart_X hX
  have hξ : ξ = c • z + (ξ - wbPart k r ξ) := by rw [← hw]; abel
  have hcz : inWb k r (c • z) := fun i hi => by simp [hz.1 i hi]
  have e1 : herm (Hpk k r) ξ ξ = herm (Hpk k r) (c • z) (c • z) := by
    conv_lhs => rw [hξ]
    exact herm_add_X hcz hcz hx hx
  have e2 : herm (Hpk k r) ξ z = herm (Hpk k r) (c • z) z := by
    conv_lhs => rw [hξ]
    rw [hm_add_l, herm_X_gen hx (wb_hi hz.1), add_zero]
  rw [e1, e2]
  simp only [hm_smul_l, hm_smul_r, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, star_mul', star_neg, Complex.star_def,
    Complex.conj_ofReal]
  ring

lemma adj_LL (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    M.adjugate (Fin.last r) (Fin.last r) = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [Fin.succAbove_last, ← two_mul]

lemma xcof_self {z z' : Fin (2 * r + k + 1) → ℂ} (hz' : C2.StdZ k r z') {y : B.Mat k r} (hy : y ∈ B.GV k r) :
    herm (Hpk k r) (xcof k r z z' y) (xcof k r z z' y) =
      (Zhat k r z z' y).adjugate (Fin.last r) (Fin.last r) *
        (star ((Zhat k r z z' y).adjugate (Fin.last r) (Fin.last r)) * herm (Hpk k r) z' z') := by
  unfold xcof
  rw [hm_sum_l]
  simp_rw [hm_sum_r, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · rw [fv_last]
    · intro b' _ hb'
      rw [fv_last, herm_wb_X (fv_X z' b' hb') (wb_hi hz'.1), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b' _ => ?_)
    rw [herm_X_gen (fv_X z' b hb) (fv_hi hz'.1 b'), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma herm_Hpk_xcof_eq_det_Zhat (z z' : Fin (2 * r + k + 1) → ℂ) (y : B.Mat k r) :
    herm (Hpk k r) (xcof k r z z' y) z = (Zhat k r z z' y).det := by
  unfold xcof
  rw [hm_sum_l]
  have h := congrFun (congrFun (Matrix.mul_adjugate (Zhat k r z z' y)) (Fin.last r)) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]
  simp only [Zhat, fv_last]

lemma xcofL_self {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (y : B.Mat k r) :
    herm (Hpk k r) (xcofL k r z z' y) (xcofL k r z z' y) =
      star ((Zhat k r z z' y).adjugate (Fin.last r) (Fin.last r)) *
        ((Zhat k r z z' y).adjugate (Fin.last r) (Fin.last r) * herm (Hpk k r) z z) := by
  unfold xcofL
  rw [hm_sum_l]
  simp_rw [hm_sum_r, star_star]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · rw [fv_last]
    · intro b' _ hb'
      rw [fv_last, herm_wb_X (fv_X z b' hb') (wb_hi hz.1), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun b' _ => ?_)
    rw [herm_X_gen (fv_X z b hb) (fv_hi hz.1 b'), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma ginv_cancel {y : B.Mat k r} (hy : y ∈ B.GV k r) (v : Fin (2 * r + k + 1) → ℂ) : y *ᵥ (y⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy), one_mulVec]

lemma xi_hermitian_cofactor_det {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hy : y ∈ B.GV k r) :
    herm (Hpk k r) (y⁻¹ *ᵥ xcofL k r z z' y) z' = star (Zhat k r z z' y).det := by
  rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy (y⁻¹ *ᵥ xcofL k r z z' y) z', ginv_cancel hy]
  unfold xcofL
  rw [hm_sum_l]
  have h := congrFun (congrFun (Matrix.adjugate_mul (Zhat k r z z' y)) (Fin.last r)) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  rw [← h, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_mul']
  congr 1
  simp only [Zhat, fv_last]
  exact hm_symm _ hH_ct (y *ᵥ z') (fvec k r z a)

lemma omW_ne {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {y : B.Mat k r}
    (hy : y ∈ B.GV k r) (hG : 0 < Gf k r z z' y) : omW k r z z' y ≠ 0 := by
  intro h0
  have key := key_pr hz (xcof_esI z z' y) h0
  rw [xcof_self hz' hy, herm_Hpk_xcof_eq_det_Zhat, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, adj_LL] at key
  have hG' : 0 < Complex.normSq (Zhat k r z z' y).det -
      Tz k r z * Tz k r z' * Complex.normSq ((Zhat k r z z' y).submatrix Fin.castSucc Fin.castSucc).det := hG
  set a := ((Zhat k r z z' y).submatrix Fin.castSucc Fin.castSucc).det
  set d := (Zhat k r z z' y).det
  simp only [Complex.star_def] at key
  have e : ((Complex.normSq a * Tz k r z' * Tz k r z : ℝ) : ℂ) = ((Complex.normSq d : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    linear_combination key
  have e' := Complex.ofReal_injective e
  linarith [e', show Tz k r z * Tz k r z' * Complex.normSq a = Complex.normSq a * Tz k r z' * Tz k r z by ring]

lemma omW'_ne {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {y : B.Mat k r}
    (hy : y ∈ B.GV k r) (hG : 0 < Gf k r z z' y) : omW' k r z z' y ≠ 0 := by
  intro h0
  have key := key_pr hz' (ginv_xcofL_esI z z' hy) h0
  have hs : herm (Hpk k r) (y⁻¹ *ᵥ xcofL k r z z' y) (y⁻¹ *ᵥ xcofL k r z z' y) =
      herm (Hpk k r) (xcofL k r z z' y) (xcofL k r z z' y) := by
    rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ginv_cancel hy]
  rw [hs, xcofL_self hz, xi_hermitian_cofactor_det hy, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_self_eq, adj_LL,
    star_star] at key
  have hG' : 0 < Complex.normSq (Zhat k r z z' y).det -
      Tz k r z * Tz k r z' * Complex.normSq ((Zhat k r z z' y).submatrix Fin.castSucc Fin.castSucc).det := hG
  set a := ((Zhat k r z z' y).submatrix Fin.castSucc Fin.castSucc).det
  set d := (Zhat k r z z' y).det
  simp only [Complex.star_def] at key
  have e : ((Complex.normSq a * Tz k r z' * Tz k r z : ℝ) : ℂ) = ((Complex.normSq d : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj, ← Complex.mul_conj]
    linear_combination key
  have e' := Complex.ofReal_injective e
  linarith [e', show Tz k r z * Tz k r z' * Complex.normSq a = Complex.normSq a * Tz k r z' * Tz k r z by ring]

end hpk

end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

abbrev Sm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (s : Set E) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f s

lemma sv_iff {m : ℕ} {v : E → Fin m → ℂ} : Sm v s ↔ ∀ i, Sm (fun x => v x i) s := by
  exact contDiffOn_pi

lemma sm_iff {p q : ℕ} {M : E → Matrix (Fin p) (Fin q) ℂ} : Sm M s ↔ ∀ i j, Sm (fun x => M x i j) s := by
  unfold Sm
  exact contDiffOn_pi.trans (forall_congr' fun i => contDiffOn_pi)

lemma s_star {f : E → ℂ} (hf : Sm f s) : Sm (fun x => star (f x)) s := by
  exact Complex.conjCLE.contDiff.comp_contDiffOn hf

lemma s_re {f : E → ℂ} (hf : Sm f s) : Sm (fun x => (f x).re) s := by
  exact Complex.reCLM.contDiff.comp_contDiffOn hf

lemma s_ofReal {f : E → ℝ} (hf : Sm f s) : Sm (fun x => ((f x : ℝ) : ℂ)) s := by
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hf

lemma s_mulVec {m : ℕ} {M : E → Matrix (Fin m) (Fin m) ℂ} {v : E → Fin m → ℂ} (hM : Sm M s) (hv : Sm v s) :
    Sm (fun x => M x *ᵥ v x) s := by
  rw [sv_iff]
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun j _ => (sm_iff.1 hM i j).mul (sv_iff.1 hv j)

lemma s_herm {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) {v w : E → Fin m → ℂ} (hv : Sm v s) (hw : Sm w s) :
    Sm (fun x => herm H (v x) (w x)) s := by
  have hH : Sm (fun x => H *ᵥ v x) s := s_mulVec contDiffOn_const hv
  simp only [herm, dotProduct, Pi.star_apply]
  exact ContDiffOn.sum fun i _ => (s_star (sv_iff.1 hw i)).mul (sv_iff.1 hH i)

lemma s_smul {m : ℕ} {c : E → ℂ} {v : E → Fin m → ℂ} (hc : Sm c s) (hv : Sm v s) :
    Sm (fun x => c x • v x) s := by
  rw [sv_iff]
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  exact hc.mul (sv_iff.1 hv i)

lemma s_mmul {m : ℕ} {A B : E → Matrix (Fin m) (Fin m) ℂ} (hA : Sm A s) (hB : Sm B s) :
    Sm (fun x => A x * B x) s := by
  rw [sm_iff]
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (sm_iff.1 hA i l).mul (sm_iff.1 hB l j)

lemma s_ct {m : ℕ} {A : E → Matrix (Fin m) (Fin m) ℂ} (hA : Sm A s) : Sm (fun x => (A x)ᴴ) s := by
  rw [sm_iff]
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact s_star (sm_iff.1 hA j i)

private lemma sm_finset_prod {ι : Type*} (u : Finset ι) {f : ι → E → ℂ} (h : ∀ i ∈ u, Sm (f i) s) :
    Sm (fun x => ∏ i ∈ u, f i x) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using contDiffOn_const
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma s_det {p : ℕ} {M : E → Matrix (Fin p) (Fin p) ℂ} (h : ∀ i j, Sm (fun x => M x i j) s) :
    Sm (fun x => (M x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (sm_finset_prod _ fun i _ => h (σ i) i)

lemma s_adj {p : ℕ} {M : E → Matrix (Fin p) (Fin p) ℂ} (h : ∀ i j, Sm (fun x => M x i j) s) (a b : Fin p) :
    Sm (fun x => (M x).adjugate a b) s := by
  simp only [Matrix.adjugate_apply]
  refine s_det fun i j => ?_
  simp only [Matrix.updateRow_apply]
  by_cases hi : i = b
  · simp only [hi, if_true]
    exact contDiffOn_const
  · simp only [hi, if_false]
    exact h i j

variable {k r : ℕ}

lemma s_wbPart {v : E → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s) : Sm (fun x => wbPart k r (v x)) s := by
  rw [sv_iff]
  intro i
  simp only [wbPart]
  by_cases hc : r ≤ i.val ∧ i.val ≤ r + k
  · simp only [hc, and_self, if_true]
    exact sv_iff.1 hv i
  · simp only [hc, if_false]
    exact contDiffOn_const

lemma s_prW (z : Fin (2 * r + k + 1) → ℂ) {v : E → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s) :
    Sm (fun x => prW k r z (v x)) s := by
  simp only [prW]
  exact (s_wbPart hv).add (s_smul ((s_herm _ (s_wbPart hv) contDiffOn_const).div_const _) contDiffOn_const)

lemma s_Zhat (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) (a b : Fin (r + 1)) :
    Sm (fun x => Zhat k r z z' (Y x) a b) s := by
  simp only [Zhat]
  exact s_herm _ (s_mulVec hY contDiffOn_const) contDiffOn_const

lemma s_xcofL (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) :
    Sm (fun x => xcofL k r z z' (Y x)) s := by
  simp only [xcofL]
  exact ContDiffOn.sum fun a _ =>
    s_smul (s_star (s_adj (fun i j => s_Zhat z z' hY i j) _ _)) contDiffOn_const

lemma s_xcof (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) :
    Sm (fun x => xcof k r z z' (Y x)) s := by
  simp only [xcof]
  exact ContDiffOn.sum fun b _ =>
    s_smul (s_adj (fun i j => s_Zhat z z' hY i j) _ _) (s_mulVec hY contDiffOn_const)

lemma s_omW (z z' : Fin (2 * r + k + 1) → ℂ) {Y : E → B.Mat k r} (hY : Sm Y s) :
    Sm (fun x => omW k r z z' (Y x)) s := by
  simp only [omW]
  exact s_prW z (s_xcof z z' hY)

end smooth

end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section locb

variable {k r : ℕ}

lemma s_qr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m : ℕ}
    (H : Matrix (Fin m) (Fin m) ℂ) {u : E → Fin m → ℂ} {c : E → ℂ} (hu : Sm u s) (hc : Sm c s)
    (hc0 : ∀ x ∈ s, c x ≠ 0) : Sm (fun x => qr H (u x) (c x)) s := by
  have hci : Sm (fun x => (c x)⁻¹) s := hc.inv hc0
  have hsu : Sm (fun x => star (u x)) s := sv_iff.2 fun l => by simpa using s_star (sv_iff.1 hu l)
  have hw : Sm (fun x => star (u x) ᵥ* H) s := by
    simp_rw [← Matrix.mulVec_transpose]; exact s_mulVec contDiffOn_const hsu
  refine sm_iff.2 fun i j => ?_
  simp only [qr, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact contDiffOn_const.sub (hci.mul ((sv_iff.1 hu i).mul (sv_iff.1 hw j)))

def omS (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  prW k r z' ((Hpk k r * gᴴ * Hpk k r) *ᵥ xcofL k r z z' g)

lemma inv_uh {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hL : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hH_sq]
  exact Matrix.inv_eq_left_inv hL

lemma omS_eq (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    omW' k r z z' g = omS k r z z' g := by
  rw [omW', omS, inv_uh hg]

lemma s_omS (z z' : Fin (2 * r + k + 1) → ℂ) {s : Set (B.Mat k r)} : Sm (fun g => omS k r z z' g) s := by
  unfold omS
  have h1 : Sm (fun g : B.Mat k r => Hpk k r * gᴴ * Hpk k r) s :=
    s_mmul (s_mmul contDiffOn_const (s_ct contDiffOn_id)) contDiffOn_const
  exact s_prW z' (s_mulVec h1 (s_xcofL z z' contDiffOn_id))

lemma locB_core {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    (nu' q : Fin (2 * r + k + 1) → ℂ) (S : B.Mat k r) (hq1 : herm (Hpk k r) q q = 1) (hq : q ∈ Wsp k r z')
    (hS : S ∈ UWset k r z') (hSq : S *ᵥ nu' = q) {g₀ : B.Mat k r} (hg₀ : g₀ ∈ B.GV k r)
    (hG₀ : 0 < Gf k r z z' g₀) (hre : (herm (Hpk k r) q (omS k r z z' g₀)).re ≤ 0) :
    ∃ (O : Set (B.Mat k r)) (bf : B.Mat k r → B.Mat k r),
        IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bf O ∧
        ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
          bf g ∈ UWset k r z' ∧ ∃ t : ℝ, 0 < t ∧ omW' k r z z' (g * bf g) = (t : ℂ) • nu' := by
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  let f1 : B.Mat k r → ℝ := fun g => (herm (Hpk k r) (omS k r z z' g) (omS k r z z' g)).re
  let f2 : B.Mat k r → ℝ := fun g => (herm (Hpk k r) q (omS k r z z' g)).re
  have sf1 : Sm f1 Set.univ := s_re (s_herm _ (s_omS z z') (s_omS z z'))
  have sf2 : Sm f2 Set.univ := s_re (s_herm _ contDiffOn_const (s_omS z z'))
  have cf1 : Continuous f1 := (contDiffOn_univ.1 sf1).continuous
  have cf2 : Continuous f2 := (contDiffOn_univ.1 sf2).continuous
  let O : Set (B.Mat k r) := {g | 0 < f1 g} ∩ {g | f2 g < Real.sqrt (f1 g)}
  have hc_re : ∀ g ∈ O, 0 < (1 - herm (Hpk k r) q (nz k r (omS k r z z' g))).re := by
    intro g hg
    have hpos : 0 < Real.sqrt (f1 g) := Real.sqrt_pos.2 hg.1
    have e : (1 - herm (Hpk k r) q (nz k r (omS k r z z' g))).re = 1 - (Real.sqrt (f1 g))⁻¹ * f2 g := by
      unfold nz
      rw [hm_smul_r]
      simp only [Complex.star_def, Complex.conj_ofReal, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
      rfl
    rw [e]
    have h3 : f2 g / Real.sqrt (f1 g) < 1 := (div_lt_one hpos).2 hg.2
    rw [div_eq_inv_mul] at h3
    linarith
  refine ⟨O, fun g => qr (Hpk k r) (q - nz k r (omS k r z z' g))
      (1 - herm (Hpk k r) q (nz k r (omS k r z z' g))) * S,
    (isOpen_lt continuous_const cf1).inter (isOpen_lt cf2 (Real.continuous_sqrt.comp cf1)), ?_, ?_, ?_⟩
  · have hω : omS k r z z' g₀ ≠ 0 := by rw [← omS_eq z z' hg₀]; exact omW'_ne hz hz' hg₀ hG₀
    have hm := prW_mem hz' ((Hpk k r * g₀ᴴ * Hpk k r) *ᵥ xcofL k r z z' g₀)
    have h1 : 0 < f1 g₀ := posV hz' hm.1 hm.2 hω
    exact ⟨h1, lt_of_le_of_lt hre (Real.sqrt_pos.2 h1)⟩
  · have hs1 : Sm (fun g => Real.sqrt (f1 g)) O := (sf1.mono (Set.subset_univ _)).sqrt fun g hg => (hg.1).ne'
    have hN : Sm (fun g => ((Real.sqrt (f1 g))⁻¹ : ℝ)) O := hs1.inv fun g hg => (Real.sqrt_pos.2 hg.1).ne'
    have hy : Sm (fun g => nz k r (omS k r z z' g)) O := by
      unfold nz; exact s_smul (s_ofReal hN) (s_omS z z')
    exact s_mmul (s_qr _ (contDiffOn_const.sub hy) (contDiffOn_const.sub (s_herm _ contDiffOn_const hy))
      fun g hg h0 => by have := hc_re g hg; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this)
      contDiffOn_const
  · intro g hg hgG _
    beta_reduce
    have h1 : 0 < f1 g := hg.1
    have hωW : omS k r z z' g ∈ Wsp k r z' := prW_mem hz' _
    set ω := omS k r z z' g with hωdef
    set y := nz k r ω with hydef
    have hy1 : herm (Hpk k r) y y = 1 := nz_unit h1
    have hyW : inWb k r y := nz_inWb hωW.1
    have hyz : herm (Hpk k r) y z' = 0 := by rw [hydef, nz_herm_l, hωW.2, mul_zero]
    have hc0 : 1 - herm (Hpk k r) q y ≠ 0 := by
      intro h0; have := hc_re g hg; rw [← hydef, h0, Complex.zero_re] at this; exact lt_irrefl _ this
    set c := 1 - herm (Hpk k r) q y with hcdef
    have hqu : herm (Hpk k r) q (q - y) = c := by rw [hm_sub_r, hq1]
    have hcu : c + star c = herm (Hpk k r) (q - y) (q - y) := by
      simp only [hm_sub_l, hm_sub_r]
      rw [hq1, hy1, hm_symm _ hH_ct q y, hcdef, star_sub, star_one]
      ring
    have huW : inWb k r (q - y) := fun i hi => by simp [hq.1 i hi, hyW i hi]
    have huz : herm (Hpk k r) (q - y) z' = 0 := by rw [hm_sub_l, hq.2, hyz, sub_zero]
    have hfix : ∀ v, herm (Hpk k r) v (q - y) = 0 → S *ᵥ v = v → (qr (Hpk k r) (q - y) c * S) *ᵥ v = v := by
      intro v h0 hSv
      rw [← mulVec_mulVec, hSv, qr_fix _ _ h0]
    have hbU : qr (Hpk k r) (q - y) c * S ∈ UWset k r z' := by
      refine ⟨uh_mul _ (qr_uh _ hH_ct _ hc0 hcu) hS.1, fun a => ⟨?_, ?_⟩, ?_⟩
      · exact hfix _ (herm_out_wb (bvec_eI_mid a) huW) (hS.2.1 a).1
      · exact hfix _ (herm_out_wb (bvec_esI_mid a) huW) (hS.2.1 a).2
      · exact hfix _ (by rw [hm_symm _ hH_ct (q - y) z', huz, star_zero]) hS.2.2
    refine ⟨hbU, Real.sqrt (f1 g), Real.sqrt_pos.2 h1, ?_⟩
    have hbν : (qr (Hpk k r) (q - y) c * S) *ᵥ nu' = y := by
      rw [← mulVec_mulVec, hSq, qr_mulVec, hqu, div_self hc0, one_smul, sub_sub_cancel]
    have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hbU.1
    have hinv : (qr (Hpk k r) (q - y) c * S)⁻¹ *ᵥ y = nu' := by
      calc (qr (Hpk k r) (q - y) c * S)⁻¹ *ᵥ y
          = (qr (Hpk k r) (q - y) c * S)⁻¹ *ᵥ ((qr (Hpk k r) (q - y) c * S) *ᵥ nu') := by rw [hbν]
        _ = nu' := by rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    have hscale : ω = ((Real.sqrt (f1 g) : ℝ) : ℂ) • y := by
      rw [hydef]; unfold nz
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 h1).ne', Complex.ofReal_one,
        one_smul]
    have e1 := omW'_UW hz hz' Wz.one_mem hbU g
    rw [one_mul] at e1
    rw [e1, omS_eq z z' hgG, ← hωdef, hscale, mulVec_smul, hinv]

theorem locB : LocB := by
  intro k r z z' hk hr hz hz' D0 g₀ hg₀ hG₀
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  by_cases h : (herm (Hpk k r) D0.nu' (omS k r z z' g₀)).re ≤ 0
  · exact locB_core hz hz' D0.nu' D0.nu' 1 D0.nu'_unit D0.nu'_mem Wz'.one_mem (one_mulVec _) hg₀ hG₀ h
  · have hS : qr (Hpk k r) D0.nu' (1 / 2) ∈ UWset k r z' := by
      refine ⟨qr_uh _ hH_ct _ (by norm_num) (by rw [D0.nu'_unit, star_div₀, star_one, star_ofNat]; norm_num),
        fun a => ⟨qr_fix _ _ (herm_out_wb (bvec_eI_mid a) D0.nu'_mem.1),
          qr_fix _ _ (herm_out_wb (bvec_esI_mid a) D0.nu'_mem.1)⟩, qr_fix _ _ ?_⟩
      rw [hm_symm _ hH_ct D0.nu' z', D0.nu'_mem.2, star_zero]
    refine locB_core hz hz' D0.nu' ((-1 : ℂ) • D0.nu') (qr (Hpk k r) D0.nu' (1 / 2)) ?_ ?_ hS ?_ hg₀ hG₀ ?_
    · rw [hm_smul_l, hm_smul_r, D0.nu'_unit]; norm_num
    · exact ⟨fun i hi => by simp [D0.nu'_mem.1 i hi], by rw [hm_smul_l, D0.nu'_mem.2, mul_zero]⟩
    · rw [qr_mulVec, D0.nu'_unit]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [hm_smul_l, neg_one_mul, Complex.neg_re]
      linarith [not_le.1 h]

end locb

end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section loca

variable {k r : ℕ}

lemma aps {V : Type*} [AddCommGroup V] (a b : V) : a + (b - a) = b := by
  exact add_sub_cancel a b

lemma spa {V : Type*} [AddCommGroup V] (a b : V) : b - a + a = b := by
  exact sub_add_cancel b a

def Rk (k r : ℕ) (p q : Fin (2 * r + k + 1) → ℂ) : B.Mat k r := vecMulVec p (star q ᵥ* Hpk k r)

lemma Rk_mulVec (p q v : Fin (2 * r + k + 1) → ℂ) : Rk k r p q *ᵥ v = herm (Hpk k r) v q • p := by
  unfold Rk
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, ← Matrix.dotProduct_mulVec]
  rfl

def Dw (k r : ℕ) : B.Mat k r := diagonal fun i => if r ≤ i.val ∧ i.val ≤ r + k then 1 else 0

lemma Dw_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Dw k r *ᵥ v = wbPart k r v := by
  funext i
  simp [Dw, Matrix.mulVec_diagonal, wbPart]

def Pm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  Dw k r + ((Tz k r z : ℂ))⁻¹ • (Rk k r z z * Dw k r)

lemma Pm_mulVec (z v : Fin (2 * r + k + 1) → ℂ) : Pm k r z *ᵥ v = prW k r z v := by
  unfold Pm
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Dw_mulVec, Rk_mulVec, smul_smul]
  unfold prW
  rw [div_eq_inv_mul]

def wv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Fin (r + 1) → ℂ := fun a => herm (Hpk k r) (M *ᵥ u) (fvec k r z a)

def gam (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Fin (r + 1) → ℂ :=
  (-((Zhat k r z z' M).det)⁻¹) • ((Zhat k r z z' M).adjugate *ᵥ wv k r z M u)

def Lm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  1 + ∑ c : Fin (r + 1), ∑ a : Fin (r + 1),
    (-((Zhat k r z z' M).det)⁻¹ * (Zhat k r z z' M).adjugate c a) • (Rk k r (fvec k r z' c) (fvec k r z a) * M)

lemma Lm_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Lm k r z z' M *ᵥ u = u + ∑ c, gam k r z z' M u c • fvec k r z' c := by
  unfold Lm gam wv
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Rk_mulVec, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

def Phi (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  Pm k r z * M * Lm k r z z' M

lemma Phi_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ) :
    Phi k r z z' M *ᵥ u = prW k r z (M *ᵥ (Lm k r z z' M *ᵥ u)) := by
  unfold Phi
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Pm_mulVec]

def ev (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  nz k r (omW k r z z' M)

def Am (k r : ℕ) (z z' nu : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) : B.Mat k r :=
  (1 - Pm k r z) + Phi k r z z' M * (Pm k r z - Rk k r nu nu * Pm k r z) + Rk k r (ev k r z z' M) nu * Pm k r z

lemma Am_mulVec (z z' nu : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    Am k r z z' nu M *ᵥ v = (v - prW k r z v) +
      Phi k r z z' M *ᵥ (prW k r z v - herm (Hpk k r) (prW k r z v) nu • nu) +
      herm (Hpk k r) (prW k r z v) nu • ev k r z z' M := by
  unfold Am
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Pm_mulVec,
    Rk_mulVec]

lemma s_msmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m : ℕ} {c : E → ℂ}
    {M : E → Matrix (Fin m) (Fin m) ℂ} (hc : Sm c s) (hM : Sm M s) : Sm (fun x => c x • M x) s :=
  sm_iff.2 fun i j => by simp only [Matrix.smul_apply, smul_eq_mul]; exact hc.mul (sm_iff.1 hM i j)

lemma s_Rk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {p : E → Fin (2 * r + k + 1) → ℂ}
    (hp : Sm p s) (q : Fin (2 * r + k + 1) → ℂ) : Sm (fun x => Rk k r (p x) q) s :=
  sm_iff.2 fun i j => by simp only [Rk, vecMulVec_apply]; exact (sv_iff.1 hp i).mul contDiffOn_const

lemma s_Am {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (z z' nu : Fin (2 * r + k + 1) → ℂ)
    {Y : E → B.Mat k r} (hY : Sm Y s) (hd : ∀ x ∈ s, (Zhat k r z z' (Y x)).det ≠ 0)
    (hn : ∀ x ∈ s, 0 < (herm (Hpk k r) (omW k r z z' (Y x)) (omW k r z z' (Y x))).re) :
    Sm (fun x => Am k r z z' nu (Y x)) s := by
  have hdi : Sm (fun x => -((Zhat k r z z' (Y x)).det)⁻¹) s := ((s_det (s_Zhat z z' hY)).inv hd).neg
  have hL : Sm (fun x => Lm k r z z' (Y x)) s := by
    unfold Lm
    exact contDiffOn_const.add (ContDiffOn.sum fun c _ => ContDiffOn.sum fun a _ =>
      s_msmul (hdi.mul (s_adj (s_Zhat z z' hY) c a)) (s_mmul contDiffOn_const hY))
  have hP : Sm (fun x => Phi k r z z' (Y x)) s := by
    unfold Phi
    exact s_mmul (s_mmul contDiffOn_const hY) hL
  have hf : Sm (fun x => (herm (Hpk k r) (omW k r z z' (Y x)) (omW k r z z' (Y x))).re) s :=
    s_re (s_herm _ (s_omW z z' hY) (s_omW z z' hY))
  have hN : Sm (fun x => ((Real.sqrt (herm (Hpk k r) (omW k r z z' (Y x)) (omW k r z z' (Y x))).re)⁻¹ : ℝ)) s :=
    (hf.sqrt fun x hx => (hn x hx).ne').inv fun x hx => (Real.sqrt_pos.2 (hn x hx)).ne'
  have he : Sm (fun x => ev k r z z' (Y x)) s := by
    unfold ev nz
    exact s_smul (s_ofReal hN) (s_omW z z' hY)
  unfold Am
  exact (contDiffOn_const.add (s_mmul hP contDiffOn_const)).add (s_mmul (s_Rk he nu) contDiffOn_const)

end loca

end PI.UnitaryGroupMassFormula.GsFr
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section loca2

variable {k r : ℕ}

lemma Wsp_sub {z p q : Fin (2 * r + k + 1) → ℂ} (hp : p ∈ Wsp k r z) (hq : q ∈ Wsp k r z) : p - q ∈ Wsp k r z := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  show inWb k r (p - q) ∧ herm (Hpk k r) (p - q) z = 0
  refine ⟨fun i hi => by simp [hp1 i hi, hq1 i hi], ?_⟩
  simp only [herm, Matrix.mulVec_sub, dotProduct_sub] at hp2 hq2 ⊢
  rw [hp2, hq2, sub_zero]

lemma Wsp_smul {z p : Fin (2 * r + k + 1) → ℂ} (c : ℂ) (hp : p ∈ Wsp k r z) : c • p ∈ Wsp k r z := by
  obtain ⟨hp1, hp2⟩ := hp
  show inWb k r (c • p) ∧ herm (Hpk k r) (c • p) z = 0
  refine ⟨fun i hi => by simp [hp1 i hi], ?_⟩
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul] at hp2 ⊢
  rw [hp2, smul_zero]

lemma wbPart_of_inWb {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : wbPart k r v = v := by
  funext i
  unfold wbPart
  split_ifs with h
  · rfl
  · symm
    exact hv i (by omega)

lemma prW_of_mem {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) : prW k r z q = q := by
  obtain ⟨h1, h2⟩ := hq
  unfold prW
  rw [wbPart_of_inWb h1, h2, zero_div, zero_smul, add_zero]

lemma prW_of_mid {z v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → v i = 0) : prW k r z v = 0 := by
  have h0 : wbPart k r v = 0 := by
    funext i
    unfold wbPart
    split_ifs with h
    · exact hv i h.1 h.2
    · rfl
  unfold prW
  rw [h0]
  simp [herm]

private lemma herm_star_lemma (v w : Fin (2 * r + k + 1) → ℂ) :
    star (herm (Hpk k r) v w) = herm (Hpk k r) w v := by
  unfold herm
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, star_star, hH_ct, Matrix.dotProduct_mulVec]

lemma prW_self {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) : prW k r z z = 0 := by
  obtain ⟨hzw, hT⟩ := hz
  have hre : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := by
    have h1 := herm_star_lemma (k := k) (r := r) z z
    apply Complex.ext
    · simp [Tz]
    · have := congrArg Complex.im h1
      simp only [Complex.star_def, Complex.conj_im] at this
      simp only [Complex.ofReal_im]
      linarith
  have hT' : (Tz k r z : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold prW
  rw [wbPart_of_inWb hzw, hre, Complex.ofReal_neg, neg_div, div_self hT', neg_one_smul,
    add_neg_cancel]

lemma perp_l {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (v - prW k r z v) q = 0 := by
  have h := herm_prW_l hq v
  unfold herm at h ⊢
  rw [Matrix.mulVec_sub, dotProduct_sub, h, sub_self]

lemma perp_r {z q : Fin (2 * r + k + 1) → ℂ} (hq : q ∈ Wsp k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) q (v - prW k r z v) = 0 := by
  have h := herm_prW_r hq v
  unfold herm at h ⊢
  rw [star_sub, sub_dotProduct, h, sub_self]

lemma X_mid {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Xsp k r) :
    ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → x i = 0 := by
  intro i hi1 _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    have := a.isLt
    show bvec (eI k r a) i = 0
    unfold bvec
    rw [Pi.single_apply, if_neg]
    intro h
    have h' : (i : ℕ) = a := by simpa [eI] using congrArg Fin.val h
    omega
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

lemma sub_prW_X {z q : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z)
    (hq : ∀ a, herm (Hpk k r) q (fvec k r z a) = 0) : q - prW k r z q ∈ Xsp k r := by
  obtain ⟨hzw, -⟩ := hz
  have hqz : herm (Hpk k r) q z = 0 := by
    have := hq (Fin.last r)
    simpa [fvec] using this
  have hX : ∀ a : Fin r, q (esI k r a) = 0 := by
    intro a
    have ha := a.isLt
    have h := hq ⟨a.val, by omega⟩
    have hf : fvec k r z ⟨a.val, by omega⟩ = bvec (eI k r a) := by
      simp [fvec, ha]
    rw [hf] at h
    have hc : herm (Hpk k r) q (bvec (eI k r a)) = q (esI k r a) := by
      simp only [herm, bvec, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (eI k r a)]
      · rw [Finset.sum_eq_single (esI k r a)]
        · simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul]
          dsimp only [Hpk, eI, esI]
          rw [if_pos ⟨ha, by omega⟩, one_mul]
        · intro j _ hj
          have hj' : (j : ℕ) ≠ 2 * r + k - a := fun h => hj (Fin.ext h)
          have hjl := j.isLt
          dsimp only [Hpk, eI]
          split_ifs <;> first | (exfalso; omega) | simp
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro i _ hi
        simp [Pi.single_apply, hi]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hc] at h
    exact h
  have hwb : herm (Hpk k r) (wbPart k r q) z = 0 := by
    have h1 : herm (Hpk k r) (q - wbPart k r q) z = 0 :=
      herm_out_wb (fun i hi1 hi2 => by simp [wbPart, hi1, hi2]) hzw
    have h2 : herm (Hpk k r) (q - wbPart k r q) z =
        herm (Hpk k r) q z - herm (Hpk k r) (wbPart k r q) z := by
      simp [herm, Matrix.mulVec_sub, dotProduct_sub]
    rw [h2, hqz] at h1
    linear_combination -h1
  have hpr : prW k r z q = wbPart k r q := by
    unfold prW
    rw [hwb, zero_div, zero_smul, add_zero]
  rw [hpr]
  exact sub_wbPart_X hX

lemma Am_fix (z z' nu : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : prW k r z v = 0) : Am k r z z' nu M *ᵥ v = v := by
  have h0 : herm (Hpk k r) 0 nu = 0 := by simp [herm]
  rw [Am_mulVec, hv]
  simp [h0]

private lemma herm_GV_lemma {y : B.Mat k r} (hy : y ∈ B.GV k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (y *ᵥ v) (y *ᵥ w) = herm (Hpk k r) v w := by
  have h1 : y * y⁻¹ = 1 := by
    ext i j
    have := congrFun (ginv_cancel hy (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
      using this
  have h2 : y⁻¹ * y = 1 := by
    first
      | exact mul_eq_one_comm.mp h1
      | exact Matrix.mul_eq_one_comm.1 h1
      | exact Matrix.nonsing_inv_mul y
          (IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, h1, Matrix.det_one]))
  have h3 : yᴴ * Hpk k r = Hpk k r * y⁻¹ := by
    rw [inv_uh hy, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hH_sq, Matrix.one_mul]
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3,
    Matrix.mul_assoc, h2, Matrix.mul_one]

lemma lift_X {z z' : Fin (2 * r + k + 1) → ℂ} (D0 : GfBaseD k r z z') {y : B.Mat k r}
    (hy : y ∈ B.GV k r) {t : ℝ} (hom' : omW' k r z z' y = (t : ℂ) • D0.nu') {u : Fin (2 * r + k + 1) → ℂ}
    (hu : u ∈ D0.U0) : Lm k r z z' y *ᵥ u - u ∈ Xsp k r := by
  have hu' := (D0.isotropic_subspace_eq_primed u).1 hu
  have hgl : gam k r z z' y u (Fin.last r) = 0 := by
    have hsum : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * wv k r z y u a =
        herm (Hpk k r) (y *ᵥ u) (xcofL k r z z' y) := by
      simp only [xcofL, wv, herm, star_sum, star_smul, sum_dotProduct, smul_dotProduct, star_star,
        smul_eq_mul]
    have hun := herm_GV_lemma hy u (y⁻¹ *ᵥ xcofL k r z z' y)
    rw [ginv_cancel hy] at hun
    have hpr := herm_prW_r hu'.1 (y⁻¹ *ᵥ xcofL k r z z' y)
    have hom : herm (Hpk k r) u (omW' k r z z' y) = 0 := by
      have h0 := hu'.2
      rw [hom']
      unfold herm at h0 ⊢
      rw [star_smul, smul_dotProduct, h0, smul_zero]
    have hmv : ((Zhat k r z z' y).adjugate *ᵥ wv k r z y u) (Fin.last r) = 0 := by
      change ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * wv k r z y u a = 0
      rw [hsum, hun, ← hpr]
      exact hom
    simp [gam, hmv]
  rw [Lm_mulVec, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = Fin.last r
  · subst hc
    rw [hgl, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (fv_X z' c hc)

lemma lift_orth {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hd : (Zhat k r z z' y).det ≠ 0)
    (u : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) :
    herm (Hpk k r) (y *ᵥ (Lm k r z z' y *ᵥ u)) (fvec k r z a) = 0 := by
  have hadd : ∀ v w f : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) (v + w) f = herm (Hpk k r) v f + herm (Hpk k r) w f := by
    intro v w f
    simp [herm, Matrix.mulVec_add, dotProduct_add]
  have hsmul : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (c • v) f = c * herm (Hpk k r) v f := by
    intro c v f
    simp [herm, Matrix.mulVec_smul, dotProduct_smul]
  have hsum : ∀ (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (∑ c, g c) f = ∑ c, herm (Hpk k r) (g c) f := by
    intro g f
    simp [herm, Matrix.mulVec_sum, dotProduct_sum]
  rw [Lm_mulVec, Matrix.mulVec_add, Matrix.mulVec_sum, hadd, hsum]
  simp only [Matrix.mulVec_smul, hsmul]
  change wv k r z y u a + ∑ c, gam k r z z' y u c * Zhat k r z z' y a c = 0
  have hZg : Zhat k r z z' y *ᵥ gam k r z z' y u = -wv k r z y u := by
    unfold gam
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, smul_smul, neg_mul, inv_mul_cancel₀ hd, neg_smul, one_smul]
  rw [show ∑ c, gam k r z z' y u c * Zhat k r z z' y a c = (Zhat k r z z' y *ᵥ gam k r z z' y u) a by
    simp [Matrix.mulVec, dotProduct, mul_comm], hZg]
  simp

lemma phi_iso {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (D0 : GfBaseD k r z z')
    {y : B.Mat k r} (hy : y ∈ B.GV k r) (hd : (Zhat k r z z' y).det ≠ 0) {t : ℝ}
    (hom' : omW' k r z z' y = (t : ℂ) • D0.nu') {u u' : Fin (2 * r + k + 1) → ℂ} (hu : u ∈ D0.U0)
    (hu' : u' ∈ D0.U0) :
    herm (Hpk k r) (Phi k r z z' y *ᵥ u) (Phi k r z z' y *ᵥ u') = herm (Hpk k r) u u' := by
  have hX : ∀ v ∈ D0.U0, (y *ᵥ (Lm k r z z' y *ᵥ v)) - Phi k r z z' y *ᵥ v ∈ Xsp k r := by
    intro v _
    rw [Phi_mulVec]
    exact sub_prW_X hz (fun a => lift_orth hd v a)
  have hinW : ∀ v, inWb k r (Phi k r z z' y *ᵥ v) := by
    intro v
    rw [Phi_mulVec]
    exact (prW_mem hz _).1
  have hL : ∀ v ∈ D0.U0, Lm k r z z' y *ᵥ v - v ∈ Xsp k r := fun v hv => lift_X D0 hy hom' hv
  have hUw : ∀ v ∈ D0.U0, inWb k r v := fun v hv => ((D0.isotropic_subspace_eq v).1 hv).1.1
  have e1 := herm_add_X (hinW u) (hinW u') (hX u hu) (hX u' hu')
  have e2 := herm_add_X (hUw u hu) (hUw u' hu') (hL u hu) (hL u' hu')
  rw [add_sub_cancel, add_sub_cancel] at e1 e2
  rw [← e1, herm_GV_lemma hy, e2]

private lemma herm_bvec_lemma (q : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) q (bvec (eI k r a)) = q (esI k r a) := by
  have ha := a.isLt
  simp only [herm, bvec, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (eI k r a)]
  · rw [Finset.sum_eq_single (esI k r a)]
    · simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul]
      dsimp only [Hpk, eI, esI]
      rw [if_pos ⟨ha, by omega⟩, one_mul]
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 2 * r + k - a := fun h => hj (Fin.ext h)
      have hjl := j.isLt
      dsimp only [Hpk, eI]
      split_ifs <;> first | (exfalso; omega) | simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma phi_perp {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    (D0 : GfBaseD k r z z') {y : B.Mat k r} (hy : y ∈ B.GV k r) (hd : (Zhat k r z z' y).det ≠ 0) {t : ℝ}
    (hom' : omW' k r z z' y = (t : ℂ) • D0.nu') {u : Fin (2 * r + k + 1) → ℂ} (hu : u ∈ D0.U0) :
    herm (Hpk k r) (Phi k r z z' y *ᵥ u) (omW k r z z' y) = 0 := by
  have hsum1 : ∀ (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (∑ c, g c) f = ∑ c, herm (Hpk k r) (g c) f := by
    intro g f
    simp [herm, Matrix.mulVec_sum, dotProduct_sum]
  have hsmul1 : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) (c • v) f = c * herm (Hpk k r) v f := by
    intro c v f
    simp [herm, Matrix.mulVec_smul, dotProduct_smul]
  have hsum2 : ∀ (v : Fin (2 * r + k + 1) → ℂ) (g : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) v (∑ c, g c) = ∑ c, herm (Hpk k r) v (g c) := by
    intro v g
    simp [herm, star_sum, sum_dotProduct]
  have hsmul2 : ∀ (c : ℂ) (v f : Fin (2 * r + k + 1) → ℂ),
      herm (Hpk k r) v (c • f) = star c * herm (Hpk k r) v f := by
    intro c v f
    simp [herm, star_smul, smul_dotProduct]
  set w := y *ᵥ (Lm k r z z' y *ᵥ u) with hw
  have hu' := (D0.isotropic_subspace_eq_primed u).1 hu
  have hLf : ∀ b, herm (Hpk k r) (Lm k r z z' y *ᵥ u) (fvec k r z' b) = 0 := by
    intro b
    have hx0 := lift_X D0 hy hom' hu
    have hsplit : Lm k r z z' y *ᵥ u = u + (Lm k r z z' y *ᵥ u - u) := by abel
    rw [hsplit]
    by_cases hb : b = Fin.last r
    · subst hb
      have hf : fvec k r z' (Fin.last r) = z' + 0 := by simp [fvec]
      rw [hf, herm_add_X hu'.1.1 hz'.1 hx0 (Submodule.zero_mem _)]
      exact hu'.1.2
    · have hf : fvec k r z' b = 0 + fvec k r z' b := by simp
      rw [hf, herm_add_X (q := (0 : Fin (2 * r + k + 1) → ℂ)) hu'.1.1 (fun i _ => rfl) hx0 (fv_X z' b hb)]
      simp [herm]
  have hwx : herm (Hpk k r) w (xcof k r z z' y) = 0 := by
    have hb : ∀ b, herm (Hpk k r) w (y *ᵥ fvec k r z' b) = 0 := fun b => by
      rw [hw, herm_GV_lemma hy]
      exact hLf b
    unfold xcof
    rw [hsum2]
    simp only [hsmul2, hb, mul_zero, Finset.sum_const_zero]
  have hxl : ∀ a : Fin r, xcof k r z z' y (esI k r a) = 0 := by
    intro a
    have ha := a.isLt
    set a' : Fin (r + 1) := ⟨a.val, by omega⟩ with ha'
    have hne : a' ≠ Fin.last r := fun h => by
      have := congrArg Fin.val h
      simp [a'] at this
      omega
    have hf : bvec (eI k r a) = fvec k r z a' := by simp [fvec, a', ha]
    rw [← herm_bvec_lemma (xcof k r z z' y) a, hf]
    have hZ : herm (Hpk k r) (xcof k r z z' y) (fvec k r z a') =
        ((Zhat k r z z' y) * (Zhat k r z z' y).adjugate) a' (Fin.last r) := by
      unfold xcof
      rw [hsum1, Matrix.mul_apply]
      simp only [hsmul1]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [hZ, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply_ne hne, smul_zero]
  have hxw : w - prW k r z w ∈ Xsp k r := sub_prW_X hz (fun a => lift_orth hd u a)
  have hxc : xcof k r z z' y - wbPart k r (xcof k r z z' y) ∈ Xsp k r := sub_wbPart_X hxl
  have hwbI : inWb k r (wbPart k r (xcof k r z z' y)) := fun i hi => by
    unfold wbPart
    rw [if_neg (by omega)]
  have hpm := prW_mem hz w
  have e1 : herm (Hpk k r) w (xcof k r z z' y) =
      herm (Hpk k r) (prW k r z w) (wbPart k r (xcof k r z z' y)) := by
    have := herm_add_X hpm.1 hwbI hxw hxc
    rwa [add_sub_cancel, add_sub_cancel] at this
  have e2 : herm (Hpk k r) (prW k r z w) (xcof k r z z' y) =
      herm (Hpk k r) (prW k r z w) (wbPart k r (xcof k r z z' y)) := by
    have := herm_add_X hpm.1 hwbI (Submodule.zero_mem _) hxc
    rwa [add_zero, add_sub_cancel] at this
  rw [Phi_mulVec, ← hw]
  unfold omW
  rw [herm_prW_r hpm, e2, ← e1, hwx]

end loca2

end PI.UnitaryGroupMassFormula.GsFr
end
end
