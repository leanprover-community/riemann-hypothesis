import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon

section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc Matrix

private theorem scal_mem {O L : Type} [CommRing O] [CommRing L] [Algebra O L] (u : Lˣ)
    (d : (integralClosure O L)ˣ)
    (h : u ^ 2 * Units.map ((integralClosure O L).val : integralClosure O L →* L) d = 1) :
    ∃ w : (integralClosure O L)ˣ, Units.map ((integralClosure O L).val : integralClosure O L →* L) w = u := by
  have h1 : u ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  have h2 : u⁻¹ ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d := by
    rw [inv_pow, h1, map_inv, inv_inv]
  have i1 : IsIntegral O (u : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h1]
    exact ((d⁻¹ : (integralClosure O L)ˣ) : integralClosure O L).2
  have i2 : IsIntegral O ((u⁻¹ : Lˣ) : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h2]
    exact (d : integralClosure O L).2
  exact ⟨⟨⟨u, i1⟩, ⟨(u⁻¹ : Lˣ), i2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, Units.ext rfl⟩

theorem UpperTheory.orbitalFiber_det_eq_one :
    UpperTheory.V.Z.Sym.Glob.Fib.DetOne := by
  intro O K _ _ _ Δ g hg hs
  have hn : (ZD Δ).Normal := by
    refine ⟨fun n hn x => ?_⟩
    have : x * n * x⁻¹ = n := by
      obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hn
      rw [mul_inv_eq_iff_eq_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hz]
      apply Units.ext
      exact ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm).eq
    rwa [this]
  obtain ⟨s, hsz, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  refine mul_mem ?_ hk
  obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hsz
  obtain ⟨k₀, hk₀⟩ := Subgroup.mem_subgroupOf.1 hk
  have hd : GeneralLinearGroup.det ((s : GL (Fin 2) (Lsq K Δ)) * (k : GL (Fin 2) (Lsq K Δ))) = 1 := hs
  rw [map_mul, ← hz, ← hk₀] at hd
  obtain ⟨w, hw⟩ := scal_mem (O := O) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z)
    (GeneralLinearGroup.det k₀) (by
      rw [← hd]
      congr 1
      · apply Units.ext
        simp [pow_two])
  refine Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.scalar (Fin 2) w, ?_⟩
  rw [← hz, MonoidHom.comp_apply, ← hw]
  apply Units.ext
  ext i j : 1
  by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply]
end

section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

private theorem comap_relIndex_ne_zero {G H : Type} [Group G] [Group H] (p : G →* H) (A B : Subgroup H)
    (T : Subgroup G) (hAB : A.relIndex B ≠ 0) (hT : ∀ g ∈ T, p g ∈ B) : (A.comap p).relIndex T ≠ 0 := by
  rw [Subgroup.relIndex_comap]
  intro h
  exact hAB (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_iff_le_comap.mpr hT) h)

private theorem finset_relIndex_ne_zero {G I : Type} [Group G] (H : I → Subgroup G) (T : Subgroup G) (S : Finset I)
    (h : ∀ v ∈ S, (H v).relIndex T ≠ 0) : ∃ W : Subgroup G, W.relIndex T ≠ 0 ∧ ∀ v ∈ S, W ≤ H v := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨W, hW, hWS⟩ := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
    refine ⟨H a ⊓ W, Subgroup.relIndex_inf_ne_zero (h a (Finset.mem_insert_self a S)) hW, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact inf_le_left
    · exact inf_le_right.trans (hWS v hv)

theorem UpperTheory.orbitalFiber_level_finite :
    UpperTheory.V.Z.Sym.Glob.Fib.LevFin := by
  unfold Fib.LevFin
  intro F _ _ Δ D hD
  have hDet : Fib.DetOne := UpperTheory.orbitalFiber_det_eq_one
  unfold Fib.DetOne at hDet
  set P := rpg (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v)) with hP
  have hle : ∀ v, D.J2v v ≤ KD ((cv v) Δ) (Ov v) := by
    intro v
    rw [Dat.J2v.eq_1]
    split_ifs with hv
    · exact SigOk.levelTwoLeIntegral (hD.sig v hv)
    · exact le_rfl
  have hT : ∀ v, ∀ g ∈ D.UZ ⊓ SA Δ, P.p v g ∈ KD ((cv v) Δ) (Ov v) := by
    intro v g hg
    have h1 : g ∈ D.UZ := hg.1
    have h2 : g ∈ SA Δ := hg.2
    rw [Dat.UZ.eq_1, RPG.box.eq_1, Subgroup.mem_iInf] at h1
    rw [SA.eq_1, Subgroup.mem_iInf] at h2
    have a := h1 v
    have b := h2 v
    rw [Subgroup.mem_comap] at a b
    exact hDet _ _ _ _ (sup_le_sup_left (hle v) _ a) b
  have hfin : ∀ v ∈ D.Sg, ((D.J2v v).comap (P.p v)).relIndex (D.UZ ⊓ SA Δ) ≠ 0 := by
    intro v hv
    apply comap_relIndex_ne_zero (P.p v) (D.J2v v) (KD ((cv v) Δ) (Ov v))
    · rw [Dat.J2v.eq_1, if_pos hv]
      exact SigOk.levelTwoFiniteIndex (hD.sig v hv)
    · exact hT v
  obtain ⟨W, hW, hWS⟩ := finset_relIndex_ne_zero (fun v => (D.J2v v).comap (P.p v)) _ D.Sg hfin
  have hsub : W ⊓ (D.UZ ⊓ SA Δ) ≤ D.U2 := by
    intro g hg
    rw [Dat.U2.eq_1, RPG.box.eq_1, Subgroup.mem_iInf]
    intro v
    rw [Subgroup.mem_comap]
    by_cases hv : v ∈ D.Sg
    · exact hWS v hv hg.1
    · have e := hT v g hg.2
      rw [Dat.J2v.eq_1, if_neg hv]
      exact e
  refine ⟨?_, ?_⟩
  · rw [Dat.U2.eq_1, Dat.UZ.eq_1, RPG.box.eq_1, RPG.box.eq_1]
    exact iInf_mono fun v => Subgroup.comap_mono le_sup_right
  · intro h
    apply hW
    rw [← Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_eq_zero_of_le_left hsub h
end
