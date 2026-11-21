import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecFunct
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_ur_lift (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    ∃ t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ, IsLocallyConstant t ∧
      ∀ g : GK p K, (QuotientAddGroup.mk (t (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g) := by
  let sec : QZ → ℚ := Function.surjInv (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  have hsec : ∀ q : QZ, (QuotientAddGroup.mk (sec q) : QZ) = q :=
    Function.surjInv_eq (QuotientAddGroup.mk'_surjective (Int.castAddHom ℚ).range)
  let f : GK p K → QZ := fun g => χ.1 (Additive.ofMul g)
  have hf : IsLocallyConstant f := χ.2
  have hfq : ∀ g : GK p K, f (QuotientGroup.mk g : GalLK p K (MaximalUnramifiedExtension p K)).out = f g := by
    intro g
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul (subG p K (MaximalUnramifiedExtension p K)) g
    rw [hn]
    show χ.1 (Additive.ofMul g + Additive.ofMul n.1) = _
    rw [map_add, hχ n.1 n.2, add_zero]
  have hloc : IsLocallyConstant fun q : GalLK p K (MaximalUnramifiedExtension p K) => f q.out := by
    intro s
    rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isOpen_preimage]
    have h0 : (QuotientGroup.mk : GK p K → GalLK p K (MaximalUnramifiedExtension p K)) ⁻¹'
        ((fun q : GalLK p K (MaximalUnramifiedExtension p K) => f q.out) ⁻¹' s) = f ⁻¹' s := by
      ext g
      show f (QuotientGroup.mk g : GalLK p K (MaximalUnramifiedExtension p K)).out ∈ s ↔ f g ∈ s
      rw [hfq]
    rw [h0]
    exact hf s
  refine ⟨fun q => sec (f q.out), hloc.comp sec, fun g => ?_⟩
  rw [hsec]
  exact hfq g

variable (p K) in

noncomputable def urOfK (a : Kˣ) : (urT p K).V :=
  toLayer p ⟨ofK p K (Additive.ofMul a), le_Kur (K := K) (ofK_mem p K _)⟩

theorem urOfK_val (a : Kˣ) : (urOfK p K a).1 = ofK p K (Additive.ofMul a) := rfl

theorem exists_ur_cocycle (a : Kˣ) (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    ∃ (t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ) (z : (urT p K).coch.X 2)
      (hz : (urT p K).coch.d 2 z = 0), IsLocallyConstant t ∧
      (∀ g : GK p K, (QuotientAddGroup.mk (t (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g)) ∧
      (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) ∧ (∀ g, z.1 g = m g • urOfK p K a) ∧
      pairBr p K a χ = (layerInf p K (MaximalUnramifiedExtension p K)).hom.H 2 ((urT p K).coch.cls 2 z hz) := by
  obtain ⟨t, ht, htχ⟩ := exists_ur_lift χ hχ
  have hex : ∀ g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K), ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
    intro g
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (g 0)
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (g 1)
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [← hσ, ← hτ, ← QuotientGroup.mk_mul, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, htχ, htχ, htχ,
        ofMul_mul, map_add, sub_self]
    exact (QuotientAddGroup.eq_zero_iff _).1 h0
  choose m hm using hex
  have hmc : IsLocallyConstant m := by
    apply IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) _ Int.cast_injective
    have h0 : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
    rw [h0]
    exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  have hzc : Continuous fun g : Fin 2 → GalLK p K (MaximalUnramifiedExtension p K) => m g • urOfK p K a :=
    (hmc.comp fun k : ℤ => k • urOfK p K a).continuous
  let z : (urT p K).coch.X 2 := ⟨fun g => m g • urOfK p K a, hzc⟩
  have hinv := (layer_invariant_iff (urOfK p K a)).2 (ofK_mem p K _)
  have hz : (urT p K).coch.d 2 z = 0 := by
    apply LowDeg.coch_d_eq_zero
    funext g
    have h1 : m ![g 1, g 2] - m ![g 0 * g 1, g 2] + m ![g 0, g 1 * g 2] - m ![g 0, g 1] = 0 := by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hm, hm, hm, hm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
      ring
    rw [LowDeg.dn_two_apply]
    show (urT p K).rho (g 0) (m ![g 1, g 2] • urOfK p K a) - m ![g 0 * g 1, g 2] • urOfK p K a +
      m ![g 0, g 1 * g 2] • urOfK p K a - m ![g 0, g 1] • urOfK p K a = 0
    rw [map_zsmul, hinv, ← sub_smul, ← add_smul, ← sub_smul, h1, zero_smul]
  refine ⟨t, m, z, hz, ht, htχ, hm, fun _ => rfl, ?_⟩
  refine IsPairClass.unique (isPairClass_pairBr a χ)
    ⟨fun g => t (QuotientGroup.mk g), fun g => m fun i => QuotientGroup.mk (g i),
      (layerInf p K (MaximalUnramifiedExtension p K)).hom.f 2 z, by rw [← (layerInf p K (MaximalUnramifiedExtension p K)).hom.comm, hz, map_zero],
      ht.comp_continuous continuous_quot_mk, htχ, fun g => hm _, fun g => rfl, rfl⟩

theorem pairK_unit_unr (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (ha : a ∈ UK p K) (χ : charGrp (GK p K))
    (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) : pairK p K a χ = 0 := by
  obtain ⟨t, m, z, hz, -, -, -, hzm, h⟩ := exists_ur_cocycle a χ hχ
  have hv : vLayerMap p K (MaximalUnramifiedExtension p K) (urOfK p K a) = 0 := by
    apply Int.cast_injective (α := ℝ)
    rw [vLayerMap_spec p le_Kur, urOfK_val, vbar_apply]
    have ha' : ‖((a : K) : PadicAlgCl p)‖ = 1 := ha
    show (eK p (MaximalUnramifiedExtension p K) : ℝ) * - Real.logb p ‖((a : K) : PadicAlgCl p)‖ = _
    rw [ha']
    simp
  have hf0 : (vLayer p K (MaximalUnramifiedExtension p K)).hom.f 2 z = 0 := by
    apply Subtype.ext
    funext g
    show vLayerMap p K (MaximalUnramifiedExtension p K) (z.1 fun i => g i) = 0
    rw [hzm, map_zsmul, hv, smul_zero]
  have hc : (urT p K).coch.cls 2 z hz = 0 := by
    apply (valuation_unramified_closure_h2_bijective hK).1
    rw [map_zero]
    show (trivRep (GalLK p K (MaximalUnramifiedExtension p K)) ℤ).coch.cls 2 ((vLayer p K (MaximalUnramifiedExtension p K)).hom.f 2 z) _ = 0
    refine (LongExactSequenceMaps.cls_eq_zero _ 2 _ _).2 ?_
    rw [hf0]
    exact Submodule.zero_mem _
  unfold pairK
  rw [h, hc, map_zero, map_zero]

theorem pairK_uniformiser_unr (hK : FiniteDimensional ℚ_[p] K) (π : Kˣ) (hπ : vK p K π = 1) (χ : charGrp (GK p K))
    (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) : pairK p K π χ = χ.1 (Additive.ofMul (frobK p K)) := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzm, h⟩ := exists_ur_cocycle π χ hχ
  have h1 : (eK p K : ℝ) * vbar p (urOfK p K π).1 = 1 := by
    have h2 := vOn_spec p K ⟨ofK p K (Additive.ofMul π), ofK_mem p K _⟩
    have h3 : vOn p K ⟨ofK p K (Additive.ofMul π), ofK_mem p K _⟩ = 1 := hπ
    rw [h3, Int.cast_one] at h2
    exact h2.symm
  unfold pairK
  rw [h, invBr_layerInf hK, isInv_invUr hK (urOfK p K π) t m z hz (ofK_mem p K _) h1 ht hm hzm]
  exact htχ (frobK p K)

theorem pairK_unr (hK : FiniteDimensional ℚ_[p] K) (a : Kˣ) (χ : charGrp (GK p K)) (hχ : TrivOn p K (MaximalUnramifiedExtension p K) χ) :
    pairK p K a χ = vK p K a • χ.1 (Additive.ofMul (frobK p K)) := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  have hzpow : ∀ n : ℤ, pairK p K (π ^ n) χ = n • pairK p K π χ := by
    intro n
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
    · rw [zpow_natCast, pairK_pow, natCast_zsmul]
    · rw [zpow_neg, zpow_natCast, pairK_inv, pairK_pow, neg_smul, natCast_zsmul]
  have hu : a * (π ^ vK p K a)⁻¹ ∈ UK p K := by
    rw [mem_UK_iff p K hK, vK_mul, vK_inv, vK_zpow, hπ]
    ring
  have ha : a = a * (π ^ vK p K a)⁻¹ * π ^ vK p K a := by rw [inv_mul_cancel_right]
  conv_lhs => rw [ha]
  rw [pairK_mul, pairK_unit_unr hK _ hu χ hχ, zero_add, hzpow, pairK_uniformiser_unr hK π hπ χ hχ]

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ofK_injective : Injective (ofK p K) := by
  intro a b hab
  have h1 : (((Additive.toMul a : Kˣ) : K) : PadicAlgCl p) = (((Additive.toMul b : Kˣ) : K) : PadicAlgCl p) :=
    congrArg (fun y : KbarMult p => ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)) hab
  exact Additive.toMul.injective (Units.ext (Subtype.ext h1))

theorem exists_ofK_eq (y : KbarMult p) (hy : y ∈ multOf p K) : ∃ a : Kˣ, ofK p K (Additive.ofMul a) = y := by
  have hne : (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ : K) ≠ 0 := fun h0 =>
    (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h0)
  exact ⟨Units.mk0 _ hne, Additive.toMul.injective (Units.ext rfl)⟩

theorem exists_normUnits (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    ∃ ν : Lˣ →* Kˣ, ∀ b, ofK p K (Additive.ofMul (ν b)) = normHom p K L (ofK p L (Additive.ofMul b)) := by
  choose ν hν using fun b : Lˣ => exists_ofK_eq _ (normHom_mem hL h _ (ofK_mem p L (Additive.ofMul b)))
  refine ⟨MonoidHom.mk' ν fun a b => ?_, hν⟩
  apply Additive.ofMul.injective
  apply ofK_injective (p := p) (K := K)
  rw [hν, ofMul_mul, ofMul_mul, map_add, map_add, map_add, hν, hν]

theorem mem_normGrp_iff_exists (a : Kˣ) :
    a ∈ normGrp p K L ↔ ∃ b : Lˣ, ofK p K (Additive.ofMul a) = normHom p K L (ofK p L (Additive.ofMul b)) := by
  rw [mem_normGrp_iff]
  constructor
  · rintro ⟨y, hy, hya⟩
    obtain ⟨b, rfl⟩ := exists_ofK_eq y hy
    exact ⟨b, hya.symm⟩
  · rintro ⟨b, hb⟩
    exact ⟨_, ofK_mem p L _, hb.symm⟩

theorem normGrp_eq_range (ν : Lˣ →* Kˣ)
    (hν : ∀ b, ofK p K (Additive.ofMul (ν b)) = normHom p K L (ofK p L (Additive.ofMul b))) :
    normGrp p K L = ν.range := by
  ext a
  rw [mem_normGrp_iff_exists, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, Additive.ofMul.injective (ofK_injective ((hν b).trans hb.symm))⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, hν b⟩

theorem normGrp_eq_map {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L') (h : K ≤ L) (h' : L ≤ L')
    (ν : Lˣ →* Kˣ) (hν : ∀ b, ofK p K (Additive.ofMul (ν b)) = normHom p K L (ofK p L (Additive.ofMul b))) :
    normGrp p K L' = (normGrp p L L').map ν := by
  ext a
  rw [mem_normGrp_iff_exists, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb⟩ := exists_ofK_eq _ (normHom_mem (K := L) hL' h' _ (ofK_mem p L' (Additive.ofMul c)))
    refine ⟨b, (mem_normGrp_iff_exists b).2 ⟨c, hb⟩, Additive.ofMul.injective (ofK_injective ?_)⟩
    rw [hν, hb, normHom_trans hL' h h' _ (ofK_mem p L' _), hc]
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨c, hc⟩ := (mem_normGrp_iff_exists b).1 hb
    exact ⟨c, by rw [hν, hc, normHom_trans hL' h h' _ (ofK_mem p L' _)]⟩

theorem index_normGrp_tower_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : FiniteDimensional ℚ_[p] L) (hL' : FiniteDimensional ℚ_[p] L')
    (h : K ≤ L) (h' : L ≤ L') :
    (normGrp p K L').index ≤ (normGrp p L L').index * (normGrp p K L).index := by
  obtain ⟨ν, hν⟩ := exists_normUnits hL h
  rw [normGrp_eq_map hL' h h' ν hν, normGrp_eq_range ν hν, Subgroup.index_map]
  have := finiteIndex_normGrp hL hL' h'
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (Nat.pos_of_ne_zero this.index_ne_zero)
    (Subgroup.index_dvd_of_le le_sup_left))

theorem IsAbLK.base {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : IsAbLK p K L) (h : K ≤ M) (h' : M ≤ L) : IsAbLK p M L := by
  refine ⟨h', hL.fin, ?_⟩
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  have h1 : ⁅resGK h g₁, resGK h g₂⁆ ∈ subG p K L :=
    hL.comm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  rw [← map_commutatorElement] at h1
  exact h1

theorem resChar_eq_zero (h : K ≤ L) (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) : resChar h χ = 0 := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro s
  exact hχ (resGK h (Additive.toMul s)) ((range_resGK h).le ⟨_, rfl⟩)

theorem local_pairing_eq_zero_of_mem_normGroup (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (a : Kˣ)
    (ha : a ∈ normGrp p K L) (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) : pairK p K a χ = 0 := by
  obtain ⟨b, hb⟩ := (mem_normGrp_iff_exists a).1 ha
  rw [pairK_norm hK hL h b a hb χ, resChar_eq_zero h χ hχ, pairK_zero]

theorem index_normGrp_le_step (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (g : GK p K) (χ : charGrp (GK p K))
    (hχ : TrivOn p K L χ) (hg : χ.1 (Additive.ofMul g) ≠ 0) :
    ∃ M : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] M ∧ IsAbLK p M L ∧ degLK p M L < degLK p K L ∧
      degLK p K L = degLK p K M * degLK p M L ∧ (normGrp p K L).index ≤ (normGrp p M L).index * degLK p K M := by
  obtain ⟨M, hKM, hM, hMχ⟩ := exists_field_of_char hK χ
  have hn := normal_of_char χ hMχ
  obtain ⟨g₀, hg₀⟩ := cyclic_of_char hM χ hMχ
  have hML : M ≤ L := by
    have := (subG_le_iff (L' := L) hKM).1 fun s hs => (hMχ s).1 (hχ s hs)
    rwa [sup_eq_right.2 hL.le] at this
  have hdeg := degLK_mul hKM hML
  have h1 : degLK p K M ≠ 1 := fun h1 => by
    have : subG p K M = ⊤ := Subgroup.index_eq_one.1 h1
    exact hg ((hMχ g).2 (this ▸ Subgroup.mem_top g))
  have h2 : 1 < degLK p K M := lt_of_le_of_ne (degLK_pos hM) (Ne.symm h1)
  refine ⟨M, hM, hL.base hKM hML, ?_, hdeg, ?_⟩
  · rw [hdeg]
    exact lt_mul_of_one_lt_left (degLK_pos hL.fin) h2
  · rw [← index_normGrp_cyclic hK hM hKM g₀ hg₀]
    exact index_normGrp_tower_le hM hL.fin hKM hML

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Function

noncomputable section

theorem qz_mk_eq_zero_iff (q : ℚ) : (QuotientAddGroup.mk q : QZ) = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  rw [QuotientAddGroup.eq_zero_iff]; rfl

theorem qz_nsmul_mk (l : ℕ) (q : ℚ) : l • (QuotientAddGroup.mk q : QZ) = QuotientAddGroup.mk ((l : ℚ) * q) := by
  rw [← nsmul_eq_mul]; rfl

theorem qz_zsmul_mk (l : ℤ) (q : ℚ) : l • (QuotientAddGroup.mk q : QZ) = QuotientAddGroup.mk ((l : ℚ) * q) := by
  rw [← zsmul_eq_mul]; rfl

theorem qz_exists_zsmul (n : ℕ) (hn : n ≠ 0) (x : QZ) (hx : n • x = 0) :
    ∃ k : ℤ, x = k • (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [qz_nsmul_mk, qz_mk_eq_zero_iff] at hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  rw [qz_zsmul_mk, hk]
  have : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  congr 1
  field_simp

theorem qz_nsmul_inv_eq_zero_iff (n : ℕ) (hn : n ≠ 0) (l : ℕ) :
    l • (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) = 0 ↔ n ∣ l := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [qz_nsmul_mk, qz_mk_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    have h : ((k * n : ℤ) : ℚ) = ((l : ℤ) : ℚ) := by
      push_cast
      rw [hk]
      field_simp
    have h' : k * n = (l : ℤ) := Int.cast_injective h
    exact Int.natCast_dvd_natCast.1 ⟨k, by rw [← h', mul_comm]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    field_simp

scoped instance hasEnoughRootsOfUnity_QZ (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity (Multiplicative QZ) n where
  prim := ⟨Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n)),
    { pow_eq_one := by
        rw [← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]; rfl
      dvd_of_pow_eq_one := fun l hl => by
        rw [← ofAdd_nsmul] at hl
        exact (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) l).1 (Multiplicative.ofAdd.injective hl) }⟩
  cyc := by
    have h0 : (toUnits (Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ))) ∈
        rootsOfUnity n (Multiplicative QZ) := by
      rw [mem_rootsOfUnity, ← map_pow, ← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]
      exact map_one _
    refine ⟨⟨⟨_, h0⟩, fun x => ?_⟩⟩
    have hx : n • Multiplicative.toAdd (x.1 : Multiplicative QZ) = 0 := by
      have := x.2
      rw [mem_rootsOfUnity] at this
      have h2 := congrArg (fun u : (Multiplicative QZ)ˣ => Multiplicative.toAdd (u : Multiplicative QZ)) this
      simpa using h2
    obtain ⟨k, hk⟩ := qz_exists_zsmul n (NeZero.ne n) _ hx
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply Multiplicative.toAdd.injective
    rw [hk]
    simp

section fin

variable (A : Type) [AddCommGroup A] [Finite A]

def homEquivUnits : (A →+ QZ) ≃ (Multiplicative A →* (Multiplicative QZ)ˣ) :=
  AddMonoidHom.toMultiplicative.trans (toUnits (G := Multiplicative QZ)).monoidHomCongrRight.toEquiv

theorem homEquivUnits_apply (χ : A →+ QZ) (a : A) :
    Multiplicative.toAdd ((homEquivUnits A χ (Multiplicative.ofAdd a) : (Multiplicative QZ)ˣ) : Multiplicative QZ) = χ a := rfl

scoped instance : NeZero (Monoid.exponent (Multiplicative A)) := ⟨Monoid.exponent_ne_zero_of_finite⟩

theorem card_hom_QZ : Nat.card (A →+ QZ) = Nat.card A := by
  rw [Nat.card_congr (homEquivUnits A),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative A) (Multiplicative QZ)]
  rfl

scoped instance finite_hom_QZ : Finite (A →+ QZ) :=
  Nat.finite_of_card_ne_zero (by rw [card_hom_QZ]; exact Nat.card_pos.ne')

variable {A}

theorem exists_hom_QZ_ne_zero {a : A} (ha : a ≠ 0) : ∃ χ : A →+ QZ, χ a ≠ 0 := by
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative A) (Multiplicative QZ)
    (a := Multiplicative.ofAdd a) (fun h => ha (Multiplicative.ofAdd.injective h))
  refine ⟨(homEquivUnits A).symm φ, fun h => hφ ?_⟩
  rw [← homEquivUnits_apply, Equiv.apply_symm_apply] at h
  exact Units.ext (Multiplicative.toAdd.injective h)

theorem exists_eval_QZ (f : (A →+ QZ) →+ QZ) : ∃ a : A, ∀ χ : A →+ QZ, χ a = f χ := by
  let ev : A →+ ((A →+ QZ) →+ QZ) := AddMonoidHom.flip (AddMonoidHom.id (A →+ QZ))
  have hinj : Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    obtain ⟨χ, hχ⟩ := exists_hom_QZ_ne_zero h
    exact hχ (DFunLike.congr_fun ha χ)
  have hbij : Bijective ev := hinj.bijective_of_nat_card_le (by rw [card_hom_QZ, card_hom_QZ])
  obtain ⟨a, ha⟩ := hbij.2 f
  exact ⟨a, fun χ => DFunLike.congr_fun ha χ⟩

end fin

section top

variable {G : Type} [Group G] [TopologicalSpace G] {A : Type} [AddCommGroup A] (π : Additive G →+ A)
  (hc : IsLocallyConstant fun g : G => π (Additive.ofMul g))

def pullChar : (A →+ QZ) →+ charGrp G where
  toFun ψ := ⟨ψ.comp π, hc.comp ψ⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pullChar_apply (ψ : A →+ QZ) (g : G) : (pullChar π hc ψ).1 (Additive.ofMul g) = ψ (π (Additive.ofMul g)) := rfl

variable {π}

theorem pullChar_injective (hπ : Surjective π) : Injective (pullChar π hc) := by
  intro ψ ψ' h
  ext a
  obtain ⟨g, rfl⟩ := hπ a
  exact DFunLike.congr_fun (congrArg Subtype.val h) g

theorem exists_pullChar_eq (hπ : Surjective π) (χ : charGrp G)
    (h : ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) : ∃ ψ, pullChar π hc ψ = χ := by
  refine ⟨π.liftOfSurjective hπ ⟨χ.1, fun g hg => h (Additive.toMul g) hg⟩, Subtype.ext ?_⟩
  exact AddMonoidHom.liftOfRightInverse_comp _ _ _ _

include hc

theorem exists_character_ne_zero_of_quotient [Finite A] (g : G) (hg : π (Additive.ofMul g) ≠ 0) :
    ∃ χ : charGrp G, (∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) ∧ χ.1 (Additive.ofMul g) ≠ 0 := by
  obtain ⟨ψ, hψ⟩ := exists_hom_QZ_ne_zero hg
  exact ⟨pullChar π hc ψ, fun g hg => by rw [pullChar_apply, hg, map_zero], hψ⟩

theorem card_characters_of_finite_quotient [Finite A] (hπ : Surjective π) :
    Nat.card {χ : charGrp G // ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0} = Nat.card A := by
  rw [← card_hom_QZ A]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun ψ : A →+ QZ => (⟨pullChar π hc ψ, fun g hg => by rw [pullChar_apply, hg, map_zero]⟩ :
      {χ : charGrp G // ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0})) ⟨?_, ?_⟩)).symm
  · intro ψ ψ' h
    exact pullChar_injective hc hπ (congrArg Subtype.val h)
  · rintro ⟨χ, hχ⟩
    obtain ⟨ψ, hψ⟩ := exists_pullChar_eq hc hπ χ hχ
    exact ⟨ψ, Subtype.ext hψ⟩

theorem exists_element_evaluating_characters [Finite A] (hπ : Surjective π) (f : charGrp G →+ QZ) :
    ∃ g : G, ∀ χ : charGrp G, (∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) →
      χ.1 (Additive.ofMul g) = f χ := by
  obtain ⟨a, ha⟩ := exists_eval_QZ (f.comp (pullChar π hc))
  obtain ⟨g, rfl⟩ := hπ a
  refine ⟨Additive.toMul g, fun χ hχ => ?_⟩
  obtain ⟨ψ, rfl⟩ := exists_pullChar_eq hc hπ χ hχ
  exact ha ψ

end top

section quot

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]

abbrev quotAddCommGroup (h : commutator G ≤ H) : AddCommGroup (Additive (G ⧸ H)) :=
  { (inferInstance : AddGroup (Additive (G ⧸ H))) with
    add_comm := fun a b => by
      have := (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := H)).2 h
      exact congrArg Additive.ofMul (this.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }

end quot

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem TrivOn.of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') {χ : charGrp (GK p K)} (hχ : TrivOn p K L χ) : TrivOn p K L' χ :=
  fun g hg => hχ g fun x hx => hg x (h hx)

theorem IsRecip.of_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') {a : Kˣ} {g : GK p K} (hg : IsRecip p K L' a g) :
    IsRecip p K L a g := fun χ hχ => hg χ (hχ.of_le h)

theorem IsRecip.mul {a b : Kˣ} {g g' : GK p K} (h : IsRecip p K L a g) (h' : IsRecip p K L b g') :
    IsRecip p K L (a * b) (g * g') := fun χ hχ => by
  rw [pairK_mul, ← h χ hχ, ← h' χ hχ, ofMul_mul, map_add]

theorem IsRecip.congr {a : Kˣ} {g g' : GK p K} (h : IsRecip p K L a g) (hg : g⁻¹ * g' ∈ subG p K L) :
    IsRecip p K L a g' := fun χ hχ => by
  rw [← h χ hχ, show g' = g * (g⁻¹ * g') by group, ofMul_mul, map_add, hχ _ hg, add_zero]

theorem exists_quot_data (hL : IsAbLK p K L) : ∃ (A : Type) (_ : AddCommGroup A) (_ : Finite A) (π : Additive (GK p K) →+ A),
    Surjective π ∧ (IsLocallyConstant fun g : GK p K => π (Additive.ofMul g)) ∧ Nat.card A = degLK p K L ∧
    ∀ g : GK p K, π (Additive.ofMul g) = 0 ↔ g ∈ subG p K L := by
  have := hL.normal
  have := discreteTopology_GalLK (K := K) hL.fin
  refine ⟨Additive (GalLK p K L), quotAddCommGroup (subG p K L) hL.comm,
    finite_GalLK (K := K) hL.fin, MonoidHom.toAdditive (QuotientGroup.mk' (subG p K L)), ?_, ?_, ?_, ?_⟩
  · exact fun x => (QuotientGroup.mk'_surjective (subG p K L) (Additive.toMul x)).imp fun g hg => congrArg Additive.ofMul hg
  · exact (IsLocallyConstant.of_discrete (fun x : GalLK p K L => Additive.ofMul x)).comp_continuous
      QuotientGroup.continuous_mk
  · rfl
  · intro g
    exact QuotientGroup.eq_one_iff g

theorem exists_char_ne_zero (hL : IsAbLK p K L) (g : GK p K) (hg : g ∉ subG p K L) :
    ∃ χ : charGrp (GK p K), TrivOn p K L χ ∧ χ.1 (Additive.ofMul g) ≠ 0 := by
  obtain ⟨A, _, _, π, hπ, hc, -, hker⟩ := exists_quot_data hL
  obtain ⟨χ, h1, h2⟩ := exists_character_ne_zero_of_quotient hc g (fun h => hg ((hker g).1 h))
  exact ⟨χ, fun g hg => h1 g ((hker g).2 hg), h2⟩

theorem card_trivOn (hL : IsAbLK p K L) :
    Nat.card {χ : charGrp (GK p K) // TrivOn p K L χ} = degLK p K L := by
  obtain ⟨A, _, _, π, hπ, hc, hcard, hker⟩ := exists_quot_data hL
  rw [← hcard, ← card_characters_of_finite_quotient hc hπ]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun χ =>
    ⟨fun h g hg => h g ((hker g).1 hg), fun h g hg => h g ((hker g).2 hg)⟩)

theorem exists_eval (hL : IsAbLK p K L) (f : charGrp (GK p K) →+ QZ) :
    ∃ g : GK p K, ∀ χ, TrivOn p K L χ → χ.1 (Additive.ofMul g) = f χ := by
  obtain ⟨A, _, _, π, hπ, hc, -, hker⟩ := exists_quot_data hL
  obtain ⟨g, hg⟩ := exists_element_evaluating_characters hc hπ f
  exact ⟨g, fun χ hχ => hg χ fun g hg => hχ g ((hker g).1 hg)⟩

theorem IsRecip.unique (hL : IsAbLK p K L) {a : Kˣ} {g g' : GK p K} (h : IsRecip p K L a g)
    (h' : IsRecip p K L a g') : g⁻¹ * g' ∈ subG p K L := by
  by_contra hn
  obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL _ hn
  apply hne
  rw [ofMul_mul, map_add, ofMul_inv, map_neg, h χ hχ, h' χ hχ, neg_add_cancel]

theorem exists_isRecip (hL : IsAbLK p K L) (a : Kˣ) : ∃ g : GK p K, IsRecip p K L a g :=
  exists_eval hL
    { toFun := fun χ => pairK p K a χ
      map_zero' := pairK_zero a
      map_add' := pairK_add a }

theorem index_normGrp_le (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) :
    (normGrp p K L).index ≠ 0 ∧ (normGrp p K L).index ≤ degLK p K L := by
  refine ⟨(finiteIndex_normGrp hK hL.fin hL.le).index_ne_zero, ?_⟩
  induction hn : degLK p K L using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    by_cases hall : ∀ g : GK p K, g ∈ subG p K L
    · have h1 : L ≤ K := by
        have := (subG_le_iff (L' := K) hL.le).1 fun s _ => hall s
        rwa [sup_idem] at this
      have h2 : L = K := le_antisymm h1 hL.le
      rw [h2, normGrp_self, Subgroup.index_top]
      exact hn ▸ degLK_pos hL.fin
    · push Not at hall
      obtain ⟨g, hg⟩ := hall
      obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL g hg
      obtain ⟨M, hM, hML, hlt, hdeg, hle⟩ := index_normGrp_le_step hK hL g χ hχ hne
      have h3 := ih _ (hn ▸ hlt) hM hML rfl
      calc (normGrp p K L).index ≤ (normGrp p M L).index * degLK p K M := hle
        _ ≤ degLK p M L * degLK p K M := Nat.mul_le_mul_right _ h3
        _ = n := by rw [← hn, hdeg, mul_comm]

theorem pairK_eq_zero_of_mem_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (a : Kˣ) (ha : a ∈ normGrp p K L)
    (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) : pairK p K a χ = 0 :=
  local_pairing_eq_zero_of_mem_normGroup hK hL.fin hL.le a ha χ hχ

theorem IsRecip.inv {a : Kˣ} {g : GK p K} (h : IsRecip p K L a g) : IsRecip p K L a⁻¹ g⁻¹ := fun χ hχ => by
  rw [pairK_inv, ← h χ hχ, ofMul_inv, map_neg]

theorem isRecip_one_of_mem {g : GK p K} (hg : g ∈ subG p K L) : IsRecip p K L 1 g := fun χ hχ => by
  rw [pairK_one, hχ g hg]

variable (p K L) in

def recipImage (H : Subgroup Kˣ) : Subgroup (GK p K) where
  carrier := {g | ∃ a ∈ H, IsRecip p K L a g}
  one_mem' := ⟨1, H.one_mem, isRecip_one_of_mem (subG p K L).one_mem⟩
  mul_mem' := fun ⟨a, ha, h⟩ ⟨b, hb, h'⟩ => ⟨a * b, H.mul_mem ha hb, h.mul h'⟩
  inv_mem' := fun ⟨a, ha, h⟩ => ⟨a⁻¹, H.inv_mem ha, h.inv⟩

theorem exists_field_recipImage (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (H : Subgroup Kˣ) :
    ∃ L₀ : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L₀ ∧ L₀ ≤ L ∧ subG p K L₀ = recipImage p K L H := by
  have hle : subG p K L ≤ recipImage p K L H := fun g hg => ⟨1, H.one_mem, isRecip_one_of_mem hg⟩
  obtain ⟨L₀, h0, -, he⟩ := exists_subG_eq_of_isOpen hK _ (Subgroup.isOpen_mono hle (isOpen_subG hL.fin))
  have h1 : L₀ ≤ L := by
    have := (subG_le_iff (L' := L) h0).1 (he ▸ hle)
    rwa [sup_eq_right.2 hL.le] at this
  exact ⟨L₀, hL.of_le h0 h1, h1, he⟩

theorem exists_isRecip_of_gal (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (g : GK p K) : ∃ a : Kˣ, IsRecip p K L a g := by
  obtain ⟨L₀, hL₀, hle, he⟩ := exists_field_recipImage hK hL ⊤
  by_contra hcon
  have hg : g ∉ subG p K L₀ := by
    rw [he]
    rintro ⟨a, -, ha⟩
    exact hcon ⟨a, ha⟩
  obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL₀ g hg
  have h0 : χ = 0 := eq_zero_of_pairK_eq_zero hK χ fun a => by
    obtain ⟨g', hg'⟩ := exists_isRecip hL a
    rw [← hg' χ (hχ.of_le hle)]
    exact hχ g' (he ▸ ⟨a, trivial, hg'⟩)
  exact hne (by rw [h0]; rfl)

theorem exists_recipHom (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) [(subG p K L).Normal] :
    ∃ φ : Kˣ →* GalLK p K L, Surjective φ ∧ ∀ a g, IsRecip p K L a g ↔ φ a = QuotientGroup.mk g := by
  choose γ hγ using fun a => exists_isRecip hL a
  refine ⟨MonoidHom.mk' (fun a => QuotientGroup.mk (γ a)) (fun a b => ?_), ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul]
    exact QuotientGroup.eq.2 (IsRecip.unique hL (hγ _) ((hγ a).mul (hγ b)))
  · intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨a, ha⟩ := exists_isRecip_of_gal hK hL g
      exact ⟨a, QuotientGroup.eq.2 (IsRecip.unique hL (hγ a) ha)⟩
  · intro a g
    constructor
    · intro h
      exact QuotientGroup.eq.2 (IsRecip.unique hL (hγ a) h)
    · intro h
      exact (hγ a).congr (QuotientGroup.eq.1 h)

theorem IsRecip.mem_subG_of_mem_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) {a : Kˣ} {g : GK p K}
    (h : IsRecip p K L a g) (ha : a ∈ normGrp p K L) : g ∈ subG p K L := by
  by_contra hg
  obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL g hg
  exact hne ((h χ hχ).trans (pairK_eq_zero_of_mem_normGrp hK hL a ha χ hχ))

theorem recipHom_ker (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) [(subG p K L).Normal] (φ : Kˣ →* GalLK p K L)
    (hs : Surjective φ) (hφ : ∀ a g, IsRecip p K L a g ↔ φ a = QuotientGroup.mk g) :
    φ.ker = normGrp p K L ∧ (normGrp p K L).index = degLK p K L := by
  have hle : normGrp p K L ≤ φ.ker := fun a ha => by
    obtain ⟨g, hg⟩ := exists_isRecip hL a
    rw [MonoidHom.mem_ker, (hφ a g).1 hg]
    exact (QuotientGroup.eq_one_iff g).2 (hg.mem_subG_of_mem_normGrp hK hL ha)
  have hk : φ.ker.index = degLK p K L := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top]
    rfl
  obtain ⟨h0, h1⟩ := index_normGrp_le hK hL
  have h2 : (normGrp p K L).index = degLK p K L :=
    le_antisymm h1 (hk ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Subgroup.index_dvd_of_le hle))
  refine ⟨le_antisymm ?_ hle, h2⟩
  have h3 := Subgroup.relIndex_mul_index hle
  rw [hk, h2] at h3
  have h4 : (normGrp p K L).relIndex φ.ker = 1 :=
    Nat.eq_of_mul_eq_mul_right (degLK_pos hL.fin) (by rw [h3, one_mul])
  exact Subgroup.relIndex_eq_one.1 h4

theorem IsRecip.mem_subG_iff (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) {a : Kˣ} {g : GK p K} (h : IsRecip p K L a g) :
    g ∈ subG p K L ↔ a ∈ normGrp p K L := by
  have := hL.normal
  obtain ⟨φ, hs, hφ⟩ := exists_recipHom hK hL
  rw [← (recipHom_ker hK hL φ hs hφ).1, MonoidHom.mem_ker, (hφ a g).1 h]
  exact (QuotientGroup.eq_one_iff g).symm

theorem index_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) : (normGrp p K L).index = degLK p K L := by
  have := hL.normal
  obtain ⟨φ, hs, hφ⟩ := exists_recipHom hK hL
  exact (recipHom_ker hK hL φ hs hφ).2

theorem normGrp_sup (hK : FiniteDimensional ℚ_[p] K) {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : IsAbLK p K L) (hL' : IsAbLK p K L') :
    normGrp p K (L ⊔ L') = normGrp p K L ⊓ normGrp p K L' := by
  ext a
  obtain ⟨g, hg⟩ := exists_isRecip (hL.sup hL') a
  rw [Subgroup.mem_inf, ← hg.mem_subG_iff hK (hL.sup hL'), ← (hg.of_le le_sup_left).mem_subG_iff hK hL,
    ← (hg.of_le le_sup_right).mem_subG_iff hK hL', subG_sup_eq_inf, Subgroup.mem_inf]

theorem normGrp_le_iff (hK : FiniteDimensional ℚ_[p] K) {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : IsAbLK p K L) (hL' : IsAbLK p K L') :
    normGrp p K L' ≤ normGrp p K L ↔ L ≤ L' := by
  refine ⟨fun h => ?_, fun h => normGrp_anti hL'.fin hL.le h⟩
  have h1 : normGrp p K (L ⊔ L') = normGrp p K L' := by rw [normGrp_sup hK hL hL', inf_eq_right.2 h]
  have h2 : degLK p K (L ⊔ L') = degLK p K L' := by
    rw [← index_normGrp hK (hL.sup hL'), ← index_normGrp hK hL', h1]
  have hle : subG p K (L ⊔ L') ≤ subG p K L' := subG_anti le_sup_right
  have h3 := Subgroup.relIndex_mul_index hle
  have h4 : (subG p K (L ⊔ L')).relIndex (subG p K L') = 1 :=
    Nat.eq_of_mul_eq_mul_right (degLK_pos (K := K) hL'.fin) (by rw [one_mul]; exact h3.trans h2)
  have h5 : subG p K L' ≤ subG p K L := (Subgroup.relIndex_eq_one.1 h4).trans (subG_anti le_sup_left)
  have := (subG_le_iff hL.le).1 h5
  rwa [sup_eq_right.2 hL'.le] at this

theorem exists_normGrp_eq_of_le (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (H : Subgroup Kˣ) (hH : normGrp p K L ≤ H) :
    ∃ L₀ : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L₀ ∧ L₀ ≤ L ∧ normGrp p K L₀ = H := by
  obtain ⟨L₀, hL₀, hle, he⟩ := exists_field_recipImage hK hL H
  refine ⟨L₀, hL₀, hle, ?_⟩
  ext a
  obtain ⟨g, hg⟩ := exists_isRecip hL a
  rw [← (hg.of_le hle).mem_subG_iff hK hL₀, he]
  constructor
  · rintro ⟨a', ha', hg'⟩
    have h1 : IsRecip p K L (a * a'⁻¹) 1 := by
      have := hg.mul hg'.inv
      rwa [mul_inv_cancel] at this
    have h2 : a * a'⁻¹ ∈ H := hH ((h1.mem_subG_iff hK hL).1 (subG p K L).one_mem)
    have := H.mul_mem h2 ha'
    rwa [inv_mul_cancel_right] at this
  · intro ha
    exact ⟨a, ha, hg⟩

theorem isRecip_uniformiser_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (π : Kˣ) (hπ : vK p K π = 1) :
    IsRecip p K (Kn p K n) π (frobK p K) := fun χ hχ =>
  (pairK_uniformiser_unr hK π hπ χ (hχ.of_le (Kn_le_Kur hn))).symm

theorem IsRecip.norm (hK : FiniteDimensional ℚ_[p] K) {M E : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : FiniteDimensional ℚ_[p] M) (h : K ≤ M) (hE : E ≤ L) {b : Mˣ} {a : Kˣ}
    (ha : ofK p K (Additive.ofMul a) = normHom p K M (ofK p M (Additive.ofMul b))) {g : GK p M}
    (hg : IsRecip p M L b g) : IsRecip p K E a (resGK h g) := fun χ hχ => by
  rw [pairK_norm hK hM h b a ha χ]
  exact hg (resChar h χ) fun s hs => hχ (resGK h s) fun x hx => hs x (hE hx)

theorem stable_inv_of_stable {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : FiniteDimensional ℚ_[p] M) (σ : GK p K)
    (h : ∀ x ∈ M, σ x ∈ M) : ∀ x ∈ M, σ⁻¹ x ∈ M := by
  let f : M →ₐ[ℚ_[p]] M := AlgHom.codRestrict
    (((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp M.val)
    M.toSubalgebra (fun x => h x.1 x.2)
  have hf := Algebra.IsAlgebraic.algHom_bijective f
  intro x hx
  obtain ⟨y, hy⟩ := hf.2 ⟨x, hx⟩
  have h1 : σ y.1 = x := congrArg Subtype.val hy
  rw [← h1]
  show (σ⁻¹ * σ) y.1 ∈ M
  rw [inv_mul_cancel]
  exact y.2

theorem exists_conjGK {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : FiniteDimensional ℚ_[p] M) (h : K ≤ M) (σ : GK p K)
    (hσ : ∀ x ∈ M, σ x ∈ M) :
    ∃ c : GK p M →* GK p M, Continuous c ∧ ∀ g, resGK h (c g) = σ * resGK h g * σ⁻¹ := by
  have hinv := stable_inv_of_stable hM σ hσ
  have hex : ∀ g : GK p M, ∃ g' : GK p M, resGK h g' = σ * resGK h g * σ⁻¹ := fun g => by
    have : σ * resGK h g * σ⁻¹ ∈ (resGK h).range := by
      rw [range_resGK h]
      intro x hx
      show σ (g (σ⁻¹ x)) = x
      rw [show g (σ⁻¹ x) = σ⁻¹ x from g.commutes ⟨_, hinv x hx⟩]
      show (σ * σ⁻¹) x = x
      rw [mul_inv_cancel]; rfl
    exact this
  choose c hc using hex
  refine ⟨MonoidHom.mk' c fun a b => resGK_injective h ?_, ?_, hc⟩
  · rw [map_mul, hc, hc, hc, map_mul]; group
  · rw [(isClosedEmbedding_resGK h).isInducing.continuous_iff]
    have : (resGK h ∘ (MonoidHom.mk' c fun a b => resGK_injective h (by rw [map_mul, hc, hc, hc, map_mul]; group))) =
        fun g => σ * resGK h g * σ⁻¹ := funext hc
    rw [this]
    exact (continuous_const.mul (resGK_continuous h)).mul continuous_const

theorem IsRecip.conj (hK : FiniteDimensional ℚ_[p] K) {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : FiniteDimensional ℚ_[p] M) (h : K ≤ M) (σ : GK p K)
    (hM : ∀ x ∈ M, σ x ∈ M) (hL : ∀ x ∈ L, σ x ∈ L) (hL' : ∀ x ∈ L, σ⁻¹ x ∈ L) {b b' : Mˣ} (hb : ((b' : M) : PadicAlgCl p) = σ ((b : M) : PadicAlgCl p))
    {g g' : GK p M} (hg' : resGK h g' = σ * resGK h g * σ⁻¹) (hg : IsRecip p M L b g) :
    IsRecip p M L b' g' := by
  have hfd : FiniteDimensional ℚ_[p] M := by assumption
  obtain ⟨c, hcc, hc⟩ := exists_conjGK hfd h σ hM
  intro χ' hχ'
  let χ : charGrp (GK p M) := ⟨χ'.1.comp (MonoidHom.toAdditive c),
    (show IsLocallyConstant fun g : GK p M => χ'.1 (Additive.ofMul g) from χ'.2).comp_continuous hcc⟩
  have hχ : ∀ s s' : GK p M, resGK h s' = σ * resGK h s * σ⁻¹ →
      χ'.1 (Additive.ofMul s') = χ.1 (Additive.ofMul s) := fun s s' hs => by
    rw [resGK_injective h (hs.trans (hc s).symm)]; rfl
  have htriv : TrivOn p M L χ := fun s hs => by
    refine hχ' (c s) fun x hx => ?_
    show resGK h (c s) x = x
    rw [hc]
    show σ (s (σ⁻¹ x)) = x
    rw [hs _ (hL' x hx)]
    show (σ * σ⁻¹) x = x
    rw [mul_inv_cancel]; rfl
  rw [pairK_conj hK hfd h σ hM b b' hb χ χ' hχ, ← hg χ htriv]
  exact hχ g g' hg'

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function
open scoped commutatorElement

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_maxAb (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] :
    ∃ E : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K E ∧ E ≤ L ∧ subG p K E = subG p K L ⊔ commutator (GK p K) := by
  have hK : FiniteDimensional ℚ_[p] K := finDim_of_le p hL h
  obtain ⟨E, hKE, hE, hEU⟩ := exists_subG_eq_of_isOpen hK (subG p K L ⊔ commutator (GK p K))
    (Subgroup.isOpen_mono le_sup_left (isOpen_subG hL))
  refine ⟨E, ⟨hKE, hE, hEU ▸ le_sup_right⟩, ?_, hEU⟩
  have := (subG_le_iff (L := E) (L' := L) hKE).1 (hEU ▸ le_sup_left)
  rwa [sup_eq_right.2 h] at this

section grp

variable {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (s : G)

include hH in

theorem exists_twist_subgroup_nl : ∃ I : Subgroup G, ∀ x, x ∈ I ↔ ∃ h ∈ H, x = s * h * s⁻¹ * h⁻¹ := by
  have hc : ∀ a ∈ H, s * a * s⁻¹ ∈ H := fun a ha => Subgroup.Normal.conj_mem inferInstance a ha s
  refine ⟨{ carrier := {x | ∃ h ∈ H, x = s * h * s⁻¹ * h⁻¹}
            one_mem' := ⟨1, H.one_mem, by group⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * b, H.mul_mem ha hb, ?_⟩
    have h1 := hH a⁻¹ (H.inv_mem ha) (s * b * s⁻¹ * b⁻¹) (H.mul_mem (hc b hb) (H.inv_mem hb))
    calc s * a * s⁻¹ * a⁻¹ * (s * b * s⁻¹ * b⁻¹) = s * a * s⁻¹ * (a⁻¹ * (s * b * s⁻¹ * b⁻¹)) := by group
      _ = s * a * s⁻¹ * ((s * b * s⁻¹ * b⁻¹) * a⁻¹) := by rw [h1]
      _ = _ := by group
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, H.inv_mem ha, ?_⟩
    have h1 := hH a ha (s * a⁻¹ * s⁻¹) (hc _ (H.inv_mem ha))
    calc (s * a * s⁻¹ * a⁻¹)⁻¹ = a * (s * a⁻¹ * s⁻¹) := by group
      _ = _ := by rw [h1]; group

end grp

theorem exists_of_mem_commutator {G : Type*} [Group G] (H : Subgroup G) [H.Normal] (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (s : G) (hs : ∀ g : G, ∃ (k : ℤ), g * s ^ k ∈ H) (x : G) (hx : x ∈ commutator G) :
    ∃ h ∈ H, x = s * h * s⁻¹ * h⁻¹ := by
  obtain ⟨I, hI⟩ := exists_twist_subgroup_nl H hH s
  rw [← hI]
  have hc : ∀ (g : G), ∀ a ∈ H, g * a * g⁻¹ ∈ H := fun g a ha => Subgroup.Normal.conj_mem inferInstance a ha g
  have key : ∀ (i : ℤ), ∀ h ∈ H, s ^ i * h * (s ^ i)⁻¹ * h⁻¹ ∈ I := by
    intro i
    induction i using Int.induction_on with
    | zero => intro h _; simp
    | succ i ih =>
      intro h hh
      have h1 : s * (s ^ (i : ℤ) * h * (s ^ (i : ℤ))⁻¹) * s⁻¹ * (s ^ (i : ℤ) * h * (s ^ (i : ℤ))⁻¹)⁻¹ ∈ I :=
        (hI _).2 ⟨_, hc _ h hh, rfl⟩
      have := I.mul_mem h1 (ih h hh)
      convert this using 1
      rw [zpow_add_one]
      have : s ^ (i : ℤ) * s = s * s ^ (i : ℤ) := by rw [← zpow_add_one, ← zpow_one_add, add_comm]
      rw [this]
      group
    | pred i ih =>
      intro h hh
      have h1 : s * (s ^ (-(i : ℤ) - 1) * h * (s ^ (-(i : ℤ) - 1))⁻¹) * s⁻¹ *
          (s ^ (-(i : ℤ) - 1) * h * (s ^ (-(i : ℤ) - 1))⁻¹)⁻¹ ∈ I :=
        (hI _).2 ⟨_, hc _ h hh, rfl⟩
      have := I.mul_mem (I.inv_mem h1) (ih h hh)
      convert this using 1
      have e : s ^ (-(i : ℤ)) = s * s ^ (-(i : ℤ) - 1) := by rw [← zpow_one_add]; congr 1; ring
      rw [e]
      group
  have hle : commutator G ≤ I := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨i, hi⟩ := hs a
    obtain ⟨j, hj⟩ := hs b
    set u := a * s ^ i with hu
    set v := b * s ^ j with hv
    have ea : a = u * s ^ (-i) := by rw [hu, zpow_neg]; group
    have eb : b = v * s ^ (-j) := by rw [hv, zpow_neg]; group
    have k1 := key (-i) v hj
    have k2 := I.inv_mem (key (-j) u hi)
    have := I.mul_mem k1 k2
    convert this using 1
    have c1 := hH u hi (s ^ (-i) * v * (s ^ (-i))⁻¹ * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * v⁻¹)
      (H.mul_mem (H.mul_mem (hc _ v hj) (hc _ _ (H.inv_mem hi))) (H.inv_mem hj))
    have c2 := hH (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) (hc _ _ (H.inv_mem hi)) (v⁻¹ * u) (H.mul_mem (H.inv_mem hj) hi)
    calc ⁅a, b⁆ = u * (s ^ (-i) * v * (s ^ (-i))⁻¹ * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * v⁻¹) := by
          rw [commutatorElement_def, ea, eb]; group
      _ = (s ^ (-i) * v * (s ^ (-i))⁻¹ * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * v⁻¹) * u := c1
      _ = s ^ (-i) * v * (s ^ (-i))⁻¹ * ((s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹) * (v⁻¹ * u)) := by group
      _ = s ^ (-i) * v * (s ^ (-i))⁻¹ * ((v⁻¹ * u) * (s ^ (-j) * u⁻¹ * (s ^ (-j))⁻¹)) := by rw [c2]
      _ = _ := by group
  exact hle hx

theorem exists_ofK_eq_nl (x : KbarMult p) (hx : x ∈ multOf p K) : ∃ a : Kˣ, ofK p K (Additive.ofMul a) = x := by
  have hne : (⟨((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p), hx⟩ : K) ≠ 0 := fun h =>
    (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h)
  refine ⟨Units.mk0 _ hne, ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem normHom_kbarRep_nl (hL : FiniteDimensional ℚ_[p] L) [(subG p K L).Normal] (σ : GK p K) (y : KbarMult p)
    (hy : y ∈ multOf p L) : normHom p K L (kbarRep p K σ y) = normHom p K L y := by
  have : Finite (GK p K ⧸ subG p K L) := finite_GalLK hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  rw [normHom_apply, normHom_apply]
  calc ∑ c : GK p K ⧸ subG p K L, kbarRep p K c.out (kbarRep p K σ y)
      = ∑ c : GalLK p K L, kbarRep p K ((Equiv.mulRight (QuotientGroup.mk σ : GalLK p K L)) c).out y := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← kbarRep_mul, ← kbarRep_out y hy (c.out * σ)]
        congr 3
        rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
        rfl
    _ = _ := Equiv.sum_comp _ (fun c : GalLK p K L => kbarRep p K c.out y)

theorem normGrp_le_of_tower_nl {M L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : FiniteDimensional ℚ_[p] L)
    (hL' : FiniteDimensional ℚ_[p] L') (hKM : K ≤ M) (hML : M ≤ L) (hML' : M ≤ L')
    (h : normGrp p M L ≤ normGrp p M L') : normGrp p K L ≤ normGrp p K L' := by
  intro a ha
  obtain ⟨y, hy, hya⟩ := (mem_normGrp_iff p K L a).1 ha
  obtain ⟨b, hb⟩ := exists_ofK_eq_nl _ (normHom_mem hL hML y hy)
  obtain ⟨y', hy', hyb⟩ := (mem_normGrp_iff p M L' b).1 (h ((mem_normGrp_iff p M L b).2 ⟨y, hy, hb.symm⟩))
  refine (mem_normGrp_iff p K L' a).2 ⟨y', hy', ?_⟩
  rw [← normHom_trans hL' hKM hML' y' hy', hyb, hb, normHom_trans hL hKM hML y hy, hya]

theorem map_resGK_subG_nl {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ M) (h' : M ≤ L) :
    (subG p M L).map (resGK h) = subG p K L := by
  rw [← comap_resGK_subG h L, Subgroup.map_comap_eq, range_resGK, inf_eq_right]
  exact subG_anti h'

theorem exists_twist_nl {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKM : K ≤ M) [(subG p K M).Normal]
    [(subG p K L).Normal] (σ : GK p K)
    (hσ : ∀ g : GalLK p K M, g ∈ Subgroup.zpowers (QuotientGroup.mk σ : GalLK p K M))
    (hcomm : commutator (GK p M) ≤ subG p M L) (g : GK p K) (hg : g ∈ subG p K L ⊔ commutator (GK p K)) :
    ∃ h' : GK p M, g⁻¹ * (σ * resGK hKM h' * σ⁻¹ * (resGK hKM h')⁻¹) ∈ subG p K L := by
  let π : GK p K →* GalLK p K L := QuotientGroup.mk' (subG p K L)
  have hπ : Surjective π := QuotientGroup.mk'_surjective _
  let H : Subgroup (GalLK p K L) := (subG p K M).map π
  have : H.Normal := Subgroup.Normal.map inferInstance π hπ
  have hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, ← range_resGK hKM] at ha hb
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    have h1 : ⁅a, b⁆ ∈ subG p M L :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have h2 : ⁅resGK hKM a, resGK hKM b⁆ ∈ subG p K L := by
      rw [← map_commutatorElement]; exact h1
    have h3 : π ⁅resGK hKM a, resGK hKM b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h2
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  have hs : ∀ x : GalLK p K L, ∃ k : ℤ, x * (π σ) ^ k ∈ H := by
    intro x
    obtain ⟨x, rfl⟩ := hπ x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ (QuotientGroup.mk x))
    refine ⟨-k, x * σ ^ (-k), ?_, by rw [map_mul, map_zpow]⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, ← hk, zpow_neg,
      mul_inv_cancel]
  have hx : π g ∈ commutator (GalLK p K L) := by
    have h1 : π g ∈ (subG p K L ⊔ commutator (GK p K)).map π := Subgroup.mem_map_of_mem _ hg
    have e : (subG p K L).map π = ⊥ := (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge
    rwa [Subgroup.map_sup, e, bot_sup_eq, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 hπ, ← commutator_def] at h1
  obtain ⟨_, ⟨h0, hh0, rfl⟩, hx'⟩ := exists_of_mem_commutator H hH (π σ) hs (π g) hx
  rw [SetLike.mem_coe, ← range_resGK hKM] at hh0
  obtain ⟨h', rfl⟩ := hh0
  refine ⟨h', ?_⟩
  rw [← QuotientGroup.eq]
  exact hx'

theorem normGrp_eq_of_cyclic_of_ab (hK : FiniteDimensional ℚ_[p] K) {M E : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKM : K ≤ M) [(subG p K M).Normal] (σ : GK p K)
    (hσ : ∀ g : GalLK p K M, g ∈ Subgroup.zpowers (QuotientGroup.mk σ : GalLK p K M)) (hL : IsAbLK p M L)
    [(subG p K L).Normal] (hE : IsAbLK p K E) (hEL : E ≤ L)
    (hE' : subG p K E = subG p K L ⊔ commutator (GK p K)) : normGrp p K L = normGrp p K E := by
  have hLf := hL.fin
  have hML := hL.le
  have hKL := hKM.trans hML
  have hM : FiniteDimensional ℚ_[p] M := finDim_of_le p hLf hML
  refine le_antisymm (normGrp_anti hLf hE.le hEL) fun a ha => ?_
  have hMab : IsAbLK p K M := isAbLK_of_cyclic hM hKM _ hσ
  have hME : M ≤ E := by
    have := (subG_le_iff (L := M) (L' := E) hKM).1 (by rw [hE']; exact sup_le (subG_anti hML) hMab.comm)
    rwa [sup_eq_right.2 hE.le] at this
  have hEab : IsAbLK p M E := hL.of_le hME hEL
  obtain ⟨y, hy, hya⟩ := (mem_normGrp_iff p K E a).1 ha
  obtain ⟨b, hb⟩ := exists_ofK_eq_nl _ (normHom_mem hE.fin hME y hy)
  have hbN : b ∈ normGrp p M E := (mem_normGrp_iff p M E b).2 ⟨y, hy, hb.symm⟩
  have hba : normHom p K M (ofK p M (Additive.ofMul b)) = ofK p K (Additive.ofMul a) := by
    rw [hb, normHom_trans hE.fin hKM hME y hy, hya]
  obtain ⟨g, hg⟩ := exists_isRecip hL b
  have hgE : g ∈ subG p M E := ((hg.of_le hEL).mem_subG_iff hM hEab).2 hbN
  have hgE' : resGK hKM g ∈ subG p K L ⊔ commutator (GK p K) := by
    rw [← hE']; exact hgE
  obtain ⟨h', hh'⟩ := exists_twist_nl hKM σ hσ hL.comm _ hgE'
  obtain ⟨c, hc⟩ := exists_isRecip_of_gal hM hL h'
  have stM := (subG_normal_iff hKM).1 inferInstance
  have stL := (subG_normal_iff hKL).1 inferInstance
  have hσc : kbarRep p K σ (ofK p M (Additive.ofMul c)) ∈ multOf p M := stM σ _ (ofK_mem p M _)
  obtain ⟨c', hc'⟩ := exists_ofK_eq_nl _ hσc
  obtain ⟨g', hg'⟩ : ∃ g' : GK p M, resGK hKM g' = σ * resGK hKM h' * σ⁻¹ := by
    have : σ * resGK hKM h' * σ⁻¹ ∈ (resGK hKM).range := by
      rw [range_resGK]
      exact Subgroup.Normal.conj_mem inferInstance _ (by rw [← range_resGK hKM]; exact ⟨_, rfl⟩) σ
    exact this
  have hc'' : IsRecip p M L c' g' := IsRecip.conj hK hM hKM σ (stM σ) (stL σ) (stL σ⁻¹) (b := c) (b' := c')
    (congrArg (fun z : KbarMult p => ((Additive.toMul z : (PadicAlgCl p)ˣ) : PadicAlgCl p)) hc') hg' hc
  have hd : IsRecip p M L (b⁻¹ * (c' * c⁻¹)) (g⁻¹ * (g' * h'⁻¹)) := hg.inv.mul (hc''.mul hc.inv)
  have hdm : g⁻¹ * (g' * h'⁻¹) ∈ subG p M L := by
    rw [← comap_resGK_subG hKM L, Subgroup.mem_comap]
    simp only [map_mul, map_inv, hg']
    exact hh'
  obtain ⟨l, hl, hld⟩ := (mem_normGrp_iff p M L _).1 ((hd.mem_subG_iff hM hL).1 hdm)
  refine (mem_normGrp_iff p K L a).2 ⟨-l, neg_mem hl, ?_⟩
  rw [map_neg, ← normHom_trans hLf hKM hML l hl, hld, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add, map_add,
    map_neg, map_neg, map_add, map_add, map_neg, map_neg, hc', normHom_kbarRep_nl hM σ _ (ofK_mem p M _), hba]
  abel

theorem exists_cyclic_quotient_nl {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ (H : Subgroup G) (s : G), H.Normal ∧ H ≠ ⊤ ∧ ∀ g : G, ∃ k : ℤ, (s ^ k)⁻¹ * g ∈ H := by
  obtain ⟨H, hH, hle⟩ := (eq_top_or_exists_le_coatom (commutator G)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne
  have hn : H.Normal := ⟨fun n hn g => by
    have h1 : ⁅g, n⁆ ∈ H := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have h2 := H.mul_mem h1 hn
    rwa [commutatorElement_def, inv_mul_cancel_right] at h2⟩
  obtain ⟨s, hs⟩ : ∃ s, s ∉ H := by
    by_contra hc
    push Not at hc
    exact hH.1 (eq_top_iff.2 fun x _ => hc x)
  refine ⟨H, s, hn, hH.1, ?_⟩
  let V : Subgroup G := (Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H)).comap (QuotientGroup.mk' H)
  have hlt : H < V := by
    refine lt_of_le_of_ne (fun x hx => ?_) fun h => hs (h ▸ (Subgroup.mem_zpowers _ : _ ∈ Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H)))
    show (QuotientGroup.mk x : G ⧸ H) ∈ Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H)
    rw [(QuotientGroup.eq_one_iff x).2 hx]
    exact Subgroup.one_mem _
  have hV : V = ⊤ := hH.2 V hlt
  intro g
  have hg : g ∈ V := hV ▸ Subgroup.mem_top g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (show (QuotientGroup.mk g : G ⧸ H) ∈ Subgroup.zpowers (QuotientGroup.mk s : G ⧸ H) from hg)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hk]

theorem normGrp_eq_of_soluble_nl (n : ℕ) : ∀ (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
    (_ : FiniteDimensional ℚ_[p] K) (_ : FiniteDimensional ℚ_[p] L) (_ : K ≤ L) [(subG p K L).Normal]
    (_ : Group.IsSolvable (GalLK p K L)) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : IsAbLK p K E) (_ : E ≤ L)
    (_ : subG p K E = subG p K L ⊔ commutator (GK p K)), degLK p K L = n → normGrp p K L = normGrp p K E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L hK hL h _ hsol E hE hEL hE' hn
  have : Finite (GalLK p K L) := finite_GalLK hL
  rcases subsingleton_or_nontrivial (GalLK p K L) with hss | hnt
  · have htop : subG p K L = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton _ hss
    have hLab : IsAbLK p K L := ⟨h, hL, by rw [htop]; exact le_top⟩
    have : (subG p K K).Normal := (isAbLK_self hK).normal
    have hσ : ∀ g : GalLK p K K, g ∈ Subgroup.zpowers (QuotientGroup.mk (1 : GK p K) : GalLK p K K) := by
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [(QuotientGroup.eq_one_iff g).2 (show g ∈ subG p K K from fun x hx => g.commutes ⟨x, hx⟩)]
        exact Subgroup.one_mem _
    exact normGrp_eq_of_cyclic_of_ab hK (le_refl K) 1 hσ hLab hE hEL hE'
  · obtain ⟨H, s, hHn, hHtop, hs⟩ := exists_cyclic_quotient_nl (G := GalLK p K L)
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective s
    let π : GK p K →* GalLK p K L := QuotientGroup.mk' (subG p K L)
    have hπ : Surjective π := QuotientGroup.mk'_surjective _
    have hUle : subG p K L ≤ H.comap π := fun x hx => by
      rw [Subgroup.mem_comap, show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
      exact H.one_mem
    obtain ⟨M, hKM, hM, hMU⟩ := exists_subG_eq_of_isOpen hK (H.comap π)
      (Subgroup.isOpen_mono hUle (isOpen_subG hL))
    have hML : M ≤ L := by
      have := (subG_le_iff (L := M) (L' := L) hKM).1 (hMU ▸ hUle)
      rwa [sup_eq_right.2 h] at this
    have hMn : (subG p K M).Normal := hMU ▸ hHn.comap π
    have hσ : ∀ g : GalLK p K M, g ∈ Subgroup.zpowers (QuotientGroup.mk σ : GalLK p K M) := by
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨k, hk⟩ := hs (π g)
        refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
        rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, hMU, Subgroup.mem_comap, map_mul, map_inv, map_zpow]
        exact hk
    have hlt : degLK p M L < n := by
      have h1 := degLK_mul hKM hML
      have h2 : degLK p K M ≠ 1 := by
        unfold degLK
        rw [hMU, Subgroup.index_comap_of_surjective _ hπ]
        exact fun h => hHtop (Subgroup.index_eq_one.1 h)
      have h3 := degLK_pos (K := K) hM
      have h4 := degLK_pos (K := M) hL
      rw [← hn, h1]
      exact lt_mul_of_one_lt_left h4 (by omega)
    have hMLn : (subG p M L).Normal := subG_normal_of_le hKM h inferInstance
    have hsolM : Group.IsSolvable (GalLK p M L) := by
      let f : GalLK p M L →* GalLK p K L := QuotientGroup.map _ _ (resGK hKM) (comap_resGK_subG hKM L).ge
      have hf : Injective f := by
        rw [injective_iff_map_eq_one]
        intro x
        induction x using QuotientGroup.induction_on with
        | H z =>
          intro hx
          exact (QuotientGroup.eq_one_iff _).2 ((QuotientGroup.eq_one_iff (resGK hKM z)).1 hx)
      exact Group.isSolvable_of_isSolvable_injective hf
    obtain ⟨E', hE'ab, hE'L, hE'U⟩ := exists_maxAb (K := M) hL hML
    have e1 : normGrp p M L = normGrp p M E' := ih _ hlt M L hM hL hML hsolM E' hE'ab hE'L hE'U rfl
    have hME' := hE'ab.le
    have e2 : normGrp p K L = normGrp p K E' :=
      le_antisymm (normGrp_le_of_tower_nl hL hE'ab.fin hKM hML hME' e1.le)
        (normGrp_le_of_tower_nl hE'ab.fin hL hKM hME' hML e1.ge)
    have e3 : subG p K E' = subG p K L ⊔ ⁅subG p K M, subG p K M⁆ := by
      rw [← map_resGK_subG_nl hKM hME', hE'U, Subgroup.map_sup, map_resGK_subG_nl hKM hML, commutator_def,
        Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_resGK]
    have hE'n : (subG p K E').Normal := by rw [e3]; infer_instance
    have e4 : subG p K E = subG p K E' ⊔ commutator (GK p K) := by
      rw [hE', e3, sup_assoc, commutator_def, sup_eq_right.2 (Subgroup.commutator_mono le_top le_top)]
    have hEE' : E ≤ E' := by
      have := (subG_le_iff (L := E) (L' := E') hE.le).1 (e4 ▸ le_sup_left)
      rwa [sup_eq_right.2 (hKM.trans hME')] at this
    rw [e2]
    exact normGrp_eq_of_cyclic_of_ab hK hKM σ hσ hE'ab hE hEE' e4

theorem normGrp_eq_of_soluble (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal]
    (hsol : Group.IsSolvable (GalLK p K L)) {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (hE : IsAbLK p K E) (hEL : E ≤ L)
    (hE' : subG p K E = subG p K L ⊔ commutator (GK p K)) : normGrp p K L = normGrp p K E :=
  normGrp_eq_of_soluble_nl _ K L hK hL h hsol E hE hEL hE' rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
