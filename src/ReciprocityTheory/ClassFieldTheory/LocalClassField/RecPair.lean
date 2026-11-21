import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem kbarT_rho_ofK (g : GK p K) (a : Additive Kˣ) : (kbarT p K).rho g (ofK p K a) = ofK p K a :=
  Units.ext (g.commutes _)

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_int_of_mk_eq {x y : ℚ} (h : (QuotientAddGroup.mk x : QZ) = QuotientAddGroup.mk y) :
    ∃ n : ℤ, (n : ℚ) = x - y := by
  have h0 : (QuotientAddGroup.mk (x - y) : QZ) = 0 := by
    rw [QuotientAddGroup.mk_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (QuotientAddGroup.eq_zero_iff _).1 h0
  exact ⟨n, hn⟩

theorem exists_defect (χ : Additive G →+ QZ) (t : G → ℚ)
    (ht : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ (Additive.ofMul g)) :
    ∃ m : (Fin 2 → G) → ℤ, ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
  have h : ∀ g : Fin 2 → G, ∃ n : ℤ, (n : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := fun g =>
    exists_int_of_mk_eq (by rw [QuotientAddGroup.mk_add, ht, ht, ht, ofMul_mul, map_add])
  choose m hm using h
  exact ⟨m, hm⟩

theorem defect_isLocallyConstant {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) : IsLocallyConstant m := by
  have h : IsLocallyConstant (fun g : Fin 2 → G => t (g 0) + t (g 1) - t (g 0 * g 1)) :=
    ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
      (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))
  refine IsLocallyConstant.desc m (fun n : ℤ => (n : ℚ)) ?_ Int.cast_injective
  have e : (fun n : ℤ => (n : ℚ)) ∘ m = fun g : Fin 2 → G => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
  rw [e]; exact h

theorem defect_cocycle {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (v : Fin 3 → G) :
    m ![v 1, v 2] - m ![v 0 * v 1, v 2] + m ![v 0, v 1 * v 2] - m ![v 0, v 1] = 0 := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, hm, hm, hm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
  ring

theorem trep_dn_one {R : Type} [CommRing R] (M : TRep R G) (f : (Fin 1 → G) → M.V) (v : Fin 2 → G) :
    ReciprocityTheory.Gal.dn M.rho 1 f v = M.rho (v 0) (f ![v 1]) - f ![v 0 * v 1] + f ![v 0] :=
  LowDeg.dn_one_apply M.rho f v

theorem trep_dn_two {R : Type} [CommRing R] (M : TRep R G) (f : (Fin 2 → G) → M.V) (v : Fin 3 → G) :
    ReciprocityTheory.Gal.dn M.rho 2 f v = M.rho (v 0) (f ![v 1, v 2]) - f ![v 0 * v 1, v 2] + f ![v 0, v 1 * v 2] -
      f ![v 0, v 1] :=
  LowDeg.dn_two_apply M.rho f v

variable (M : TRep ℤ G)

theorem exists_defect_cocycle {a : M.V} (ha : ∀ g, M.rho g a = a) {t : G → ℚ} (ht : IsLocallyConstant t)
    {m : (Fin 2 → G) → ℤ} (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) :
    ∃ (z : M.coch.X 2) (_ : M.coch.d 2 z = 0), ∀ g, z.1 g = m g • a := by
  refine ⟨⟨fun g => m g • a, ((defect_isLocallyConstant ht hm).comp (· • a)).continuous⟩, ?_, fun g => rfl⟩
  refine LowDeg.coch_d_eq_zero M (funext fun v => ?_)
  rw [trep_dn_two]
  show M.rho (v 0) (m ![v 1, v 2] • a) - m ![v 0 * v 1, v 2] • a + m ![v 0, v 1 * v 2] • a - m ![v 0, v 1] • a = 0
  rw [map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul, defect_cocycle hm, zero_smul]

theorem defect_cls_eq {a : M.V} (ha : ∀ g, M.rho g a = a) {t t' : G → ℚ} (ht : IsLocallyConstant t)
    (ht' : IsLocallyConstant t') (htt : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = QuotientAddGroup.mk (t' g))
    {m m' : (Fin 2 → G) → ℤ} (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1))
    (hm' : ∀ g, (m' g : ℚ) = t' (g 0) + t' (g 1) - t' (g 0 * g 1))
    {z z' : M.coch.X 2} (hz : M.coch.d 2 z = 0) (hz' : M.coch.d 2 z' = 0)
    (hzv : ∀ g, z.1 g = m g • a) (hzv' : ∀ g, z'.1 g = m' g • a) :
    M.coch.cls 2 z hz = M.coch.cls 2 z' hz' := by
  choose u hu using fun g => exists_int_of_mk_eq (htt g)
  have hul : IsLocallyConstant u := by
    refine IsLocallyConstant.desc u (fun n : ℤ => (n : ℚ)) ?_ Int.cast_injective
    have e : (fun n : ℤ => (n : ℚ)) ∘ u = fun g => t g - t' g := funext hu
    rw [e]; exact ht.sub ht'
  rw [Cx.cls_eq_iff]
  refine ⟨⟨fun g => u (g 0) • a,
    ((hul.comp_continuous (continuous_apply 0)).comp (· • a)).continuous⟩, Subtype.ext (funext fun v => ?_)⟩
  refine (trep_dn_one M (fun g => u (g 0) • a) v).trans ?_
  show M.rho (v 0) (u (v 1) • a) - u (v 0 * v 1) • a + u (v 0) • a = z.1 v - z'.1 v
  rw [hzv, hzv']
  rw [map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul]
  congr 1
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hu, hu, hu, hm, hm']
  ring

end General

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_lift_char (χ : charGrp (GK p K)) : ∃ t : GK p K → ℚ, IsLocallyConstant t ∧
    ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ.1 (Additive.ofMul g) :=
  ⟨fun g => (χ.1 (Additive.ofMul g)).out,
    (show IsLocallyConstant fun g : GK p K => χ.1 (Additive.ofMul g) from χ.2).comp Quotient.out,
    fun _ => QuotientAddGroup.out_eq' _⟩

theorem exists_isPairClass_of_inv {a : (kbarT p K).V} (ha : ∀ g, (kbarT p K).rho g a = a) (χ : charGrp (GK p K)) :
    ∃ c, IsPairClass p K a χ c := by
  obtain ⟨t, ht, htχ⟩ := exists_lift_char χ
  obtain ⟨m, hm⟩ := exists_defect χ.1 t htχ
  obtain ⟨z, hz, hzv⟩ := exists_defect_cocycle (kbarT p K) ha ht hm
  exact ⟨_, t, m, z, hz, ht, htχ, hm, hzv, rfl⟩

theorem IsPairClass.unique_of_inv {a : (kbarT p K).V} (ha : ∀ g, (kbarT p K).rho g a = a) {χ : charGrp (GK p K)}
    {c c' : Br p K} (h : IsPairClass p K a χ c) (h' : IsPairClass p K a χ c') : c = c' := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzv, rfl⟩ := h
  obtain ⟨t', m', z', hz', ht', htχ', hm', hzv', rfl⟩ := h'
  exact defect_cls_eq (kbarT p K) ha ht ht' (fun g => (htχ g).trans (htχ' g).symm) hm hm' hz hz' hzv hzv'

theorem IsPairClass.add_left {a b : (kbarT p K).V} (hb : ∀ g, (kbarT p K).rho g b = b) {χ : charGrp (GK p K)}
    {c c' : Br p K} (h : IsPairClass p K a χ c) (h' : IsPairClass p K b χ c') :
    IsPairClass p K (a + b) χ (c + c') := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzv, rfl⟩ := h
  obtain ⟨z', hz', hzv'⟩ := exists_defect_cocycle (kbarT p K) hb ht hm
  have e : c' = (kbarT p K).coch.cls 2 z' hz' :=
    IsPairClass.unique_of_inv hb h' ⟨t, m, z', hz', ht, htχ, hm, hzv', rfl⟩
  subst e
  refine ⟨t, m, z + z', Cx.d_add_eq_zero hz hz', ht, htχ, hm, fun g => ?_, rfl⟩
  show z.1 g + z'.1 g = _
  rw [hzv, hzv', smul_add]

theorem IsPairClass.add_right {a : (kbarT p K).V} {χ ψ : charGrp (GK p K)}
    {c c' : Br p K} (h : IsPairClass p K a χ c) (h' : IsPairClass p K a ψ c') :
    IsPairClass p K a (χ + ψ) (c + c') := by
  obtain ⟨t, m, z, hz, ht, htχ, hm, hzv, rfl⟩ := h
  obtain ⟨t', m', z', hz', ht', htχ', hm', hzv', rfl⟩ := h'
  refine ⟨t + t', m + m', z + z', Cx.d_add_eq_zero hz hz', ht.add ht', fun g => ?_, fun g => ?_, fun g => ?_, rfl⟩
  · show (QuotientAddGroup.mk (t g + t' g) : QZ) = χ.1 (Additive.ofMul g) + ψ.1 (Additive.ofMul g)
    rw [QuotientAddGroup.mk_add, htχ, htχ']
  · show ((m g + m' g : ℤ) : ℚ) = (t (g 0) + t' (g 0)) + (t (g 1) + t' (g 1)) - (t (g 0 * g 1) + t' (g 0 * g 1))
    rw [Int.cast_add, hm, hm']; ring
  · show z.1 g + z'.1 g = (m g + m' g) • a
    rw [hzv, hzv', add_smul]

theorem exists_isPairClass (a : Kˣ) (χ : charGrp (GK p K)) :
    ∃ c, IsPairClass p K (ofK p K (Additive.ofMul a)) χ c :=
  exists_isPairClass_of_inv (fun g => kbarT_rho_ofK g _) χ

theorem IsPairClass.unique {a : Kˣ} {χ : charGrp (GK p K)} {c c' : Br p K}
    (h : IsPairClass p K (ofK p K (Additive.ofMul a)) χ c)
    (h' : IsPairClass p K (ofK p K (Additive.ofMul a)) χ c') : c = c' :=
  IsPairClass.unique_of_inv (fun g => kbarT_rho_ofK g _) h h'

theorem isPairClass_pairBr (a : Kˣ) (χ : charGrp (GK p K)) :
    IsPairClass p K (ofK p K (Additive.ofMul a)) χ (pairBr p K a χ) := by
  unfold pairBr
  rw [dif_pos (exists_isPairClass a χ)]
  exact (exists_isPairClass a χ).choose_spec

theorem pairBr_mul (a b : Kˣ) (χ : charGrp (GK p K)) :
    pairBr p K (a * b) χ = pairBr p K a χ + pairBr p K b χ := by
  refine IsPairClass.unique (isPairClass_pairBr (a * b) χ) ?_
  rw [ofMul_mul, map_add]
  exact (isPairClass_pairBr a χ).add_left (fun g => kbarT_rho_ofK g _) (isPairClass_pairBr b χ)

theorem pairBr_add (a : Kˣ) (χ ψ : charGrp (GK p K)) :
    pairBr p K a (χ + ψ) = pairBr p K a χ + pairBr p K a ψ :=
  IsPairClass.unique (isPairClass_pairBr a (χ + ψ)) ((isPairClass_pairBr a χ).add_right (isPairClass_pairBr a ψ))

theorem pairK_mul (a b : Kˣ) (χ : charGrp (GK p K)) : pairK p K (a * b) χ = pairK p K a χ + pairK p K b χ := by
  unfold pairK
  rw [pairBr_mul, map_add]

theorem pairK_add (a : Kˣ) (χ ψ : charGrp (GK p K)) : pairK p K a (χ + ψ) = pairK p K a χ + pairK p K a ψ := by
  unfold pairK
  rw [pairBr_add, map_add]

theorem pairK_one (χ : charGrp (GK p K)) : pairK p K 1 χ = 0 := by
  have h := pairK_mul 1 1 χ
  rw [mul_one] at h
  simpa using h

theorem pairK_zero (a : Kˣ) : pairK p K a 0 = 0 := by
  have h := pairK_add a 0 0
  rw [add_zero] at h
  simpa using h

theorem pairK_inv (a : Kˣ) (χ : charGrp (GK p K)) : pairK p K a⁻¹ χ = - pairK p K a χ := by
  apply eq_neg_of_add_eq_zero_left
  rw [← pairK_mul, inv_mul_cancel, pairK_one]

theorem pairK_pow (a : Kˣ) (n : ℕ) (χ : charGrp (GK p K)) : pairK p K (a ^ n) χ = n • pairK p K a χ := by
  induction n with
  | zero => rw [pow_zero, pairK_one, zero_smul]
  | succ n ih => rw [pow_succ, pairK_mul, ih, succ_nsmul]

theorem pairK_nsmul (a : Kˣ) (n : ℕ) (χ : charGrp (GK p K)) : pairK p K a (n • χ) = n • pairK p K a χ := by
  induction n with
  | zero => rw [zero_smul, pairK_zero, zero_smul]
  | succ n ih => rw [succ_nsmul, pairK_add, ih, succ_nsmul]

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
