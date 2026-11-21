import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

section
noncomputable section
open LateralTheory.E.t_E6Cut

namespace LateralTheory.E.LeafRoofPf

theorem qiso_of {B W D : Type} [CommRing B] [CommRing W] [CommRing D] (α : B →+* W) (I : Ideal B) (h : W →+* D)
    (hI : ∀ x, h (α x) = 0 ↔ x ∈ I) (hs : ∀ w, ∃ x, h w = h (α x)) (hk : ∀ w, h w = 0 → w ∈ I.map α) :
    QIso α I := by
  have hle : I.map α ≤ RingHom.ker h := Ideal.map_le_iff_le_comap.mpr fun x hx => by
    simpa [RingHom.mem_ker] using (hI x).mpr hx
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Ideal.quotientMap_mk] at hxy
    rw [Ideal.Quotient.eq] at hxy ⊢
    apply (hI _).mp
    have := hle (by simpa [map_sub] using hxy)
    simpa [RingHom.mem_ker, map_sub] using this
  · intro w
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨x, hx⟩ := hs w
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    simp only [Ideal.quotientMap_mk]
    rw [Ideal.Quotient.eq]
    exact hk _ (by simp [map_sub, hx])

def LeafRoofEt : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ∃ (P : Type) (_ : CommRing P) (a : B →+* P) (b : MvPolynomial (Fin d) (B ⧸ varIdeal φ) →+* P)
    (m : P →+* B ⧸ varIdeal φ) (g : P), a.Etale ∧ b.Etale ∧ (∀ j, a (φ (MvPolynomial.X j)) = b (MvPolynomial.X j)) ∧
    m.comp a = Ideal.Quotient.mk _ ∧ m.comp b = MvPolynomial.constantCoeff ∧ m g = 1 ∧
    ∀ x, m x = 0 → ∃ n : ℕ, g ^ n * x ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j))

def LeafKerC : Prop := ∀ (d : ℕ) (D : Type) [CommRing D] (p : MvPolynomial (Fin d) D),
  MvPolynomial.constantCoeff p = 0 → p ∈ varIdeal (RingHom.id (MvPolynomial (Fin d) D))

theorem kerC_of : LeafKerC := by
  intro d D _ p hp
  have : p ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin d))) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro mo hmo
    by_contra hne
    push_neg at hne
    have h0 : mo = 0 := by ext i; simpa using hne i (Set.mem_univ i)
    subst h0
    exact (MvPolynomial.mem_support_iff.mp hmo) (by simpa [MvPolynomial.constantCoeff_eq] using hp)
  simpa [varIdeal, Set.image_univ] using this

theorem map_varIdeal {d : ℕ} {C B W : Type} [CommRing C] [CommRing B] [CommRing W]
    (φ : MvPolynomial (Fin d) C →+* B) (α : B →+* W) :
    (varIdeal φ).map α = Ideal.span (Set.range fun j => α (φ (MvPolynomial.X j))) := by
  unfold varIdeal; rw [Ideal.map_span, ← Set.range_comp]; rfl

theorem LeafRoof_of (h1 : LeafRoofEt) : LeafRoof := by
  intro d C B _ _ φ hφ
  obtain ⟨P, _, a, b, m, g, ha, hb, hab, hma, hmb, hg, hk⟩ := h1 d φ hφ
  have hu : IsUnit (m g) := by rw [hg]; exact isUnit_one
  let h : Localization.Away g →+* (B ⧸ varIdeal φ) := IsLocalization.Away.lift g hu
  have hh : ∀ x, h (algebraMap P (Localization.Away g) x) = m x := fun x =>
    IsLocalization.Away.lift_eq g hu x
  have hJ : ∀ w : Localization.Away g, h w = 0 →
      w ∈ (Ideal.span (Set.range fun j => b (MvPolynomial.X j))).map (algebraMap P (Localization.Away g)) := by
    intro w hw
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) w
    have hy : m y = 0 := by
      have := (IsLocalization.lift_mk'_spec (M := Submonoid.powers g) (S := Localization.Away g) _ y 0 s).mp hw
      simpa using this
    obtain ⟨n, hn⟩ := hk y hy
    have hm := Ideal.mem_map_of_mem (algebraMap P (Localization.Away g)) hn
    have hunit : IsUnit (algebraMap P (Localization.Away g) (g ^ n * s)) := by
      rw [map_mul]
      exact (IsLocalization.map_units _ (⟨g ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers g) n⟩ : Submonoid.powers g)).mul (IsLocalization.map_units _ s)
    rw [← Ideal.mul_unit_mem_iff_mem _ hunit]
    have e : IsLocalization.mk' (Localization.Away g) y s * algebraMap P _ (g ^ n * s) =
        algebraMap P _ (g ^ n * y) := by
      rw [map_mul, map_mul, mul_comm (algebraMap P _ (g ^ n)), ← mul_assoc, IsLocalization.mk'_spec, mul_comm]
    rw [e]; exact hm
  have hloc : (algebraMap P (Localization.Away g)).Etale := by
    rw [RingHom.etale_algebraMap]; exact Algebra.Etale.of_isLocalizationAway g
  refine ⟨B ⧸ varIdeal φ, Localization.Away g, inferInstance, inferInstance, Ideal.Quotient.mk _,
    (algebraMap P _).comp a, (algebraMap P _).comp b,
    RingHom.Etale.stableUnderComposition _ _ ha hloc, RingHom.Etale.stableUnderComposition _ _ hb hloc,
    fun j => by simp [hab], ?_, ?_⟩
  · apply qiso_of _ _ h
    · intro x
      rw [RingHom.comp_apply, hh, ← RingHom.comp_apply, hma, Ideal.Quotient.eq_zero_iff_mem]
    · intro w
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (h w)
      exact ⟨x, by rw [RingHom.comp_apply, hh, ← RingHom.comp_apply, hma, hx]⟩
    · intro w hw
      have := hJ w hw
      convert this using 1
      rw [map_varIdeal, Ideal.map_span, ← Set.range_comp]
      congr 1; ext j; simp [hab]
  · apply qiso_of _ _ h
    · intro p
      rw [RingHom.comp_apply, hh, ← RingHom.comp_apply, hmb]
      refine ⟨kerC_of d _ p, fun hp => ?_⟩
      have hle : varIdeal (RingHom.id (MvPolynomial (Fin d) (B ⧸ varIdeal φ))) ≤
          RingHom.ker (MvPolynomial.constantCoeff (R := B ⧸ varIdeal φ) (σ := Fin d)) := by
        exact Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; simp)
      exact hle hp
    · intro w
      exact ⟨MvPolynomial.C (h w), by rw [RingHom.comp_apply, hh, ← RingHom.comp_apply, hmb]; simp⟩
    · intro w hw
      have := hJ w hw
      convert this using 1
      rw [map_varIdeal, Ideal.map_span, ← Set.range_comp]
      rfl

end LateralTheory.E.LeafRoofPf
end
end

section
noncomputable section
open LateralTheory.E.t_E6Cut

namespace LateralTheory.E.LeafRoofEtPf

def LeafRoofEtP : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ∃ (P : Type) (_ : CommRing P) (a : B →+* P) (b : MvPolynomial (Fin d) (B ⧸ varIdeal φ) →+* P)
    (m : P →+* B ⧸ varIdeal φ) (e : P), a.Etale ∧ b.Etale ∧ (∀ j, a (φ (MvPolynomial.X j)) = b (MvPolynomial.X j)) ∧
    m.comp a = Ideal.Quotient.mk _ ∧ m.comp b = MvPolynomial.constantCoeff ∧
    m e = 0 ∧ e * e - e ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ∧
    ∀ x, m x = 0 → x ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ⊔ Ideal.span {e}

theorem LeafRoofEt_of (h : LeafRoofEtP) : LateralTheory.E.LeafRoofPf.LeafRoofEt := by
  intro d C B _ _ φ hφ
  obtain ⟨P, _, a, b, m, e, ha, hb, hab, hma, hmb, hme, he, hk⟩ := h d φ hφ
  refine ⟨P, inferInstance, a, b, m, 1 - e, ha, hb, hab, hma, hmb, by simp [hme], fun x hx => ⟨1, ?_⟩⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hk x hx)
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have : (1 - e) ^ 1 * (y + r * e) = (1 - e) * y - r * (e * e - e) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ he)

end LateralTheory.E.LeafRoofEtPf
end
end

section
noncomputable section
open LateralTheory.E.t_E6Cut TensorProduct

namespace LateralTheory.E.LeafRoofEtPPf

theorem diag {C D : Type} [CommRing C] [CommRing D] [Algebra C D] [Algebra.Etale C D] :
    ∃ e : D ⊗[C] D, IsIdempotentElem e ∧ Algebra.TensorProduct.lmul' C e = 0 ∧
      ∀ x, Algebra.TensorProduct.lmul' C x = 0 → x ∈ Ideal.span {e} := by
  obtain ⟨e, he, hsp⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg C D)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[D⁄C]
  refine ⟨e, he, ?_, fun x hx => ?_⟩
  · have : e ∈ KaehlerDifferential.ideal C D := hsp ▸ Submodule.mem_span_singleton_self e
    simpa [RingHom.mem_ker] using this
  · have : x ∈ KaehlerDifferential.ideal C D := by simpa [RingHom.mem_ker] using hx
    rw [hsp] at this
    exact this

def LeafQuotEt : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ((Ideal.Quotient.mk (varIdeal φ)).comp (φ.comp MvPolynomial.C)).Etale

def LeafPolyEt : Prop := ∀ (d : ℕ) {C B D : Type} [CommRing C] [CommRing B] [CommRing D] [Algebra C D]
  (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  letI := (φ.comp MvPolynomial.C).toAlgebra
  (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : D →ₐ[C] B ⊗[C] D).toRingHom
     (fun j => φ (MvPolynomial.X j) ⊗ₜ[C] (1:D))).Etale

theorem roofEtale_of_quotientEtale_polynomialEtale (h1 : LeafQuotEt) (h2 : LeafPolyEt) : LateralTheory.E.LeafRoofEtPf.LeafRoofEtP := by
  intro d C B _ _ φ hφ
  letI : Algebra C B := (φ.comp MvPolynomial.C).toAlgebra
  haveI hD : Algebra.Etale C (B ⧸ varIdeal φ) := by
    rw [← RingHom.etale_algebraMap]; exact h1 d φ hφ
  let q : B ⊗[C] (B ⧸ varIdeal φ) →ₐ[C] (B ⧸ varIdeal φ) ⊗[C] (B ⧸ varIdeal φ) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C (varIdeal φ)) (AlgHom.id C _)
  let m : B ⊗[C] (B ⧸ varIdeal φ) →+* B ⧸ varIdeal φ := ((Algebra.TensorProduct.lmul' C).comp q).toRingHom
  let b : MvPolynomial (Fin d) (B ⧸ varIdeal φ) →+* B ⊗[C] (B ⧸ varIdeal φ) :=
    MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : (B ⧸ varIdeal φ) →ₐ[C] B ⊗[C] _).toRingHom
     (fun j => φ (MvPolynomial.X j) ⊗ₜ[C] (1 : B ⧸ varIdeal φ))
  obtain ⟨e0, hi, he0, hk0⟩ := diag (C := C) (D := B ⧸ varIdeal φ)
  have hq : Function.Surjective q :=
    Algebra.TensorProduct.map_surjective _ _ (Ideal.Quotient.mkₐ_surjective C _) (fun x => ⟨x, rfl⟩)
  obtain ⟨e, rfl⟩ := hq e0
  have hbX : ∀ j, b (MvPolynomial.X j) = φ (MvPolynomial.X j) ⊗ₜ[C] (1 : B ⧸ varIdeal φ) := fun j => by
    simp [b]
  have hker : RingHom.ker q = Ideal.span (Set.range fun j => b (MvPolynomial.X j)) := by
    have hk : RingHom.ker (Ideal.Quotient.mkₐ C (varIdeal φ)) =
        Ideal.span (Set.range fun j => φ (MvPolynomial.X j)) := by
      ext x; exact Ideal.Quotient.eq_zero_iff_mem
    rw [Algebra.TensorProduct.rTensor_ker _ (Ideal.Quotient.mkₐ_surjective C _), hk, Ideal.map_span, ← Set.range_comp]
    congr 1
    ext x
    simp [hbX]
  have hmem : ∀ x, x ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ↔ q x = 0 := fun x => by
    rw [← hker, RingHom.mem_ker]
  refine ⟨B ⊗[C] (B ⧸ varIdeal φ), inferInstance, algebraMap B _, b, m, e,
    RingHom.etale_algebraMap.mpr inferInstance, h2 d φ hφ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; rw [hbX]; rfl
  · ext x; simp [m, q]
  · apply MvPolynomial.ringHom_ext
    · intro r; simp [m, q, b]
    · intro j
      simp only [RingHom.comp_apply, hbX, MvPolynomial.constantCoeff_X]
      simp only [m, q, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one,
        Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  · exact he0
  · rw [hmem, map_sub, map_mul, hi.eq, sub_self]
  · intro x hx
    obtain ⟨r0, hr0⟩ := Ideal.mem_span_singleton'.mp (hk0 (q x) hx)
    obtain ⟨r, rfl⟩ := hq r0
    have : x - r * e ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) := by
      rw [hmem, map_sub, map_mul, hr0, sub_self]
    have h3 : x = (x - r * e) + r * e := by ring
    rw [h3]
    exact Ideal.add_mem _ (Ideal.mem_sup_left this)
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))

end LateralTheory.E.LeafRoofEtPPf
end
end
