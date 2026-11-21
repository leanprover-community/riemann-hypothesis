import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import BuildAid.ForwardExisting

section
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem IsCplAt.approx_step {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (t : S) (ht : t ∈ maximalIdeal S ^ k) :
    ∀ c : S, ∃ a b : R, b ∉ q ∧ φ b * (c * t) - φ a ∈ maximalIdeal S ^ (k + 1) := by
  have e : maximalIdeal S ^ k = (q ^ k).map φ := by rw [h.max_eq, Ideal.map_pow]
  rw [e, Ideal.map] at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro c
    obtain ⟨a, b, hb, hab⟩ := h.res c
    refine ⟨a * x, b, hb, ?_⟩
    have : φ b * (c * φ x) - φ (a * x) = φ x * (φ b * c - φ a) := by rw [map_mul]; ring
    rw [this, pow_succ]
    exact Ideal.mul_mem_mul (e ▸ Ideal.mem_map_of_mem φ hx) hab
  | zero =>
    intro c
    exact ⟨0, 1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨a, b, hb, hab⟩ := hx c
    obtain ⟨a', b', hb', hab'⟩ := hy c
    refine ⟨b' * a + b * a', b * b', fun hh => (hq.mem_or_mem hh).elim hb hb', ?_⟩
    have : φ (b * b') * (c * (x + y)) - φ (b' * a + b * a')
        = φ b' * (φ b * (c * x) - φ a) + φ b * (φ b' * (c * y) - φ a') := by
      simp only [map_mul, map_add]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hab) (Ideal.mul_mem_left _ _ hab')
  | smul r x _ hx =>
    intro c
    obtain ⟨a, b, hb, hab⟩ := hx (c * r)
    exact ⟨a, b, hb, by simpa [mul_assoc] using hab⟩

theorem IsCplAt.approx_surj {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (s : S) :
    ∃ a b : R, b ∉ q ∧ φ b * s - φ a ∈ maximalIdeal S ^ k := by
  induction k with
  | zero => exact ⟨0, 1, (Ideal.ne_top_iff_one q).1 hq.ne_top, by simp⟩
  | succ k ih =>
    obtain ⟨a, b, hb, hab⟩ := ih
    obtain ⟨a', b', hb', hab'⟩ := h.approx_step k _ hab 1
    refine ⟨b' * a + a', b * b', fun hh => (hq.mem_or_mem hh).elim hb hb', ?_⟩
    have : φ (b * b') * s - φ (b' * a + a') = φ b' * (1 * (φ b * s - φ a)) - φ a' := by
      simp only [map_mul, map_add]; ring
    rw [this]
    exact hab'

theorem IsCplAt.approx_inj {R S : Type} [CommRing R] [CommRing S] [IsLocalRing S] {q : Ideal R}
    [hq : q.IsPrime] {φ : R →+* S} (h : IsCplAt q φ) (k : ℕ) (a : R)
    (ha : φ a ∈ maximalIdeal S ^ k) : ∃ b ∉ q, b * a ∈ q ^ k := by
  let L := Localization.AtPrime q
  have hu : ∀ y : q.primeCompl, IsUnit (φ y) := by
    intro y
    by_contra hy
    have : (y : R) ∈ (maximalIdeal S).comap φ := (mem_maximalIdeal _).2 hy
    rw [h.comap_eq] at this
    exact y.2 this
  letI : Algebra R S := φ.toAlgebra
  let ψ : L →+* S := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra L S := ψ.toAlgebra
  have hψ : ∀ r, ψ (algebraMap R L r) = φ r := fun r => IsLocalization.lift_eq hu r
  haveI : IsScalarTower R L S := IsScalarTower.of_algebraMap_eq fun r => (hψ r).symm
  have hfl : Module.Flat R S := h.flat
  haveI : Module.Flat L S := (Module.flat_iff_of_isLocalization L q.primeCompl S).2 hfl
  have hcomp : (algebraMap L S).comp (algebraMap R L) = φ := RingHom.ext hψ
  haveI : IsLocalHom (algebraMap L S) := by
    apply ((local_hom_TFAE (algebraMap L S)).out 0 2).2
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hcomp, h.max_eq]
  haveI : Module.FaithfullyFlat L S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have key := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) ((q ^ k).map (algebraMap R L))
  rw [Ideal.map_map, hcomp, Ideal.map_pow φ, ← h.max_eq] at key
  have ha' : algebraMap R L a ∈ (q ^ k).map (algebraMap R L) := by
    rw [← key, Ideal.mem_comap]
    exact (hψ a).symm ▸ ha
  obtain ⟨m, hm, hma⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl L _ a).1 ha'
  exact ⟨m, hm, hma⟩

theorem isCplAt_approx : ∀ (R S : Type) [CommRing R] [CommRing S] [IsLocalRing S] (q : Ideal R)
    [q.IsPrime] (φ : R →+* S), IsCplAt q φ → ∀ k : ℕ,
    (∀ s : S, ∃ a b : R, b ∉ q ∧ φ b * s - φ a ∈ maximalIdeal S ^ k) ∧
      ∀ a : R, φ a ∈ maximalIdeal S ^ k → ∃ b ∉ q, b * a ∈ q ^ k :=
  fun _ _ _ _ _ _ _ _ h k => ⟨h.approx_surj k, h.approx_inj k⟩

end GlobalTheory.Pat
end

section
section
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat.CplMap

variable {R S S' : Type} [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
  {q : Ideal R} {φ : R →+* S} {ψ : R →+* S'}

theorem isUnit_mk (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {b : R} (hb : b ∉ q) :
    IsUnit (Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b)) := by
  have h1 : IsUnit (ψ b) := by
    by_contra h
    exact hb (hψ ▸ (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr h)))
  exact h1.map _

theorem map_mem_pow (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {a : R} (ha : a ∈ q ^ n) :
    ψ a ∈ maximalIdeal S' ^ n := by
  have h : (q ^ n).map ψ ≤ maximalIdeal S' ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hψ.ge) n
  exact h (Ideal.mem_map_of_mem ψ ha)

theorem ext_mem_pow (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) {F : S →+* S'}
    (hF : F.comp φ = ψ) (n : ℕ) {x : S} (hx : x ∈ maximalIdeal S ^ n) :
    F x ∈ maximalIdeal S' ^ n := by
  have h1 : (maximalIdeal S).map F ≤ maximalIdeal S' := by
    rw [hφ.max_eq, Ideal.map_map, hF]
    exact Ideal.map_le_iff_le_comap.mpr hψ.ge
  have h2 : (maximalIdeal S ^ n).map F ≤ maximalIdeal S' ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h1 n
  exact h2 (Ideal.mem_map_of_mem F hx)

variable [hq : q.IsPrime]

def IsVal (q : Ideal R) (φ : R →+* S) (ψ : R →+* S') (n : ℕ) (s : S)
    (t : S' ⧸ maximalIdeal S' ^ n) : Prop :=
  ∀ a b : R, b ∉ q → φ b * s - φ a ∈ maximalIdeal S ^ n →
    Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b) * t = Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ a)

theorem exists_val (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) (s : S) :
    ∃ t, IsVal q φ ψ n s t := by
  obtain ⟨a0, b0, hb0, h0⟩ := (isCplAt_approx R S q φ hφ n).1 s
  obtain ⟨u, hu⟩ := isUnit_mk hψ n hb0
  refine ⟨Ideal.Quotient.mk _ (ψ a0) * (↑u⁻¹ : S' ⧸ maximalIdeal S' ^ n), fun a b _ h => ?_⟩
  have hm : φ (b * a0 - b0 * a) ∈ maximalIdeal S ^ n := by
    have : φ (b * a0 - b0 * a) = φ b0 * (φ b * s - φ a) - φ b * (φ b0 * s - φ a0) := by
      simp only [map_sub, map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h0)
  obtain ⟨c, hc, hcq⟩ := (isCplAt_approx R S q φ hφ n).2 _ hm
  have h1 := Ideal.Quotient.eq_zero_iff_mem.mpr (map_mem_pow hψ n hcq)
  simp only [map_mul, map_sub] at h1
  have h2 := sub_eq_zero.mp ((isUnit_mk hψ n hc).mul_right_eq_zero.mp h1)
  rw [← mul_assoc, h2, ← hu, mul_right_comm, Units.mul_inv, one_mul]

omit hq in
theorem val_unique_of_pair (hψ : (maximalIdeal S').comap ψ = q) {n : ℕ} {s : S}
    {t t' : S' ⧸ maximalIdeal S' ^ n} (ht : IsVal q φ ψ n s t) {a b : R} (hb : b ∉ q)
    (h : φ b * s - φ a ∈ maximalIdeal S ^ n)
    (e : Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b) * t' =
      Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ a)) : t = t' :=
  (isUnit_mk hψ n hb).mul_left_cancel ((ht a b hb h).trans e.symm)

theorem one_notMem : (1 : R) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).mpr h)

theorem exists_levHom (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) :
    ∃ f : S →+* S' ⧸ maximalIdeal S' ^ n, ∀ s, IsVal q φ ψ n s (f s) := by
  choose f hf using exists_val hφ hψ n
  have ap := (isCplAt_approx R S q φ hφ n).1
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · exact val_unique_of_pair hψ (hf 1) (a := 1) (b := 1) one_notMem (by simp) (by simp)
  · intro x y
    obtain ⟨a1, b1, hb1, h1⟩ := ap x
    obtain ⟨a2, b2, hb2, h2⟩ := ap y
    have hb : b1 * b2 ∉ q := fun h => (hq.mem_or_mem h).elim hb1 hb2
    refine val_unique_of_pair hψ (hf (x * y)) (a := a1 * a2) hb ?_ ?_
    · have : φ (b1 * b2) * (x * y) - φ (a1 * a2) =
          (φ b1 * x - φ a1) * (φ b2 * y) + φ a1 * (φ b2 * y - φ a2) := by
        simp only [map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · simp only [map_mul]
      rw [← hf x a1 b1 hb1 h1, ← hf y a2 b2 hb2 h2]; ring
  · exact val_unique_of_pair hψ (hf 0) (a := 0) (b := 1) one_notMem (by simp) (by simp)
  · intro x y
    obtain ⟨a1, b1, hb1, h1⟩ := ap x
    obtain ⟨a2, b2, hb2, h2⟩ := ap y
    have hb : b1 * b2 ∉ q := fun h => (hq.mem_or_mem h).elim hb1 hb2
    refine val_unique_of_pair hψ (hf (x + y)) (a := a1 * b2 + a2 * b1) hb ?_ ?_
    · have : φ (b1 * b2) * (x + y) - φ (a1 * b2 + a2 * b1) =
          φ b2 * (φ b1 * x - φ a1) + φ b1 * (φ b2 * y - φ a2) := by
        simp only [map_mul, map_add]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · simp only [map_mul, map_add]
      rw [← hf x a1 b1 hb1 h1, ← hf y a2 b2 hb2 h2]; ring

end GlobalTheory.Pat.CplMap

namespace GlobalTheory.Pat

open CplMap

theorem isCplAt_existsUnique_map : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing S'] [IsLocalRing S'] [IsAdicComplete (maximalIdeal S') S'] (q : Ideal R) [q.IsPrime]
    (φ : R →+* S) (ψ : R →+* S'), IsCplAt q φ → (maximalIdeal S').comap ψ = q →
    ∃! θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = ψ := by
  intro R S S' _ _ _ _ _ _ q _ φ ψ hφ hψ
  choose f hf using exists_levHom hφ hψ
  have hc : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal S') hle).comp (f n) = f m := by
    intro m n hle
    ext s
    obtain ⟨a, b, hb, h⟩ := (isCplAt_approx R S q φ hφ n).1 s
    refine (val_unique_of_pair hψ (hf m s) hb (Ideal.pow_le_pow_right hle h) ?_).symm
    have e := congrArg (Ideal.Quotient.factorPow (maximalIdeal S') hle) (hf n s a b hb h)
    rw [map_mul] at e
    exact e
  have hcomp : (IsAdicComplete.liftRingHom (maximalIdeal S') f hc).comp φ = ψ := by
    ext r
    refine congrFun (IsHausdorff.funext' (maximalIdeal S')
      (f := fun r => IsAdicComplete.liftRingHom (maximalIdeal S') f hc (φ r)) (g := fun r => ψ r)
      (fun n r => ?_)) r
    rw [IsAdicComplete.mk_liftRingHom]
    exact val_unique_of_pair hψ (hf n (φ r)) (a := r) (b := 1) one_notMem (by simp) (by simp)
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal S') f hc, ⟨⟨fun s hs => ?_⟩, hcomp⟩, ?_⟩
  · by_contra hn
    have h1 := ext_mem_pow hφ hψ hcomp 1 (x := s) (by
      rw [pow_one]; exact (mem_maximalIdeal _).mpr hn)
    rw [pow_one] at h1
    exact (mem_maximalIdeal _).mp h1 hs
  · rintro F ⟨-, hF⟩
    refine IsAdicComplete.eq_liftRingHom _ f hc F (fun n => ?_)
    ext s
    obtain ⟨a, b, hb, h⟩ := (isCplAt_approx R S q φ hφ n).1 s
    refine (val_unique_of_pair hψ (hf n s) hb h ?_).symm
    have h1 := ext_mem_pow hφ hψ hF n h
    rw [RingHom.comp_apply, ← map_mul, Ideal.Quotient.eq, ← hF]
    simpa using h1

end GlobalTheory.Pat
end

open IsLocalRing GlobalTheory.Pat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_universal_local_hom : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] [IsAdicComplete (maximalIdeal S') S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (ψ : R →+* S'), IsCplAt q φ → (maximalIdeal S').comap ψ = q → ∃! θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = ψ := by
  atlas_forward_decl GlobalTheory.Pat.isCplAt_existsUnique_map
end

section
section
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem isCplAt_unique : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by
  intro R S S' _ _ _ _ _ q _ φ φ' h h'
  haveI := h.complete
  haveI := h'.complete
  obtain ⟨θ, ⟨hθl, hθ⟩, -⟩ := GlobalTheory.T.completion_universal_local_hom R S S' q φ φ' h h'.comap_eq
  obtain ⟨η, ⟨hηl, hη⟩, -⟩ := GlobalTheory.T.completion_universal_local_hom R S' S q φ' φ h' h.comap_eq
  have u := (GlobalTheory.T.completion_universal_local_hom R S S q φ φ h h.comap_eq).unique
    (y₁ := η.comp θ) (y₂ := RingHom.id S)
    ⟨RingHom.isLocalHom_comp η θ, by rw [RingHom.comp_assoc, hθ, hη]⟩
    ⟨inferInstance, RingHom.id_comp φ⟩
  have u' := (GlobalTheory.T.completion_universal_local_hom R S' S' q φ' φ' h' h'.comap_eq).unique
    (y₁ := θ.comp η) (y₂ := RingHom.id S')
    ⟨RingHom.isLocalHom_comp θ η, by rw [RingHom.comp_assoc, hη, hθ]⟩
    ⟨inferInstance, RingHom.id_comp φ'⟩
  exact ⟨RingEquiv.ofRingHom θ η u' u, hθ⟩

end GlobalTheory.Pat
end

open IsLocalRing GlobalTheory.Pat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_unique_up_to_iso : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S'] (q : Ideal R) [q.IsPrime] (φ : R →+* S) (φ' : R →+* S'), IsCplAt q φ → IsCplAt q φ' → ∃ e : S ≃+* S', (e : S →+* S').comp φ = φ' := by
  atlas_forward_decl GlobalTheory.Pat.isCplAt_unique
end

section
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem flat_quotientMap_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    (I : Ideal R) : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Flat := by
  algebraize [φ]
  have h1 : (algebraMap (R ⧸ I) (TensorProduct R (R ⧸ I) S)).Flat :=
    RingHom.flat_algebraMap_iff.2 inferInstance
  let e : TensorProduct R (R ⧸ I) S ≃+* S ⧸ I.map φ :=
    (Algebra.TensorProduct.comm R (R ⧸ I) S).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toRingEquiv
  have h2 : (e : TensorProduct R (R ⧸ I) S →+* S ⧸ I.map φ).Flat := RingHom.Flat.of_bijective e.bijective
  have h3 := h1.comp h2
  convert h3 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have : (Ideal.Quotient.mk I r) ⊗ₜ[R] (1 : S) = (1 : R ⧸ I) ⊗ₜ[R] (φ r) := by
    have := TensorProduct.smul_tmul (R := R) r (1 : R ⧸ I) (1 : S)
    simp only [Algebra.smul_def, mul_one] at this
    exact this
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_coe]
  rw [this]
  apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).injective
  simp [e]
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk S I (φ r)


end GlobalTheory.Pat
end
