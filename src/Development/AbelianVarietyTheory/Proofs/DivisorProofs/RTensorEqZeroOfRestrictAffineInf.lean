import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.TensorDevissage

variable {A : Type} [CommRing A] {I : Type} {B : I → Type} [∀ i, CommRing (B i)]

def JointInj (φ : ∀ i, A →+* B i) (L : Type) [AddCommGroup L] : Prop :=
  ∀ h : A ⊗[ℤ] L, (∀ i, LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0

variable (φ : ∀ i, A →+* B i)

theorem comm_sq {L L' : Type} [AddCommGroup L] [AddCommGroup L'] (g : L →ₗ[ℤ] L') (i : I)
    (h : A ⊗[ℤ] L) :
    LinearMap.rTensor L' (φ i).toAddMonoidHom.toIntLinearMap (LinearMap.lTensor A g h) =
      LinearMap.lTensor (B i) g (LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

theorem all_zero_of_subsingleton (L : Type) [AddCommGroup L] [Subsingleton L] (h : A ⊗[ℤ] L) :
    h = 0 := by
  induction h using TensorProduct.induction_on with
  | zero => rfl
  | tmul a l => rw [Subsingleton.elim l 0, tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem of_subsingleton (L : Type) [AddCommGroup L] [Subsingleton L] : JointInj φ L :=
  fun h _ => all_zero_of_subsingleton L h

theorem of_injective [Module.Flat ℤ A] {L L' : Type} [AddCommGroup L] [AddCommGroup L']
    (g : L →ₗ[ℤ] L') (hg : Function.Injective g) (h' : JointInj φ L') : JointInj φ L := by
  intro h hh
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := A) g hg
  rw [map_zero]
  exact h' _ fun i => by rw [comm_sq, hh i, map_zero]

theorem zero_of_mem_range [∀ i, Module.Flat ℤ (B i)] {L L' : Type} [AddCommGroup L]
    [AddCommGroup L'] (g : L' →ₗ[ℤ] L) (hg : Function.Injective g) (h' : JointInj φ L')
    (h : A ⊗[ℤ] L) (hr : ∃ y, LinearMap.lTensor A g y = h)
    (hh : ∀ i, LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h = 0) : h = 0 := by
  obtain ⟨h0, rfl⟩ := hr
  rw [h' h0 fun i => ?_, map_zero]
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := B i) g hg
  rw [map_zero, ← comm_sq, hh i]

theorem of_exact [∀ i, Module.Flat ℤ (B i)] {L' L L'' : Type} [AddCommGroup L'] [AddCommGroup L]
    [AddCommGroup L''] (f : L' →ₗ[ℤ] L) (g : L →ₗ[ℤ] L'') (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (h1 : JointInj φ L')
    (h3 : JointInj φ L'') : JointInj φ L := by
  intro h hh
  have h0 : LinearMap.lTensor A g h = 0 := h3 _ fun i => by rw [comm_sq, hh i, map_zero]
  obtain ⟨y, hy⟩ := (lTensor_exact A hfg hg h).mp h0
  exact zero_of_mem_range φ f hf h1 h ⟨y, hy⟩ hh

theorem subsingleton_of_surj {C : Type} [AddCommGroup C] (t : ℤ →ₗ[ℤ] C)
    (ht : Function.Surjective t) (h0 : ∀ n, t n = 0) : Subsingleton C :=
  ⟨fun a b => by
    obtain ⟨m, rfl⟩ := ht a
    obtain ⟨n, rfl⟩ := ht b
    rw [h0, h0]⟩

theorem of_prime [Module.Flat ℤ A] (p : ℕ) (hp : p.Prime) (hP : JointInj φ (ZMod p)) {C : Type}
    [AddCommGroup C] (t : ℤ →ₗ[ℤ] C) (ht : Function.Surjective t) (htp : t p = 0) :
    JointInj φ C := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  by_cases htop : LinearMap.ker t = ⊤
  · haveI := subsingleton_of_surj t ht fun n => by
      rw [LinearMap.ker_eq_top.mp htop]; rfl
    exact of_subsingleton φ C
  · have hk : LinearMap.ker t = Ideal.span {(p : ℤ)} := by
      refine (hmax.eq_of_le htop ?_).symm
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact LinearMap.mem_ker.mpr htp
    let e : C ≃+ ZMod p := ((t.quotKerEquivOfSurjective ht).symm.toAddEquiv.trans
      (Submodule.quotEquivOfEq _ _ hk).toAddEquiv).trans (Int.quotientSpanNatEquivZMod p).toAddEquiv
    exact of_injective φ e.toAddMonoidHom.toIntLinearMap e.injective hP

theorem of_killed [Module.Flat ℤ A] [∀ i, Module.Flat ℤ (B i)]
    (hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p)) :
    ∀ (k : ℕ), 0 < k → ∀ (C : Type) [AddCommGroup C] (t : ℤ →ₗ[ℤ] C),
      Function.Surjective t → t k = 0 → JointInj φ C := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk C _ t ht htk
  by_cases h1 : k = 1
  · subst h1
    haveI := subsingleton_of_surj t ht fun n => by
      rw [show n = n • (((1 : ℕ) : ℤ)) by simp, map_zsmul, htk, smul_zero]
    exact of_subsingleton φ C
  have hp : k.minFac.Prime := Nat.minFac_prime h1
  obtain ⟨m, hm⟩ : k.minFac ∣ k := Nat.minFac_dvd k
  have hp2 := hp.two_le
  by_cases hm1 : m = 1
  · subst hm1
    rw [_root_.mul_one] at hm
    rw [hm] at htk
    exact of_prime φ _ hp (hP _ hp) t ht htk
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hmk : m < k := by nlinarith
  have hpk : k.minFac < k := by
    have : 2 ≤ m := by omega
    nlinarith
  let s : ℤ →ₗ[ℤ] C := ((k.minFac : ℕ) : ℤ) • t
  have hs1 : JointInj φ (LinearMap.range s) := by
    refine ih m hmk hm0 _ s.rangeRestrict s.surjective_rangeRestrict ?_
    apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, ZeroMemClass.coe_zero, s, LinearMap.rangeRestrict,
      LinearMap.smul_apply]
    rw [← map_zsmul, smul_eq_mul, ← Nat.cast_mul, ← hm, htk]
  have hs3 : JointInj φ (C ⧸ LinearMap.range s) := by
    refine ih _ hpk hp.pos _ ((LinearMap.range s).mkQ ∘ₗ t)
      ((LinearMap.range s).mkQ_surjective.comp ht) ?_
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨1, ?_⟩
    simp only [s, LinearMap.smul_apply]
    rw [← map_zsmul, smul_eq_mul, _root_.mul_one]
  exact of_exact φ _ _ (LinearMap.range s).injective_subtype
    (LinearMap.exact_subtype_mkQ _) (LinearMap.range s).mkQ_surjective hs1 hs3

end GlobalTheory.TensorDevissage

theorem GlobalTheory.TensorDevissage.all_zero_of_subsingleton' {A L : Type} [CommRing A] [Subsingleton A]
    [AddCommGroup L] (h : A ⊗[ℤ] L) : h = 0 := by
  induction h using TensorProduct.induction_on with
  | zero => rfl
  | tmul a l => rw [Subsingleton.elim a 0, zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

namespace GlobalTheory.TensorDevissage

variable {A : Type} [CommRing A] {I : Type} {B : I → Type} [∀ i, CommRing (B i)]
variable (φ : ∀ i, A →+* B i)

theorem of_cyclic [Module.Flat ℤ A] [∀ i, Module.Flat ℤ (B i)] (hZ : JointInj φ ℤ)
    (hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p)) (C : Type) [AddCommGroup C] (t : ℤ →ₗ[ℤ] C)
    (ht : Function.Surjective t) : JointInj φ C := by
  by_cases hex : ∃ k : ℕ, 0 < k ∧ t k = 0
  · obtain ⟨k, hk, htk⟩ := hex
    exact of_killed φ hP k hk C t ht htk
  · push_neg at hex
    have hinj : Function.Injective t := by
      refine (injective_iff_map_eq_zero t).mpr fun n hn => ?_
      by_contra hne
      apply hex n.natAbs (Int.natAbs_pos.mpr hne)
      rcases Int.natAbs_eq n with h | h
      · rw [← h]; exact hn
      · rw [show ((n.natAbs : ℕ) : ℤ) = -n by omega, map_neg, hn, neg_zero]
    let e := LinearEquiv.ofBijective t ⟨hinj, ht⟩
    exact of_injective φ e.symm.toLinearMap e.symm.injective hZ

theorem of_fg [Module.Flat ℤ A] [∀ i, Module.Flat ℤ (B i)] (hZ : JointInj φ ℤ)
    (hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p)) :
    ∀ (n : ℕ) (L : Type) [AddCommGroup L] (s : Finset L), s.card ≤ n →
      Submodule.span ℤ (s : Set L) = ⊤ → JointInj φ L := by
  classical
  intro n
  induction n with
  | zero =>
    intro L _ s hs hspan
    rw [Nat.le_zero, Finset.card_eq_zero] at hs
    subst hs
    haveI : Subsingleton L := ⟨fun a b => by
      have ha : a ∈ Submodule.span ℤ ((∅ : Finset L) : Set L) := hspan ▸ Submodule.mem_top
      have hb : b ∈ Submodule.span ℤ ((∅ : Finset L) : Set L) := hspan ▸ Submodule.mem_top
      rw [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at ha hb
      rw [ha, hb]⟩
    exact of_subsingleton φ L
  | succ n ih =>
    intro L _ s hs hspan
    rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · subst h
      exact ih L ∅ (by simp) hspan
    have h1 : JointInj φ (LinearMap.range (LinearMap.toSpanSingleton ℤ L x)) :=
      of_cyclic φ hZ hP _ _ (LinearMap.surjective_rangeRestrict _)
    have h3 : JointInj φ (L ⧸ LinearMap.range (LinearMap.toSpanSingleton ℤ L x)) := by
      refine ih _ ((s.erase x).image (LinearMap.range (LinearMap.toSpanSingleton ℤ L x)).mkQ)
        (Finset.card_image_le.trans ?_) ?_
      · have := Finset.card_erase_of_mem hx
        omega
      · rw [Finset.coe_image, ← Submodule.map_span, Submodule.map_mkQ_eq_top,
          ← LinearMap.span_singleton_eq_range, ← Submodule.span_insert, Finset.coe_erase,
          Set.insert_diff_singleton, Set.insert_eq_of_mem (by exact_mod_cast hx), hspan]
    exact of_exact φ _ _ (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ _)
      (Submodule.mkQ_surjective _) h1 h3

theorem of_all [Module.Flat ℤ A] [∀ i, Module.Flat ℤ (B i)] (hZ : JointInj φ ℤ)
    (hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p)) (L : Type) [AddCommGroup L] :
    JointInj φ L := by
  intro h hh
  obtain ⟨L0, hfin, hsub⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite {h} (Set.finite_singleton h)
  obtain ⟨s, hs⟩ := hfin.fg_top
  have h0 : JointInj φ L0 := of_fg φ hZ hP s.card L0 s le_rfl hs
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hsub (Set.mem_singleton h))
  exact zero_of_mem_range φ L0.subtype (Submodule.injective_subtype _) h0 h ⟨y, hy⟩ hh

end GlobalTheory.TensorDevissage

namespace GlobalTheory

open GlobalTheory.TensorDevissage in

theorem jointInj_tensor_of_rat_and_zmod : ∀ (N : ℕ) (I A : Type) [CommRing A] (B : I → Type) [∀ i, CommRing (B i)] (φ : ∀ i, A →+* B i),
    Module.Flat ℤ A → (∀ i, Module.Flat ℤ (B i)) → IsUnit ((N : ℤ) : A) →
    (N ≠ 0 → ∀ h : A ⊗[ℤ] ℚ, (∀ i, LinearMap.rTensor ℚ (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ h : A ⊗[ℤ] ZMod p,
      (∀ i, LinearMap.rTensor (ZMod p) (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    ∀ (L : Type) [AddCommGroup L] (h : A ⊗[ℤ] L),
      (∀ i, LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0 := by
  intro N I A _ B _ φ hA hB hN hQ hp L _ h hh
  haveI := hA
  haveI := hB
  by_cases hN0 : N = 0
  · subst hN0
    haveI : Subsingleton A := by
      have : IsUnit (0 : A) := by simpa using hN
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp this)
    exact all_zero_of_subsingleton' h
  have hZ : JointInj φ ℤ :=
    of_injective φ (Int.castAddHom ℚ).toIntLinearMap Int.cast_injective (hQ hN0)
  have hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p) := by
    intro p hpp
    by_cases hpN : p ∣ N
    · intro x _
      have hkill : ∀ y : A ⊗[ℤ] ZMod p, (N : ℤ) • y = 0 := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a z =>
          rw [← TensorProduct.tmul_smul, zsmul_eq_mul, Int.cast_natCast]
          obtain ⟨c, rfl⟩ := hpN
          rw [Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul, tmul_zero]
        | add y1 y2 h1 h2 => rw [smul_add, h1, h2, add_zero]
      obtain ⟨u, hu⟩ := hN
      have hx : x = ((u⁻¹ : Aˣ) : A) • (((N : ℤ) : A) • x) := by
        rw [smul_smul, ← hu, Units.inv_mul, one_smul]
      rw [hx, Int.cast_smul_eq_zsmul, hkill, smul_zero]
    · exact hp p hpp hpN
  exact of_all φ hZ hP L h hh

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_rational_injectivity : ∀ (N : ℕ) (I A : Type) [CommRing A] (B : I → Type) [∀ i, CommRing (B i)] (φ : ∀ i, A →+* B i),
    Module.Flat ℤ A → (∀ i, Module.Flat ℤ (B i)) → IsUnit ((N : ℤ) : A) →
    (N ≠ 0 → ∀ h : A ⊗[ℤ] ℚ, (∀ i, LinearMap.rTensor ℚ (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ h : A ⊗[ℤ] ZMod p,
      (∀ i, LinearMap.rTensor (ZMod p) (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    ∀ (L : Type) [AddCommGroup L] (h : A ⊗[ℤ] L),
      (∀ i, LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0 := by
  atlas_forward_decl GlobalTheory.jointInj_tensor_of_rat_and_zmod
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem flat_and_isUnit_sections_of_flat_over_away :
    ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))), Flat s →
    ∀ (W : M.Opens), IsAffineOpen W → Module.Flat ℤ Γ(M, W) ∧ IsUnit ((N : ℤ) : Γ(M, W)) := by
  intro N M s hs W hW
  have htop : IsAffineOpen (⊤ : (Sp (Localization.Away (N : ℤ))).Opens) := isAffineOpen_top _
  have hfl : RingHom.Flat (s.appLE ⊤ W le_top).hom :=
    HasRingHomProperty.appLE (P := @Flat) (Q := RingHom.Flat) s hs ⟨⊤, htop⟩ ⟨W, hW⟩ le_top
  let φ : Localization.Away (N : ℤ) →+* Γ(M, W) :=
    (s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (N : ℤ)))).inv.hom
  have hφ : RingHom.Flat φ := by
    refine RingHom.Flat.comp ?_ hfl
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have hloc : RingHom.Flat (algebraMap ℤ (Localization.Away (N : ℤ))) := by
    rw [RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat _ (Submonoid.powers (N : ℤ))
  have hcomp : RingHom.Flat (φ.comp (algebraMap ℤ (Localization.Away (N : ℤ)))) := hloc.comp hφ
  have heq : φ.comp (algebraMap ℤ (Localization.Away (N : ℤ))) = algebraMap ℤ Γ(M, W) :=
    Subsingleton.elim _ _
  rw [heq, RingHom.flat_algebraMap_iff] at hcomp
  refine ⟨hcomp, ?_⟩
  have hu : IsUnit (algebraMap ℤ (Localization.Away (N : ℤ)) (N : ℤ)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have := hu.map φ
  simpa [map_intCast] using this

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_affine_open_units : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))), Flat s →
    ∀ (W : M.Opens), IsAffineOpen W → Module.Flat ℤ Γ(M, W) ∧ IsUnit ((N : ℤ) : Γ(M, W)) := by
  first | exact @GlobalTheory.flat_and_isUnit_sections_of_flat_over_away | exact GlobalTheory.flat_and_isUnit_sections_of_flat_over_away | (intros; apply GlobalTheory.flat_and_isUnit_sections_of_flat_over_away <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreRing

variable (R A K : Type) [CommRing R] [CommRing A] [CommRing K] [Algebra R A] [Algebra R K]
  (hR : ∀ f g : R →+* A ⊗[ℤ] K, f = g)

def inclK : K →ₐ[R] A ⊗[ℤ] K :=
  { (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := K)).toRingHom with
    commutes' := fun r => by
      have h : ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := K)).toRingHom.comp (algebraMap R K)) =
          algebraMap R (A ⊗[ℤ] K) :=
        hR _ _
      exact RingHom.congr_fun h r }

def toR : A ⊗[ℤ] K →+* A ⊗[R] K :=
  (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := K)).toIntAlgHom
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := K)).toRingHom.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

def ofR : A ⊗[R] K →+* A ⊗[ℤ] K :=
  (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (R := ℤ) (S := R) (A := A) (B := K))
    (inclK R A K hR) (fun _ _ => Commute.all _ _)).toRingHom

lemma toR_tmul (a : A) (k : K) : toR R A K (a ⊗ₜ[ℤ] k) = a ⊗ₜ[R] k := by
  simp [toR, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]

lemma ofR_tmul (a : A) (k : K) : ofR R A K hR (a ⊗ₜ[R] k) = a ⊗ₜ[ℤ] k := by
  simp [ofR, inclK, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.tmul_mul_tmul]

def tensorIntEquiv : A ⊗[ℤ] K ≃+* A ⊗[R] K :=
  RingEquiv.ofRingHom (toR R A K) (ofR R A K hR)
    (by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a k => simp [ofR_tmul, toR_tmul]
      | add x y hx hy => simp only [map_add, RingHom.comp_apply, RingHom.id_apply] at hx hy ⊢; rw [hx, hy])
    (by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a k => simp [ofR_tmul, toR_tmul]
      | add x y hx hy => simp only [map_add, RingHom.comp_apply, RingHom.id_apply] at hx hy ⊢; rw [hx, hy])

lemma tensorIntEquiv_tmul (a : A) (k : K) : tensorIntEquiv R A K hR (a ⊗ₜ[ℤ] k) = a ⊗ₜ[R] k := toR_tmul R A K a k

end GlobalTheory.FibreRing

namespace GlobalTheory.RealMult

theorem fibre_tensor_reduced_minimalPrimes : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (V : M.Opens),
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
      pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) →
    ∀ (K : Type) [Field K], (N : K) ≠ 0 → ∀ (W : M.Opens) (hW : IsAffineOpen W),
      IsReduced (Γ(M, W) ⊗[ℤ] K) ∧ ∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
        hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V := by
  intro N M s V hnorm hcodim K _ hNK W hW
  classical
  have hu : IsUnit (Int.castRingHom K (N : ℤ)) := by
    rw [isUnit_iff_ne_zero]; simpa using hNK
  let φ : Localization.Away (N : ℤ) →+* K := IsLocalization.Away.lift (N : ℤ) hu
  letI : Algebra (Localization.Away (N : ℤ)) K := φ.toAlgebra
  let t : Sp K ⟶ Sp (Localization.Away (N : ℤ)) := spMap φ
  have H : IsPullback (pullback.fst s t) (pullback.snd s t) s
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away (N : ℤ)) K))) :=
    IsPullback.of_hasPullback s t
  letI : Algebra (Localization.Away (N : ℤ)) Γ(M, W) := (DVR.FlatBC.algX s W).toAlgebra
  let U' := pullback.fst s t ⁻¹ᵁ W ⊓ pullback.snd s t ⁻¹ᵁ ⊤
  let E : Γ(M, W) ⊗[ℤ] K ≃+* Γ(pullback s t, U') :=
    (GlobalTheory.FibreRing.tensorIntEquiv (Localization.Away (N : ℤ)) Γ(M, W) K
      (fun f g => IsLocalization.ringHom_ext (Submonoid.powers (N : ℤ)) (RingHom.ext_int _ _))).trans
      (DVR.FlatBC.eTens s (pullback.snd s t) (pullback.fst s t) H W hW)
  have hE : ∀ a, E (a ⊗ₜ[ℤ] 1) = ((pullback.fst s t).appLE W U' inf_le_left).hom a := by
    intro a
    simp only [E, RingEquiv.trans_apply, GlobalTheory.FibreRing.tensorIntEquiv_tmul]
    erw [DVR.FlatBC.eTens_tmul]
    rw [map_one, _root_.mul_one]
  have hU' : IsAffineOpen U' := by
    have e : U' = pullback.fst s t ⁻¹ᵁ W := by simp [U']
    rw [e]
    haveI : IsAffineHom (pullback.fst s t) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback s t).flip inferInstance
    exact hW.preimage _
  have hst := hnorm K t
  haveI : ∀ y : ↥(pullback s t), _root_.IsReduced ((pullback s t).presheaf.stalk y) := fun y => by
    haveI := (hst y).1; infer_instance
  haveI : IsReduced (pullback s t) := isReduced_of_isReduced_stalk _
  refine ⟨isReduced_of_injective E.toRingHom E.injective, ?_⟩
  intro q hq
  haveI : q.IsPrime := hq.1.1
  let q' : Ideal Γ(pullback s t, U') := q.comap E.symm.toRingHom
  haveI hq'p : q'.IsPrime := Ideal.comap_isPrime _ _
  have hq' : q' ∈ minimalPrimes Γ(pullback s t, U') := by
    refine ⟨⟨hq'p, bot_le⟩, fun p hp hle => ?_⟩
    haveI : p.IsPrime := hp.1
    have h1 : p.comap E.toRingHom ≤ q := by
      intro x hx
      have := hle hx
      simpa [q'] using this
    have h2 := hq.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ h1
    intro x hx
    have h3 : E.symm x ∈ p.comap E.toRingHom := h2 hx
    rw [Ideal.mem_comap] at h3
    simpa using h3
  let y' : PrimeSpectrum Γ(pullback s t, U') := ⟨q', hq'p⟩
  have hmem : hU'.fromSpec y' ∈ U' := by
    have h := hU'.range_fromSpec
    show hU'.fromSpec y' ∈ (U' : Set ↥(pullback s t))
    rw [← h]; exact ⟨y', rfl⟩
  letI algSt : Algebra Γ(pullback s t, U') ((pullback s t).presheaf.stalk (hU'.fromSpec y')) :=
    TopCat.Presheaf.algebra_section_stalk (pullback s t).presheaf ⟨hU'.fromSpec y', hmem⟩
  have hst' := hU'.isLocalization_stalk' y' hmem
  have hd := @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q' _
    ((pullback s t).presheaf.stalk (hU'.fromSpec y')) _ algSt hst'
  have hdim : ringKrullDim ((pullback s t).presheaf.stalk (hU'.fromSpec y')) = 0 := by
    rw [hd,
      Ideal.height_eq_zero_iff.mpr hq']
    rfl
  have hV : pullback.fst s t (hU'.fromSpec y') ∈ V := by
    by_contra hn
    have := hcodim K t _ hn
    rw [hdim] at this
    exact absurd this (by decide)
  have e := IsAffineOpen.SpecMap_appLE_fromSpec (pullback.fst s t) hW hU' inf_le_left
  have hpt : pullback.fst s t (hU'.fromSpec y') =
      hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K))
        ⟨q, hq.1.1⟩) := by
    change (hU'.fromSpec ≫ pullback.fst s t) y' = _
    rw [← e]
    change hW.fromSpec ((Spec.map ((pullback.fst s t).appLE W U' inf_le_left)) y') = _
    congr 1
    apply PrimeSpectrum.ext
    ext x
    show x ∈ Ideal.comap ((pullback.fst s t).appLE W U' inf_le_left).hom q' ↔ _
    simp only [Ideal.mem_comap, q', PrimeSpectrum.comap_asIdeal]
    rw [← hE]
    simp
  rw [← hpt]; exact hV

end GlobalTheory.RealMult
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_fibres_char_unit : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (V : M.Opens),
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
      pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) →
    ∀ (K : Type) [Field K], (N : K) ≠ 0 → ∀ (W : M.Opens) (hW : IsAffineOpen W),
      IsReduced (Γ(M, W) ⊗[ℤ] K) ∧ ∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
        hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V := by
  atlas_forward_decl GlobalTheory.RealMult.fibre_tensor_reduced_minimalPrimes
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_restrictions_zero_of_minimalPrimes_over :
    ∀ (M : Scheme.{0}) (V W : M.Opens) (hW : IsAffineOpen W) (K : Type) [Field K],
    IsReduced (Γ(M, W) ⊗[ℤ] K) →
    (∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
      hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V) →
    ∀ (h : Γ(M, W) ⊗[ℤ] K),
    (∀ (W' : M.Opens), IsAffineOpen W' → ∀ hW' : W' ≤ W ⊓ V,
      LinearMap.rTensor K (M.presheaf.map (homOfLE (hW'.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap h = 0) →
    h = 0 := by
  intro M V W hW K _ hred hV h hh
  have key : ∀ q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K), h ∈ q := by
    intro q hq
    haveI : q.IsPrime := hq.1.1
    set p : PrimeSpectrum Γ(M, W) := PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom
      (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩ with hp
    have hxW : hW.fromSpec p ∈ W := by
      have h1 : hW.fromSpec p ∈ Set.range hW.fromSpec := ⟨p, rfl⟩
      rwa [hW.range_fromSpec] at h1
    have hxV : hW.fromSpec p ∈ V := hV q hq
    obtain ⟨f, hfle, hxf⟩ := hW.exists_basicOpen_le (V := W ⊓ V) ⟨hW.fromSpec p, hxW, hxV⟩ hxW
    have hfp : f ⊗ₜ[ℤ] (1 : K) ∉ q := by
      have h1 : p ∈ hW.fromSpec ⁻¹ᵁ M.basicOpen f := hxf
      rw [hW.fromSpec_preimage_basicOpen] at h1
      exact h1
    have h0 := hh (M.basicOpen f) (hW.basicOpen f) hfle
    let φ : Γ(M, W) →+* Γ(M, M.basicOpen f) :=
      (M.presheaf.map (homOfLE (hfle.trans inf_le_left)).op).hom
    letI : Algebra Γ(M, W) Γ(M, M.basicOpen f) := φ.toAlgebra
    haveI : IsLocalization.Away f Γ(M, M.basicOpen f) := hW.isLocalization_basicOpen f
    let g0 : Γ(M, W) →+* Localization.AtPrime q :=
      (algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q)).comp
        Algebra.TensorProduct.includeLeftRingHom
    have hu : IsUnit (g0 f) :=
      IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q) ⟨f ⊗ₜ[ℤ] (1 : K), hfp⟩
    let g1 : Γ(M, M.basicOpen f) →+* Localization.AtPrime q := IsLocalization.Away.lift f hu
    let g2 : K →+* Localization.AtPrime q :=
      (algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q)).comp
        Algebra.TensorProduct.includeRight.toRingHom
    let G : Γ(M, M.basicOpen f) ⊗[ℤ] K →ₐ[ℤ] Localization.AtPrime q :=
      Algebra.TensorProduct.lift (⟨g1, fun n => by simp⟩ : Γ(M, M.basicOpen f) →ₐ[ℤ] Localization.AtPrime q)
        (⟨g2, fun n => by simp⟩ : K →ₐ[ℤ] Localization.AtPrime q) (fun _ _ => Commute.all _ _)
    have hG : ∀ z : Γ(M, W) ⊗[ℤ] K,
        G (LinearMap.rTensor K φ.toAddMonoidHom.toIntLinearMap z) =
          algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a k =>
        rw [LinearMap.rTensor_tmul]
        have e1 : g1 (φ a) = g0 a := IsLocalization.Away.lift_eq f hu a
        change g1 (φ a) * g2 k = _
        rw [e1]
        simp only [g0, g2, RingHom.comp_apply, ← map_mul]
        congr 1
        simp
      | add x y hx hy => simp only [map_add, hx, hy]
    have hz : algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q) h = 0 := by
      rw [← hG h]
      change G (LinearMap.rTensor K φ.toAddMonoidHom.toIntLinearMap h) = 0
      rw [h0, map_zero]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ h).1 hz
    have hmq : (m : Γ(M, W) ⊗[ℤ] K) * h ∈ q := by rw [hm]; exact q.zero_mem
    exact (‹q.IsPrime›.mem_or_mem hmq).resolve_left m.2
  have hrad : h ∈ (⊥ : Ideal (Γ(M, W) ⊗[ℤ] K)).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr key
  obtain ⟨n, hn⟩ := hrad
  exact IsNilpotent.eq_zero ⟨n, Ideal.mem_bot.mp hn⟩

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_tensor_vanishing_local : ∀ (M : Scheme.{0}) (V W : M.Opens) (hW : IsAffineOpen W) (K : Type) [Field K],
    IsReduced (Γ(M, W) ⊗[ℤ] K) →
    (∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
      hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V) →
    ∀ (h : Γ(M, W) ⊗[ℤ] K),
    (∀ (W' : M.Opens), IsAffineOpen W' → ∀ hW' : W' ≤ W ⊓ V,
      LinearMap.rTensor K (M.presheaf.map (homOfLE (hW'.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap h = 0) →
    h = 0 := by
  atlas_forward_decl GlobalTheory.affine_restrictions_zero_of_minimalPrimes_over
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem rTensor_eq_zero_of_restrict_affine_inf : ∀ (N : ℕ) (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (N : ℤ))) (V : M.Opens), Flat s →
  (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback s t)) →
  (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback s t)),
    pullback.fst s t y ∉ V → 2 ≤ ringKrullDim ((pullback s t).presheaf.stalk y)) →
  ∀ (W : M.Opens), IsAffineOpen W → ∀ (L : Type) [AddCommGroup L] (h : Γ(M, W) ⊗[ℤ] L),
    (∀ (W' : M.Opens), IsAffineOpen W' → ∀ hW' : W' ≤ W ⊓ V,
      LinearMap.rTensor L (M.presheaf.map (homOfLE (hW'.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap h = 0) →
    h = 0 := by
  intro N M s V hs hn hc W hW L _ h hh
  have hA := GlobalTheory.T.flat_affine_open_units N M s hs W hW
  exact GlobalTheory.T.tensor_rational_injectivity N {W' : M.Opens // IsAffineOpen W' ∧ W' ≤ W ⊓ V} Γ(M, W) (fun i => Γ(M, i.1))
    (fun i => (M.presheaf.map (homOfLE (i.2.2.trans inf_le_left)).op).hom) hA.1
    (fun i => (GlobalTheory.T.flat_affine_open_units N M s hs i.1 i.2.1).1) hA.2
    (fun hN0 h' hh' => by
      obtain ⟨h1, h2⟩ := GlobalTheory.T.normal_fibres_char_unit N M s V hn hc ℚ (by exact_mod_cast hN0) W hW
      exact GlobalTheory.T.rational_tensor_vanishing_local M V W hW ℚ h1 h2 h' (fun W' hW' hle => hh' ⟨W', hW', hle⟩))
    (fun p hp hpN h' hh' => by
      haveI := Fact.mk hp
      obtain ⟨h1, h2⟩ := GlobalTheory.T.normal_fibres_char_unit N M s V hn hc (ZMod p) (by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpN) W hW
      exact GlobalTheory.T.rational_tensor_vanishing_local M V W hW (ZMod p) h1 h2 h' (fun W' hW' hle => hh' ⟨W', hW', hle⟩))
    L h (fun i => hh i.1 i.2.1 i.2.2)

end GlobalTheory.RealMult
end
