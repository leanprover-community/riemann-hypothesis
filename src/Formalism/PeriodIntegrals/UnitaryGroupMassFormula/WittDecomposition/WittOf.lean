import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Anisotropic

section
namespace PI.Witt

variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]

theorem nondeg_extend (h1 : OneVector) (h2 : Anisotropic) [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x) :
    ∀ (n : ℕ) (U : Submodule K V), Module.finrank K U = n →
      (∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0) →
      ∀ f : U →ₗ[K] V, (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ (∀ x : U, g x = f x) ∧
        ∀ z, (∀ u : U, B (u : V) z = 0) → (∀ u : U, B (f u) z = 0) → g z = z := by
  intro n
  refine Nat.strong_induction_on n (fun n ih => ?_)
  intro U hU hnd f hf
  by_cases hex : ∃ x ∈ U, ∃ y ∈ U, B x y ≠ 0
  · obtain ⟨u, hu, hBu⟩ := h2 K V B hB U hex
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ :=
      h1 K V B hB u (f ⟨u, hu⟩) (hf ⟨u, hu⟩ ⟨u, hu⟩).symm hBu
    have hsym : ∀ a b, B (g₁.symm a) b = B a (g₁ b) := by
      intro a b
      rw [← hg₁ (g₁.symm a) b, LinearEquiv.apply_symm_apply]
    have hsym₂ : ∀ a b, B (g₁.symm a) (g₁.symm b) = B a b := by
      intro a b
      rw [hsym, LinearEquiv.apply_symm_apply]
    let U' : Submodule K V := U ⊓ LinearMap.ker (B u)
    have hle : U' ≤ U := inf_le_left
    have hker : ∀ w ∈ U', B u w = 0 := fun w hw => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2
    have hwu : ∀ w ∈ U', B w u = 0 := by
      intro w hw
      rw [← hB u w, hker w hw, star_zero]
    have hproj : ∀ y ∈ U, y - (B u y / B u u) • u ∈ U' := by
      intro y hy
      refine Submodule.mem_inf.mpr ⟨U.sub_mem hy (U.smul_mem _ hu), LinearMap.mem_ker.mpr ?_⟩
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hBu, sub_self]
    have hlt : Module.finrank K U' < n := by
      rw [← hU]
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle fun heq => hBu ?_)
      have hu' : u ∈ U' := by rw [heq]; exact hu
      exact hker u hu'
    have hnd' : ∀ x ∈ U', (∀ y ∈ U', B x y = 0) → x = 0 := by
      intro x hx hxy
      refine hnd x (hle hx) fun y hy => ?_
      have h := hxy _ (hproj y hy)
      rw [map_sub, map_smul, hwu x hx, smul_zero, sub_zero] at h
      exact h
    let f' : U' →ₗ[K] V := g₁.symm.toLinearMap ∘ₗ f ∘ₗ Submodule.inclusion hle
    have hf'x : ∀ x : U', f' x = g₁.symm (f (Submodule.inclusion hle x)) := fun x => rfl
    have hf' : ∀ x y : U', B (f' x) (f' y) = B x y := by
      intro x y
      rw [hf'x, hf'x, hsym₂, hf]
      rfl
    obtain ⟨g₂, hg₂, hg₂f, hg₂fix⟩ := ih _ hlt U' rfl hnd' f' hf'
    have hg₂u : g₂ u = u := by
      refine hg₂fix u (fun w => hwu w w.2) fun w => ?_
      rw [hf'x, hsym, hg₁u, hf]
      exact hwu w w.2
    refine ⟨g₂.trans g₁, fun x y => ?_, fun x => ?_, fun z hz₁ hz₂ => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      rw [hg₁, hg₂]
    · obtain ⟨c, hc⟩ : ∃ c : K, c = B u x / B u u := ⟨_, rfl⟩
      have hmem : (x : V) - c • u ∈ U' := hc ▸ hproj x x.2
      let x' : U' := ⟨_, hmem⟩
      have hxv : (x : V) = c • u + (x' : V) := by simp [x']
      have hxU : x = c • (⟨u, hu⟩ : U) + Submodule.inclusion hle x' := Subtype.ext (by simp [x'])
      calc (g₂.trans g₁) (x : V) = g₁ (g₂ (c • u + (x' : V))) := by rw [← hxv]; rfl
        _ = c • g₁ u + g₁ (f' x') := by
            rw [map_add, map_smul, hg₂u, hg₂f x', map_add, map_smul]
        _ = f x := by
            rw [hg₁u, hf'x, LinearEquiv.apply_symm_apply]
            conv_rhs => rw [hxU]
            rw [map_add, map_smul]
    · have hg₁z : g₁ z = z := hg₁fix z (hz₁ ⟨u, hu⟩) (hz₂ ⟨u, hu⟩)
      have hg₂z : g₂ z = z := by
        refine hg₂fix z (fun w => hz₁ (Submodule.inclusion hle w)) fun w => ?_
        rw [hf'x, hsym, hg₁z]
        exact hz₂ _
      show g₁ (g₂ z) = z
      rw [hg₂z, hg₁z]
  · push Not at hex
    refine ⟨LinearEquiv.refl K V, fun x y => rfl, fun x => ?_, fun z _ _ => rfl⟩
    have hx0 : x = 0 := Subtype.ext (hnd x x.2 (hex x x.2))
    subst hx0
    simp

end PI.Witt
end

section
namespace PI.Witt

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem riesz [FiniteDimensional K V] (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (φ : V →ₗ[K] K) : ∃ v, ∀ z, B v z = φ z := by
  classical
  let b := Module.finBasis K V
  rcases isEmpty_or_nonempty (Fin (Module.finrank K V)) with hE | hNE
  · refine ⟨0, fun z => ?_⟩
    have hz : z = 0 := by rw [← b.sum_repr z]; simp
    simp [hz]
  have hli : LinearIndependent K (fun i => B (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : B (∑ j, star (g j) • b j) = 0 := by
      rw [map_sum]
      simp only [map_smulₛₗ, starRingEnd_apply, star_star]
      exact hg
    have h2 : ∑ j, star (g j) • b j = 0 := hnd _ (fun y => by rw [h1, LinearMap.zero_apply])
    have h3 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h2 i
    exact star_eq_zero.mp h3
  have hcard : Fintype.card (Fin (Module.finrank K V)) = Module.finrank K (V →ₗ[K] K) := by
    rw [Fintype.card_fin]; exact (Subspace.dual_finrank_eq).symm
  let b' := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨∑ i, star (b'.repr φ i) • b i, fun z => ?_⟩
  conv_rhs => rw [← b'.sum_repr φ]
  rw [map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, LinearMap.smul_apply, starRingEnd_apply, star_star,
    coe_basisOfLinearIndependentOfCardEqFinrank]

end PI.Witt
end

section
namespace PI.Witt

variable {K V : Type} [Field K] [StarRing K] [CharZero K] [AddCommGroup V] [Module K V]

theorem expand (B : V →ₗ⋆[K] V →ₗ[K] K) (p u u' : V) (c c' : K) :
    B (u + c • p) (u' + c' • p) =
      B u u' + c' * B u p + star c * B p u' + star c * c' * B p p := by
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply]
  generalize B u u' = A1
  generalize B u p = A2
  generalize B p u' = A3
  generalize B p p = A4
  generalize star c = s
  ring

theorem partner (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x) (r p0 : V)
    (hrr : B r r = 0) (h1 : B p0 r = 1) :
    ∃ p, B p p = 0 ∧ ∀ u, B r u = 0 → B p u = B p0 u := by
  set a := B p0 p0 with ha_def
  have ha : star a = a := hB p0 p0
  have hr1 : B r p0 = 1 := by rw [← hB p0 r, h1, star_one]
  have hc : star (-(a / 2)) = -(a / 2) := by
    rw [star_neg, star_div₀, ha, star_ofNat]
  refine ⟨p0 + (-(a / 2)) • r, ?_, ?_⟩
  · rw [expand B r p0 p0 (-(a / 2)) (-(a / 2)), h1, hr1, hrr, hc]
    ring
  · intro u hu
    simp [hu]

theorem enlarge_step [FiniteDimensional K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (hB : ∀ x y, star (B x y) = B y x) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (U : Submodule K V) (f : U →ₗ[K] V) (hinj : Function.Injective f)
    (hf : ∀ x y : U, B (f x) (f y) = B x y)
    (r : V) (hrU : r ∈ U) (hr0 : r ≠ 0) (hr : ∀ u ∈ U, B r u = 0) :
    ∃ (U' : Submodule K V) (hlt : U < U') (f' : U' →ₗ[K] V), Function.Injective f' ∧
      (∀ x y : U', B (f' x) (f' y) = B x y) ∧ ∀ u : U, f' ⟨u, hlt.le u.2⟩ = f u := by
  classical

  obtain ⟨φ0, hφ0⟩ : ∃ φ : Module.Dual K V, φ r ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr0 ((Module.forall_dual_apply_eq_zero_iff K r).1 h)
  set φ : V →ₗ[K] K := (φ0 r)⁻¹ • φ0 with hφdef
  have hφr : φ r = 1 := by simp [hφdef, hφ0]
  obtain ⟨p0, hp0⟩ := riesz B hB hnd φ
  obtain ⟨p, hpp, hpU'⟩ := partner B hB r p0 (hr r hrU) (by rw [hp0, hφr])
  have hpU : ∀ u ∈ U, B p u = φ u := fun u hu => by rw [hpU' u (hr u hu), hp0]

  set e := LinearEquiv.ofInjective f hinj with he
  obtain ⟨χ, hχ⟩ := LinearMap.exists_extend ((φ.comp U.subtype).comp e.symm.toLinearMap)
  have hχf : ∀ u : U, χ (f u) = φ u := fun u => by
    have := LinearMap.congr_fun hχ (e u)
    simpa [he] using this
  obtain ⟨q0, hq0⟩ := riesz B hB hnd χ
  set r' : U := ⟨r, hrU⟩ with hr'
  have hφr' : φ (r' : V) = 1 := hφr
  have hfr : ∀ u : U, B (f r') (f u) = 0 := fun u => by rw [hf]; exact hr u u.2
  obtain ⟨q, hqq, hqU'⟩ := partner B hB (f r') q0 (hfr r') (by rw [hq0, hχf]; exact hφr')
  have hqU : ∀ u : U, B q (f u) = φ u := fun u => by rw [hqU' _ (hfr u), hq0, hχf]

  set Φ : (U × K) →ₗ[K] V := U.subtype.coprod (LinearMap.toSpanSingleton K V p) with hΦdef
  set Ψ : (U × K) →ₗ[K] V := f.coprod (LinearMap.toSpanSingleton K V q) with hΨdef
  have hΦ : ∀ a : U × K, Φ a = (a.1 : V) + a.2 • p := fun a => by simp [hΦdef]
  have hΨ : ∀ a : U × K, Ψ a = f a.1 + a.2 • q := fun a => by simp [hΨdef]
  have hpnot : p ∉ U := by
    intro hp
    have h1 : B r p = 0 := hr p hp
    have h2 : B p r = 1 := by rw [hpU r hrU, hφr]
    have h3 := hB p r
    rw [h2, h1, star_one] at h3
    exact one_ne_zero h3
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, c⟩ h
    rw [hΦ] at h
    have hc : c = 0 := by
      by_contra hc
      apply hpnot
      have h' : c • p = -(u : V) := by
        rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h
      have : p = c⁻¹ • -(u : V) := by rw [← h', smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact U.smul_mem _ (U.neg_mem u.2)
    subst hc
    refine Prod.ext ?_ rfl
    ext
    simpa using h
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, c⟩ h
    rw [hΨ] at h
    have hc : c = 0 := by
      have h4 := congrArg (B (f r')) h
      rw [map_add, map_smul, hfr u, ← hB q (f r'), hqU r', hφr', map_zero] at h4
      simpa using h4
    subst hc
    have hu : f u = 0 := by simpa using h
    have hu0 : u = 0 := hinj (by rw [hu, map_zero])
    subst hu0
    rfl
  have hlt : U < LinearMap.range Φ := by
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun u hu => ⟨(⟨u, hu⟩, 0), by simp [hΦ]⟩, p, ⟨(0, 1), by simp [hΦ]⟩, hpnot⟩
  set eΦ := LinearEquiv.ofInjective Φ hΦinj with heΦ
  have hval : ∀ x : LinearMap.range Φ, (x : V) = Φ (eΦ.symm x) := fun x =>
    (congrArg Subtype.val (eΦ.apply_symm_apply x)).symm.trans (LinearEquiv.ofInjective_apply _ _)
  refine ⟨LinearMap.range Φ, hlt, Ψ.comp eΦ.symm.toLinearMap, hΨinj.comp eΦ.symm.injective, ?_, ?_⟩
  · intro x y
    rw [hval x, hval y]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    generalize eΦ.symm x = a
    generalize eΦ.symm y = b
    obtain ⟨u, c⟩ := a
    obtain ⟨u', c'⟩ := b
    rw [hΨ, hΨ, hΦ, hΦ]
    dsimp only
    rw [expand B q (f u) (f u') c c', expand B p (u : V) (u' : V) c c', hf, hqq, hpp,
      ← hB q (f u), ← hB p (u : V), hqU u, hqU u', hpU _ u.2, hpU _ u'.2]
  · intro u
    have h5 : eΦ.symm ⟨u, hlt.le u.2⟩ = (u, 0) := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      rw [LinearEquiv.ofInjective_apply, hΦ]
      simp
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h5, hΨ, zero_smul, add_zero]

end PI.Witt
end

section
namespace PI.Witt

theorem witt_of (h1 : OneVector) (h2 : Anisotropic) : PI.WittExtension := by
  intro K V _ _ _ _ _ _ B hB hnd
  have key : ∀ (m : ℕ) (U : Submodule K V), Module.finrank K V - Module.finrank K U = m →
      ∀ f : U →ₗ[K] V, Function.Injective f → (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ x : U, g x = f x := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro U hm f hinj hf
    by_cases hU : ∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0
    · obtain ⟨g, hg, hge, -⟩ := nondeg_extend h1 h2 B hB _ U rfl hU f hf
      exact ⟨g, hg, hge⟩
    · push Not at hU
      obtain ⟨r, hrU, hr, hr0⟩ := hU
      obtain ⟨U', hlt, f', hinj', hf', hext⟩ := enlarge_step B hB hnd U f hinj hf r hrU hr0 hr
      have h3 : Module.finrank K U < Module.finrank K U' := Submodule.finrank_lt_finrank_of_lt hlt
      have h4 : Module.finrank K U' ≤ Module.finrank K V := Submodule.finrank_le U'
      obtain ⟨g, hg, hge⟩ := ih (Module.finrank K V - Module.finrank K U') (by omega) U' rfl f' hinj' hf'
      refine ⟨g, hg, fun x => ?_⟩
      rw [← hext x, ← hge]
  intro U f hinj hf
  exact key _ U rfl f hinj hf

end PI.Witt
end
