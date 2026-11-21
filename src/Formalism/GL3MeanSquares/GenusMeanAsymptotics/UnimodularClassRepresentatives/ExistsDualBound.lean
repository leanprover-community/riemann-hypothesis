import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem ι_pow_smul (π : 𝓞 F) (r : ℕ) (w : V) :
    ι (π ^ r) • w = algebraMap F K (π : F) ^ r • w := by
  rw [← algebraMap_smul K (ι (π ^ r)) w]
  congr 1
  rw [map_pow, map_pow]
  rfl

theorem exists_pow_smul_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) (w : V) :
    ∃ n : ℕ, algebraMap F K (π : F) ^ n • w ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnw⟩ := Formalism.HermitianLatticesTheory.traceReal_mult A₀ hA₀ w
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u, hu, ?_⟩⟩
  have : ι u • (algebraMap F K (π : F) ^ r • w) = ι v • (n • w) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n w, smul_smul, ← map_mul, mul_comm v, ← hv, map_mul,
      mul_smul, ι_pow_smul]
  rw [this]
  exact A₀.smul_mem _ hnw

theorem exists_smul_le {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hA₀ hB₀
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 A₀ y).1 hy
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu ht, ?_⟩
  have : ι (u * t) • (algebraMap F K (π : F) ^ r • y) = ι v • (n • (ι t • y)) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n, ← ι_pow_smul, smul_smul, smul_smul, smul_smul,
      ← map_mul, ← map_mul, ← map_mul]
    congr 2
    linear_combination t * hv
  rw [this]
  exact B₀.smul_mem _ (hnx _ hty)

theorem eq_zero_of_forall_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {v : V} (hv : ∀ j : ℕ, v ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    v = 0 := by
  have := h𝔭.isPrime
  have h0 : v ∈ locF 𝔭 A₀ := by simpa [pow_zero_smul] using hv 0
  obtain ⟨t, ht, htv⟩ := (LocalSpans.mem_locF 𝔭 A₀ v).1 h0
  have h1 : ∀ j : ℕ, ι t • v ∈ extP K 𝔭 ^ j • A₀ := fun j =>
    localizedQuotients.mem_smul_of_mem_smul_locF h𝔭 A₀ j htv (Submodule.smul_mem _ _ (hv j))
  have : Module.Finite (𝓞 K) ↥A₀ := Module.Finite.iff_fg.2 hA₀.fg
  have h2 : (⟨ι t • v, htv⟩ : ↥A₀) ∈ (⨅ i : ℕ, extP K 𝔭 ^ i • ⊤ : Submodule (𝓞 K) ↥A₀) := by
    rw [Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_smul_top_iff]
    exact h1 j
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (extP K 𝔭) _).1 h2
  have hr' : (r : 𝓞 K) • (ι t • v) = ι t • v := congrArg Subtype.val hr
  have hr1 : (r : 𝓞 K) ≠ 1 := by
    intro e
    have h3 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := by rw [pow_one, ← e]; exact r.2
    have h4 : (1 : 𝓞 F) ∈ 𝔭 ^ 1 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by simpa using h3)
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h4))
  have h5 : (algebraMap (𝓞 K) K ((r : 𝓞 K) - 1) * algebraMap F K (t : F)) • v = 0 := by
    rw [mul_smul, ← MeanB.algebraMap_comp, algebraMap_smul, algebraMap_smul, sub_smul, hr', one_smul,
      sub_self]
  rcases smul_eq_zero.1 h5 with h6 | h6
  · rcases mul_eq_zero.1 h6 with h7 | h7
    · exact absurd (sub_eq_zero.1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 h7)) hr1
    · exact absurd h7 (notMem_ne_zero ht)
  · exact h6

theorem unif_pow_mem_pK_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ : π ∈ 𝔭) (k : ℕ) :
    algebraMap F K (π : F) ^ k ∈ pK K 𝔭 0 := by
  refine ⟨1, Submonoid.one_mem _, ?_⟩
  rw [one_smul]
  refine ⟨ι (π ^ k), by simp, ?_⟩
  show algebraMap (𝓞 K) K (ι (π ^ k)) = _
  rw [map_pow, map_pow]
  rfl

theorem mem_of_add_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) (j : ℕ) {w : V}
    (hw : w + D w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) : w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  set p : K := algebraMap F K (π : F) with hp
  have key : ∀ w : V, w + D w ∈ locF 𝔭 A₀ → w ∈ locF 𝔭 A₀ := by
    intro w hw
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hA₀ h𝔭 hπ w
    induction n with
    | zero => simpa using hn
    | succ n ih =>
      apply ih
      have h1 : D (p ^ (n + 1) • w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        rw [pow_one]; exact hD _ hn
      have h2 : p ^ (n + 1) • (w + D w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ :=
        (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨p ^ n • (w + D w),
          smul_mem_locF h𝔭 A₀ (unif_pow_mem_pK_zero hπ n) hw, by rw [smul_smul, pow_one, pow_succ']⟩
      have h3 : p ^ (n + 1) • w ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        have := sub_mem h2 h1
        rwa [map_smul, smul_add, add_sub_cancel_right] at this
      obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h3
      have : p ^ n • w = y := by
        apply smul_right_injective V hπ0
        show p • p ^ n • w = p • y
        rw [smul_smul, ← pow_succ', e, pow_one]
      rwa [this]
  obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hw
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨(p ^ j)⁻¹ • w, key _ ?_, ?_⟩
  · rw [map_smul, ← smul_add, e, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hπ0), one_smul]
    exact hy
  · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero j hπ0), one_smul]

theorem exists_equiv_of_mem_endL {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) :
    ∃ X : V ≃ₗ[K] V, (∀ x, X x = x + D x) ∧ X ∈ glSub (locF 𝔭 A₀) := by
  have hinj : Function.Injective (LinearMap.id + D : V →ₗ[K] V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : w + D w = 0 := hw
    exact eq_zero_of_forall_mem hA₀ h𝔭 fun j =>
      mem_of_add_mem hA₀ h𝔭 hD j (by rw [hw']; exact zero_mem _)
  refine ⟨LinearEquiv.ofInjectiveEndo _ hinj, fun x => ?_, ?_⟩
  · rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
  · have hX : ∀ x, LinearEquiv.ofInjectiveEndo _ hinj x = x + D x := fun x => by
      rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
    rw [mem_glSub]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show LinearEquiv.ofInjectiveEndo _ hinj x ∈ _
      rw [hX]
      exact add_mem hx (Submodule.smul_le_right (hD x hx))
    · intro y hy
      refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
      have h1 := hX ((LinearEquiv.ofInjectiveEndo _ hinj).symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      have := mem_of_add_mem hA₀ h𝔭 hD 0 (w := (LinearEquiv.ofInjectiveEndo _ hinj).symm y)
        (by rw [← h1, pow_zero_smul]; exact hy)
      rwa [pow_zero_smul] at this

theorem mem_glSub_of_sub_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {X : V ≃ₗ[K] V}
    (hX : ∀ x ∈ locF 𝔭 A₀, X x - x ∈ extP K 𝔭 • locF 𝔭 A₀) : X ∈ glSub (locF 𝔭 A₀) := by
  obtain ⟨Y, hY, hY'⟩ := exists_equiv_of_mem_endL hA₀ h𝔭
    (D := (X : V →ₗ[K] V) - LinearMap.id) (fun x hx => hX x hx)
  have : X = Y := by
    ext x
    rw [hY]
    simp
  rwa [this]

end Formalism.HermitianLattices.Ext.L3.D2
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) : h.Nondegenerate := by
  have key : ∀ x : V, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h1 := hd x hne φ
    rw [hx, map_zero, Complex.zero_re] at h1
    exact lt_irrefl _ h1
  exact ⟨fun x hx => key x (hx x), fun y hy => key y (hy y)⟩

theorem exists_dual_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ e : ℕ, ∀ (k : ℕ) (x : V), (∀ y ∈ locF 𝔭 A₀, h y x ∈ pK K 𝔭 (k + e)) →
      x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀ := by
  classical
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨b, hb, -⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  have hnd := nondegenerate hd
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis h hnd b
  choose n hn using fun j => exists_pow_smul_mem hA₀ h𝔭 hπ (bs j)
  refine ⟨∑ j, n j, fun k x hx => ?_⟩
  rw [Formalism.HermitianLatticesTheory.dualLattice_expand h hnd b bs hbs x]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨c, hc, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 (hx (b j) (LocF.le_locF 𝔭 A₀ (hb j)))
  rw [e]
  have hle : n j ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2
    ⟨(c * algebraMap F K (π : F) ^ (∑ j, n j - n j)) • (algebraMap F K (π : F) ^ n j • bs j),
      smul_mem_locF h𝔭 A₀ (by simpa using mul_mem_pK h𝔭 hc (unif_pow_mem_pK_zero hπ _)) (hn j), ?_⟩
  rw [smul_smul, smul_smul]
  congr 1
  have : k + ∑ j, n j = k + (∑ j, n j - n j) + n j := by omega
  rw [this, pow_add, pow_add]; ring

theorem exists_endL_le {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, ∀ d : ℕ, endL (locF 𝔭 A₀) (extP K 𝔭 ^ (d + r) • locF 𝔭 A₀) ≤
      endL (locF 𝔭 B₀) (extP K 𝔭 ^ d • locF 𝔭 B₀) := by
  obtain ⟨r1, h1⟩ := exists_smul_le hA₀ hB₀ h𝔭
  obtain ⟨r2, h2⟩ := exists_smul_le hB₀ hA₀ h𝔭
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  refine ⟨r1 + r2, fun d D hD y hy => ?_⟩
  have hy' := h2 ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨y, hy, rfl⟩)
  obtain ⟨z, hz, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 (hD _ hy')
  have hz' := h1 ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨z, hz, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, hz', ?_⟩
  apply smul_right_injective V (pow_ne_zero r2 hπ0)
  show algebraMap F K (π : F) ^ r2 • D y = algebraMap F K (π : F) ^ r2 • _
  rw [← map_smul, e, smul_smul, smul_smul]
  congr 1
  rw [pow_add, pow_add]; ring


theorem nSub_le_sSub (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    nSub (locF 𝔭 A₀) 𝔭 k ≤ sSub h (locF 𝔭 A₀) 𝔭 k := by
  rintro X ⟨hX, hX'⟩
  refine ⟨hX, fun x hx y hy => ?_⟩
  have hx0 : x ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := by rwa [pow_zero_smul]
  have hy0 : y ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := by rwa [pow_zero_smul]
  have e : h (X x) (X y) - h x y = h (X x - x) y + h x (X y - y) + h (X x - x) (X y - y) := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  rw [e]
  refine add_mem (add_mem ?_ ?_) ?_
  · simpa using form_mem_pK hF hA₀i h𝔭 (hX' x hx) hy0
  · simpa using form_mem_pK hF hA₀i h𝔭 hx0 (hX' y hy)
  · exact pK_anti 𝔭 (Nat.le_add_right k k) (form_mem_pK hF hA₀i h𝔭 (hX' x hx) (hX' y hy))

theorem nSub_le_glSub {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 A₀) 𝔭 k ≤ glSub (locF 𝔭 B₀) := by
  obtain ⟨r, hr⟩ := exists_endL_le hA₀ hB₀ h𝔭
  refine ⟨1 + r, fun k hk X hX => mem_glSub_of_sub_mem hB₀ h𝔭 fun y hy => ?_⟩
  have h1 : ((X : V →ₗ[K] V) - LinearMap.id) ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ (1 + r) • locF 𝔭 A₀) :=
    fun x hx => smul_anti 𝔭 _ hk (hX.2 x hx)
  have := hr 1 h1 y hy
  rwa [pow_one] at this

end Formalism.HermitianLattices.Ext.L3.D2
end
end
