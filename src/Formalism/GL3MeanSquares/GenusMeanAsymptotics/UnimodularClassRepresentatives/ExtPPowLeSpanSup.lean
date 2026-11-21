import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountPowSuccInert

section
open Module

set_option linter.deprecated false

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MeanA

theorem exists_mul_sub_one_mem_pow {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t : R}
    (ht : t ∉ 𝔭) (k : ℕ) : ∃ u : R, u * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨(∑ j ∈ Finset.range k, i ^ j) * y, ?_⟩
  have h1 : (∑ j ∈ Finset.range k, i ^ j) * (i - 1) = i ^ k - 1 := geom_sum_mul i k
  have h2 : (∑ j ∈ Finset.range k, i ^ j) * y * t - 1 = -(i ^ k) := by
    linear_combination (∑ j ∈ Finset.range k, i ^ j) * hyi - h1
  rw [h2]
  exact (𝔭 ^ k).neg_mem (Ideal.pow_mem_pow hi k)

theorem mem_pow_of_mul_mem {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t c : R}
    (ht : t ∉ 𝔭) {k : ℕ} (h : t * c ∈ 𝔭 ^ k) : c ∈ 𝔭 ^ k := by
  obtain ⟨u, hu⟩ := exists_mul_sub_one_mem_pow h𝔭 ht k
  have e : c = u * (t * c) - (u * t - 1) * c := by ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ u h) (Ideal.mul_mem_right c _ hu)

variable {R F V : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F] [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  [FiniteDimensional F V]

theorem exists_local_basis (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) :
    ∃ (x : Fin (finrank F V) → M) (s : R), s ∉ 𝔭 ∧ LinearIndependent R x ∧
      ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := by
  have := h𝔭
  let : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  let Q := M ⧸ (𝔭 • ⊤ : Submodule R M)
  have : Module.Finite (R ⧸ 𝔭) Q := Module.Finite.of_restrictScalars_finite R _ _
  let b := Module.finBasis (R ⧸ 𝔭) Q
  choose x hx using fun i => Submodule.Quotient.mk_surjective _ (b i)
  have hli : LinearIndependent F (M.subtype ∘ x) := by
    refine Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (S := R ⧸ 𝔭) F ?_ M.subtype
      M.injective_subtype (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ?_
    · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact h𝔭.ne_top
    · have : (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ∘ x = b := by
        funext i; exact hx i
      rw [this]; exact b.linearIndependent
  have hsup : (⊤ : Submodule R M) ≤ Submodule.span R (Set.range x) ⊔ 𝔭 • ⊤ := by
    intro v _
    have hv : (Submodule.Quotient.mk v : Q) ∈ Submodule.span (R ⧸ 𝔭) (Set.range b) := b.mem_span _
    rw [← @Submodule.restrictScalars_mem R,
      Submodule.restrictScalars_span R (R ⧸ 𝔭) Ideal.Quotient.mk_surjective] at hv
    have hb : Set.range b = (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) '' Set.range x := by
      rw [← Set.range_comp]; congr 1; funext i; exact (hx i).symm
    rw [hb, ← Submodule.map_span] at hv
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 hv
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at e
    have : v = y - (y - v) := by abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right e)
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top (R := R) (M := M)) le_rfl hsup
  have hs𝔭 : s ∉ 𝔭 := fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem h hs1; simpa using this))
  have hsv : ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := fun v =>
    hs (Submodule.smul_mem_pointwise_smul v s ⊤ trivial)
  have hs0 : algebraMap R F s ≠ 0 := by
    intro h0
    have : s = 0 := (IsFractionRing.injective R F) (by rw [h0, map_zero])
    exact hs𝔭 (this ▸ 𝔭.zero_mem)
  have hsp : ⊤ ≤ Submodule.span F (Set.range (M.subtype ∘ x)) := by
    rw [← hspan, Submodule.span_le]
    intro v hv
    have h1 := hsv ⟨v, hv⟩
    have h2 : (s • v : V) ∈ Submodule.span F (Set.range (M.subtype ∘ x)) := by
      have h3 : M.subtype (s • ⟨v, hv⟩) ∈ (Submodule.span R (Set.range x)).map M.subtype :=
        Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact Submodule.span_le_restrictScalars R F _ h3
    have h4 : v = (algebraMap R F s)⁻¹ • (s • v) := by
      rw [← algebraMap_smul F s v, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [h4]
    exact Submodule.smul_mem _ _ h2
  have hcard : finrank (R ⧸ 𝔭) Q = finrank F V := by
    have := finrank_eq_card_basis (Basis.mk hli hsp)
    simpa using this.symm
  have hliR : LinearIndependent R x := by
    have := hli.restrict_scalars (R := R) (by
      intro a b hab
      simpa [Algebra.smul_def] using hab |> fun h => (IsFractionRing.injective R F) (by simpa [Algebra.smul_def] using h))
    exact LinearIndependent.of_comp M.subtype this
  refine ⟨x ∘ Fin.cast hcard.symm, s, hs𝔭, hliR.comp _ (Fin.cast_injective _), fun v => ?_⟩
  have : Set.range (x ∘ Fin.cast hcard.symm) = Set.range x :=
    (Fin.castOrderIso hcard.symm).surjective.range_comp x
  rw [this]; exact hsv v

theorem card_quot_pow_smul_top (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (M ⧸ (𝔭 ^ k • ⊤ : Submodule R M)) = Nat.card (R ⧸ 𝔭 ^ k) ^ finrank F V := by
  obtain ⟨x, s, hs, hli, hsx⟩ := exists_local_basis M hfg hspan h𝔭
  let φ : (Fin (finrank F V) → R) →ₗ[R] M :=
    { toFun := fun c => ∑ i, c i • x i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
  have hφ : ∀ c, φ c = ∑ i, c i • x i := fun c => rfl
  let ψ := (𝔭 ^ k • ⊤ : Submodule R M).mkQ ∘ₗ φ
  have hP : ∀ v ∈ (𝔭 ^ k • ⊤ : Submodule R M), ∃ d : Fin (finrank F V) → R,
      (∀ i, d i ∈ 𝔭 ^ k) ∧ s • v = ∑ i, d i • x i := by
    intro v hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha m _
      obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)
      refine ⟨fun i => a * r i, fun i => Ideal.mul_mem_right _ _ ha, ?_⟩
      rw [smul_comm s a m, ← hr, Finset.smul_sum]
      simp only [smul_smul]
    · intro v w hv hw
      obtain ⟨d, hd, hd'⟩ := hv
      obtain ⟨d', hd2, hd2'⟩ := hw
      refine ⟨d + d', fun i => Ideal.add_mem _ (hd i) (hd2 i), ?_⟩
      rw [smul_add, hd', hd2']
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨u, hu⟩ := exists_mul_sub_one_mem_pow h𝔭 hs k
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp (hsx m)
    refine ⟨fun i => u * r i, ?_⟩
    show Submodule.Quotient.mk (φ (fun i => u * r i)) = Submodule.Quotient.mk m
    rw [hφ, Submodule.Quotient.eq]
    have e : ∑ i, (u * r i) • x i - m = (u * s - 1) • m := by
      simp only [mul_smul, ← Finset.smul_sum, hr, sub_smul, one_smul]
    rw [e]
    exact Submodule.smul_mem_smul hu Submodule.mem_top
  have hker : LinearMap.ker ψ = Submodule.pi Set.univ (fun _ => 𝔭 ^ k) := by
    ext c
    rw [LinearMap.mem_ker, Submodule.mem_pi]
    show Submodule.Quotient.mk (φ c) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, hφ]
    constructor
    · intro hc i _
      obtain ⟨d, hd, hsd⟩ := hP _ hc
      have h0 : ∑ i, (s * c i - d i) • x i = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, ← hsd, sub_self]
      have h1 := Fintype.linearIndependent_iff.mp hli _ h0 i
      exact mem_pow_of_mul_mem h𝔭 hs (by rw [sub_eq_zero.mp h1]; exact hd i)
    · intro hc
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (hc i (Set.mem_univ i)) Submodule.mem_top
  have e := ((LinearMap.quotKerEquivOfSurjective ψ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (Submodule.quotientPi (fun _ => 𝔭 ^ k))))
  rw [Nat.card_congr e.toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Formalism.HermitianLattices.Ext.L3.MeanA
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.MeanB

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ θ : K, star θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 K)
  obtain ⟨θ, t, e, h⟩ := hK.2.2 P hP
  refine ⟨algebraMap (𝓞 K) K θ, fun h' => h ?_⟩
  rw [h'] at e
  have : t = θ := RingOfIntegers.coe_injective e
  rw [this, sub_self]; exact P.zero_mem

theorem star_algebraMap (hF : IsFixF K F) (a : F) : star (algebraMap F K a) = algebraMap F K a :=
  (hF _).2 ⟨a, rfl⟩

theorem finrank_eq_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) : finrank F K = 2 := by
  obtain ⟨θ, hθ⟩ := exists_star_ne hK
  set δ : K := θ - star θ with hδ
  have hδ0 : δ ≠ 0 := fun h => hθ (sub_eq_zero.1 h).symm
  have hsδ : star δ = -δ := by rw [hδ, star_sub, star_star]; ring
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hli : LinearIndependent F ![(1 : K), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t e
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at e
    have e' := congrArg star e
    rw [star_add, star_mul', star_algebraMap hF, star_algebraMap hF, hsδ, star_zero] at e'
    have hs : algebraMap F K s = 0 := by
      have : 2 * algebraMap F K s = 0 := by linear_combination e + e'
      exact (mul_eq_zero.1 this).resolve_left h2
    have ht : algebraMap F K t = 0 := by
      rw [hs, zero_add] at e
      exact (mul_eq_zero.1 e).resolve_right hδ0
    exact ⟨(map_eq_zero _).1 hs, (map_eq_zero _).1 ht⟩
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), δ]) := by
    intro a _
    obtain ⟨f1, hf1⟩ := (hF ((a + star a) / 2)).1 (by
      rw [star_div₀, star_add, star_star, star_ofNat, add_comm])
    obtain ⟨f2, hf2⟩ := (hF ((a - star a) / (2 * δ))).1 (by
      rw [star_div₀, star_sub, star_star, star_mul', star_ofNat, hsδ]
      field_simp
      ring)
    have : Set.range ![(1 : K), δ] = {1, δ} := by
      simp [Matrix.range_cons, Set.pair_comm]
    rw [this, Submodule.mem_span_pair]
    refine ⟨f1, f2, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, hf1, hf2]
    field_simp
    ring
  have := finrank_eq_card_basis (Basis.mk hli hsp)
  simpa using this

theorem algebraMap_comp (a : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap F K (a : F) := rfl

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem card_quot_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V * k) := by
  let _ : Module F V := Module.compHom V (algebraMap F K)
  have t1 : IsScalarTower F K V := ⟨fun a b v => by
    change (a • b) • v = (algebraMap F K a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let _ : Module (𝓞 F) V := Module.compHom V (algebraMap (𝓞 F) (𝓞 K))
  have t2 : IsScalarTower (𝓞 F) (𝓞 K) V := ⟨fun a b v => by
    change (a • b) • v = (algebraMap (𝓞 F) (𝓞 K) a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have t3 : IsScalarTower (𝓞 F) F V := ⟨fun a b v => by
    change (algebraMap F K (a • b)) • v = (algebraMap (𝓞 F) (𝓞 K) a) • ((algebraMap F K b) • v)
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) a), algebraMap_comp, Algebra.smul_def, map_mul,
      mul_smul]⟩
  have : FiniteDimensional F V := FiniteDimensional.trans F K V
  have hrank : finrank F V = 2 * finrank K V := by
    rw [← finrank_mul_finrank F K V, finrank_eq_two hK hF]
  let M : Submodule (𝓞 F) V := L.restrictScalars (𝓞 F)
  let e : ↥M ≃ₗ[𝓞 F] ↥L := (Submodule.restrictScalarsEquiv (𝓞 F) (𝓞 K) V L).restrictScalars (𝓞 F)
  have hfg : M.FG := by
    have : Module.Finite (𝓞 K) ↥L := Module.Finite.iff_fg.2 hL.fg
    have : Module.Finite (𝓞 F) ↥L := Module.Finite.trans (𝓞 K) ↥L
    exact Module.Finite.iff_fg.1 (Module.Finite.equiv e.symm)
  have hspan : Submodule.span F (M : Set V) = ⊤ := by
    have key : ∀ (a : K), ∀ w ∈ Submodule.span F (M : Set V), a • w ∈ Submodule.span F (M : Set V) := by
      intro a w hw
      induction hw using Submodule.span_induction with
      | mem l hl =>
        obtain ⟨d, hd, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2
          (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a)).exists_integral_multiple
        let z : 𝓞 K := ⟨d • a, hint⟩
        have hz : algebraMap (𝓞 K) K z = d • a := rfl
        have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
        have : a • l = ((d : F)⁻¹) • (z • l) := by
          rw [← algebraMap_smul K z l, hz, ← algebraMap_smul K ((d : F)⁻¹), smul_smul, map_inv₀,
            map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Int.cast_ne_zero.2 hd), one_mul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (L.smul_mem z hl))
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul f x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro v hv0
    clear hv0
    have hv : v ∈ Submodule.span K (L : Set V) := hL.span_eq_top ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem l hl => exact Submodule.subset_span hl
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact key a x hx
  have main := MeanA.card_quot_pow_smul_top (F := F) M hfg hspan h𝔭 k
  have hQ : Nat.card (𝓞 F ⧸ 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ k := by
    rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hmap : (𝔭 ^ k • ⊤ : Submodule (𝓞 F) ↥M).map (e : ↥M →ₗ[𝓞 F] ↥L) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L).restrictScalars (𝓞 F) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range, extP, ← Ideal.map_pow,
      Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  have e1 := Submodule.Quotient.equiv _ _ e hmap
  have e2 := Submodule.Quotient.restrictScalarsEquiv (𝓞 F)
    ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)
  rw [← Nat.card_congr e2.toEquiv, ← Nat.card_congr e1.toEquiv, main, hQ, hrank, ← pow_mul]
  congr 1; ring

theorem exists_star_int (a : 𝓞 K) : ∃ a' : 𝓞 K, algebraMap (𝓞 K) K a' = star (algebraMap (𝓞 K) K a) :=
  ⟨⟨star (algebraMap (𝓞 K) K a), map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)⟩, rfl⟩

theorem star_mem_extP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    ∃ z' ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z' = star (algebraMap (𝓞 K) K z) := by
  rw [extP, ← Ideal.map_pow, Ideal.map] at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨_, Ideal.subset_span ⟨t, ht, rfl⟩, by rw [algebraMap_comp, star_algebraMap hF]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add, map_add, star_add, ex, ey]⟩
  | smul a x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨a', ea⟩ := exists_star_int a
    exact ⟨a' * x', Ideal.mul_mem_left _ _ hx', by
      rw [smul_eq_mul, map_mul, map_mul, star_mul', ex, ea]⟩

theorem comap_extP_pow (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (extP K 𝔭 ^ k).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 ^ k := by
  rw [extP, ← Ideal.map_pow, Ideal.comap_map_eq_self_of_faithfullyFlat]

theorem congrP_algebraMap_iff_sub_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (a b : 𝓞 F) :
    CongrP (K := K) 𝔭 k (algebraMap F K (a : F)) (algebraMap F K (b : F)) ↔ a - b ∈ 𝔭 ^ k := by
  constructor
  · rintro ⟨t, ht, z, hz, e⟩
    have : z = algebraMap (𝓞 F) (𝓞 K) (t * (a - b)) := by
      apply RingOfIntegers.coe_injective
      rw [e, algebraMap_comp]
      simp
    rw [this, ← Ideal.mem_comap, comap_extP_pow] at hz
    exact MeanA.mem_pow_of_mul_mem h𝔭 ht hz
  · intro h
    refine ⟨1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), algebraMap (𝓞 F) (𝓞 K) (a - b), ?_, ?_⟩
    · rw [← Ideal.mem_comap, comap_extP_pow]; exact h
    · rw [algebraMap_comp]; simp

section form

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}

theorem exists_val (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (y : ↥L) :
    ∃ n : 𝓞 F, h (y : V) (y : V) = algebraMap F K (n : F) := by
  obtain ⟨a, ha⟩ := (hF (h y y)).1 (hs.eq y y)
  obtain ⟨z, hz⟩ := Submodule.mem_one.1 (hLi y y.2 y y.2)
  have hint : IsIntegral ℤ a := by
    rw [← isIntegral_algebraMap_iff (algebraMap F K).injective, ha, ← hz]
    exact RingOfIntegers.isIntegral_coe z
  exact ⟨⟨a, hint⟩, ha.symm⟩

theorem form_mem_right (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (u : ↥L) {w : ↥L}
    (hw : w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ z ∈ extP K 𝔭 ^ k, algebraMap (𝓞 K) K z = h (u : V) (w : V) := by
  induction hw using Submodule.smul_induction_on' with
  | smul a ha v _ =>
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hLi u u.2 v v.2)
    refine ⟨a * c, Ideal.mul_mem_right _ _ ha, ?_⟩
    rw [map_mul, hc, Submodule.coe_smul, ← algebraMap_smul K a (v : V), map_smul, smul_eq_mul]
  | add a _ b _ ha hb =>
    obtain ⟨x', hx', ex⟩ := ha
    obtain ⟨y', hy', ey⟩ := hb
    exact ⟨x' + y', add_mem hx' hy', by rw [map_add, ex, ey, Submodule.coe_add, map_add]⟩

theorem val_congr (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (𝔭 : Ideal (𝓞 F)) (k : ℕ) {y y' : ↥L} {n n' : 𝓞 F}
    (hy : y - y' ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L))
    (e : h (y : V) (y : V) = algebraMap F K (n : F))
    (e' : h (y' : V) (y' : V) = algebraMap F K (n' : F)) : n - n' ∈ 𝔭 ^ k := by
  obtain ⟨z1, hz1, e1⟩ := form_mem_right hLi 𝔭 k y' hy
  obtain ⟨z2, hz2, e2⟩ := form_mem_right hLi 𝔭 k (y - y') hy
  obtain ⟨z3, hz3, e3⟩ := star_mem_extP hF 𝔭 k hz1
  rw [← comap_extP_pow (K := K), Ideal.mem_comap]
  have : algebraMap (𝓞 F) (𝓞 K) (n - n') = z1 + z2 + z3 := by
    apply RingOfIntegers.coe_injective
    have h3 : star (h (y' : V) ((y - y' : ↥L) : V)) = h ((y - y' : ↥L) : V) (y' : V) := hs.eq _ _
    rw [algebraMap_comp, map_add, map_add, e1, e2, e3, e1, h3]
    have : algebraMap F K ((n - n' : 𝓞 F) : F) = algebraMap F K (n : F) - algebraMap F K (n' : F) := by
      simp
    rw [this, ← e, ← e']
    simp only [Submodule.coe_sub, map_sub, LinearMap.sub_apply]
    ring
  rw [this]
  exact add_mem (add_mem hz1 hz2) hz3

end form

end Formalism.HermitianLattices.Ext.L3.MeanB
end
end

section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

section DedekindLFunctions

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}

theorem pow_le_span_sup (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c : ℕ} (hg : g ∉ P ^ (c + 1)) (N : ℕ) :
    P ^ c ≤ Ideal.span {g} ⊔ P ^ N := by
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  have hdvd : Ideal.span {g} ⊔ P ^ N ∣ P ^ N := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow hpr N).mp hdvd
  rw [associated_iff_eq] at hm
  have hgm : g ∈ P ^ m := by
    rw [← hm]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self g)
  have hmc : m ≤ c := by
    by_contra h
    exact hg (Ideal.pow_le_pow_right (by omega) hgm)
  rw [hm]
  exact Ideal.pow_le_pow_right hmc

private theorem not_pow_dvd_mul_of_not_pow_dvd_of_not_pow_dvd (hpr : Prime P) (i : ℕ) :
    ∀ (j : ℕ) (A B : Ideal R), ¬ P ^ (i + 1) ∣ A → ¬ P ^ (j + 1) ∣ B →
      ¬ P ^ (i + j + 1) ∣ A * B := by
  induction i with
  | zero =>
    intro j A B hA hB h
    apply hB
    have hA' : ¬ P ∣ A := by simpa using hA
    have h' : P ^ (j + 1) ∣ A * B := by simpa using h
    exact hpr.pow_dvd_of_dvd_mul_left (j + 1) hA' h'
  | succ i ih =>
    intro j A B hA hB h
    by_cases hPA : P ∣ A
    · obtain ⟨A1, rfl⟩ := hPA
      apply ih j A1 B
      · intro h1
        apply hA
        rw [pow_succ']
        exact mul_dvd_mul_left P h1
      · exact hB
      · have h2 : P * P ^ (i + j + 1) ∣ P * (A1 * B) := by
          rw [← pow_succ', ← mul_assoc]
          have e : i + j + 1 + 1 = i + 1 + j + 1 := by omega
          rw [e]
          exact h
        exact (mul_dvd_mul_iff_left hpr.ne_zero).mp h2
    · apply hB
      have h3 := hpr.pow_dvd_of_dvd_mul_left (i + 1 + j + 1) hPA h
      exact dvd_trans (pow_dvd_pow P (by omega)) h3

theorem mul_notMem (hP : P.IsPrime) (hP0 : P ≠ ⊥) {a b : R} {i j : ℕ} (ha : a ∉ P ^ (i + 1))
    (hb : b ∉ P ^ (j + 1)) : a * b ∉ P ^ (i + j + 1) := by
  intro hab
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  refine not_pow_dvd_mul_of_not_pow_dvd_of_not_pow_dvd hpr i j (Ideal.span {a}) (Ideal.span {b}) ?_ ?_ ?_
  · rwa [Ideal.dvd_span_singleton]
  · rwa [Ideal.dvd_span_singleton]
  · rwa [Ideal.span_singleton_mul_span_singleton, Ideal.dvd_span_singleton]

theorem pow_le_span_mul_sup (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c k : ℕ} (hg : g ∉ P ^ (c + 1))
    (hck : c ≤ k) : P ^ k ≤ Ideal.span {g} * P ^ (k - c) ⊔ P ^ (k + 1) := by
  have hpr : Prime P := Ideal.prime_of_isPrime hP0 hP
  obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt
    (Ideal.pow_right_strictAnti P hP0 hP.ne_top (by omega : k - c < k - c + 1))
  have hdvd : Ideal.span {g} * P ^ (k - c) ⊔ P ^ (k + 1) ∣ P ^ (k + 1) :=
    Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow hpr (k + 1)).mp hdvd
  rw [associated_iff_eq] at hm
  have hgx : g * x ∈ P ^ m := by
    rw [← hm]
    exact Ideal.mem_sup_left (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self g) hx)
  have hmk : m ≤ k := by
    by_contra h
    have h1 := mul_notMem hP hP0 hg hx'
    have e : c + (k - c) + 1 = k + 1 := by omega
    rw [e] at h1
    exact h1 (Ideal.pow_le_pow_right (by omega) hgx)
  rw [hm]
  exact Ideal.pow_le_pow_right hmk

theorem exists_fill (hP : P.IsPrime) (hP0 : P ≠ ⊥) {g : R} {c k : ℕ} (hg : g ∉ P ^ (c + 1))
    (hck : c ≤ k) {s : R} (hs : s ∈ P ^ k) : ∃ r ∈ P ^ (k - c), s - g * r ∈ P ^ (k + 1) := by
  have h := pow_le_span_mul_sup hP hP0 hg hck hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  refine ⟨r, hr, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

end DedekindLFunctions

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem ne_bot {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)

theorem map_ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : extP K 𝔭 ≠ ⊥ := by
  intro h
  apply ne_bot h𝔭
  have h1 : Ideal.comap ι (Ideal.map ι 𝔭) = 𝔭 := Ideal.comap_map_eq_self_of_faithfullyFlat _
  have h3 : Ideal.comap ι (Ideal.map ι (⊥ : Ideal (𝓞 F))) = ⊥ :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  rw [Ideal.map_bot] at h3
  change Ideal.map ι 𝔭 = ⊥ at h
  rw [← h1, h, h3]

theorem mem_pow_iff (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 F) : ι a ∈ extP K 𝔭 ^ k ↔ a ∈ 𝔭 ^ k := by
  have h : Ideal.comap ι (Ideal.map ι (𝔭 ^ k)) = 𝔭 ^ k :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  change ι a ∈ (Ideal.map ι 𝔭) ^ k ↔ a ∈ 𝔭 ^ k
  rw [← Ideal.map_pow]
  constructor
  · intro ha
    rw [← h]
    exact Ideal.mem_comap.mpr ha
  · intro ha
    exact Ideal.mem_map_of_mem _ ha

private theorem coe_iota_eq_algebraMap_coe (a : 𝓞 F) : ((ι a : 𝓞 K) : K) = algebraMap F K (a : F) := by
  first
  | rfl
  | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K a).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K a)

private theorem coe_conjO_eq_star_coe (z : 𝓞 K) : ((conjO K z : 𝓞 K) : K) = star (z : K) := by
  first
  | rfl
  | (unfold conjO; rfl)

theorem conjO_map (hF : IsFixF K F) (a : 𝓞 F) : conjO K (ι a) = ι a := by
  apply RingOfIntegers.ext
  rw [coe_conjO_eq_star_coe, coe_iota_eq_algebraMap_coe]
  exact (hF _).mpr ⟨_, rfl⟩

theorem conjO_mem_pow (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    ∀ z ∈ extP K 𝔭 ^ k, conjO K z ∈ extP K 𝔭 ^ k := by
  intro z hz
  have hcomp : (conjO K).comp ι = ι := RingHom.ext (fun a => conjO_map hF a)
  have hJ : extP K 𝔭 ^ k = Ideal.map ι (𝔭 ^ k) := by
    rw [Ideal.map_pow]
    rfl
  rw [hJ] at hz ⊢
  have h1 := Ideal.mem_map_of_mem (conjO K) hz
  rwa [Ideal.map_map, hcomp] at h1

theorem map_pow_le_span_sup {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} {c : ℕ}
    (hd : d ∉ 𝔭 ^ (c + 1)) (N : ℕ) : extP K 𝔭 ^ c ≤ Ideal.span {ι d} ⊔ extP K 𝔭 ^ N := by
  have h := pow_le_span_sup h𝔭.isPrime (ne_bot h𝔭) hd N
  have h2 := Ideal.map_mono (f := ι) h
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow] at h2
  exact h2

theorem exists_fillO {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} {c k : ℕ}
    (hd : d ∉ 𝔭 ^ (c + 1)) (hck : c ≤ k) {s : 𝓞 K} (hs : s ∈ extP K 𝔭 ^ k) :
    ∃ r ∈ extP K 𝔭 ^ (k - c), s - ι d * r ∈ extP K 𝔭 ^ (k + 1) := by
  have h := pow_le_span_mul_sup h𝔭.isPrime (ne_bot h𝔭) hd hck
  have h2 := Ideal.map_mono (f := ι) h
  simp only [Ideal.map_sup, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
    Ideal.map_pow] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (h2 hs)
  obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  refine ⟨r, hr, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

theorem mem_of_mul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} {v j : ℕ}
    (hd : d ∉ 𝔭 ^ (v + 1)) {z : 𝓞 K} (hz : ι d * z ∈ extP K 𝔭 ^ (v + j)) : z ∈ extP K 𝔭 ^ j := by
  have hpr : Prime 𝔭 := Ideal.prime_of_isPrime (ne_bot h𝔭) h𝔭.isPrime
  have hdvd : Ideal.span {d} ⊔ 𝔭 ^ (v + j) ∣ 𝔭 ^ (v + j) := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow hpr (v + j)).mp hdvd
  rw [associated_iff_eq] at hm
  have hdm : d ∈ 𝔭 ^ m := by
    rw [← hm]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self d)
  have hmv : m ≤ v := by
    by_contra h
    exact hd (Ideal.pow_le_pow_right (by omega) hdm)
  have hS : Ideal.span {ι d} ⊔ extP K 𝔭 ^ (v + j) = extP K 𝔭 ^ m := by
    have h1 := congrArg (Ideal.map ι) hm
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow] at h1
    exact h1
  have hle : extP K 𝔭 ^ m * Ideal.span {z} ≤ extP K 𝔭 ^ (v + j) := by
    rw [← hS, Ideal.sup_mul]
    refine sup_le ?_ (by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right)
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_iff_mem]
    exact hz
  have hdiv : extP K 𝔭 ^ m * extP K 𝔭 ^ (v + j - m) ∣ extP K 𝔭 ^ m * Ideal.span {z} := by
    rw [← pow_add, show m + (v + j - m) = v + j by omega]
    exact Ideal.dvd_iff_le.mpr hle
  have h0 : extP K 𝔭 ^ m ≠ 0 :=
    pow_ne_zero _ (by rw [Ne, Ideal.zero_eq_bot]; exact map_ne_bot_of_isMaximal h𝔭)
  have h2 := (mul_dvd_mul_iff_left h0).mp hdiv
  exact Ideal.dvd_span_singleton.mp (dvd_trans (pow_dvd_pow _ (by omega)) h2)

private theorem exists_iota_eq_of_star_coe_eq (hF : IsFixF K F) (w : 𝓞 K) (hw : star (w : K) = (w : K)) :
    ∃ a : 𝓞 F, ι a = w := by
  obtain ⟨f, hf⟩ := (hF _).mp hw
  have hfi : IsIntegral ℤ f := by
    have h1 : IsIntegral ℤ (algebraMap F K f) := by
      rw [hf]
      exact RingOfIntegers.isIntegral_coe w
    exact (isIntegral_algHom_iff ((algebraMap F K).toIntAlgHom) (algebraMap F K).injective).mp h1
  refine ⟨⟨f, by
    first
    | exact hfi
    | exact (mem_integralClosure_iff ℤ F).mpr hfi
    | exact (NumberField.mem_ringOfIntegers F f).mpr hfi
    | simpa [integralClosure] using hfi⟩, ?_⟩
  apply RingOfIntegers.ext
  exact (coe_iota_eq_algebraMap_coe _).trans hf

theorem exists_tr (hF : IsFixF K F) (z : 𝓞 K) : ∃ a : 𝓞 F, ι a = z + conjO K z := by
  apply exists_iota_eq_of_star_coe_eq hF
  have e : ((z + conjO K z : 𝓞 K) : K) = (z : K) + star (z : K) := by
    rw [← coe_conjO_eq_star_coe]
    rfl
  rw [e, star_add, star_star, add_comm]

theorem ι_inj : Function.Injective (ι) := by
  intro a b hab
  have h : Ideal.comap ι (Ideal.map ι (⊥ : Ideal (𝓞 F))) = ⊥ :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  rw [Ideal.map_bot] at h
  have h1 : a - b ∈ Ideal.comap ι (⊥ : Ideal (𝓞 K)) := by
    rw [Ideal.mem_comap, map_sub, hab, sub_self]
    exact Ideal.zero_mem _
  rw [h, Ideal.mem_bot, sub_eq_zero] at h1
  exact h1

def trf (hF : IsFixF K F) (z : 𝓞 K) : 𝓞 F := Classical.choose (exists_tr hF z)

theorem trf_spec (hF : IsFixF K F) (z : 𝓞 K) : ι (trf hF z) = z + conjO K z := Classical.choose_spec (exists_tr hF z)

def trF (hF : IsFixF K F) : 𝓞 K →ₗ[𝓞 F] 𝓞 F where
  toFun z := trf hF z
  map_add' x y := by
    apply ι_inj (K := K)
    rw [map_add, trf_spec, trf_spec, trf_spec, map_add]
    ring
  map_smul' a x := by
    apply ι_inj (K := K)
    rw [RingHom.id_apply, smul_eq_mul, map_mul, trf_spec, trf_spec, Algebra.smul_def, map_mul,
      conjO_map hF]
    ring

theorem trF_spec (hF : IsFixF K F) (z : 𝓞 K) : ι (trF hF z) = z + conjO K z := trf_spec hF z

theorem trF_mem_pow (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) {z : 𝓞 K} (hz : z ∈ extP K 𝔭 ^ k) :
    trF hF z ∈ 𝔭 ^ k := (mem_pow_iff (K := K) 𝔭 k _).mp (by
    rw [trF_spec]
    exact Ideal.add_mem _ hz (conjO_mem_pow hF 𝔭 k z hz))

theorem exists_theta (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ θ : 𝓞 K, Ideal.span {θ - conjO K θ} ⊔ extP K 𝔭 = ⊤ := by
  have hne : extP K 𝔭 ≠ ⊤ := by
    intro h
    have h1 : ι 1 ∈ extP K 𝔭 ^ 1 := by
      rw [pow_one, h]
      exact Submodule.mem_top
    rw [mem_pow_iff, pow_one] at h1
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hK.2.2 P hPmax
  have htc : t = conjO K θ := by
    apply RingOfIntegers.ext
    rw [coe_conjO_eq_star_coe]
    exact ht
  subst htc
  refine ⟨θ, ?_⟩
  have hδc : ((θ - conjO K θ : 𝓞 K) : K) = (θ : K) - star (θ : K) := by
    rw [← coe_conjO_eq_star_coe]
    rfl
  have hfix : star (((θ - conjO K θ) * (θ - conjO K θ) : 𝓞 K) : K) =
      (((θ - conjO K θ) * (θ - conjO K θ) : 𝓞 K) : K) := by
    have e : (((θ - conjO K θ) * (θ - conjO K θ) : 𝓞 K) : K) =
        ((θ - conjO K θ : 𝓞 K) : K) * ((θ - conjO K θ : 𝓞 K) : K) := rfl
    rw [e, hδc, star_mul, star_sub, star_star]
    ring
  obtain ⟨r, hr⟩ := exists_iota_eq_of_star_coe_eq hF _ hfix
  have hr𝔭 : r ∉ 𝔭 := by
    intro hr'
    have h1 : ι r ∈ P := hPle (Ideal.mem_map_of_mem _ hr')
    rw [hr] at h1
    exact hθt ((hPmax.isPrime.mem_or_mem h1).elim id id)
  have h1 : Ideal.span {r} ⊔ 𝔭 = ⊤ := by
    refine h𝔭.1.2 _ (lt_of_le_of_ne le_sup_right (fun h => hr𝔭 ?_))
    rw [h]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self r)
  have h2 := congrArg (Ideal.map ι) h1
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_top] at h2
  rw [hr] at h2
  refine eq_top_iff.mpr ?_
  rw [← h2]
  exact sup_le_sup_right
    (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)) _

theorem exists_inv_theta {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) (N : ℕ) :
    ∃ e : 𝓞 K, δ * e - 1 ∈ extP K 𝔭 ^ N := by
  have h : Ideal.span {δ} ⊔ extP K 𝔭 ^ N = ⊤ := by
    first
    | exact Ideal.sup_pow_eq_top hδ
    | exact Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr hδ).pow_right)
  have h1 : (1 : 𝓞 K) ∈ Ideal.span {δ} ⊔ extP K 𝔭 ^ N := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp h1
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  refine ⟨e, ?_⟩
  have e2 : δ * e - 1 = -w := by
    rw [← hyw]
    ring
  rw [e2]
  exact neg_mem hw

theorem mem_of_unit_mul_mem {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) {N : ℕ}
    {z : 𝓞 K} (hz : δ * z ∈ extP K 𝔭 ^ N) : z ∈ extP K 𝔭 ^ N := by
  obtain ⟨e, he⟩ := exists_inv_theta hδ N
  have e2 : z = e * (δ * z) - (δ * e - 1) * z := by ring
  rw [e2]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ e hz) (Ideal.mul_mem_right z _ he)

end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
end
end
