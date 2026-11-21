import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.LatCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent

section
namespace UpperTheory.V.Z.Sym.Loc.CP

open IsLocalRing

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K}
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] {B : V →ₗ[K] V →ₗ[K] K} {S : Submodule O V}

theorem exists_smul_mem (L : IsLoc O Δ) (hf : S.FG) (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, B x y ∈ (algebraMap O K).range) (y : V) :
    ∃ k : K, k ≠ 0 ∧ k • y ∈ S := by
  haveI := L.frac
  classical
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) (s.image fun x => B x y)
  refine ⟨algebraMap O K b, (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero b.2), (hd _).2 fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hb _ (Finset.mem_image_of_mem _ hx)
    exact ⟨a, by rw [ha, map_smul, Algebra.smul_def, smul_eq_mul]⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | smul a x _ hx =>
    rw [← algebraMap_smul K a x, LinearMap.map_smul₂, smul_eq_mul]
    exact mul_mem ⟨a, rfl⟩ hx

theorem exists_unit (L : IsLoc O Δ) (hB : ∀ x y, B x y = B y x) (hf : S.FG) (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, B x y ∈ (algebraMap O K).range)
    (P : V →ₗ[K] V) (hP : ∀ x ∈ S, P x ∈ S) (hPP : ∀ x, P (P x) = P x) (hadj : ∀ x y, B x (P y) = B (P x) (P y)) (h0 : P ≠ 0) :
    ∃ v ∈ S, P v = v ∧ ∃ u : Oˣ, B v v = algebraMap O K u := by
  haveI := L.frac
  by_contra hn
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp' : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  have h1 : ∀ v ∈ S, ∃ a : O, B (P v) (P v) = algebraMap O K (p * a) := fun v hv => by
    obtain ⟨a, ha⟩ := (hd _).1 (hP v hv) _ (hP v hv)
    have : a ∈ maximalIdeal O := fun hu => hn ⟨P v, hP v hv, hPP v, hu.unit, ha.symm⟩
    rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    obtain ⟨b, rfl⟩ := this
    exact ⟨b, ha.symm⟩
  obtain ⟨i, hi⟩ := L.two.exists_right_inv
  have hi' : (2 : K) * algebraMap O K i = 1 := by rw [← map_ofNat (algebraMap O K) 2, ← map_mul, hi, map_one]
  have h2 : ∀ v ∈ S, (algebraMap O K p)⁻¹ • P v ∈ S := fun v hv => (hd _).2 fun w hw => by
    obtain ⟨a, ha⟩ := h1 v hv
    obtain ⟨b, hb⟩ := h1 w hw
    obtain ⟨c, hc⟩ := h1 (v + w) (add_mem hv hw)
    simp only [map_add, LinearMap.add_apply, map_mul] at ha hb hc
    refine ⟨i * (c - a - b), ?_⟩
    rw [map_smul, hadj, smul_eq_mul, map_mul, map_sub, map_sub]
    rw [hB (P v) (P w)] at hc
    field_simp
    linear_combination (-algebraMap O K i) * hc + algebraMap O K i * ha + algebraMap O K i * hb + B (P w) (P v) * hi'
  have h3 : S.map (P.restrictScalars O) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) _ (hf.map _) ?_ (maximalIdeal_le_jacobson _)
    rintro _ ⟨v, hv, rfl⟩
    have : (P.restrictScalars O) v = p • (P.restrictScalars O) ((algebraMap O K p)⁻¹ • P v) := by
      simp only [LinearMap.restrictScalars_apply, map_smul, hPP]
      rw [← algebraMap_smul K p, smul_smul, mul_inv_cancel₀ hp', one_smul]
    rw [this]
    exact Submodule.smul_mem_smul hp.not_isUnit ⟨_, h2 v hv, rfl⟩
  refine h0 (LinearMap.ext fun y => ?_)
  obtain ⟨k, hk, hy⟩ := exists_smul_mem L hf hd y
  have : P (k • y) = 0 := (Submodule.eq_bot_iff _).1 h3 _ ⟨_, hy, rfl⟩
  rw [map_smul] at this
  exact (smul_eq_zero.1 this).resolve_left hk

theorem not_span_two (h3 : Module.finrank K V = 3) (a b : V) (h : ∀ x, ∃ s t : K, x = s • a + t • b) : False := by
  have := finrank_le_of_span_eq_top (R := K) (v := ![a, b]) (by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨s, t, rfl⟩ := h x
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
  simp [h3] at this

theorem exists_frame (L : IsLoc O Δ) (h3 : Module.finrank K V = 3) (hB : ∀ x y, B x y = B y x) (hf : S.FG)
    (hd : ∀ y, y ∈ S ↔ ∀ x ∈ S, B x y ∈ (algebraMap O K).range) :
    ∃ e ∈ S, ∃ f ∈ S, ∃ h ∈ S, ∃ η : Oˣ, B e e = 0 ∧ B f f = 0 ∧ B e f = 1 ∧ B e h = 0 ∧ B f h = 0 ∧ B h h = algebraMap O K η ∧
      ∀ v ∈ S, ∃ a b c : O, v = a • e + b • f + c • h := by
  haveI := L.frac
  have sm : ∀ (a : O) (x : V), algebraMap O K a • x = a • x := fun a x => algebraMap_smul K a x
  have un : ∀ u : Oˣ, algebraMap O K u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
  have iv : ∀ u : Oˣ, (algebraMap O K u)⁻¹ = algebraMap O K (u⁻¹ : Oˣ) := fun u =>
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])
  have pm : ∀ (e : V) (u : Oˣ), e ∈ S → ∀ x ∈ S, ∀ g ∈ S, ((algebraMap O K u)⁻¹ * B e x) • g ∈ S := fun e u he x hx g hg => by
    obtain ⟨a, ha⟩ := (hd x).1 hx e he
    rw [iv, ← ha, ← map_mul, sm]; exact S.smul_mem _ hg
  obtain ⟨e₁, m₁, -, u₁, q₁⟩ := exists_unit L hB hf hd LinearMap.id (fun _ h => h) (fun _ => rfl) (fun _ _ => rfl) fun h =>
    not_span_two h3 0 0 fun x => ⟨0, 0, by simpa using LinearMap.congr_fun h x⟩
  let P₂ : V →ₗ[K] V := LinearMap.id - ((algebraMap O K u₁)⁻¹ • B e₁).smulRight e₁
  have a₂ : ∀ x, P₂ x = x - ((algebraMap O K u₁)⁻¹ * B e₁ x) • e₁ := fun x => rfl
  have o₂ : ∀ x, B e₁ (P₂ x) = 0 := fun x => by rw [a₂, map_sub, map_smul, q₁, smul_eq_mul]; field_simp [un u₁]; ring
  obtain ⟨e₂, m₂, p₂, u₂, q₂⟩ := exists_unit L hB hf hd P₂ (fun x hx => sub_mem hx (pm e₁ u₁ m₁ x hx _ m₁))
    (fun x => by rw [a₂ (P₂ x), o₂]; simp) (fun x y => by rw [a₂ x, LinearMap.map_sub₂, LinearMap.map_smul₂, o₂]; simp) fun h =>
    not_span_two h3 e₁ 0 fun x => ⟨_, 0, by simpa [a₂, sub_eq_zero] using LinearMap.congr_fun h x⟩
  have b12 : B e₁ e₂ = 0 := p₂ ▸ o₂ e₂
  have b21 : B e₂ e₁ = 0 := hB _ _ ▸ b12
  let P₃ : V →ₗ[K] V := P₂ - ((algebraMap O K u₂)⁻¹ • B e₂).smulRight e₂
  have a₃ : ∀ x, P₃ x = x - ((algebraMap O K u₁)⁻¹ * B e₁ x) • e₁ - ((algebraMap O K u₂)⁻¹ * B e₂ x) • e₂ := fun x => rfl
  have o₃ : ∀ x, B e₁ (P₃ x) = 0 := fun x => by simp only [a₃, map_sub, map_smul, q₁, b12, smul_eq_mul]; field_simp [un u₁]; ring
  have o₃' : ∀ x, B e₂ (P₃ x) = 0 := fun x => by simp only [a₃, map_sub, map_smul, q₂, b21, smul_eq_mul]; field_simp [un u₂]; ring
  obtain ⟨e₃, m₃, p₃, u₃, q₃⟩ := exists_unit L hB hf hd P₃ (fun x hx => sub_mem (sub_mem hx (pm e₁ u₁ m₁ x hx _ m₁)) (pm e₂ u₂ m₂ x hx _ m₂))
    (fun x => by rw [a₃ (P₃ x), o₃, o₃']; simp)
    (fun x y => by rw [a₃ x, LinearMap.map_sub₂, LinearMap.map_sub₂, LinearMap.map_smul₂, LinearMap.map_smul₂, o₃, o₃']; simp) fun h =>
    not_span_two h3 e₁ e₂ fun x => ⟨_, _, by
      have := LinearMap.congr_fun h x
      rw [a₃, sub_sub, LinearMap.zero_apply, sub_eq_zero] at this
      exact this⟩
  have b13 : B e₁ e₃ = 0 := p₃ ▸ o₃ e₃
  have b23 : B e₂ e₃ = 0 := p₃ ▸ o₃' e₃
  have b31 : B e₃ e₁ = 0 := hB _ _ ▸ b13
  have b32 : B e₃ e₂ = 0 := hB _ _ ▸ b23
  obtain ⟨a, b, hab⟩ := L.nm_unit (-(u₂ * u₁⁻¹)) (-(u₃ * u₁⁻¹))
  have hab' : algebraMap O K u₁ * algebraMap O K a ^ 2 + algebraMap O K u₂ * algebraMap O K b ^ 2 + algebraMap O K u₃ = 0 := by
    have := congrArg (algebraMap O K) hab
    simp only [Units.val_neg, Units.val_mul, map_sub, map_mul, map_neg, map_pow, ← iv] at this
    have h1 := un u₁
    field_simp at this
    linear_combination this
  let t : Oˣ := L.two.unit * u₃
  have ht : algebraMap O K t = 2 * algebraMap O K u₃ := by simp [t, map_ofNat]
  have h2 : (2 : K) ≠ 0 := fun h => un t (by rw [ht, h, zero_mul])
  set A := algebraMap O K a with hA
  set C := algebraMap O K b with hC
  let e := A • e₁ + C • e₂ + e₃
  let f := (algebraMap O K t)⁻¹ • (e₃ - A • e₁ - C • e₂)
  let h := (algebraMap O K u₂ * C) • e₁ - (algebraMap O K u₁ * A) • e₂
  have me : e ∈ S := add_mem (add_mem (by rw [hA, sm]; exact S.smul_mem _ m₁) (by rw [hC, sm]; exact S.smul_mem _ m₂)) m₃
  have mf : f ∈ S := by
    simp only [f]
    rw [iv, sm]
    exact S.smul_mem _ (sub_mem (sub_mem m₃ (by rw [hA, sm]; exact S.smul_mem _ m₁)) (by rw [hC, sm]; exact S.smul_mem _ m₂))
  have mh : h ∈ S := sub_mem (by rw [hC, ← map_mul, sm]; exact S.smul_mem _ m₁) (by rw [hA, ← map_mul, sm]; exact S.smul_mem _ m₂)
  have n₃ := un u₃
  have g1 : B e e = 0 := by simp [e, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32]; linear_combination hab'
  have g2 : B f f = 0 := by
    simp [f, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32, ht]
    field_simp
    first | linear_combination hab' | (right; right; linear_combination hab') | (simp [h2, n₃]; linear_combination hab')
  have g3 : B e f = 1 := by simp [e, f, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32, ht]; field_simp; linear_combination -hab'
  have g4 : B e h = 0 := by simp [e, h, q₁, q₂, q₃, b12, b21, b13, b31, b23, b32]; ring
  have g5 : B f h = 0 := by
    simp only [f, h, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, q₁, q₂, b12, b21, b31, b32]; ring
  have g6 : B h h = algebraMap O K (-(u₁ * u₂ * u₃) : Oˣ) := by
    simp [h, q₁, q₂, q₃, b12, b21]; linear_combination (algebraMap O K u₁ * algebraMap O K u₂) * hab'
  refine ⟨e, me, f, mf, h, mh, _, g1, g2, g3, g4, g5, g6, fun v hv => ?_⟩
  set η : Oˣ := -(u₁ * u₂ * u₃)
  have g3' : B f e = 1 := hB _ _ ▸ g3
  have g4' : B h e = 0 := hB _ _ ▸ g4
  have g5' : B h f = 0 := hB _ _ ▸ g5
  have li : LinearIndependent K ![e, f, h] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have k1 := congrArg (B f) hg
    have k2 := congrArg (B e) hg
    have k3 := congrArg (B h) hg
    simp [g1, g2, g3, g4, g5, g6, g3', g4', g5', un η] at k1 k2 k3
    intro i; fin_cases i <;> assumption
  have sp := li.span_eq_top_of_card_eq_finrank (by simp [h3])
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (sp ▸ Submodule.mem_top : v ∈ Submodule.span K (Set.range ![e, f, h]))
  rw [Fin.sum_univ_three] at hg
  obtain ⟨x, hx⟩ := (hd v).1 hv f mf
  obtain ⟨y, hy⟩ := (hd v).1 hv e me
  obtain ⟨z, hz⟩ := (hd v).1 hv h mh
  rw [← hg] at hx hy hz
  simp [g1, g2, g3, g4, g5, g6, g3', g4', g5'] at hx hy hz
  refine ⟨x, y, z * (η⁻¹ : Oˣ), ?_⟩
  rw [← sm, ← sm, ← sm, map_mul, hx, hy, hz, ← iv, mul_inv_cancel_right₀ (un η)]
  exact hg.symm

end UpperTheory.V.Z.Sym.Loc.CP
end

section
noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ τ : K}

variable (τ) in

def Bf (c t : K) : K × Etau K τ →ₗ[K] K × Etau K τ →ₗ[K] K :=
  LinearMap.mk₂ K (fun v w => c * v.1 * w.1 + t * QuadraticAlgebra.trace (v.2 * star w.2))
    (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring) (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring)
    (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring) (fun a b w => by simp [QuadraticAlgebra.trace_def]; ring)

theorem Bf_apply (c t : K) (v w : K × Etau K τ) : Bf τ c t v w = c * v.1 * w.1 + t * QuadraticAlgebra.trace (v.2 * star w.2) := rfl

theorem Bf_symm (c t : K) (v w : K × Etau K τ) : Bf τ c t v w = Bf τ c t w v := by
  simp [Bf_apply, QuadraticAlgebra.trace_def]; ring

def psi (s : K) (β : Etau K τ) : K × Etau K τ →ₗ[K] Etau K τ →ₗ[K] Etau K τ :=
  LinearMap.mk₂ K (fun v y => s • (v.1 • ((ω - star ω) * y) + v.2 * β * star y))
    (fun a b w => by ext <;> simp <;> ring) (fun a b w => by ext <;> simp <;> ring)
    (fun a b w => by ext <;> simp <;> ring) (fun a b w => by ext <;> simp <;> ring)

theorem psi_apply (s : K) (β : Etau K τ) (v : K × Etau K τ) (y : Etau K τ) :
    psi s β v y = s • (v.1 • ((ω - star ω) * y) + v.2 * β * star y) := rfl

theorem psi_anti {c t s ε : K} {β : Etau K τ} (hc : c = (τ ^ 2 - 4) * ε * s ^ 2) (hβ : QuadraticAlgebra.norm β * ε * s ^ 2 = 2 * t)
    (v w : K × Etau K τ) (y : Etau K τ) : ε • (psi s β v (psi s β w y) + psi s β w (psi s β v y)) = (2 * Bf τ c t v w) • y := by
  subst hc
  rw [QuadraticAlgebra.norm_def] at hβ
  ext <;> simp [psi_apply, Bf_apply, QuadraticAlgebra.trace_def]
  · linear_combination (2 * v.2.re * w.2.re + τ * v.2.re * w.2.im + 2 * v.2.im * w.2.im + τ * v.2.im * w.2.re) * y.re * hβ
  · linear_combination (2 * v.2.re * w.2.re + τ * v.2.re * w.2.im + 2 * v.2.im * w.2.im + τ * v.2.im * w.2.re) * y.im * hβ

theorem psi_quo (s : K) (β : Etau K τ) (z : (Etau K τ)ˣ) (v : K × Etau K τ) (y : Etau K τ) :
    psi s β (v.1, quo z * v.2) ((z : Etau K τ) * y) = (z : Etau K τ) * psi s β v y := by
  have h1 : star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  simp only [psi_apply, quo, star_mul, Algebra.smul_def]
  linear_combination (algebraMap K (Etau K τ) s * (z : Etau K τ) * v.2 * β * star y) * h1

theorem psi_inj {s : K} {β : Etau K τ} (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hβ : IsUnit β) {v : K × Etau K τ} (h : ∀ y, psi s β v y = 0) : v = 0 := by
  have h1 := h 1
  have h2 := h ω
  simp only [psi_apply, Algebra.smul_def] at h1 h2
  have hs' : IsUnit (algebraMap K (Etau K τ) s) := (isUnit_iff_ne_zero.mpr hs).map _
  rw [hs'.mul_right_eq_zero] at h1 h2
  simp only [star_one, mul_one] at h1
  have hΩ2 : (ω - star ω : Etau K τ) * (ω - star ω) = algebraMap K (Etau K τ) (τ ^ 2 - 4) := by
    ext <;> simp [pow_two] <;> ring
  have key : algebraMap K (Etau K τ) (v.1 * (τ ^ 2 - 4)) = 0 := by
    rw [map_mul, ← hΩ2]; linear_combination h2 - star ω * h1
  have hv1 : v.1 = 0 :=
    (mul_eq_zero.mp ((algebraMap K (Etau K τ)).injective (key.trans (map_zero _).symm))).resolve_right hD
  have hv2 : v.2 = 0 := by
    rw [hv1, map_zero, zero_mul, zero_add] at h1
    exact hβ.mul_left_eq_zero.mp h1
  exact Prod.ext hv1 hv2

theorem exists_psi {s : K} {β : Etau K τ} (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hβ : IsUnit β) (y y' : Etau K τ) :
    ∃ v, ∀ b, psi s β v b = (b * star y).im • y' + (b * star y').im • y := by
  have hDu : IsUnit (algebraMap K (Etau K τ) (τ ^ 2 - 4)) := (isUnit_iff_ne_zero.mpr hD).map _
  have hΩ2 : (ω - star ω : Etau K τ) * (ω - star ω) = algebraMap K (Etau K τ) (τ ^ 2 - 4) := by
    ext <;> simp [pow_two] <;> ring
  have hΩu : IsUnit (ω - star ω : Etau K τ) := isUnit_of_mul_isUnit_left (hΩ2 ▸ hDu)
  have htr : algebraMap K (Etau K τ) (QuadraticAlgebra.trace (star y * y')) = star y * y' + y * star y' := by
    ext <;> simp [QuadraticAlgebra.trace_def] <;> ring
  have hk : algebraMap K (Etau K τ) s * algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ *
      algebraMap K (Etau K τ) (τ ^ 2 - 4) = 1 := by
    rw [← map_mul, ← map_mul, ← map_one (algebraMap K (Etau K τ))]; congr 1; field_simp
  have hsub : ∀ z : Etau K τ, algebraMap K (Etau K τ) z.im * (ω - star ω) = z - star z := by
    intro z; rw [QuadraticAlgebra.sub_star z, Algebra.smul_def]
  have hinv : ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * β = 1 := by
    have := hβ.unit.inv_mul; rwa [hβ.unit_spec] at this
  refine ⟨((s * (τ ^ 2 - 4))⁻¹ * QuadraticAlgebra.trace (star y * y'),
    -(2 * (algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ *
      (y * y' * (ω - star ω) * ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ))))), fun b => ?_⟩
  have hs1 := hsub (b * star y)
  have hs2 := hsub (b * star y')
  rw [star_mul, star_star] at hs1 hs2
  apply hΩu.mul_left_cancel
  simp only [psi_apply, Algebra.smul_def, map_mul]
  linear_combination
    (algebraMap K (Etau K τ) s * algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ *
        algebraMap K (Etau K τ) (QuadraticAlgebra.trace (star y * y')) * b -
      2 * algebraMap K (Etau K τ) s * algebraMap K (Etau K τ) (s * (τ ^ 2 - 4))⁻¹ * y * y' *
        ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * β * star b) * hΩ2 +
    (algebraMap K (Etau K τ) (QuadraticAlgebra.trace (star y * y')) * b -
      2 * y * y' * ((hβ.unit⁻¹ : (Etau K τ)ˣ) : Etau K τ) * β * star b) * hk +
    (-2 * y * y' * star b) * hinv + b * htr - y' * hs1 - y * hs2

variable (O) in

def S0 (s : K) (β : Etau K τ) (Λ : Set (Etau K τ)) : Set (K × Etau K τ) := {v | ∀ y ∈ Λ, psi s β v y ∈ Λ}

variable (O) in

structure Uni (c t : K) (S : Set (K × Etau K τ)) : Prop where
  fg : ∃ s : Finset (K × Etau K τ), S = Submodule.span O (s : Set (K × Etau K τ))
  dual : ∀ y, y ∈ S ↔ ∀ x ∈ S, Bf τ c t x y ∈ (algebraMap O K).range

theorem coord {y₁ y₂ : Etau K τ} (hg : (y₂ * star y₁).im ≠ 0) (b : Etau K τ) :
    b = (-(b * star y₂).im / (y₂ * star y₁).im) • y₁ + ((b * star y₁).im / (y₂ * star y₁).im) • y₂ := by
  have key : (y₂ * star y₁).im • b = (-(b * star y₂).im) • y₁ + (b * star y₁).im • y₂ := by
    ext <;> simp <;> ring
  calc b = ((y₂ * star y₁).im)⁻¹ • ((y₂ * star y₁).im • b) := by
        rw [smul_smul, inv_mul_cancel₀ hg, one_smul]
    _ = _ := by rw [key, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

theorem coord_uniq {y₁ y₂ : Etau K τ} (hg : (y₂ * star y₁).im ≠ 0) {a b a' b' : K} (h : a • y₁ + b • y₂ = a' • y₁ + b' • y₂) : a = a' ∧ b = b' := by
  have e1 := congrArg (fun z => (z * star y₁).im) h
  have e2 := congrArg (fun z => (z * star y₂).im) h
  simp only [add_mul, smul_mul_assoc, im_add, im_smul, smul_eq_mul] at e1 e2
  have n1 : (y₁ * star y₁).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have n2 : (y₂ * star y₂).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have h12 : (y₁ * star y₂).im = -(y₂ * star y₁).im := by
    rw [← im_star, star_mul, star_star]
  rw [n1] at e1
  rw [n2, h12] at e2
  constructor
  · have : (a - a') * (y₂ * star y₁).im = 0 := by linear_combination -e2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg)
  · have : (b - b') * (y₂ * star y₁).im = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg)

theorem exists_efh {s : K} {β : Etau K τ} (hD : τ ^ 2 - 4 ≠ 0) (h2 : (2 : K) ≠ 0) (hs : s ≠ 0) (hβ : IsUnit β) {y₁ y₂ : Etau K τ}
    (hg : (y₂ * star y₁).im ≠ 0) : ∃ e f h, psi s β e y₁ = 0 ∧ psi s β e y₂ = y₁ ∧ psi s β f y₁ = y₂ ∧ psi s β f y₂ = 0 ∧
      psi s β h y₁ = -y₁ ∧ psi s β h y₂ = y₂ := by
  have n1 : (y₁ * star y₁).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have n2 : (y₂ * star y₂).im = 0 := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_im]
  have h12 : (y₁ * star y₂).im = -(y₂ * star y₁).im := by
    rw [← im_star, star_mul, star_star]
  have hstar : ∀ (k : K) (x : Etau K τ), star (k • x) = k • star x := by
    intro k x; ext <;> simp <;> ring
  set G := (y₂ * star y₁).im with hG
  obtain ⟨e, he⟩ := exists_psi hD hs hβ y₁ ((2 * G)⁻¹ • y₁)
  obtain ⟨f, hf⟩ := exists_psi hD hs hβ y₂ ((-(2 * G))⁻¹ • y₂)
  obtain ⟨h, hh⟩ := exists_psi hD hs hβ y₁ (G⁻¹ • y₂)
  refine ⟨e, f, h, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [he, hf, hh, hstar, mul_smul_comm, im_smul, smul_eq_mul, n1, n2, h12, ← hG, zero_smul,
      mul_zero, zero_add, add_zero, smul_smul, ← add_smul]
  all_goals (ext <;> simp <;> field_simp <;> ring)

end UpperTheory.V.Z.Sym.Loc.CP
end
end

section
noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}

theorem lat_basis (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) {Λ : Set (Etau K τ)} (h : IsLat O τ Λ) :
    ∃ y₁ y₂ : Etau K τ, (y₂ * star y₁).im ≠ 0 ∧ ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y₁ + algebraMap O K q • y₂ := by
  obtain ⟨y, x, hx, -, -, rfl⟩ := latCls O K Δ τ L hD Λ h
  have hs : ∀ (p : O) (z : Etau K τ), p • z = algebraMap O K p • z := fun p z => (algebraMap_smul K p z).symm
  have hn : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 :=
    (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp y.isUnit).ne_zero
  refine ⟨y, y * x, ?_, ?_⟩
  · have e : (y : Etau K τ) * x * star (y : Etau K τ) = x * algebraMap K _ (QuadraticAlgebra.norm (y : Etau K τ)) := by
      rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
      ring
    rw [e, QuadraticAlgebra.im_mul]
    simp
    exact ⟨hx, hn⟩
  · intro b
    simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_span_pair]
    constructor
    · rintro ⟨z, ⟨p, q, rfl⟩, rfl⟩
      refine ⟨p, q, ?_⟩
      rw [hs, hs, mul_add, mul_smul_comm, mul_smul_comm, mul_one]
    · rintro ⟨p, q, rfl⟩
      refine ⟨p • 1 + q • x, ⟨p, q, rfl⟩, ?_⟩
      rw [hs, hs, mul_add, mul_smul_comm, mul_smul_comm, mul_one]

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem mem_S0_of_sum_eq {s : K} {β y₁ y₂ : Etau K τ} {Λ : Set (Etau K τ)} (h : ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y₁ + algebraMap O K q • y₂)
    {v : K × Etau K τ} : v ∈ S0 s β Λ ↔ psi s β v y₁ ∈ Λ ∧ psi s β v y₂ ∈ Λ := by
  simp only [S0, Set.mem_setOf_eq]
  constructor
  · intro hv
    exact ⟨hv _ ((h _).2 ⟨1, 0, by simp⟩), hv _ ((h _).2 ⟨0, 1, by simp⟩)⟩
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨p, q, rfl⟩ := (h _).1 hy
    obtain ⟨p1, q1, e1⟩ := (h _).1 h1
    obtain ⟨p2, q2, e2⟩ := (h _).1 h2
    refine (h _).2 ⟨p * p1 + q * p2, p * q1 + q * q2, ?_⟩
    rw [map_add, map_smul, map_smul, e1, e2]
    simp only [map_add, map_mul, smul_add, smul_smul, add_smul]
    abel

variable {c t s : K} {ε : Oˣ} {β : Etau K τ}

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem Bf_int (L2 : IsUnit (2 : O)) (hc : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2) (hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t)
    {y₁ y₂ : Etau K τ} (hg : (y₂ * star y₁).im ≠ 0) {Λ : Set (Etau K τ)}
    (h : ∀ b, b ∈ Λ ↔ ∃ p q : O, b = algebraMap O K p • y₁ + algebraMap O K q • y₂) {v w : K × Etau K τ} (hv : v ∈ S0 s β Λ) (hw : w ∈ S0 s β Λ) :
    Bf τ c t v w ∈ (algebraMap O K).range := by
  have hadd : ∀ a b, a ∈ Λ → b ∈ Λ → a + b ∈ Λ := by
    intro a b ha hb
    obtain ⟨p, q, rfl⟩ := (h _).1 ha
    obtain ⟨p', q', rfl⟩ := (h _).1 hb
    refine (h _).2 ⟨p + p', q + q', ?_⟩
    simp only [map_add, add_smul]
    abel
  have hsm : ∀ (r : O) a, a ∈ Λ → algebraMap O K r • a ∈ Λ := by
    intro r a ha
    obtain ⟨p, q, rfl⟩ := (h _).1 ha
    refine (h _).2 ⟨r * p, r * q, ?_⟩
    simp only [map_mul, smul_add, smul_smul]
  have h1 : y₁ ∈ Λ := (h _).2 ⟨1, 0, by simp⟩
  have key : (2 * Bf τ c t v w) • y₁ ∈ Λ := by
    rw [← psi_anti hc hβ v w y₁]
    exact hsm ε _ (hadd _ _ (hv _ (hw _ h1)) (hw _ (hv _ h1)))
  obtain ⟨p, q, e⟩ := (h _).1 key
  have e' : (2 * Bf τ c t v w) • y₁ + (0 : K) • y₂ = algebraMap O K p • y₁ + algebraMap O K q • y₂ := by
    rw [zero_smul, add_zero]
    exact e
  obtain ⟨e1, -⟩ := coord_uniq hg e'
  refine ⟨((L2.unit⁻¹ : Oˣ) : O) * p, ?_⟩
  have h2 : algebraMap O K ((L2.unit⁻¹ : Oˣ) : O) * 2 = 1 := by
    rw [← map_ofNat (algebraMap O K) 2, ← map_mul, IsUnit.val_inv_mul, map_one]
  rw [map_mul, ← e1, ← mul_assoc, h2, one_mul]

theorem isUnimodular_cliffordLatticeStabilizer (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hu : IsUnit β) (hc : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2)
    (hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t) {Λ : Set (Etau K τ)} (hΛ : IsLat O τ Λ) : Uni O c t (S0 s β Λ) := by
  obtain ⟨y₁, y₂, hg, hΛ'⟩ := lat_basis L hD hΛ
  have h2K : (2 : K) ≠ 0 := by
    have := (L.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  have hεK : algebraMap O K ε ≠ 0 := ((ε.isUnit).map (algebraMap O K)).ne_zero
  obtain ⟨e, f, k, he1, he2, hf1, hf2, hk1, hk2⟩ := exists_efh hD h2K hs hu hg
  have ev1 : ∀ a b d : K, psi s β (a • e + b • f + d • k) y₁ = (-d) • y₁ + b • y₂ := by
    intro a b d
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, he1, hf1, hk1]
    module
  have ev2 : ∀ a b d : K, psi s β (a • e + b • f + d • k) y₂ = a • y₁ + d • y₂ := by
    intro a b d
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, he2, hf2, hk2]
    module
  have dec : ∀ v : K × Etau K τ, ∃ a b d : K, v = a • e + b • f + d • k := by
    intro v
    obtain ⟨α, b, h1⟩ : ∃ α b : K, psi s β v y₁ = α • y₁ + b • y₂ := ⟨_, _, coord hg _⟩
    obtain ⟨a, δ, h2⟩ : ∃ a δ : K, psi s β v y₂ = a • y₁ + δ • y₂ := ⟨_, _, coord hg _⟩
    have A1 := psi_anti hc hβ v k y₁
    have A2 := psi_anti hc hβ v k y₂
    simp only [hk1, hk2, map_neg, h1, h2, map_add, map_smul] at A1 A2
    have E1 : (algebraMap O K ε * (-2 * α)) • y₁ + (0 : K) • y₂ = (2 * Bf τ c t v k) • y₁ + (0 : K) • y₂ := by
      rw [← A1]
      module
    have E2 : (0 : K) • y₁ + (algebraMap O K ε * (2 * δ)) • y₂ = (0 : K) • y₁ + (2 * Bf τ c t v k) • y₂ := by
      rw [← A2]
      module
    obtain ⟨r1, -⟩ := coord_uniq hg E1
    obtain ⟨-, r2⟩ := coord_uniq hg E2
    have hδ : δ = -α := by
      have := mul_left_cancel₀ hεK (r2.trans r1.symm)
      exact mul_left_cancel₀ h2K (by linear_combination this)
    refine ⟨a, b, -α, ?_⟩
    rw [← sub_eq_zero]
    refine psi_inj hD hs hu (fun y => ?_)
    rw [coord hg y]
    simp only [map_sub, LinearMap.sub_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h1, h2, he1, he2, hf1, hf2, hk1, hk2, hδ]
    module
  have pair : ∀ x z : K, (∃ p q : O, x • y₁ + z • y₂ = algebraMap O K p • y₁ + algebraMap O K q • y₂) ↔
      x ∈ (algebraMap O K).range ∧ z ∈ (algebraMap O K).range := by
    intro x z
    constructor
    · rintro ⟨p, q, hpq⟩
      obtain ⟨r1, r2⟩ := coord_uniq hg hpq
      exact ⟨RingHom.mem_range.mpr ⟨p, r1.symm⟩, RingHom.mem_range.mpr ⟨q, r2.symm⟩⟩
    · rintro ⟨hx, hz⟩
      obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hx
      obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hz
      exact ⟨p, q, rfl⟩
  have memc : ∀ a b d : K, a • e + b • f + d • k ∈ S0 s β Λ ↔
      a ∈ (algebraMap O K).range ∧ b ∈ (algebraMap O K).range ∧ d ∈ (algebraMap O K).range := by
    intro a b d
    rw [mem_S0_of_sum_eq hΛ', ev1, ev2, hΛ', hΛ', pair, pair, neg_mem_iff]
    tauto
  have ind : ∀ a b d a' b' d' : K, a • e + b • f + d • k = a' • e + b' • f + d' • k → a = a' ∧ b = b' ∧ d = d' := by
    intro a b d a' b' d' hv
    have q1 := congrArg (fun v => psi s β v y₁) hv
    have q2 := congrArg (fun v => psi s β v y₂) hv
    simp only [ev1, ev2] at q1 q2
    obtain ⟨u1, u2⟩ := coord_uniq hg q1
    obtain ⟨u3, -⟩ := coord_uniq hg q2
    exact ⟨u3, u2, neg_inj.mp u1⟩
  have gram : ∀ a b d : K, 2 * Bf τ c t e (a • e + b • f + d • k) = algebraMap O K ε * b ∧
      2 * Bf τ c t f (a • e + b • f + d • k) = algebraMap O K ε * a ∧
      Bf τ c t k (a • e + b • f + d • k) = algebraMap O K ε * d := by
    intro a b d
    have Ae := psi_anti hc hβ e (a • e + b • f + d • k) y₂
    have Af := psi_anti hc hβ f (a • e + b • f + d • k) y₁
    have Ak := psi_anti hc hβ k (a • e + b • f + d • k) y₁
    rw [ev2, he2, ev1, map_add, map_smul, map_smul, he1, he2] at Ae
    rw [ev1, hf1, ev2, map_add, map_smul, map_smul, hf1, hf2] at Af
    rw [ev1, hk1, map_neg, ev1, map_add, map_smul, map_smul, hk1, hk2] at Ak
    have Ee : (0 : K) • y₁ + (algebraMap O K ε * b) • y₂ = (0 : K) • y₁ + (2 * Bf τ c t e (a • e + b • f + d • k)) • y₂ := by
      rw [← Ae]
      module
    have Ef : (algebraMap O K ε * a) • y₁ + (0 : K) • y₂ = (2 * Bf τ c t f (a • e + b • f + d • k)) • y₁ + (0 : K) • y₂ := by
      rw [← Af]
      module
    have Ek : (2 * (algebraMap O K ε * d)) • y₁ + (0 : K) • y₂ = (2 * Bf τ c t k (a • e + b • f + d • k)) • y₁ + (0 : K) • y₂ := by
      rw [← Ak]
      module
    exact ⟨(coord_uniq hg Ee).2.symm, (coord_uniq hg Ef).1.symm, (mul_left_cancel₀ h2K (coord_uniq hg Ek).1).symm⟩
  refine ⟨?_, ?_⟩
  · classical
    refine ⟨{e, f, k}, ?_⟩
    ext v
    obtain ⟨a, b, d, rfl⟩ := dec v
    rw [memc]
    simp only [Finset.coe_insert, Finset.coe_singleton, SetLike.mem_coe, Submodule.mem_span_insert,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨hp, hq, hr⟩
      obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hp
      obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hq
      obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hr
      refine ⟨p, q • f + r • k, ⟨q, r • k, ⟨r, rfl⟩, rfl⟩, ?_⟩
      all_goals rw [algebraMap_smul, algebraMap_smul, algebraMap_smul, add_assoc]
    · rintro ⟨p, _, ⟨q, _, ⟨r, rfl⟩, rfl⟩, hv⟩
      rw [← algebraMap_smul K p e, ← algebraMap_smul K q f, ← algebraMap_smul K r k, ← add_assoc] at hv
      obtain ⟨u1, u2, u3⟩ := ind _ _ _ _ _ _ hv
      exact ⟨RingHom.mem_range.mpr ⟨p, u1.symm⟩, RingHom.mem_range.mpr ⟨q, u2.symm⟩, RingHom.mem_range.mpr ⟨r, u3.symm⟩⟩
  · intro y
    constructor
    · intro hy x hx
      exact Bf_int L.two hc hβ hg hΛ' hx hy
    · intro H
      obtain ⟨a, b, d, rfl⟩ := dec y
      have meme : e ∈ S0 s β Λ := by
        have := (memc 1 0 0).2 ⟨one_mem _, zero_mem _, zero_mem _⟩
        simpa using this
      have memf : f ∈ S0 s β Λ := by
        have := (memc 0 1 0).2 ⟨zero_mem _, one_mem _, zero_mem _⟩
        simpa using this
      have memk : k ∈ S0 s β Λ := by
        have := (memc 0 0 1).2 ⟨zero_mem _, zero_mem _, one_mem _⟩
        simpa using this
      obtain ⟨g1, g2, g3⟩ := gram a b d
      have hinv : algebraMap O K ↑ε⁻¹ * algebraMap O K ↑ε = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [memc]
      refine ⟨?_, ?_, ?_⟩
      · have ha : a = algebraMap O K (↑ε⁻¹ * 2) * Bf τ c t f (a • e + b • f + d • k) := by
          rw [map_mul, map_ofNat]
          linear_combination (-(algebraMap O K ↑ε⁻¹)) * g2 - a * hinv
        rw [ha]
        exact mul_mem (RingHom.mem_range_self _ _) (H f memf)
      · have hb : b = algebraMap O K (↑ε⁻¹ * 2) * Bf τ c t e (a • e + b • f + d • k) := by
          rw [map_mul, map_ofNat]
          linear_combination (-(algebraMap O K ↑ε⁻¹)) * g1 - b * hinv
        rw [hb]
        exact mul_mem (RingHom.mem_range_self _ _) (H e meme)
      · have hd : d = algebraMap O K ↑ε⁻¹ * Bf τ c t k (a • e + b • f + d • k) := by
          linear_combination (-(algebraMap O K ↑ε⁻¹)) * g3 - d * hinv
        rw [hd]
        exact mul_mem (RingHom.mem_range_self _ _) (H k memk)

end UpperTheory.V.Z.Sym.Loc.CP
end
end

section
noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ τ : K}
  {c t s : K} {ε : Oˣ} {β : Etau K τ}

theorem finrank_V : Module.finrank K (K × Etau K τ) = 3 := by
  rw [Module.finrank_prod, Module.finrank_self]
  exact congrArg (1 + ·) (QuadraticAlgebra.finrank_eq_two (-1 : K) τ)

theorem Uni.frame (L : IsLoc O Δ) {S : Set (K × Etau K τ)} (hS : Uni O c t S) :
    ∃ e ∈ S, ∃ f ∈ S, ∃ h ∈ S, ∃ η : Oˣ, Bf τ c t e e = 0 ∧ Bf τ c t f f = 0 ∧ Bf τ c t e f = 1 ∧ Bf τ c t e h = 0 ∧ Bf τ c t f h = 0 ∧
      Bf τ c t h h = algebraMap O K η ∧ ∀ v ∈ S, ∃ a b d : O, v = a • e + b • f + d • h := by
  obtain ⟨s, hs⟩ := hS.fg
  have hd : ∀ y : K × Etau K τ, y ∈ Submodule.span O (s : Set (K × Etau K τ)) ↔
      ∀ x ∈ Submodule.span O (s : Set (K × Etau K τ)), Bf τ c t x y ∈ (algebraMap O K).range := by
    intro y
    have := hS.dual y
    rw [hs] at this
    exact this
  obtain ⟨e, he, f, hf, h, hh, η, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_frame L finrank_V (Bf_symm c t) (Submodule.fg_span (Finset.finite_toSet s)) hd
  rw [hs]
  exact ⟨e, he, f, hf, h, hh, η, h1, h2, h3, h4, h5, h6, h7⟩

theorem exists_lat (L : IsLoc O Δ) (hc : c = (τ ^ 2 - 4) * algebraMap O K ε * s ^ 2)
    (hβ : QuadraticAlgebra.norm β * algebraMap O K ε * s ^ 2 = 2 * t) {S : Set (K × Etau K τ)} (hS : Uni O c t S) :
    ∃ Λ, IsLat O τ Λ ∧ S = S0 s β Λ := by
  classical
  obtain ⟨e, heS, f, hfS, h, hhS, η, hee, hff, hef, heh, hfh, hhh, hspan⟩ := Uni.frame L hS
  haveI := L.frac
  have h2O : IsUnit (2 : O) := L.two
  have h2 : (2 : K) ≠ 0 := by
    have := (h2O.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  set E : K := algebraMap O K ε with hE
  have hE0 : E ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
  have hinvE : algebraMap O K ↑ε⁻¹ * E = 1 := by
    rw [hE, ← map_mul, Units.inv_mul, map_one]
  have anti : ∀ v w y, E • (psi s β v (psi s β w y) + psi s β w (psi s β v y))
      = (2 * Bf τ c t v w) • y := fun v w y => psi_anti hc hβ v w y
  have sq0 : ∀ v, Bf τ c t v v = 0 → ∀ y, psi s β v (psi s β v y) = 0 := by
    intro v hv y
    have := anti v v y
    rw [hv, mul_zero, zero_smul, ← two_smul K, smul_smul, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 (mul_ne_zero hE0 h2)
    · exact h0
  have orth : ∀ v w, Bf τ c t v w = 0 → ∀ y, psi s β v (psi s β w y) = -psi s β w (psi s β v y) := by
    intro v w hvw y
    have := anti v w y
    rw [hvw, mul_zero, zero_smul, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd h0 hE0
    · exact eq_neg_of_add_eq_zero_left h0
  set κ : K := algebraMap O K (↑ε⁻¹ * 2) with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ, map_mul, map_ofNat]
    exact mul_ne_zero (ε⁻¹.isUnit.map (algebraMap O K)).ne_zero h2
  have ef : ∀ y, psi s β e (psi s β f y) + psi s β f (psi s β e y) = κ • y := by
    intro y
    have := anti e f y
    rw [hef, mul_one] at this
    calc _ = (algebraMap O K ↑ε⁻¹ * E) • (psi s β e (psi s β f y) + psi s β f (psi s β e y)) := by
          rw [hinvE, one_smul]
      _ = κ • y := by rw [mul_smul, this, smul_smul, hκ, map_mul, map_ofNat]
  obtain ⟨w0, hw0⟩ : ∃ w0, psi s β e w0 ≠ 0 := by
    by_contra H
    push_neg at H
    have := ef 1
    rw [H (psi s β f 1), H 1, map_zero, add_zero, eq_comm, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact hκ0 h0
    · exact one_ne_zero h0
  obtain ⟨y1, hy1d⟩ : ∃ y1, y1 = psi s β e w0 := ⟨_, rfl⟩
  obtain ⟨y2, hy2d⟩ : ∃ y2, y2 = psi s β f y1 := ⟨_, rfl⟩
  have hy1 : y1 ≠ 0 := hy1d ▸ hw0
  have pe1 : psi s β e y1 = 0 := by
    rw [hy1d]
    exact sq0 e hee w0
  have pf2 : psi s β f y2 = 0 := by
    rw [hy2d]
    exact sq0 f hff y1
  have pf1 : psi s β f y1 = y2 := hy2d.symm
  have pe2 : psi s β e y2 = κ • y1 := by
    have := ef y1
    rw [pe1, map_zero, add_zero, ← hy2d] at this
    exact this
  have hind : (y2 * star y1).im ≠ 0 := by
    intro H0
    have H1 : y2.im * y1.re = y2.re * y1.im := by
      simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] at H0
      linear_combination H0
    obtain ⟨l, hl⟩ : ∃ l : K, y2 = l • y1 := by
      by_cases hr : y1.re = 0
      · have hi : y1.im ≠ 0 := fun hi => hy1 (QuadraticAlgebra.ext hr hi)
        refine ⟨y2.im / y1.im, ?_⟩
        rw [hr, mul_zero] at H1
        ext
        · simp only [QuadraticAlgebra.re_smul, smul_eq_mul, hr, mul_zero]
          rcases mul_eq_zero.mp H1.symm with h0 | h0
          · exact h0
          · exact absurd h0 hi
        · simp only [QuadraticAlgebra.im_smul, smul_eq_mul]
          field_simp
      · refine ⟨y2.re / y1.re, ?_⟩
        ext
        · simp only [QuadraticAlgebra.re_smul, smul_eq_mul]
          field_simp
        · simp only [QuadraticAlgebra.im_smul, smul_eq_mul]
          field_simp
          linear_combination H1
    have := pe2
    rw [hl, map_smul, pe1, smul_zero, eq_comm, smul_eq_zero] at this
    rcases this with h0 | h0
    · exact hκ0 h0
    · exact hy1 h0
  have hhe : Bf τ c t h e = 0 := by rw [Bf_symm, heh]
  have hhf : Bf τ c t h f = 0 := by rw [Bf_symm, hfh]
  obtain ⟨μ, hμ⟩ : ∃ μ : K, psi s β h y1 = μ • y1 := by
    obtain ⟨α, γ, hz⟩ : ∃ α γ : K, psi s β h y1 = α • y1 + γ • y2 := ⟨_, _, coord hind _⟩
    have hpz : psi s β e (psi s β h y1) = 0 := by
      rw [orth e h heh, pe1, map_zero, neg_zero]
    rw [hz, map_add, map_smul, map_smul, pe1, pe2, smul_zero, zero_add, smul_smul, smul_eq_zero] at hpz
    rcases hpz with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact ⟨α, by rw [hz, h1, zero_smul, add_zero]⟩
      · exact absurd h1 hκ0
    · exact absurd h0 hy1
  have ph2 : psi s β h y2 = -(μ • y2) := by
    rw [hy2d, orth h f hhf, hμ, map_smul]
  have hμ2 : E * (μ * μ) = algebraMap O K η := by
    have := anti h h y1
    rw [hhh, hμ, map_smul, hμ, smul_smul, ← two_smul K, smul_smul, smul_smul, ← sub_eq_zero, ← sub_smul,
      smul_eq_zero] at this
    rcases this with h0 | h0
    · have h0' : 2 * (E * (μ * μ) - algebraMap O K η) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp h0' with h1 | h1
      · exact absurd h1 h2
      · exact sub_eq_zero.mp h1
    · exact absurd h0 hy1
  obtain ⟨mμ, hmμ⟩ : ∃ mμ : O, algebraMap O K mμ = μ := by
    have hint : IsIntegral O μ := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C (((ε⁻¹ : Oˣ) : O) * (η : O)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
      rw [map_mul, ← hμ2, ← mul_assoc, hinvE, one_mul, sq, sub_self]
    exact IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : Set (Etau K τ), ∀ b, b ∈ Λ ↔
      ∃ p q : O, b = algebraMap O K p • y1 + algebraMap O K q • y2 := ⟨_, fun _ => Iff.rfl⟩
  have hy1Λ : y1 ∈ Λ := (hΛ _).mpr ⟨1, 0, by simp⟩
  have hy2Λ : y2 ∈ Λ := (hΛ _).mpr ⟨0, 1, by simp⟩
  have hLat : IsLat O τ Λ := by
    refine ⟨⟨{y1, y2}, ?_⟩, ?_⟩
    · ext b
      rw [hΛ, Finset.coe_insert, Finset.coe_singleton, SetLike.mem_coe, Submodule.mem_span_pair]
      constructor
      · rintro ⟨p, q, rfl⟩
        exact ⟨p, q, by rw [algebraMap_smul, algebraMap_smul]⟩
      · rintro ⟨p, q, rfl⟩
        exact ⟨p, q, by rw [algebraMap_smul, algebraMap_smul]⟩
    · rw [eq_top_iff]
      intro b _
      rw [coord hind b]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span hy1Λ))
        (Submodule.smul_mem _ _ (Submodule.subset_span hy2Λ))
  have hsub : S ⊆ S0 s β Λ := by
    intro v hv
    obtain ⟨a, b, d, rfl⟩ := hspan v hv
    rw [mem_S0_of_sum_eq hΛ, ← algebraMap_smul K a e, ← algebraMap_smul K b f, ← algebraMap_smul K d h]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, pe1, pe2, pf1, pf2, hμ, ph2]
    constructor
    · refine (hΛ _).mpr ⟨d * mμ, b, ?_⟩
      rw [map_mul, hmμ]
      module
    · refine (hΛ _).mpr ⟨a * (↑ε⁻¹ * 2), -(d * mμ), ?_⟩
      rw [map_mul, ← hκ, map_neg, map_mul, hmμ]
      module
  have hsup : S0 s β Λ ⊆ S := by
    intro y hy
    rw [hS.dual]
    intro x hx
    exact Bf_int h2O hc hβ hind hΛ (hsub hx) hy
  exact ⟨Λ, hLat, Set.Subset.antisymm hsub hsup⟩

theorem lattice_homothety_of_eq_unimodular (L : IsLoc O Δ) (hD : τ ^ 2 - 4 ≠ 0) (hs : s ≠ 0) (hu : IsUnit β) {Λ Λ' : Set (Etau K τ)} (hΛ : IsLat O τ Λ) (hΛ' : IsLat O τ Λ')
    (hS : S0 s β Λ = S0 s β Λ') : ∃ k : Kˣ, Λ' = ((k : K) • ·) '' Λ := by
  obtain ⟨y₁, y₂, hy, hb⟩ := lat_basis L hD hΛ
  have h2 : (2 : K) ≠ 0 := by
    have := (L.two.map (algebraMap O K)).ne_zero
    rwa [map_ofNat] at this
  obtain ⟨e, f, h, he1, he2, hf1, hf2, -, -⟩ := exists_efh hD h2 hs hu hy
  have hy1 : y₁ ≠ 0 := by
    rintro rfl
    simp at hy
  have h0 : (0 : Etau K τ) ∈ Λ := (hb 0).mpr ⟨0, 0, by simp⟩
  have hy1m : y₁ ∈ Λ := (hb _).mpr ⟨1, 0, by simp⟩
  have hy2m : y₂ ∈ Λ := (hb _).mpr ⟨0, 1, by simp⟩
  have heS : e ∈ S0 s β Λ := (mem_S0_of_sum_eq hb).mpr ⟨by rw [he1]; exact h0, by rw [he2]; exact hy1m⟩
  have hfS : f ∈ S0 s β Λ := (mem_S0_of_sum_eq hb).mpr ⟨by rw [hf1]; exact hy2m, by rw [hf2]; exact h0⟩
  rw [hS] at heS hfS
  obtain ⟨u, hu'⟩ := hΛ'.fg
  have hspan := hΛ'.span
  subst hu'
  set M' : Submodule O (Etau K τ) := Submodule.span O (u : Set (Etau K τ)) with hM'
  set g : K →ₗ[O] Etau K τ := (LinearMap.toSpanSingleton K (Etau K τ) y₁).restrictScalars O with hg
  have hgp : ∀ p, g p = p • y₁ := fun p => rfl
  set J : Submodule O K := M'.comap g with hJ
  have hmemJ : ∀ p, p ∈ J ↔ p • y₁ ∈ M' := fun p => by rw [hJ, Submodule.mem_comap, hgp]
  have hginj : Function.Injective g := by
    intro p q hpq
    rw [hgp, hgp] at hpq
    exact smul_left_injective K hy1 hpq
  have hJfg : J.FG := Submodule.fg_of_fg_map_injective g hginj
    (Submodule.FG.of_le (Submodule.fg_span (Finset.finite_toSet u)) (Submodule.map_comap_le g M'))
  haveI := L.frac
  obtain ⟨k, hk⟩ := (FractionalIdeal.isPrincipal
    (⟨J, FractionalIdeal.isFractional_of_fg hJfg⟩ : FractionalIdeal (nonZeroDivisors O) K)).principal
  change J = Submodule.span O {k} at hk
  have hcoef : ∀ b ∈ M', ∀ p q : K, b = p • y₁ + q • y₂ → p ∈ J ∧ q ∈ J := by
    intro b hbM p q hbpq
    have hE : ∀ y ∈ M', psi s β e y ∈ M' := heS
    have hF : ∀ y ∈ M', psi s β f y ∈ M' := hfS
    have h1 := hE _ (hF _ hbM)
    have h2' := hE _ hbM
    rw [hbpq] at h1 h2'
    simp only [map_add, map_smul, he1, he2, hf1, hf2, smul_zero, add_zero, zero_add] at h1 h2'
    exact ⟨(hmemJ p).mpr h1, (hmemJ q).mpr h2'⟩
  have hback : ∀ p q : K, p ∈ J → q ∈ J → p • y₁ + q • y₂ ∈ M' := by
    intro p q hp hq
    have hF : ∀ y ∈ M', psi s β f y ∈ M' := hfS
    have := hF _ ((hmemJ q).mp hq)
    simp only [map_smul, hf1] at this
    exact M'.add_mem ((hmemJ p).mp hp) this
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hsub : (M' : Set (Etau K τ)) ⊆ {0} := by
      intro b hbM
      have hc := coord hy b
      obtain ⟨hp, hq⟩ := hcoef b hbM _ _ hc
      rw [hk, Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hp hq
      rw [hc, hp, hq]
      simp
    have : Submodule.span K (M' : Set (Etau K τ)) ≤ ⊥ := by
      rw [Submodule.span_le]
      simpa using hsub
    rw [hspan, le_bot_iff] at this
    exact hy1 (by simpa [this] using (Submodule.mem_top : y₁ ∈ (⊤ : Submodule K (Etau K τ))))
  refine ⟨Units.mk0 k hk0, ?_⟩
  ext b
  simp only [Units.val_mk0, Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hbM
    have hc := coord hy b
    obtain ⟨hp, hq⟩ := hcoef b hbM _ _ hc
    rw [hk, Submodule.mem_span_singleton] at hp hq
    obtain ⟨a, ha⟩ := hp
    obtain ⟨a', ha'⟩ := hq
    refine ⟨algebraMap O K a • y₁ + algebraMap O K a' • y₂, (hb _).mpr ⟨a, a', rfl⟩, ?_⟩
    rw [hc, ← ha, ← ha', smul_add, smul_smul, smul_smul, Algebra.smul_def a k, Algebra.smul_def a' k,
      mul_comm k, mul_comm k]
  · rintro ⟨y, hyΛ, rfl⟩
    obtain ⟨p, q, rfl⟩ := (hb y).mp hyΛ
    rw [smul_add, smul_smul, smul_smul]
    apply hback
    · rw [hk, Submodule.mem_span_singleton]
      exact ⟨p, by rw [Algebra.smul_def, mul_comm]⟩
    · rw [hk, Submodule.mem_span_singleton]
      exact ⟨q, by rw [Algebra.smul_def, mul_comm]⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem unimodular_image_mul_unit (z : (Etau K τ)ˣ) (Λ : Set (Etau K τ)) :
    S0 s β (((z : Etau K τ) * ·) '' Λ) = (fun v => (v.1, quo z * v.2)) '' S0 s β Λ := by
  have hq : quo z * quo z⁻¹ = 1 := by
    simp only [quo, inv_inv]
    calc (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) * star (z : Etau K τ))
        = ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ))
          * star ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
          rw [star_mul']
          ring
      _ = 1 := by simp
  have hw2 : ∀ w : K × Etau K τ, w = ((w.1, quo z⁻¹ * w.2).1, quo z * (w.1, quo z⁻¹ * w.2).2) := by
    intro w
    refine Prod.ext rfl ?_
    show w.2 = quo z * (quo z⁻¹ * w.2)
    rw [← mul_assoc, hq, one_mul]
  ext w
  constructor
  · intro hw
    refine ⟨(w.1, quo z⁻¹ * w.2), ?_, (hw2 w).symm⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hw ((z : Etau K τ) * y) ⟨y, hy, rfl⟩
    rw [hw2 w, psi_quo] at hxy
    have := (Units.mul_right_inj z).mp hxy
    rw [← this]
    exact hx
  · rintro ⟨v, hv, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [psi_quo]
    exact ⟨_, hv y hy, rfl⟩

omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem unimodular_image_smul_eq (k : Kˣ) (Λ : Set (Etau K τ)) : S0 s β (((k : K) • ·) '' Λ) = S0 s β Λ := by
  ext v
  simp only [S0, Set.mem_setOf_eq]
  constructor
  · intro h y hy
    have := h ((k : K) • y) ⟨y, hy, rfl⟩
    rw [map_smul] at this
    obtain ⟨x, hx, hxy⟩ := this
    have : x = psi s β v y := smul_right_injective _ (Units.ne_zero k) hxy
    exact this ▸ hx
  · rintro h _ ⟨y, hy, rfl⟩
    rw [map_smul]
    exact ⟨_, h y hy, rfl⟩

theorem Uni.iso (L : IsLoc O Δ) (ht : t ≠ 0) {S : Set (K × Etau K τ)} (hS : Uni O c t S) :
    IsSquare (τ ^ 2 - 4) ∨ ∃ a b : K, a ^ 2 - (τ ^ 2 - 4) * b ^ 2 = -2 * c * t := by
  obtain ⟨e, -, f, -, h, -, η, hee, -, hef, -⟩ := Uni.frame L hS
  have h2 : (2 : K) ≠ 0 := by
    have := L.two.map (algebraMap O K)
    rw [map_ofNat] at this
    exact this.ne_zero
  obtain ⟨x, ⟨p, q⟩⟩ := e
  rw [Bf_apply] at hee
  simp only [trace_def, re_mul, im_mul, re_star, im_star] at hee
  have hN : (2 * t) * (x ^ 2 * (c / (2 * t)) + (p ^ 2 + τ * p * q + q ^ 2)) = 0 := by
    field_simp
    linear_combination hee
  have hN' : x ^ 2 * (c / (2 * t)) + (p ^ 2 + τ * p * q + q ^ 2) = 0 :=
    (mul_eq_zero.mp hN).resolve_left (mul_ne_zero h2 ht)
  by_cases hx : x = 0
  · subst hx
    left
    by_cases hq : q = 0
    · exfalso
      subst hq
      have hp : p = 0 := by
        have : p ^ 2 = 0 := by linear_combination hN'
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      subst hp
      have : ((0 : K × Etau K τ)) = ((0 : K), (⟨0, 0⟩ : Etau K τ)) := rfl
      rw [← this, map_zero, LinearMap.zero_apply] at hef
      exact zero_ne_one hef
    · refine ⟨(2 * p + τ * q) / q, ?_⟩
      field_simp
      linear_combination (-4) * hN'
  · right
    refine ⟨t * (2 * p + τ * q) / x, t * q / x, ?_⟩
    field_simp
    linear_combination 2 * hee

end UpperTheory.V.Z.Sym.Loc.CP
end
end

section
noncomputable section

namespace UpperTheory.V.Z.Sym.Loc.CP

open QuadraticAlgebra

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ τ : K}

variable (Δ) in

def mkL (σ : K) : (K × Etau K τ) × (K × Etau K τ) →ₗ[K] Sp Δ τ where
  toFun p := (⟨p.1.1, σ * p.2.1⟩, ⟨⟨p.1.2.re, σ * p.2.2.re⟩, ⟨p.1.2.im, σ * p.2.2.im⟩⟩)
  map_add' a b := by ext <;> simp <;> ring
  map_smul' a b := by ext <;> simp <;> ring

theorem mkL_apply (σ : K) (v w : K × Etau K τ) :
    mkL Δ σ (v, w) = (⟨v.1, σ * w.1⟩, ⟨⟨v.2.re, σ * w.2.re⟩, ⟨v.2.im, σ * w.2.im⟩⟩) := rfl

theorem mkL_surj {σ : K} (hσ : σ ≠ 0) (x : Sp Δ τ) : ∃ v w, x = mkL Δ σ (v, w) := by
  refine ⟨(x.1.re, ⟨x.2.re.re, x.2.im.re⟩), (σ⁻¹ * x.1.im, ⟨σ⁻¹ * x.2.re.im, σ⁻¹ * x.2.im.im⟩), ?_⟩
  ext <;> simp [mkL_apply, hσ]

theorem mkL_inj {σ : K} (hσ : σ ≠ 0) {v w v' w' : K × Etau K τ} (h : mkL Δ σ (v, w) = mkL Δ σ (v', w')) : v = v' ∧ w = w' := by
  simp only [mkL_apply, Prod.mk.injEq, QuadraticAlgebra.mk.injEq, mul_right_inj' hσ] at h
  obtain ⟨⟨a, b⟩, ⟨c, d⟩, e, f⟩ := h
  exact ⟨Prod.ext a (QuadraticAlgebra.ext c e), Prod.ext b (QuadraticAlgebra.ext d f)⟩

def Mu (u : Etau K τ) (v : K × Etau K τ) : K × Etau K τ := (v.1, u * v.2)

theorem herm_mkL (c t σ : K) (v w v' w' : K × Etau K τ) : herm c (t • (1 : EL Δ τ)) (mkL Δ σ (v, w)) (mkL Δ σ (v', w')) =
    ⟨Bf τ c t v v' - Δ * σ ^ 2 * Bf τ c t w w', σ * (Bf τ c t w v' - Bf τ c t v w')⟩ := by
  ext <;> simp [herm, mkL_apply, Bf_apply, sigL, trace] <;> ring

theorem semi_mkL (σ : K) (u : Etau K τ) (v w : K × Etau K τ) : semi (ofE Δ u) (mkL Δ σ (v, w)) = mkL Δ σ (Mu u v, -Mu u w) := by
  ext <;> simp [semi, mkL_apply, Mu, sigL, ofE] <;> ring

theorem mul_mkL (σ : K) (u : Etau K τ) (v w : K × Etau K τ) :
    (((mkL Δ σ (v, w)).1, ofE Δ u * (mkL Δ σ (v, w)).2) : Sp Δ τ) = mkL Δ σ (Mu u v, Mu u w) := by
  ext <;> simp [mkL_apply, Mu, ofE] <;> ring

variable (Δ) in

def up (σ : K) (S : Set (K × Etau K τ)) : Set (Sp Δ τ) := {x | ∃ v ∈ S, ∃ w ∈ S, x = mkL Δ σ (v, w)}

theorem mem_up {σ : K} (hσ : σ ≠ 0) {S : Set (K × Etau K τ)} {v w : K × Etau K τ} : mkL Δ σ (v, w) ∈ up Δ σ S ↔ v ∈ S ∧ w ∈ S := by
  constructor
  · rintro ⟨v', hv', w', hw', h⟩
    obtain ⟨rfl, rfl⟩ := mkL_inj hσ h
    exact ⟨hv', hw'⟩
  · rintro ⟨hv, hw⟩
    exact ⟨v, hv, w, hw, rfl⟩

theorem up_inj {σ : K} (hσ : σ ≠ 0) {S S' : Set (K × Etau K τ)} (h : up Δ σ S = up Δ σ S') : S = S' := by
  ext p
  have key := congrArg (fun T => mkL Δ σ (p, p) ∈ T) h
  simpa [mem_up hσ] using key

theorem tor_up (σ : K) (z : (Etau K τ)ˣ) (S : Set (K × Etau K τ)) : tor Δ z '' up Δ σ S = up Δ σ (Mu (quo z) '' S) := by
  ext x
  constructor
  · rintro ⟨_, ⟨v, hv, w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, _, ⟨w, hw, rfl⟩, mul_mkL σ _ v w⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, w, hw, rfl⟩, mul_mkL σ _ v w⟩

theorem poly_mem {W : Type} [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W] (M : Submodule O W) (N : W → W)
    (hN : ∀ x ∈ M, N x ∈ M) {r : O} (h1 : IsUnit r) (h2 : IsUnit (2 + r)) {x : W} (hx : x ∈ M) :
    (algebraMap O K r)⁻¹ • (x + N x) - (algebraMap O K r * (2 + algebraMap O K r))⁻¹ • (N (N x) - (algebraMap O K r ^ 2 - 2) • N x + x) ∈ M := by
  obtain ⟨u, rfl⟩ := h1
  obtain ⟨u2, hu2⟩ := h2
  have e1 : (algebraMap O K ↑u)⁻¹ = algebraMap O K ↑u⁻¹ := (map_units_inv (algebraMap O K) u).symm
  have e2 : (algebraMap O K ↑u * (2 + algebraMap O K ↑u))⁻¹ = algebraMap O K ↑(u * u2)⁻¹ := by
    rw [map_units_inv, Units.val_mul, map_mul, hu2, map_add, map_ofNat]
  have e3 : algebraMap O K ↑u ^ 2 - 2 = algebraMap O K (↑u ^ 2 - 2) := by
    rw [map_sub, map_pow, map_ofNat]
  rw [e1, e2, e3, algebraMap_smul, algebraMap_smul, algebraMap_smul]
  exact M.sub_mem (M.smul_mem _ (M.add_mem hx (hN x hx)))
    (M.smul_mem _ (M.add_mem (M.sub_mem (hN _ (hN x hx)) (M.smul_mem _ (hN x hx))) hx))

theorem poly_Mu {r : K} (h1 : r ≠ 0) (h2 : 2 + r ≠ 0) (hr : r ^ 2 = 2 + τ) {a : Etau K τ} (ha : a = ω ∨ a = star ω) (x : K × Etau K τ) :
    Mu (r⁻¹ • (1 + a)) x = r⁻¹ • (x + Mu a x) - (r * (2 + r))⁻¹ • (Mu a (Mu a x) - (r ^ 2 - 2) • Mu a x + x) := by
  have hτ : τ = r ^ 2 - 2 := by linear_combination -hr
  subst hτ
  rcases ha with rfl | rfl <;> ext <;> simp [Mu] <;> field_simp <;> ring

theorem u_norm {r : K} (h1 : r ≠ 0) (hr : r ^ 2 = 2 + τ) : (r⁻¹ • (1 + ω) : Etau K τ) * (r⁻¹ • (1 + star ω)) = 1 := by
  ext <;> simp <;> field_simp <;> first | ring1 | linear_combination -hr | linear_combination -2 * hr

theorem Mu_Mu (a b : Etau K τ) (v : K × Etau K τ) : Mu a (Mu b v) = Mu (a * b) v := by simp [Mu, mul_assoc]

theorem Mu_one (v : K × Etau K τ) : Mu 1 v = v := by simp [Mu]

theorem omega_star : (ω : Etau K τ) * star ω = 1 := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

variable [IsDomain O] [IsDiscreteValuationRing O] {c t σ : K} {ε : Oˣ} {r : O}

private theorem exists_finset_up_span_eq_span (σ : K) (s : Finset (K × Etau K τ)) :
    ∃ t : Finset (Sp Δ τ), up Δ σ (Submodule.span O (s : Set (K × Etau K τ)) : Set (K × Etau K τ)) =
      ↑(Submodule.span O (t : Set (Sp Δ τ))) := by
  set M := Submodule.span O (s : Set (K × Etau K τ))
  have hM : M.FG := ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := (hM.prod hM).map ((mkL Δ σ).restrictScalars O)
  refine ⟨t, ?_⟩
  rw [ht]
  ext x
  simp only [up, Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_map, Submodule.mem_prod,
    LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨(v, w), ⟨hv, hw⟩, rfl⟩
  · rintro ⟨⟨v, w⟩, ⟨hv, hw⟩, rfl⟩
    exact ⟨v, hv, w, hw, rfl⟩

private theorem mu_image_eq_of_mu_omega_image_eq {M : Submodule O (K × Etau K τ)} {q : O} (h1 : IsUnit q) (h2 : IsUnit (2 + q))
    (hq : algebraMap O K q ^ 2 = 2 + τ) (hN : Mu ω '' (M : Set (K × Etau K τ)) = M) :
    Mu ((algebraMap O K q)⁻¹ • (1 + ω)) '' (M : Set (K × Etau K τ)) = M := by
  have hq1 : algebraMap O K q ≠ 0 := (h1.map (algebraMap O K)).ne_zero
  have hq2 : 2 + algebraMap O K q ≠ 0 := by
    have := (h2.map (algebraMap O K)).ne_zero
    rwa [map_add, map_ofNat] at this
  have hω : ∀ x ∈ M, Mu ω x ∈ M := by
    intro x hx
    have : Mu ω x ∈ Mu ω '' (M : Set (K × Etau K τ)) := ⟨x, hx, rfl⟩
    rwa [hN] at this
  have hω' : ∀ x ∈ M, Mu (star ω) x ∈ M := by
    intro x hx
    have : x ∈ (M : Set (K × Etau K τ)) := hx
    rw [← hN] at this
    obtain ⟨y, hy, rfl⟩ := this
    rw [Mu_Mu, mul_comm, omega_star, Mu_one]
    exact hy
  have key : ∀ a : Etau K τ, (a = ω ∨ a = star ω) → (∀ x ∈ M, Mu a x ∈ M) →
      ∀ x ∈ M, Mu ((algebraMap O K q)⁻¹ • (1 + a)) x ∈ M := by
    intro a ha hM x hx
    rw [poly_Mu hq1 hq2 hq ha x]
    exact poly_mem M (Mu a) hM h1 h2 hx
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact key ω (Or.inl rfl) hω y hy
  · intro hx
    refine ⟨Mu ((algebraMap O K q)⁻¹ • (1 + star ω)) x, key (star ω) (Or.inr rfl) hω' x hx, ?_⟩
    rw [Mu_Mu, u_norm hq1 hq, Mu_one]

theorem fix_up (L : IsLoc O Δ) (hσ : Δ * σ ^ 2 = algebraMap O K ε) (h1 : IsUnit r) (h2 : IsUnit (2 + r)) (hr : algebraMap O K r ^ 2 = 2 + τ)
    {S : Set (K × Etau K τ)} (hS : Uni O c t S) (hN : Mu ω '' S = S) :
    IsFix O c (ofE Δ ((algebraMap O K r)⁻¹ • (1 + ω))) (t • (1 : EL Δ τ)) (up Δ σ S) := by
  obtain ⟨s, hs⟩ := hS.fg
  subst hs
  set M := Submodule.span O (s : Set (K × Etau K τ))
  have hε : algebraMap O K ε ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact hε (by rw [← hσ]; ring)
  have hst := mu_image_eq_of_mu_omega_image_eq h1 h2 hr hN
  refine ⟨exists_finset_up_span_eq_span σ s, ?_, ?_⟩
  · intro y
    obtain ⟨v, w, rfl⟩ := mkL_surj hσ0 y
    rw [mem_up hσ0]
    constructor
    · rintro ⟨hv, hw⟩ x ⟨v', hv', w', hw', rfl⟩
      rw [herm_mkL, (descent O K Δ L σ ε hσ _).1]
      refine ⟨?_, ?_⟩
      · obtain ⟨a, ha⟩ := (hS.dual v).1 hv v' hv'
        obtain ⟨b, hb⟩ := (hS.dual w).1 hw w' hw'
        exact ⟨a - ε * b, by rw [map_sub, map_mul, ha, hb, hσ]⟩
      · obtain ⟨a, ha⟩ := (hS.dual v).1 hv w' hw'
        obtain ⟨b, hb⟩ := (hS.dual w).1 hw v' hv'
        exact ⟨a - b, by rw [map_sub, ha, hb]⟩
    · intro h
      have h0 : (0 : K × Etau K τ) ∈ (M : Set (K × Etau K τ)) := M.zero_mem
      refine ⟨(hS.dual v).2 fun v' hv' => ?_, (hS.dual w).2 fun w' hw' => ?_⟩
      · have key := h _ ⟨v', hv', 0, h0, rfl⟩
        rw [herm_mkL, (descent O K Δ L σ ε hσ _).1] at key
        simpa using key.1
      · have key := h _ ⟨0, h0, w', hw', rfl⟩
        rw [herm_mkL, (descent O K Δ L σ ε hσ _).1] at key
        obtain ⟨a, ha⟩ := key.1
        simp only [map_zero, LinearMap.zero_apply, zero_sub] at ha
        rw [hσ] at ha
        refine ⟨-(↑ε⁻¹ * a), ?_⟩
        rw [map_neg, map_mul, map_units_inv, ha]
        field_simp
  · ext z
    constructor
    · rintro ⟨x, ⟨v, hv, w, hw, rfl⟩, rfl⟩
      rw [semi_mkL]
      refine ⟨_, ?_, _, ?_, rfl⟩
      · rw [← hst]
        exact ⟨v, hv, rfl⟩
      · have : Mu ((algebraMap O K r)⁻¹ • (1 + ω)) w ∈ (M : Set (K × Etau K τ)) := by
          rw [← hst]
          exact ⟨w, hw, rfl⟩
        exact M.neg_mem this
    · rintro ⟨v, hv, w, hw, rfl⟩
      obtain ⟨v', hv', rfl⟩ : v ∈ Mu ((algebraMap O K r)⁻¹ • (1 + ω)) '' (M : Set (K × Etau K τ)) := by
        rw [hst]
        exact hv
      obtain ⟨w', hw', rfl⟩ : w ∈ Mu ((algebraMap O K r)⁻¹ • (1 + ω)) '' (M : Set (K × Etau K τ)) := by
        rw [hst]
        exact hw
      refine ⟨mkL Δ σ (v', -w'), ⟨v', hv', -w', M.neg_mem hw', rfl⟩, ?_⟩
      rw [semi_mkL]
      congr 2
      ext <;> simp [Mu]

private theorem mkL_mu_half_one_add_omega_eq {R : K} (h1 : R ≠ 0) (h2 : 2 + R ≠ 0) (hr : R ^ 2 = 2 + τ) (v w : K × Etau K τ) :
    mkL Δ σ (Mu (R⁻¹ • (1 + ω)) v, Mu (R⁻¹ • (1 + ω)) w) =
      R⁻¹ • (mkL Δ σ (v, w) + mkL Δ σ (Mu ω v, Mu ω w)) -
        (R * (2 + R))⁻¹ • (mkL Δ σ (Mu ω (Mu ω v), Mu ω (Mu ω w)) - (R ^ 2 - 2) • mkL Δ σ (Mu ω v, Mu ω w) +
          mkL Δ σ (v, w)) := by
  rw [poly_Mu h1 h2 hr (Or.inl rfl) v, poly_Mu h1 h2 hr (Or.inl rfl) w]
  ext <;> simp [mkL_apply] <;> ring

private theorem sq_inv_smul_one_add_omega_eq_omega {R : K} (h1 : R ≠ 0) (hr : R ^ 2 = 2 + τ) :
    (R⁻¹ • (1 + ω) : Etau K τ) * (R⁻¹ • (1 + ω)) = ω := by
  ext <;> simp <;> field_simp <;>
    first | ring1 | linear_combination hr | linear_combination -hr | linear_combination 2 * hr | linear_combination -2 * hr

private theorem isInt_herm_mkL_iff_bf_integral (L : IsLoc O Δ) (hσ : Δ * σ ^ 2 = algebraMap O K ε) (hσ0 : σ ≠ 0)
    (v w v' w' : K × Etau K τ) :
    IsInt O (herm c (t • (1 : EL Δ τ)) (mkL Δ σ (v', w')) (mkL Δ σ (v, w))) ↔
      (Bf τ c t v' v - algebraMap O K ε * Bf τ c t w' w ∈ (algebraMap O K).range ∧
        Bf τ c t w' v - Bf τ c t v' w ∈ (algebraMap O K).range) := by
  rw [herm_mkL, (descent O K Δ L σ ε hσ _).1, hσ]
  exact and_congr Iff.rfl
    ⟨fun ⟨b, hb⟩ => ⟨b, ((mul_right_inj' hσ0).1 hb).symm⟩, fun ⟨b, hb⟩ => ⟨b, by rw [← hb]⟩⟩

theorem fix_down (L : IsLoc O Δ) (hσ : Δ * σ ^ 2 = algebraMap O K ε) (h1 : IsUnit r) (h2 : IsUnit (2 + r)) (hr : algebraMap O K r ^ 2 = 2 + τ)
    {T : Set (Sp Δ τ)} (hT : IsFix O c (ofE Δ ((algebraMap O K r)⁻¹ • (1 + ω))) (t • (1 : EL Δ τ)) T) :
    ∃ S, Uni O c t S ∧ Mu ω '' S = S ∧ T = up Δ σ S := by
  obtain ⟨t0, ht0⟩ := hT.fg
  subst ht0
  obtain ⟨U, hU⟩ : ∃ U : Etau K τ, U = (algebraMap O K r)⁻¹ • (1 + ω) := ⟨_, rfl⟩
  rw [← hU] at hT
  set M := Submodule.span O (t0 : Set (Sp Δ τ)) with hMdef
  have hε : algebraMap O K ε ≠ 0 := (ε.isUnit.map (algebraMap O K)).ne_zero
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    exact hε (by rw [← hσ]; ring)
  have hR1 : algebraMap O K r ≠ 0 := (h1.map (algebraMap O K)).ne_zero
  have hR2 : 2 + algebraMap O K r ≠ 0 := by
    have := (h2.map (algebraMap O K)).ne_zero
    rwa [map_add, map_ofNat] at this
  have hUU : U * U = ω := by
    rw [hU]
    exact sq_inv_smul_one_add_omega_eq_omega hR1 hr
  have hneg : ∀ (a : Etau K τ) (x : K × Etau K τ), Mu a (-x) = -Mu a x := by
    intro a x
    ext <;> simp [Mu]
  have hMu0 : ∀ a : Etau K τ, Mu a 0 = 0 := by
    intro a
    ext <;> simp [Mu]
  have hstab := hT.stab
  have hφ : ∀ x ∈ M, semi (ofE Δ U) x ∈ M := by
    intro x hx
    have : semi (ofE Δ U) x ∈ semi (ofE Δ U) '' (M : Set (Sp Δ τ)) := ⟨x, hx, rfl⟩
    rwa [hstab] at this
  have hφ' : ∀ y ∈ M, ∃ x ∈ M, semi (ofE Δ U) x = y := by
    intro y hy
    have : y ∈ (M : Set (Sp Δ τ)) := hy
    rw [← hstab] at this
    obtain ⟨x, hx, e⟩ := this
    exact ⟨x, hx, e⟩
  have hss : ∀ a b, semi (ofE Δ U) (semi (ofE Δ U) (mkL Δ σ (a, b))) = mkL Δ σ (Mu ω a, Mu ω b) := by
    intro a b
    rw [semi_mkL, semi_mkL, hneg, neg_neg, Mu_Mu, Mu_Mu, hUU]
  have hA : ∀ v w, mkL Δ σ (v, w) ∈ M → mkL Δ σ (Mu U v, Mu U w) ∈ M := by
    intro v w h
    have key := poly_mem (K := K) M (fun x => semi (ofE Δ U) (semi (ofE Δ U) x))
      (fun x hx => hφ _ (hφ x hx)) h1 h2 h
    simp only [hss] at key
    rw [hU, mkL_mu_half_one_add_omega_eq hR1 hR2 hr]
    exact key
  obtain ⟨h2u, hh⟩ := L.two
  have hK : algebraMap O K ↑h2u⁻¹ * 2 = 1 := by
    have : algebraMap O K (↑h2u⁻¹ * ↑h2u) = 1 := by simp
    rwa [map_mul, hh, map_ofNat] at this
  have hsplit : ∀ v w, mkL Δ σ (v, w) ∈ M → mkL Δ σ (v, 0) ∈ M ∧ mkL Δ σ (0, w) ∈ M := by
    intro v w h
    obtain ⟨x, hx, hxe⟩ := hφ' _ h
    obtain ⟨a, b, rfl⟩ := mkL_surj hσ0 x
    rw [semi_mkL] at hxe
    obtain ⟨rfl, rfl⟩ := mkL_inj hσ0 hxe
    have hAx := hA a b hx
    have hφx := hφ _ hx
    rw [semi_mkL] at hφx
    constructor
    · have e : ((Mu U a, 0) : (K × Etau K τ) × (K × Etau K τ)) =
          algebraMap O K ↑h2u⁻¹ • ((Mu U a, Mu U b) + (Mu U a, -Mu U b)) := by
        rw [Prod.mk_add_mk, add_neg_cancel, ← two_smul K (Mu U a), Prod.smul_mk, smul_smul, hK, one_smul,
          smul_zero]
      rw [e, map_smul, map_add, algebraMap_smul]
      exact M.smul_mem _ (M.add_mem hAx hφx)
    · have e : ((0, -Mu U b) : (K × Etau K τ) × (K × Etau K τ)) =
          algebraMap O K ↑h2u⁻¹ • ((Mu U a, -Mu U b) - (Mu U a, Mu U b)) := by
        rw [Prod.mk_sub_mk, sub_self, ← neg_add', ← two_smul K (Mu U b), Prod.smul_mk, smul_zero, smul_neg,
          smul_smul, hK, one_smul]
      rw [e, map_smul, map_sub, algebraMap_smul]
      exact M.smul_mem _ (M.sub_mem hφx hAx)
  have hswap1 : ∀ w, mkL Δ σ (0, w) ∈ M → mkL Δ σ (w, 0) ∈ M := by
    intro w hw
    show mkL Δ σ (w, 0) ∈ (M : Set (Sp Δ τ))
    refine (hT.dual _).2 fun x hx => ?_
    obtain ⟨v', w', rfl⟩ := mkL_surj hσ0 x
    obtain ⟨hv'0, h0w'⟩ := hsplit v' w' hx
    have k1 := (hT.dual (mkL Δ σ (0, w))).1 hw (mkL Δ σ (v', 0)) hv'0
    have k2 := (hT.dual (mkL Δ σ (0, w))).1 hw (mkL Δ σ (0, w')) h0w'
    rw [isInt_herm_mkL_iff_bf_integral L hσ hσ0] at k1 k2 ⊢
    simp only [map_zero, LinearMap.zero_apply, mul_zero, sub_zero, zero_sub] at k1 k2 ⊢
    refine ⟨by simpa using (algebraMap O K).range.neg_mem k1.2, ?_⟩
    obtain ⟨a, ha⟩ := k2.1
    refine ⟨-(↑ε⁻¹ * a), ?_⟩
    rw [map_neg, map_mul, map_units_inv, ha]
    field_simp
  have hswap2 : ∀ v, mkL Δ σ (v, 0) ∈ M → mkL Δ σ (0, v) ∈ M := by
    intro v hv
    show mkL Δ σ (0, v) ∈ (M : Set (Sp Δ τ))
    refine (hT.dual _).2 fun x hx => ?_
    obtain ⟨v', w', rfl⟩ := mkL_surj hσ0 x
    obtain ⟨hv'0, h0w'⟩ := hsplit v' w' hx
    have k1 := (hT.dual (mkL Δ σ (v, 0))).1 hv (mkL Δ σ (v', 0)) hv'0
    have k2 := (hT.dual (mkL Δ σ (v, 0))).1 hv (mkL Δ σ (w', 0)) (hswap1 w' h0w')
    rw [isInt_herm_mkL_iff_bf_integral L hσ hσ0] at k1 k2 ⊢
    simp only [map_zero, LinearMap.zero_apply, mul_zero, sub_zero, zero_sub] at k1 k2 ⊢
    exact ⟨(algebraMap O K).range.neg_mem ((algebraMap O K).range.mul_mem ⟨↑ε, rfl⟩ k2.1),
      (algebraMap O K).range.neg_mem k1.1⟩
  refine ⟨{v | mkL Δ σ (v, 0) ∈ M}, ⟨?_, ?_⟩, ?_, ?_⟩
  · have inj : Function.Injective (mkL (τ := τ) Δ σ) := fun p q h => Prod.ext_iff.2 (mkL_inj hσ0 h)
    have surj : Function.Surjective (mkL (τ := τ) Δ σ) := fun x => by
      obtain ⟨v, w, h⟩ := mkL_surj hσ0 x
      exact ⟨(v, w), h.symm⟩
    let e := LinearEquiv.ofBijective (mkL (τ := τ) Δ σ) ⟨inj, surj⟩
    have he : ∀ a b, e.symm (mkL Δ σ (a, b)) = (a, b) := fun a b => e.symm_apply_apply (a, b)
    let p := ((LinearMap.fst K (K × Etau K τ) (K × Etau K τ)).comp e.symm.toLinearMap).restrictScalars O
    have hp : ∀ a b, p (mkL Δ σ (a, b)) = a := by
      intro a b
      simp [p, he]
    obtain ⟨s, hs⟩ := Submodule.FG.map p (⟨t0, rfl⟩ : M.FG)
    refine ⟨s, ?_⟩
    rw [hs]
    ext v
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_map]
    constructor
    · intro hv
      exact ⟨_, hv, hp v 0⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, b, rfl⟩ := mkL_surj hσ0 x
      rw [hp]
      exact (hsplit a b hx).1
  · intro y
    constructor
    · intro hy x hx
      have k := (hT.dual (mkL Δ σ (y, 0))).1 hy (mkL Δ σ (x, 0)) hx
      rw [isInt_herm_mkL_iff_bf_integral L hσ hσ0] at k
      simp only [map_zero, LinearMap.zero_apply, mul_zero, sub_zero] at k
      exact k.1
    · intro h
      show mkL Δ σ (y, 0) ∈ (M : Set (Sp Δ τ))
      refine (hT.dual _).2 fun x hx => ?_
      obtain ⟨v', w', rfl⟩ := mkL_surj hσ0 x
      obtain ⟨hv'0, h0w'⟩ := hsplit v' w' hx
      rw [isInt_herm_mkL_iff_bf_integral L hσ hσ0]
      simp only [map_zero, LinearMap.zero_apply, mul_zero, sub_zero]
      exact ⟨h v' hv'0, h w' (hswap1 w' h0w')⟩
  · ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      have key := hφ _ (hφ (mkL Δ σ (a, 0)) ha)
      rw [hss, hMu0] at key
      exact key
    · intro hv
      obtain ⟨x1, hx1, e1⟩ := hφ' (mkL Δ σ (v, 0)) hv
      obtain ⟨x0, hx0, e0⟩ := hφ' _ hx1
      obtain ⟨a, b, rfl⟩ := mkL_surj hσ0 x0
      rw [← e0, hss] at e1
      exact ⟨a, (hsplit a b hx0).1, (mkL_inj hσ0 e1).1⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨v, w, rfl⟩ := mkL_surj hσ0 x
      obtain ⟨h1', h2'⟩ := hsplit v w hx
      exact ⟨v, h1', w, hswap1 w h2', rfl⟩
    · rintro ⟨v, hv, w, hw, rfl⟩
      have hv' : mkL Δ σ (v, 0) ∈ M := hv
      have hw' : mkL Δ σ (w, 0) ∈ M := hw
      have key := M.add_mem hv' (hswap2 w hw')
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add] at key
      exact key

end UpperTheory.V.Z.Sym.Loc.CP
end
end
