import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.RpOfIsIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOneA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOneP
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.IndBasic

section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.NO

theorem key_id {F : Type} [Field F] (B B' d : F) (hβ : 1 - B - d ≠ 0) (hβ' : 1 - B' - d ≠ 0) :
    (1 + d / (1 - B - d)) * (1 + d / (1 - B' - d)) * (1 - 2 * d)
      - (1 + d / (1 - B - d)) * (d / (1 - B' - d)) * B'
      - (d / (1 - B - d)) * (1 + d / (1 - B' - d)) * B
      + (d / (1 - B - d)) * (d / (1 - B' - d)) = 1 := by
  field_simp
  ring

theorem hf_comb {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] (a b : K) (e v : ι → K) :
    hf c (a • e - b • v) (a • e - b • v) = a * c a * hf c e e - a * c b * hf c e v
      - b * c a * hf c v e + b * c b * hf c v v := by
  have h : ∀ i, (a * e i - b * v i) * c (a * e i - b * v i) = a * c a * (e i * c (e i))
      - a * c b * (e i * c (v i)) - b * c a * (v i * c (e i)) + b * c b * (v i * c (v i)) := by
    intro i; simp only [map_sub, map_mul]; ring
  simp only [hf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem refl_norm {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) {ι : Type} [Fintype ι]
    {e' v₀ : ι → K} {d β η : K} (hv : hf c v₀ v₀ = 1) (hu : hf c e' e' = 1 - 2 * d) (hd : c d = d)
    (hβ : β = 1 - hf c v₀ e' - d) (hβ0 : β ≠ 0) (hη : η = d / β) :
    hf c ((1 + η) • e' - η • v₀) ((1 + η) • e' - η • v₀) = 1 := by
  subst hβ hη
  have hcβ : c (1 - hf c v₀ e' - d) = 1 - c (hf c v₀ e') - d := by
    rw [map_sub, map_sub, map_one, hd]
  have hβ' : 1 - c (hf c v₀ e') - d ≠ 0 := by
    intro h; apply hβ0; rw [← hc (1 - hf c v₀ e' - d), hcβ, h, map_zero]
  have hcη : c (d / (1 - hf c v₀ e' - d)) = d / (1 - c (hf c v₀ e') - d) := by
    rw [map_div₀, hd, hcβ]
  have hca : c (1 + d / (1 - hf c v₀ e' - d)) = 1 + d / (1 - c (hf c v₀ e') - d) := by
    rw [map_add, map_one, hcη]
  rw [hf_comb, hca, hcη, hu, hv, hf_symm c hc v₀ e', mul_one]
  exact key_id _ _ d hβ0 hβ'

theorem pick {F : Type} [Field F] (X Y r : F) (h1 : r ≠ 1) (h2 : r ^ 2 ≠ 1) (h3 : r ≠ r ^ 2) :
    (X ≠ 1 ∧ Y ≠ 1) ∨ (r * X ≠ 1 ∧ Y ≠ r) ∨ (r ^ 2 * X ≠ 1 ∧ Y ≠ r ^ 2) := by
  by_cases hA : X ≠ 1 ∧ Y ≠ 1
  · exact Or.inl hA
  by_cases hB : r * X ≠ 1 ∧ Y ≠ r
  · exact Or.inr (Or.inl hB)
  rw [not_and_or, not_not, not_not] at hA hB
  refine Or.inr (Or.inr ⟨?_, ?_⟩)
  · intro hX2
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · apply h1; rw [hA, mul_one] at hB; exact hB
    · apply h2; rw [hA, mul_one] at hX2; exact hX2
    · apply h1
      have : r ^ 2 * X = r * (r * X) := by ring
      rw [this, hB, mul_one] at hX2; exact hX2
    · apply h1; rw [← hB, hA]
  · intro hY2
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · apply h1; rw [hA, mul_one] at hB; exact hB
    · exact h3 (hB.symm.trans hY2)
    · apply h2; rw [← hY2, hA]
    · apply h2; rw [← hY2, hA]

end PI.KLW.NO
end
end

section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.NO

theorem generic_pair {K : Type} [Field K] [NumberField K] {c : K →+* K} (hc : ∀ x, c (c x) = x)
    {p : ℕ} (hp : p.Prime) {ι : Type} [Fintype ι] {L : Set (ι → K)} (hU : Unimod K c p L)
    {x y : ι → K} (hx : x ∈ L) (hy : y ∈ L) (hxy : hf c x y = 1) (v₀ : ι → K) :
    ∃ x₁ ∈ L, ∃ y₁ ∈ L, hf c x₁ y₁ = 1 ∧ hf c v₀ x₁ ≠ 1 ∧ hf c v₀ y₁ ≠ 1 := by
  have key : ∀ q : ℕ, Nat.Coprime q p → q ≠ 0 → (q : K) * hf c v₀ x ≠ 1 → hf c v₀ y ≠ (q : K) →
      ∃ x₁ ∈ L, ∃ y₁ ∈ L, hf c x₁ y₁ = 1 ∧ hf c v₀ x₁ ≠ 1 ∧ hf c v₀ y₁ ≠ 1 := by
    intro q hq hq0 hX hY
    have hqK : (q : K) ≠ 0 := by exact_mod_cast hq0
    refine ⟨(q : K) • x, hU.smul_mem (Rp_natCast q) hx, (q : K)⁻¹ • y,
      hU.smul_mem (Rp_inv_natCast hq) hy, ?_, ?_, ?_⟩
    · rw [hf_smul_left, hf_smul_right, hxy, map_inv₀, map_natCast, mul_one, mul_inv_cancel₀ hqK]
    · rw [hf_smul_right, map_natCast]; exact hX
    · rw [hf_smul_right, map_inv₀, map_natCast]
      intro h; apply hY
      rw [inv_mul_eq_iff_eq_mul₀ hqK, mul_one] at h
      exact h
  have hp2 := hp.two_le
  have hp1 : Nat.Coprime (p + 1) p := Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)
  have h1 : ((p + 1 : ℕ) : K) ≠ 1 := by exact_mod_cast (show p + 1 ≠ 1 by omega)
  have h2 : ((p + 1 : ℕ) : K) ^ 2 ≠ 1 := by
    exact_mod_cast (show (p + 1) ^ 2 ≠ 1 by intro h; nlinarith)
  have h3 : ((p + 1 : ℕ) : K) ≠ ((p + 1 : ℕ) : K) ^ 2 := by
    exact_mod_cast (show p + 1 ≠ (p + 1) ^ 2 by intro h; nlinarith)
  rcases pick (hf c v₀ x) (hf c v₀ y) ((p + 1 : ℕ) : K) h1 h2 h3 with h | h | h
  · exact key 1 (Nat.coprime_one_left p) one_ne_zero (by simpa using h.1) (by simpa using h.2)
  · exact key (p + 1) hp1 (Nat.succ_ne_zero p) h.1 h.2
  · exact key ((p + 1) ^ 2) (Nat.Coprime.pow_left 2 hp1) (pow_ne_zero _ (Nat.succ_ne_zero p))
      (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem rp_two {K : Type} [Field K] [NumberField K] {p : ℕ} : Rp K p (2 : K) := by
  simpa using Rp_natCast (K := K) (p := p) 2

theorem rp_four {K : Type} [Field K] [NumberField K] {p : ℕ} : Rp K p (4 : K) := by
  simpa using Rp_natCast (K := K) (p := p) 4

theorem normOne_of_pair {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] [Nonempty ι] (L : Set (ι → K)) (hK : Module.finrank ℚ K = 2)
    (hc : ∀ x, c (c x) = x) (hp : p.Prime) (hs : SplitK c p) (hU : Unimod K c p L)
    (hS : Spans K L) {x y : ι → K} (hx : x ∈ L) (hy : y ∈ L) (hxy : hf c x y = 1) :
    ∃ e ∈ L, hf c e e = 1 := by
  classical
  have hne := ne_of_split c hs
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨v₀, hv₀def⟩ : ∃ v₀ : ι → K, v₀ = Pi.single i0 1 := ⟨_, rfl⟩
  have hv₀ : hf c v₀ v₀ = 1 := by rw [hv₀def, hf_single_left]; simp
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁, hX, hY⟩ := generic_pair hc hp hU hx hy hxy v₀
  obtain ⟨N, hN0, hNv⟩ := hS v₀
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN0
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have bound : ∀ z ∈ L, Rp K p ((N : K) * (1 - hf c v₀ z)) := by
    intro z hz
    have h1 := hU.hf_mem hz hNv
    rw [hf_smul_right, map_natCast, hf_symm c hc v₀ z] at h1
    have h2 := Rp_map c h1
    rw [map_mul, map_natCast, hc] at h2
    rw [mul_sub, mul_one]; exact Rp_sub (Rp_natCast N) h2
  obtain ⟨X, hXdef⟩ : ∃ X : K, X = hf c v₀ x₁ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : K, Y = hf c v₀ y₁ := ⟨_, rfl⟩
  have hX1 : (1 : K) - X ≠ 0 := sub_ne_zero.2 (by rw [hXdef]; exact Ne.symm hX)
  have hY1 : (1 : K) - Y ≠ 0 := sub_ne_zero.2 (by rw [hYdef]; exact Ne.symm hY)
  have hbX : Rp K p ((N : K) * (1 - X)) := by rw [hXdef]; exact bound x₁ hx₁
  have hbY : Rp K p ((N : K) * (1 - Y)) := by rw [hYdef]; exact bound y₁ hy₁
  obtain ⟨J₁, hJ₁⟩ := dvd_pow_p c hc hK hne hp hbY (mul_ne_zero hNK hY1)
  obtain ⟨J₂, hJ₂⟩ := dvd_pow_p c hc hK hne hp hbX (mul_ne_zero hNK hX1)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = J₁ + J₂ := ⟨_, rfl⟩
  obtain ⟨α', hα'def⟩ : ∃ α' : K, α' = (p : K) ^ J / (1 - Y) := ⟨_, rfl⟩
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : K, γ' = (p : K) ^ J / (1 - X) := ⟨_, rfl⟩
  have hα : Rp K p α' := by
    have : α' = (N : K) * (p : K) ^ J₂ * ((p : K) ^ J₁ / (N * (1 - Y))) := by
      rw [hα'def, hJ, pow_add]; field_simp
    rw [this]; exact Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₂)) hJ₁
  have hγ : Rp K p γ' := by
    have : γ' = (N : K) * (p : K) ^ J₁ * ((p : K) ^ J₂ / (N * (1 - X))) := by
      rw [hγ'def, hJ, pow_add]; field_simp
    rw [this]; exact Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₁)) hJ₂

  obtain ⟨ε, hε, hsum, hδ⟩ := eps c hc hK hp hs (J + 1 + 2 * N)
  have hce : c ε = 1 - ε := by linear_combination hsum
  have hcε : Rp K p (c ε) := Rp_map c hε
  obtain ⟨e', he'def⟩ : ∃ e' : ι → K, e' = ε • x₁ + c ε • y₁ := ⟨_, rfl⟩
  have he' : e' ∈ L := by rw [he'def]; exact hU.add_mem (hU.smul_mem hε hx₁) (hU.smul_mem hcε hy₁)
  obtain ⟨Z, hZdef⟩ : ∃ Z : K, Z = 2 - hf c x₁ x₁ - hf c y₁ y₁ := ⟨_, rfl⟩
  have hZ : Rp K p Z := by
    rw [hZdef]; exact Rp_sub (Rp_sub rp_two (hU.hf_mem hx₁ hx₁)) (hU.hf_mem hy₁ hy₁)
  have hcZ : c Z = Z := by
    rw [hZdef, map_sub, map_sub, map_ofNat, ← hf_symm c hc x₁ x₁, ← hf_symm c hc y₁ y₁]
  have hyx : hf c y₁ x₁ = 1 := by rw [hf_symm c hc x₁ y₁, hxy₁, map_one]
  obtain ⟨d, hddef⟩ : ∃ d : K, d = ε * c ε * Z / 2 := ⟨_, rfl⟩
  have hu : hf c e' e' = 1 - 2 * d := by
    rw [he'def, hddef, hZdef]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxy₁, hyx]
    linear_combination (ε + c ε + 1) * hsum
  have hd : c d = d := by
    rw [hddef, map_div₀, map_mul, map_mul, hc, hcZ, map_ofNat]; ring
  have hB : hf c v₀ e' = c ε * X + ε * Y := by
    rw [he'def, hXdef, hYdef]; simp only [hf_add_right, hf_smul_right, hc]
  obtain ⟨β, hβdef⟩ : ∃ β : K, β = 1 - hf c v₀ e' - d := ⟨_, rfl⟩
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : K, Γ = ε * α' + c ε * γ' := ⟨_, rfl⟩
  have hΓ : Rp K p Γ := by rw [hΓdef]; exact Rp_add (Rp_mul hε hα) (Rp_mul hcε hγ)
  obtain ⟨C, hCdef⟩ : ∃ C : K, C = ε * c ε / (2 * N * (p : K) ^ (J + 1)) := ⟨_, rfl⟩
  have hC : Rp K p C := by
    have e1 : C = ε * c ε / (p : K) ^ (J + 1 + 2 * N) * ((p : K) ^ (2 * N) / ((2 * N : ℕ) : K)) := by
      rw [hCdef, show (p : K) ^ (J + 1 + 2 * N) = (p : K) ^ (J + 1) * (p : K) ^ (2 * N) by rw [pow_add]]
      push_cast; field_simp
    rw [e1]
    exact Rp_mul hδ (rp_pow_div hp (by omega) le_rfl)
  obtain ⟨ω, hωdef⟩ : ∃ ω : K, ω = C * ((2 * ((N : K) * (1 - Y)) * γ' + 2 * ((N : K) * (1 - X)) * α')
      - ((N : K) * Z * Γ + 4 * N * (p : K) ^ J)) := ⟨_, rfl⟩
  have hω : Rp K p ω := by
    rw [hωdef]
    refine Rp_mul hC (Rp_sub (Rp_add (Rp_mul (Rp_mul rp_two hbY) hγ) (Rp_mul (Rp_mul rp_two hbX) hα))
      (Rp_add (Rp_mul (Rp_mul (Rp_natCast N) hZ) hΓ)
        (Rp_mul (Rp_mul rp_four (Rp_natCast N)) (rp_pow (Rp_natCast p) J))))
  have hβΓ : β * Γ = (p : K) ^ J * (1 + (p : K) * ω) := by
    rw [hβdef, hB, hωdef, hCdef, hΓdef, hα'def, hγ'def, hddef, hce]
    field_simp
    ring
  obtain ⟨hne1, hinv⟩ := one_add_p_unit c hc hK hne hp hω
  have hPne : (p : K) ^ J * (1 + (p : K) * ω) ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hne1
  have hβ0 : β ≠ 0 := by rintro h; apply hPne; rw [← hβΓ, h, zero_mul]
  have hΓ0 : Γ ≠ 0 := by rintro h; apply hPne; rw [← hβΓ, h, mul_zero]
  obtain ⟨η, hηdef⟩ : ∃ η : K, η = d / β := ⟨_, rfl⟩
  have hβ' : β = (p : K) ^ J * (1 + (p : K) * ω) / Γ := by rw [eq_div_iff hΓ0]; exact hβΓ
  have hηN : Rp K p (η / N) := by
    have e1 : η / N = ((p : K) * C) * (Z * Γ) * (1 + (p : K) * ω)⁻¹ := by
      rw [hηdef, hβ', hddef, hCdef, pow_succ]
      field_simp
    rw [e1]
    exact Rp_mul (Rp_mul (Rp_mul (Rp_natCast p) hC) (Rp_mul hZ hΓ)) hinv
  have hη : Rp K p η := by
    have : η = (N : K) * (η / N) := by field_simp
    rw [this]; exact Rp_mul (Rp_natCast N) hηN
  refine ⟨(1 + η) • e' - η • v₀, ?_, refl_norm c hc hv₀ hu hd hβdef hβ0 hηdef⟩
  have hv : η • v₀ = (η / N) • ((N : K) • v₀) := by rw [smul_smul, div_mul_cancel₀ _ hNK]
  rw [hv]
  exact hU.sub_mem (hU.smul_mem (Rp_add Rp_one hη) he') (hU.smul_mem hηN hNv)

end PI.KLW.NO

namespace PI.KLW

theorem normOne_of (h : PairOne) : NormOne := by
  intro K _ _ c p ι _ _ L hK hc hp hs hU hS
  obtain ⟨x, hx, y, hy, hxy⟩ := h K c p ι L hK hc hp hs hU hS
  exact NO.normOne_of_pair c p L hK hc hp hs hU hS hx hy hxy

end PI.KLW
end
end

section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.Pair

open PI.KLW

theorem smul_mem' {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {b : ι → K} (hb : b ∈ L) {r : K}
    (hr : Rp K p r) : r • b ∈ L := by
  have h := Ind.add_smul_mem hL (Ind.zero_mem_of hL) hb hr
  rwa [zero_add] at h

theorem add_mem' {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ} {ι : Type}
    [Fintype ι] {L : Set (ι → K)} (hL : Unimod K c p L) {a b : ι → K} (ha : a ∈ L) (hb : b ∈ L) :
    a + b ∈ L := by
  have h := Ind.add_smul_mem hL ha hb (Ind.rp_one p)
  rwa [one_smul] at h

theorem half {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) {p : ℕ} (hp : p.Prime) {ι : Type}
    [Fintype ι] [Nonempty ι] {L : Set (ι → K)} (hL : Unimod K c p L) (hS : Spans K L) {ε : K}
    (hε : Rp K p ε) (hsum : ε + c ε = 1) (hδ : Rp K p (ε * c ε / (p : K) ^ 2)) :
    ∃ x ∈ L, ∃ y ∈ L, ¬ Rp K p (ε * hf c x y / p) := by
  classical
  by_contra H
  push_neg at H
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hce : c ε = 1 - ε := by linear_combination hsum
  obtain ⟨T, hT⟩ : ∃ T, T = ε / p + c ε := ⟨_, rfl⟩
  have hTL : ∀ x ∈ L, T • x ∈ L := fun x hx => (hL _).2 fun y hy => by
    rw [Ind.hf_smul_left]
    have e : T * hf c x y = ε * hf c x y / p + c ε * hf c x y := by rw [hT]; ring
    rw [e]
    exact NO.rp_add (H x hx y hy) (NO.rp_mul (NO.rp_c c hε) ((hL x).1 hx y hy))
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨N, hN0, hNL⟩ := hS (Pi.single i 1)
  have hTj : ∀ j : ℕ, T ^ j • ((N : K) • Pi.single i (1 : K)) ∈ L := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_smul]; exact hNL
    | succ j ihj => rw [pow_succ', mul_smul]; exact hTL _ ihj
  have hvv : hf c ((N : K) • Pi.single i (1 : K)) ((N : K) • Pi.single i (1 : K))
      = (N : K) * N := by
    rw [Ind.hf_smul_left, Ind.hf_smul_right, Ind.hf_single_single, map_natCast, mul_one]
  have hj : ∀ j : ℕ, Rp K p (T ^ j * ((N : K) * N)) := fun j => by
    have := (hL _).1 (hTj j) _ hNL
    rwa [Ind.hf_smul_left, hvv] at this
  have hcT : c T = c ε / p + ε := by rw [hT, map_add, map_div₀, map_natCast, hc]
  have hjj : ∀ j : ℕ, Rp K p ((T * c T) ^ j * ((N : K) ^ 4)) := fun j => by
    have h1 := hj j
    have h2 := NO.rp_c c (hj j)
    rw [map_mul, map_pow, map_mul, map_natCast] at h2
    have e : (T * c T) ^ j * ((N : K) ^ 4)
        = (T ^ j * ((N : K) * N)) * (c T ^ j * ((N : K) * N)) := by ring
    rw [e]
    exact NO.rp_mul h1 h2
  obtain ⟨d, hd⟩ : ∃ d, d = ε * c ε / (p : K) ^ 2 := ⟨_, rfl⟩
  have hdR : Rp K p d := hd ▸ hδ
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = d + (p : K) ^ 2 * d - p * d - p * d := ⟨_, rfl⟩
  have hρR : Rp K p ρ := by
    rw [hρ]
    have hpd : Rp K p ((p : K) * d) := NO.rp_mul (NO.rp_natCast p) hdR
    exact NO.rp_sub (NO.rp_sub (NO.rp_add hdR (NO.rp_mul (NO.rp_pow (NO.rp_natCast p) 2) hdR))
      hpd) hpd
  have hTcT : T * c T = (1 + (p : K) * ρ) / p := by
    rw [hcT, hT, hρ, hd, hce]
    field_simp
    ring
  obtain ⟨hu0, huinv⟩ := NO.one_add_p_unit c hc hK hne hp hρR
  have hQ : N ^ 4 ≠ 0 := pow_ne_zero _ hN0
  have hpow := NO.rp_pow_div (K := K) hp hQ (le_refl (N ^ 4))
  have hA := hjj (N ^ 4 + 1)
  have hB := NO.rp_pow huinv (N ^ 4 + 1)
  obtain ⟨M, hM⟩ : ∃ M, N ^ 4 = M := ⟨_, rfl⟩
  rw [hM] at hpow hA hB
  have hMK : (M : K) = (N : K) ^ 4 := by rw [← hM]; push_cast; ring
  have hN : (N : K) ≠ 0 := by exact_mod_cast hN0
  have e1 : (1 + (p : K) * ρ) ^ (M + 1) * ((1 + (p : K) * ρ)⁻¹) ^ (M + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
  have hpM : (p : K) ^ M ≠ 0 := pow_ne_zero _ hp0
  have hN4 : (N : K) ^ 4 ≠ 0 := pow_ne_zero _ hN
  have key : ((T * c T) ^ (M + 1) * (N : K) ^ 4) * ((1 + (p : K) * ρ)⁻¹ ^ (M + 1))
      * ((p : K) ^ M / (M : K)) = ((p : K))⁻¹ := by
    have e2 : ((T * c T) ^ (M + 1) * (N : K) ^ 4) * ((1 + (p : K) * ρ)⁻¹ ^ (M + 1))
        * ((p : K) ^ M / (M : K))
        = ((1 + (p : K) * ρ) ^ (M + 1) * ((1 + (p : K) * ρ)⁻¹) ^ (M + 1))
          * ((N : K) ^ 4 / (N : K) ^ 4) * ((p : K) ^ M / ((p : K) ^ M * p)) := by
      rw [hTcT, div_pow, hMK]
      ring
    rw [e2, e1, div_self hN4, div_mul_eq_div_div, div_self hpM, one_mul, one_mul, one_div]
  apply NO.not_rp_inv_p (K := K) hp
  rw [← key]
  exact NO.rp_mul (NO.rp_mul hA hB) hpow

theorem near_one {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) {p : ℕ} (hp : p.Prime) {ι : Type}
    [Fintype ι] [Nonempty ι] {L : Set (ι → K)} (hL : Unimod K c p L) (hS : Spans K L) {ε : K}
    (hε : Rp K p ε) (hsum : ε + c ε = 1) (hδ : Rp K p (ε * c ε / (p : K) ^ 2)) :
    ∃ x ∈ L, ∃ y ∈ L, ∃ r, Rp K p r ∧ ε * (hf c x y - 1) = ε * c ε * r := by
  obtain ⟨x', hx', y', hy', hn⟩ := half c hc hK hne hp hL hS hε hsum hδ
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hce : c ε = 1 - ε := by linear_combination hsum
  obtain ⟨ρ', hρ'⟩ : ∃ ρ', ρ' = hf c x' y' := ⟨_, rfl⟩
  have hρR : Rp K p ρ' := by rw [hρ']; exact (hL x').1 hx' y' hy'
  rw [← hρ'] at hn
  obtain ⟨z, hz⟩ : ∃ z, z = ε * ρ' + c ε := ⟨_, rfl⟩
  have hzR : Rp K p z := by rw [hz]; exact NO.rp_add (NO.rp_mul hε hρR) (NO.rp_c c hε)
  have hcz : c z = c ε * c ρ' + ε := by rw [hz, map_add, map_mul, hc]
  have hnz : ¬ Rp K p (z * c z / p) := by
    intro h
    apply hn
    have key : ε * ρ' / p = ε * (z * c z / p) + ((p : K) * (ε * c ε / (p : K) ^ 2))
        * (-ε * (ρ' * c ρ' - ρ' - c ρ' + 1) + ρ' - c ρ') := by
      rw [hcz, hz, hce]
      field_simp
      ring
    rw [key]
    have hcρ : Rp K p (c ρ') := NO.rp_c c hρR
    have hW : Rp K p (-ε * (ρ' * c ρ' - ρ' - c ρ' + 1) + ρ' - c ρ') :=
      NO.rp_sub (NO.rp_add (NO.rp_mul (NO.rp_neg hε)
        (NO.rp_add (NO.rp_sub (NO.rp_sub (NO.rp_mul hρR hcρ) hρR) hcρ) NO.rp_one)) hρR) hcρ
    exact NO.rp_add (NO.rp_mul hε h) (NO.rp_mul (NO.rp_mul (NO.rp_natCast p) hδ) hW)
  obtain ⟨hz0, hzi⟩ := NO.unit_of_norm c hc hK hne hp hzR hnz
  refine ⟨x', hx', c (z⁻¹) • y', smul_mem' hL hy' (NO.rp_c c hzi), z⁻¹ * (ρ' - 1),
    NO.rp_mul hzi (NO.rp_sub hρR NO.rp_one), ?_⟩
  rw [Ind.hf_smul_right, hc, ← hρ']
  have h1 : ε * (ρ' - z) = ε * c ε * (ρ' - 1) := by rw [hz, hce]; ring
  have hzz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
  linear_combination z⁻¹ * h1 + ε * hzz

theorem pair_of_eps {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) {p : ℕ} (hp : p.Prime) {ι : Type}
    [Fintype ι] [Nonempty ι] {L : Set (ι → K)} (hL : Unimod K c p L) (hS : Spans K L) {ε : K}
    (hε : Rp K p ε) (hsum : ε + c ε = 1) (hδ : Rp K p (ε * c ε / (p : K) ^ 2)) :
    ∃ x ∈ L, ∃ y ∈ L, hf c x y = 1 := by
  obtain ⟨x1, hx1, y1, hy1, r1, hr1, h1⟩ := near_one c hc hK hne hp hL hS hε hsum hδ
  have hε' : Rp K p (c ε) := NO.rp_c c hε
  have hsum' : c ε + c (c ε) = 1 := by rw [hc, add_comm, hsum]
  have hδ' : Rp K p (c ε * c (c ε) / (p : K) ^ 2) := by rw [hc, mul_comm]; exact hδ
  obtain ⟨x2, hx2, y2, hy2, r2, hr2, h2⟩ := near_one c hc hK hne hp hL hS hε' hsum' hδ'
  rw [hc] at h2
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hxL : ε • x1 + c ε • x2 ∈ L := add_mem' hL (smul_mem' hL hx1 hε) (smul_mem' hL hx2 hε')
  have hyL : c ε • y1 + ε • y2 ∈ L := add_mem' hL (smul_mem' hL hy1 hε') (smul_mem' hL hy2 hε)
  have hd : (p : K) * ((p : K) * (ε * c ε / (p : K) ^ 2)) = ε * c ε := by field_simp
  have hxy : hf c (ε • x1 + c ε • x2) (c ε • y1 + ε • y2) = 1 + (p : K) * ((p : K)
      * (ε * c ε / (p : K) ^ 2) * (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1)) := by
    simp only [Ind.hf_add_left, Ind.hf_add_right, Ind.hf_smul_left, Ind.hf_smul_right, hc]
    linear_combination ε * h1 + c ε * h2
      - (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1) * hd + (ε + c ε + 1) * hsum
  have hQ : Rp K p ((p : K) * (ε * c ε / (p : K) ^ 2)
      * (ε * r1 + hf c x1 y2 + hf c x2 y1 + c ε * r2 - 1 - 1)) :=
    NO.rp_mul (NO.rp_mul (NO.rp_natCast p) hδ)
      (NO.rp_sub (NO.rp_sub (NO.rp_add (NO.rp_add (NO.rp_add (NO.rp_mul hε hr1)
        ((hL x1).1 hx1 y2 hy2)) ((hL x2).1 hx2 y1 hy1)) (NO.rp_mul hε' hr2)) NO.rp_one) NO.rp_one)
  obtain ⟨ha0, hai⟩ := NO.one_add_p_unit c hc hK hne hp hQ
  rw [← hxy] at ha0 hai
  refine ⟨_, hxL, c ((hf c (ε • x1 + c ε • x2) (c ε • y1 + ε • y2))⁻¹) • (c ε • y1 + ε • y2),
    smul_mem' hL hyL (NO.rp_c c hai), ?_⟩
  rw [Ind.hf_smul_right, hc, inv_mul_cancel₀ ha0]

theorem ne_of_split {K : Type} [Field K] [NumberField K] {c : K →+* K} {p : ℕ}
    (hs : SplitK c p) : ∃ z, c z ≠ z := by
  obtain ⟨P, _, _, a, b, hab, ha, hb⟩ := hs
  refine ⟨(a : K), ?_⟩
  rw [hab]
  intro h
  exact hb (by rwa [RingOfIntegers.ext h])

def EpsSplit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ),
    Module.finrank ℚ K = 2 → (∀ x, c (c x) = x) → p.Prime → SplitK c p →
      ∀ k : ℕ, ∃ ε : K, Rp K p ε ∧ ε + c ε = 1 ∧ Rp K p (ε * c ε / (p : K) ^ k)

theorem pairOne_of (h : EpsSplit) : PairOne := by
  intro K _ _ c p ι _ _ L hK hc hp hs hL hS
  obtain ⟨ε, hε, hsum, hδ⟩ := h K c p hK hc hp hs 2
  exact pair_of_eps c hc hK (ne_of_split hs) hp hL hS hε hsum hδ

theorem epsSplit : EpsSplit := by
  intro K _ _ c p hK hc hp hs k
  exact NO.eps c hc hK hp hs k

end PI.KLW.Pair

namespace PI.KLW

theorem pairOne : PairOne := Pair.pairOne_of Pair.epsSplit

end PI.KLW
end
end

section
namespace PI.KLW

theorem normOne : NormOne := normOne_of pairOne

end PI.KLW
end
