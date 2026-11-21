import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import BuildAid.ForwardExisting

section
namespace GlobalTheory.CMModel

theorem cubic_three_roots (g h e₁ e₂ e₃ : ℂ) (h₁ : 4 * e₁ ^ 3 - g * e₁ - h = 0)
    (h₂ : 4 * e₂ ^ 3 - g * e₂ - h = 0) (h₃ : 4 * e₃ ^ 3 - g * e₃ - h = 0)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    (∀ x, 4 * x ^ 3 - g * x - h = 4 * (x - e₁) * (x - e₂) * (x - e₃)) ∧
      16 * ((3 * e₁ ^ 2 - g / 4) * (3 * e₂ ^ 2 - g / 4) * (3 * e₃ ^ 2 - g / 4))
        = -(g ^ 3 - 27 * h ^ 2) := by
  have a : g = 4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₂)
    linear_combination h₂ - h₁
  have b : g = 4 * (e₁ ^ 2 + e₁ * e₃ + e₃ ^ 2) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₁₃)
    linear_combination h₃ - h₁
  have c : e₃ = -e₁ - e₂ := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr h₂₃)
    linear_combination (b - a) / 4
  have d : h = 4 * e₁ ^ 3 - g * e₁ := by linear_combination -h₁
  subst c
  rw [d, a]
  exact ⟨fun x => by ring, by ring⟩

end GlobalTheory.CMModel
end

section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubic_factor_and_discriminant_of_three_distinct_roots : ∀ (g h e₁ e₂ e₃ : ℂ), 4 * e₁ ^ 3 - g * e₁ - h = 0 → 4 * e₂ ^ 3 - g * e₂ - h = 0 → 4 * e₃ ^ 3 - g * e₃ - h = 0 → e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ → (∀ x, 4 * x ^ 3 - g * x - h = 4 * (x - e₁) * (x - e₂) * (x - e₃)) ∧ 16 * ((3 * e₁ ^ 2 - g / 4) * (3 * e₂ ^ 2 - g / 4) * (3 * e₃ ^ 2 - g / 4)) = -(g ^ 3 - 27 * h ^ 2) := by
  atlas_forward_decl GlobalTheory.CMModel.cubic_three_roots
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem derivWeierstrassP_add_half_period :
    ∀ (L : PeriodPair) (a t : ℂ), a ∉ L.lattice → 2 * a ∈ L.lattice → t ∉ L.lattice → t + a ∉ L.lattice → L.derivWeierstrassP (t + a) * (L.weierstrassP t - L.weierstrassP a) ^ 2 = -(3 * L.weierstrassP a ^ 2 - L.g₂ / 4) * L.derivWeierstrassP t := by
  intro L a t ha h2 ht hta
  have hd : L.derivWeierstrassP a = 0 :=
    (GlobalTheory.derivWeierstrassP_eq_zero_iff L ha).2 (by rw [← two_mul]; exact h2)
  have hne : L.weierstrassP t ≠ L.weierstrassP a := by
    intro h
    rcases (GlobalTheory.weierstrassP_eq_iff L ht ha).1 h with h' | h'
    · apply hta
      have := L.lattice.add_mem h' h2
      rwa [show t - a + 2 * a = t + a by ring] at this
    · exact hta h'
  obtain ⟨h1, h3⟩ := GlobalTheory.weierstrassP_add L ht ha hne
  have e1 := L.derivWeierstrassP_sq t ht
  have e2 := L.derivWeierstrassP_sq a ha
  rw [h3, h1]
  rw [hd] at e2 ⊢
  have hd0 : L.weierstrassP t - L.weierstrassP a ≠ 0 := sub_ne_zero.2 hne
  generalize L.weierstrassP t = x at *
  generalize L.weierstrassP a = e at *
  generalize L.derivWeierstrassP t = y at *
  generalize L.g₂ = g at *
  generalize L.g₃ = k at *
  have hq : ((y - 0) / (x - e)) ^ 2 = (4 * (x ^ 2 + x * e + e ^ 2) - g) / (x - e) := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hd0) hd0]
    linear_combination (x - e) * (e1 - e2)
  rw [hq]
  field_simp
  ring

end GlobalTheory
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivWeierstrassP_add_half_period' : ∀ (L : PeriodPair) (a t : ℂ), a ∉ L.lattice → 2 * a ∈ L.lattice → t ∉ L.lattice → t + a ∉ L.lattice → L.derivWeierstrassP (t + a) * (L.weierstrassP t - L.weierstrassP a) ^ 2 = -(3 * L.weierstrassP a ^ 2 - L.g₂ / 4) * L.derivWeierstrassP t := by
  atlas_forward_decl GlobalTheory.derivWeierstrassP_add_half_period
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem prod_derivWeierstrassP_translates_eq_Δ : ∀ (L : PeriodPair) (a b t : ℂ),
    a ∉ L.lattice → b ∉ L.lattice → a + b ∉ L.lattice → 2 * a ∈ L.lattice →
    2 * b ∈ L.lattice → 2 * t ∉ L.lattice →
    L.derivWeierstrassP t * L.derivWeierstrassP (t + a) * L.derivWeierstrassP (t + b) *
      L.derivWeierstrassP (t + (a + b)) = (latticeCurve L).Δ := by
  intro L a b t ha hb hc h2a h2b h2t
  have h2c : 2 * (a + b) ∈ L.lattice := by
    rw [mul_add]; exact L.lattice.add_mem h2a h2b
  have hshift : ∀ u : ℂ, 2 * u ∈ L.lattice → t + u ∉ L.lattice := by
    intro u hu htu
    apply h2t
    have := L.lattice.sub_mem (L.lattice.add_mem htu htu) hu
    convert this using 1; ring
  have ht : t ∉ L.lattice := by simpa using hshift 0 (by simp)
  have hroot : ∀ u : ℂ, u ∉ L.lattice → 2 * u ∈ L.lattice →
      4 * L.weierstrassP u ^ 3 - L.g₂ * L.weierstrassP u - L.g₃ = 0 := by
    intro u hu h2u
    rw [← L.derivWeierstrassP_sq u hu,
      (derivWeierstrassP_eq_zero_iff L hu).2 (by rwa [← two_mul])]
    ring
  have hne : ∀ u v : ℂ, u ∉ L.lattice → v ∉ L.lattice → 2 * v ∈ L.lattice →
      u + v ∉ L.lattice → L.weierstrassP u ≠ L.weierstrassP v := by
    intro u v hu hv h2v huv h
    rcases (weierstrassP_eq_iff L hu hv).1 h with h' | h'
    · apply huv
      have := L.lattice.add_mem h' h2v
      convert this using 1; ring
    · exact huv h'
  have h12 := hne a b ha hb h2b hc
  have h13 := hne a (a + b) ha hc h2c (by
    intro h; apply hb
    have := L.lattice.sub_mem h h2a
    convert this using 1; ring)
  have h23 := hne b (a + b) hb hc h2c (by
    intro h; apply ha
    have := L.lattice.sub_mem h h2b
    convert this using 1; ring)
  obtain ⟨hfac, hdisc⟩ := GlobalTheory.T.cubic_factor_and_discriminant_of_three_distinct_roots L.g₂ L.g₃ _ _ _ (hroot a ha h2a) (hroot b hb h2b)
    (hroot _ hc h2c) h12 h13 h23
  have e1 := GlobalTheory.T.derivWeierstrassP_add_half_period' L a t ha h2a ht (hshift a h2a)
  have e2 := GlobalTheory.T.derivWeierstrassP_add_half_period' L b t hb h2b ht (hshift b h2b)
  have e3 := GlobalTheory.T.derivWeierstrassP_add_half_period' L (a + b) t hc h2c ht (hshift _ h2c)
  have hsq := L.derivWeierstrassP_sq t ht
  rw [hfac] at hsq
  have hd : L.derivWeierstrassP t ≠ 0 := fun h =>
    h2t (by rw [two_mul]; exact (derivWeierstrassP_eq_zero_iff L ht).1 h)
  rw [latticeCurve_Δ]
  generalize L.derivWeierstrassP t = d at *
  generalize L.derivWeierstrassP (t + a) = d₁ at *
  generalize L.derivWeierstrassP (t + b) = d₂ at *
  generalize L.derivWeierstrassP (t + (a + b)) = d₃ at *
  generalize L.weierstrassP t = x at *
  generalize L.weierstrassP a = e₁ at *
  generalize L.weierstrassP b = e₂ at *
  generalize L.weierstrassP (a + b) = e₃ at *
  apply mul_left_cancel₀ (pow_ne_zero 3 hd)
  calc d ^ 3 * (d * d₁ * d₂ * d₃) = (d ^ 2) ^ 2 * (d₁ * d₂ * d₃) := by ring
    _ = 16 * ((d₁ * (x - e₁) ^ 2) * (d₂ * (x - e₂) ^ 2) * (d₃ * (x - e₃) ^ 2)) := by
        rw [hsq]; ring
    _ = -(16 * ((3 * e₁ ^ 2 - L.g₂ / 4) * (3 * e₂ ^ 2 - L.g₂ / 4) *
          (3 * e₃ ^ 2 - L.g₂ / 4))) * d ^ 3 := by
        rw [e1, e2, e3]; ring
    _ = d ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by rw [hdisc]; ring

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant : ∀ (L : PeriodPair) (a b t : ℂ), a ∉ L.lattice → b ∉ L.lattice → a + b ∉ L.lattice → 2 * a ∈ L.lattice → 2 * b ∈ L.lattice → 2 * t ∉ L.lattice → L.derivWeierstrassP t * L.derivWeierstrassP (t + a) * L.derivWeierstrassP (t + b) * L.derivWeierstrassP (t + (a + b)) = (latticeCurve L).Δ := by
  atlas_forward_decl GlobalTheory.CMModel.prod_derivWeierstrassP_translates_eq_Δ
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology ComplexConjugate

namespace GlobalTheory.CMModel

theorem mem_lattice_of_even_kerReps :
    ∀ (L : PeriodPair) (α a : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
      Even S.card → α * a ∈ L.lattice → 2 * a ∈ L.lattice → a ∈ L.lattice := by
  intro L α a S hα hst hS hev h1 h2
  obtain ⟨m, hm⟩ := hev
  have hc := kerRepsCard L α S hα hst hS
  obtain ⟨t, n, ht, -, -⟩ := mulStableIntegral L α hst
  have hN : α * conj α = 2 * (m : ℂ) + 1 := by
    rw [Complex.mul_conj, ← hc, hm]
    push_cast
    ring
  have key : a = t • (α * a) - α * (α * a) - m • (2 * a) := by
    rw [zsmul_eq_mul, nsmul_eq_mul, ← ht]
    linear_combination (-a) * hN
  rw [key]
  exact sub_mem (sub_mem (zsmul_mem h1 t) (hst _ h1)) (nsmul_mem h2 m)

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier : ∀ (L : PeriodPair) (α a : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → α * a ∈ L.lattice → 2 * a ∈ L.lattice → a ∈ L.lattice := by
  atlas_forward_decl GlobalTheory.CMModel.mem_lattice_of_even_kerReps
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem tendsto_cube_mul_derivWeierstrassP (L : PeriodPair) :
    Filter.Tendsto (fun z : ℂ => z ^ 3 * L.derivWeierstrassP z) (𝓝[≠] 0) (𝓝 (-2)) := by
  have hw : ContinuousAt (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) 0 := by
    have := (L.analyticAt_derivWeierstrassPExcept 0).continuousAt
    fun_prop
  have h1 : Filter.Tendsto (fun z : ℂ ↦ z ^ 3 * L.derivWeierstrassPExcept 0 z - 2) (𝓝[≠] 0)
      (𝓝 (-2)) := by
    have := hw.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa using this
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  have h := L.derivWeierstrassPExcept_sub 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [← h]
  field_simp

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_cube_mul_derivWeierstrassP_neg_two : ∀ (L : PeriodPair), Filter.Tendsto (fun z : ℂ => z ^ 3 * L.derivWeierstrassP z) (𝓝[≠] 0) (𝓝 (-2)) := by
  atlas_forward_decl GlobalTheory.CMModel.tendsto_cube_mul_derivWeierstrassP
end

section
section
open Filter PeriodPair Polynomial
open scoped Topology

namespace GlobalTheory

private lemma eq_zero_of_tendsto_eval_cobounded {B : ℂ[X]} {l : Filter ℂ} [l.NeBot] {u : ℂ → ℂ}
    (hu : Tendsto u l (Bornology.cobounded ℂ))
    (h : Tendsto (fun z ↦ B.eval (u z)) l (𝓝 0)) : B = 0 := by
  by_cases hd : 0 < B.degree
  · exfalso
    have h1 := B.tendsto_norm_atTop hd (tendsto_norm_atTop_iff_cobounded.mpr hu)
    have h2 := h.norm
    exact h1.not_tendsto (disjoint_nhds_atTop _).symm h2
  · rw [eq_C_of_degree_le_zero (not_lt.mp hd)] at h ⊢
    simp only [eval_C] at h
    rw [tendsto_nhds_unique tendsto_const_nhds h, C_0]

private lemma exists_eq_mul_of_three_roots {A : ℂ[X]} {a b c : ℂ} (hab : b ≠ a) (hac : c ≠ a)
    (hbc : c ≠ b) (ha : A.eval a = 0) (hb : A.eval b = 0) (hc : A.eval c = 0) :
    ∃ B : ℂ[X], A = (X - C a) * ((X - C b) * ((X - C c) * B)) := by
  obtain ⟨A₁, rfl⟩ := dvd_iff_isRoot.mpr ha
  have hb₁ : A₁.eval b = 0 := by simpa [sub_eq_zero, hab] using hb
  obtain ⟨A₂, rfl⟩ := dvd_iff_isRoot.mpr hb₁
  have hc₂ : A₂.eval c = 0 := by simpa [sub_eq_zero, hac, hbc] using hc
  obtain ⟨B, rfl⟩ := dvd_iff_isRoot.mpr hc₂
  exact ⟨B, rfl⟩

theorem eq_zero_of_odd_elliptic_of_tendsto : ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, z ∉ L.lattice → DifferentiableAt ℂ f z) → (∀ z l, z ∉ L.lattice → l ∈ L.lattice → f (z + l) = f z) → (∀ z, z ∉ L.lattice → f (-z) = -f z) → Filter.Tendsto (fun z : ℂ => z ^ 3 * f z) (𝓝[≠] 0) (𝓝 0) → ∀ z, z ∉ L.lattice → f z = 0 := by
  classical
  intro L f hd hp ho ht
  let g : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else f z ^ 2
  have hgd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z := fun z hz ↦ by
    refine ((hd z hz).pow 2).congr_of_eventuallyEq ?_
    filter_upwards [eventually_notMem_periodLattice L hz] with w hw
    simp [g, hw]
  have hgp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z := fun z l hl ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz, add_mem hz hl]
    · simp [g, hz, L.lattice.add_mem_iff_left hl, hp z l hz hl]
  have hge : ∀ z, g (-z) = g z := fun z ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz]
    · simp [g, hz, ho z hz]
  have hgt : Tendsto (fun z : ℂ ↦ z ^ 6 * g z) (𝓝[≠] 0) (𝓝 0) := by
    have h1 := ht.pow 2
    rw [zero_pow two_ne_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
    simp only [g, hw, if_false]
    ring
  have hgm : MeromorphicAt g 0 := by
    refine ⟨6, Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_⟩
    · filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
      have := hgd w hw
      fun_prop
    · rw [continuousAt_iff_punctured_nhds]
      simpa using hgt
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L hgm hgd hgp hge
  have hhalf : ∀ z ∉ L.lattice, z + z ∈ L.lattice → A.eval (℘[L] z) = 0 := fun z hz h2 ↦ by
    have h1 := hp (-z) (z + z) (by simpa using hz) h2
    rw [ho z hz, show -z + (z + z) = z by ring, CharZero.eq_neg_self_iff] at h1
    rw [← hA z hz]
    simp [g, h1]
  have key : ∀ a b : ℚ, (a * L.ω₁ + b * L.ω₂ : ℂ) ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 :=
    fun a b ↦ L.mul_ω₁_add_mul_ω₂_mem_lattice
  let p : ℚ → ℚ → ℂ := fun a b ↦ a * L.ω₁ + b * L.ω₂
  have padd : ∀ a b c d, p a b + p c d = p (a + c) (b + d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have psub : ∀ a b c d, p a b - p c d = p (a - c) (b - d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have pm : ∀ a b, p a b ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 := key
  have n1 : p (1 / 2) 0 ∉ L.lattice := by rw [pm]; norm_num
  have n2 : p 0 (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  have n3 : p (1 / 2) (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  obtain ⟨B, hB⟩ := exists_eq_mul_of_three_roots (A := A) (a := ℘[L] (p (1 / 2) 0))
    (b := ℘[L] (p 0 (1 / 2))) (c := ℘[L] (p (1 / 2) (1 / 2)))
    (by rw [Ne, weierstrassP_eq_iff L n2 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n2, padd, psub, pm, pm]; norm_num)
    (hhalf _ n1 (by rw [padd, pm]; norm_num))
    (hhalf _ n2 (by rw [padd, pm]; norm_num))
    (hhalf _ n3 (by rw [padd, pm]; norm_num))
  set a := ℘[L] (p (1 / 2) 0)
  set b := ℘[L] (p 0 (1 / 2))
  set c := ℘[L] (p (1 / 2) (1 / 2))
  let w : ℂ → ℂ := fun z ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1
  have hw : AnalyticAt ℂ w 0 := by fun_prop
  have hw' : ∀ z ≠ 0, w z = z ^ 2 * ℘[L] z := fun z hz ↦ by
    simpa [hz, w] using (L.ite_eq_one_sub_sq_mul_weierstrassP 0 (zero_mem _) z).symm
  let q : ℂ → ℂ := fun z ↦ (w z - z ^ 2 * a) * ((w z - z ^ 2 * b) * (w z - z ^ 2 * c))
  have hq : ContinuousAt q 0 := by
    have := hw.continuousAt
    fun_prop
  have hq0 : q 0 = 1 := by simp [q, w]
  have hq1 : Tendsto q (𝓝[≠] 0) (𝓝 1) := hq0 ▸ hq.tendsto.mono_left nhdsWithin_le_nhds
  have hB0 : B = 0 := by
    refine eq_zero_of_tendsto_eval_cobounded (tendsto_weierstrassP_cobounded L (zero_mem _)) ?_
    have h1 := hgt.div hq1 one_ne_zero
    rw [zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0, self_mem_nhdsWithin,
      hq1.eventually_ne one_ne_zero] with z hz hz0 hqz
    rw [Pi.div_apply, div_eq_iff hqz, hA z hz, hB]
    simp only [q, hw' z hz0, eval_mul, eval_sub, eval_X, eval_C]
    ring
  intro z hz
  have h1 := hA z hz
  rw [hB, hB0] at h1
  simpa [g, hz] using h1

end GlobalTheory
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_odd_elliptic_of_tendsto' : ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, z ∉ L.lattice → DifferentiableAt ℂ f z) → (∀ z l, z ∉ L.lattice → l ∈ L.lattice → f (z + l) = f z) → (∀ z, z ∉ L.lattice → f (-z) = -f z) → Filter.Tendsto (fun z : ℂ => z ^ 3 * f z) (𝓝[≠] 0) (𝓝 0) → ∀ z, z ∉ L.lattice → f z = 0 := by
  atlas_forward_decl GlobalTheory.eq_zero_of_odd_elliptic_of_tendsto
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.KerPerm

theorem prod_eq_of_perm_mod (Λ : Submodule ℤ ℂ) (T : Finset ℂ) (f ψ : ℂ → ℂ)
    (hψ : ∀ z l, l ∈ Λ → ψ (z + l) = ψ z)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a - b ∈ Λ → a = b)
    (hmap : ∀ t ∈ T, ∃ u ∈ T, f t - u ∈ Λ)
    (hinj : ∀ a b, f a - f b ∈ Λ → a - b ∈ Λ) :
    ∏ t ∈ T, ψ (f t) = ∏ t ∈ T, ψ t := by
  classical
  choose g hgT hg using hmap
  have ginj : ∀ a (ha : a ∈ T) b (hb : b ∈ T), g a ha = g b hb → a = b := by
    intro a ha b hb h
    apply hsep a ha b hb
    apply hinj
    have := Λ.sub_mem (hg a ha) (hg b hb)
    rw [h] at this
    simpa using this
  refine Finset.prod_bij g hgT ginj ?_ ?_
  · intro b hb
    obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le g hgT
      (fun a b ha hb h => ginj a ha b hb h) le_rfl b hb
    exact ⟨a, ha, h.symm⟩
  · intro a ha
    have := hψ (g a ha) _ (hg a ha)
    simpa using this

theorem prod_ker_translate_neg : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (φ : ℂ → ℂ), IsKerReps L α S → MulStable L α → (∀ z l, l ∈ L.lattice → φ (z + l) = φ z) → (∀ z s, α * s ∈ L.lattice → φ (z + s) * ∏ t ∈ S, φ (z + s + t) = φ z * ∏ t ∈ S, φ (z + t)) ∧ ∀ z, ∏ t ∈ S, φ (z - t) = ∏ t ∈ S, φ (z + t) := by
  classical
  intro L α S φ ⟨h1, h2, h3⟩ _ hφ
  have h0 : (0 : ℂ) ∉ S := fun h => (h1 0 h).2 L.lattice.zero_mem
  have hψ : ∀ z : ℂ, ∀ x l, l ∈ L.lattice → φ (z + (x + l)) = φ (z + x) := by
    intro z x l hl
    rw [← add_assoc, hφ _ _ hl]
  refine ⟨fun z s hs => ?_, fun z => ?_⟩
  · have key := prod_eq_of_perm_mod L.lattice (insert 0 S) (fun t => s + t) (fun x => φ (z + x)) (hψ z)
      (by
        intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with rfl | ha <;> rcases Finset.mem_insert.1 hb with rfl | hb
        · rfl
        · exact absurd (by simpa using hab) (h1 b hb).2
        · exact absurd (by simpa using hab) (h1 a ha).2
        · exact h2 a ha b hb hab)
      (by
        intro t ht
        have hk : α * (s + t) ∈ L.lattice := by
          rw [mul_add]
          refine L.lattice.add_mem hs ?_
          rcases Finset.mem_insert.1 ht with rfl | ht
          · simp
          · exact (h1 t ht).1
        by_cases hm : s + t ∈ L.lattice
        · exact ⟨0, Finset.mem_insert_self _ _, by simpa using hm⟩
        · obtain ⟨P, hP, h⟩ := h3 _ hk hm
          exact ⟨P, Finset.mem_insert_of_mem hP, h⟩)
      (by
        intro a b h
        simpa using h)
    rw [Finset.prod_insert h0, Finset.prod_insert h0] at key
    simpa [add_assoc] using key
  · have key := prod_eq_of_perm_mod L.lattice S (fun t => -t) (fun x => φ (z + x)) (hψ z) h2
      (by
        intro t ht
        refine h3 (-t) ?_ ?_
        · rw [mul_neg]; exact L.lattice.neg_mem (h1 t ht).1
        · intro h; exact (h1 t ht).2 (by simpa using h))
      (by
        intro a b h
        have := L.lattice.neg_mem h
        convert this using 1
        ring)
    simpa [sub_eq_add_neg] using key

end GlobalTheory.KerPerm
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_kernel_multiplier_translate_neg : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ) (φ : ℂ → ℂ), IsKerReps L α S → MulStable L α → (∀ z l, l ∈ L.lattice → φ (z + l) = φ z) → (∀ z s, α * s ∈ L.lattice → φ (z + s) * ∏ t ∈ S, φ (z + s + t) = φ z * ∏ t ∈ S, φ (z + t)) ∧ ∀ z, ∏ t ∈ S, φ (z - t) = ∏ t ∈ S, φ (z + t) := by
  atlas_forward_decl GlobalTheory.KerPerm.prod_ker_translate_neg
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem derivWeierstrassP_mul_prod_translate_kernel :
    ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → Formalism.L2.Th1.F.MulStable L α → IsKerReps L α S →
      Even S.card → ∀ z, α * z ∉ L.lattice →
      L.derivWeierstrassP z * ∏ t ∈ S, L.derivWeierstrassP (z + t)
        = (∏ t ∈ S, L.derivWeierstrassP t) * α ^ 3 * L.derivWeierstrassP (α * z) := by
  intro L α S hα hst hS hev z hz
  have hper : ∀ z l, l ∈ L.lattice → L.derivWeierstrassP (z + l) = L.derivWeierstrassP z :=
    fun z l hl => L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  obtain ⟨k1, k2⟩ := GlobalTheory.T.prod_kernel_multiplier_translate_neg L α S L.derivWeierstrassP hS hst hper
  have hdiff : ∀ w, w ∉ L.lattice → DifferentiableAt ℂ L.derivWeierstrassP w := fun w hw =>
    (L.analyticOnNhd_derivWeierstrassP w hw).differentiableAt
  have hcancel : ∀ w : ℂ, α * (w / α) = w := fun w => mul_div_cancel₀ w hα
  have h1 : ∀ w, w ∉ L.lattice → w / α ∉ L.lattice := fun w hw h => by
    have := hst _ h
    rw [hcancel] at this
    exact hw this
  have h2 : ∀ w, w ∉ L.lattice → ∀ t ∈ S, w / α + t ∉ L.lattice := fun w hw t ht h => by
    have h3 := hst _ h
    rw [mul_add, hcancel] at h3
    have h4 := L.lattice.sub_mem h3 (hS.1 t ht).1
    rw [add_sub_cancel_right] at h4
    exact hw h4
  set c : ℂ := ∏ t ∈ S, L.derivWeierstrassP t with hc
  have key := GlobalTheory.T.eq_zero_of_odd_elliptic_of_tendsto' L
    (fun w => L.derivWeierstrassP (w / α) * ∏ t ∈ S, L.derivWeierstrassP (w / α + t)
      - c * α ^ 3 * L.derivWeierstrassP w) ?_ ?_ ?_ ?_ (α * z) hz
  · have e : α * z / α = z := mul_div_cancel_left₀ z hα
    simp only [e] at key
    exact sub_eq_zero.mp key
  · intro w hw
    have d0 : DifferentiableAt ℂ (fun w : ℂ => w / α) w := differentiableAt_id.div_const α
    refine DifferentiableAt.sub (DifferentiableAt.mul ?_ ?_) ((hdiff w hw).const_mul _)
    · exact DifferentiableAt.comp w (g := L.derivWeierstrassP) (hdiff _ (h1 w hw)) d0
    · refine DifferentiableAt.fun_finsetProd fun t ht => ?_
      exact DifferentiableAt.comp w (g := L.derivWeierstrassP) (f := fun w : ℂ => w / α + t)
        (hdiff _ (h2 w hw t ht)) (d0.add_const t)
  · intro w l _ hl
    have := k1 (w / α) (l / α) (by rw [hcancel]; exact hl)
    simp only [add_div, this, hper w l hl]
  · intro w _
    have e1 : ∏ t ∈ S, L.derivWeierstrassP (-w / α + t) = ∏ t ∈ S, L.derivWeierstrassP (w / α + t) := by
      rw [← k2 (w / α)]
      have : ∀ t ∈ S, L.derivWeierstrassP (-w / α + t) = (-1) * L.derivWeierstrassP (w / α - t) := by
        intro t _
        rw [neg_one_mul, ← L.derivWeierstrassP_neg]
        congr 1
        ring
      rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, hev.neg_one_pow, one_mul]
    simp only [e1]
    rw [neg_div, L.derivWeierstrassP_neg, L.derivWeierstrassP_neg]
    ring
  · have c0 := GlobalTheory.T.tendsto_cube_mul_derivWeierstrassP_neg_two L
    have tdiv : Filter.Tendsto (fun w : ℂ => w / α) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun w : ℂ => w / α) := continuous_id.div_const α
      simpa using this.tendsto 0
    have tdiv' : Filter.Tendsto (fun w : ℂ => w / α) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tdiv.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact div_ne_zero hw hα
    have t1 := c0.comp tdiv'
    have t2 : Filter.Tendsto (fun w : ℂ => ∏ t ∈ S, L.derivWeierstrassP (w / α + t)) (𝓝[≠] 0) (𝓝 c) := by
      refine tendsto_finsetProd S fun t ht => ?_
      have ht' := (hdiff t (hS.1 t ht).2).continuousAt.tendsto
      have : Filter.Tendsto (fun w : ℂ => w / α + t) (𝓝[≠] 0) (𝓝 t) := by
        simpa using (tdiv.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).add_const t
      exact ht'.comp this
    have t3 := ((t1.const_mul (α ^ 3)).mul t2).sub (c0.const_mul (c * α ^ 3))
    have e : α ^ 3 * (-2) * c - c * α ^ 3 * (-2) = 0 := by ring
    rw [e] at t3
    refine t3.congr fun w => ?_
    simp only [Function.comp]
    field_simp

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → ∀ z, α * z ∉ L.lattice → L.derivWeierstrassP z * ∏ t ∈ S, L.derivWeierstrassP (z + t) = (∏ t ∈ S, L.derivWeierstrassP t) * α ^ 3 * L.derivWeierstrassP (α * z) := by
  atlas_forward_decl GlobalTheory.CMModel.derivWeierstrassP_mul_prod_translate_kernel
end

section
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem prod_derivWeierstrassP_kerReps_pow_four_mul :
    ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
      Even S.card →
      (∏ t ∈ S, L.derivWeierstrassP t) ^ 4 * α ^ 12 = (latticeCurve L).Δ ^ S.card := by
  intro L α S hα hst hS hev
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = L.ω₁ / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = L.ω₂ / 2 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = L.ω₁ / (4 * α) := ⟨_, rfl⟩
  have haL : a ∉ L.lattice := ha ▸ L.ω₁_div_two_notMem_lattice
  have hbL : b ∉ L.lattice := hb ▸ L.ω₂_div_two_notMem_lattice
  have habL : a + b ∉ L.lattice := by
    intro h
    have := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := 1 / 2) (β := 1 / 2)).mp
      (by convert h using 1; rw [ha, hb]; push_cast; ring)
    norm_num at this
  have ha2 : 2 * a ∈ L.lattice := by
    have : 2 * a = L.ω₁ := by rw [ha]; ring
    rw [this]; exact L.ω₁_mem_lattice
  have hb2 : 2 * b ∈ L.lattice := by
    have : 2 * b = L.ω₂ := by rw [hb]; ring
    rw [this]; exact L.ω₂_mem_lattice
  have hab2 : 2 * (a + b) ∈ L.lattice := by
    rw [mul_add]; exact add_mem ha2 hb2
  have hz2 : 2 * (α * z) ∉ L.lattice := by
    have : 2 * (α * z) = L.ω₁ / 2 := by rw [hz]; field_simp; ring
    rw [this]; exact L.ω₁_div_two_notMem_lattice
  have two : ∀ x, x ∈ L.lattice → 2 * x ∈ L.lattice := fun x hx => by
    rw [two_mul]; exact add_mem hx hx
  have hshift : ∀ c, 2 * c ∈ L.lattice → α * (z + c) ∉ L.lattice := by
    intro c hc h
    apply hz2
    have := sub_mem (two _ h) (hst _ hc)
    convert this using 1; ring
  have hz1 : α * z ∉ L.lattice := fun h => hz2 (two _ h)
  have hαc : ∀ c, 2 * c ∈ L.lattice → 2 * (α * c) ∈ L.lattice := fun c hc => by
    have := hst _ hc
    convert this using 1; ring
  have h0 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev z hz1
  have h1 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + a) (hshift a ha2)
  have h2 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + b) (hshift b hb2)
  have h3 := GlobalTheory.T.derivWeierstrassP_mul_prod_translate_of_kernel_reps L α S hα hst hS hev (z + (a + b)) (hshift _ hab2)
  have hzz : 2 * z ∉ L.lattice := fun h => hz2 (hαc z h)
  have hL0 := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b z haL hbL habL ha2 hb2 hzz
  have hLt : ∀ t ∈ S, L.derivWeierstrassP (z + t) * L.derivWeierstrassP (z + a + t)
      * L.derivWeierstrassP (z + b + t) * L.derivWeierstrassP (z + (a + b) + t)
        = (latticeCurve L).Δ := by
    intro t ht
    have h2t : 2 * (z + t) ∉ L.lattice := by
      intro h
      apply hz2
      have := sub_mem (hαc _ h) (two _ (hS.1 t ht).1)
      convert this using 1; ring
    have := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L a b (z + t) haL hbL habL ha2 hb2 h2t
    rw [← this, add_right_comm z a t, add_right_comm z b t, add_right_comm z (a + b) t]
  have hR := GlobalTheory.T.product_derivWeierstrassP_half_periods_discriminant L (α * a) (α * b) (α * z)
    (fun h => haL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α a S hα hst hS hev h ha2))
    (fun h => hbL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α b S hα hst hS hev h hb2))
    (fun h => habL (GlobalTheory.T.not_mem_half_lattice_of_odd_multiplier L α (a + b) S hα hst hS hev (by rwa [mul_add]) hab2))
    (hαc a ha2) (hαc b hb2) hz2
  rw [← mul_add α a b, ← mul_add, ← mul_add, ← mul_add] at hR
  have hP : (∏ t ∈ S, L.derivWeierstrassP (z + t)) * (∏ t ∈ S, L.derivWeierstrassP (z + a + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + b + t))
      * (∏ t ∈ S, L.derivWeierstrassP (z + (a + b) + t)) = (latticeCurve L).Δ ^ S.card := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl hLt, Finset.prod_const]
  apply mul_left_cancel₀ (latticeCurve_Δ_ne_zero L)
  have hall := congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h1) h2) h3
  rw [← hP]
  nth_rewrite 1 [← hR]
  rw [← hL0]
  linear_combination -hall

end GlobalTheory.CMModel
end

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' : ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S → Even S.card → (∏ t ∈ S, L.derivWeierstrassP t) ^ 4 * α ^ 12 = (latticeCurve L).Δ ^ S.card := by
  atlas_forward_decl GlobalTheory.CMModel.prod_derivWeierstrassP_kerReps_pow_four_mul
end
