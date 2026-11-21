import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentVectorGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentLatticeLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientsOfVectorGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientSupportHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HolomorphicPeriodicityExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem pointNorm_eq_norm_mul (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    X.pnorm la G z = ‖G z‖ * X.pnorm la (fun _ => (1 : ℂ)) z := by
  simp only [Data.pnorm, norm_one, one_mul]

theorem pointNorm_nonneg (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    0 ≤ X.pnorm la G z := by
  unfold Data.pnorm
  refine mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => ?_)
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem hatNorm_nonneg (la : Wt X.Ψ r) (G : Frame X.Ψ r → ℂ) (z : Frame X.Ψ r) :
    0 ≤ X.hatN la G z := by
  unfold Data.hatN
  refine Real.sSup_nonneg fun t ht => ?_
  obtain ⟨x', -, -, rfl⟩ := ht
  exact X.pointNorm_nonneg la G x'


end Data

theorem epsilonZero_spec {r : ℕ} (X : DataX E r) (c1 w : ℝ) (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧ flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤ 1 ∧
    ∀ ε, 0 < ε → ε < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w →
      w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) * ((4 * fdeg E : ℕ) : ℝ)) +
        ((4 * fdeg E : ℕ) : ℝ) + 2 <
        (fdeg E : ℝ) ^ 2 / ((X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 * ε) := by
  have hf1 : 1 ≤ (fdeg E : ℝ) := one_le_field_half_degree
  have hd0 : 0 < dE E := field_discr_constant_pos
  have hg0 : (0 : ℝ) < X.g := by exact_mod_cast X.g_pos
  have hNC0 : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
  generalize hK : (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) = K2
  have hK1 : 1 ≤ K2 := by
    rw [← hK]
    have : 0 ≤ (X.g : ℝ) * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := by positivity
    linarith
  have hN : ((4 * fdeg E : ℕ) : ℝ) = 4 * (fdeg E : ℝ) := by push_cast; ring
  generalize hR : w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * K2 * ((4 * fdeg E : ℕ) : ℝ)) +
      ((4 * fdeg E : ℕ) : ℝ) + 2 = R2
  have hR0 : 0 < R2 := by
    rw [← hR, hN]
    have : 0 ≤ 4 * (fdeg E : ℝ) * Real.log (2 * K2 * (4 * (fdeg E : ℝ))) :=
      mul_nonneg (by linarith) (Real.log_nonneg (by nlinarith))
    linarith
  generalize hB : (X.g * dE E ^ 2) ^ 2 * (X.NC : ℝ) ^ 2 * c1 = B
  have hB0 : 0 < B := by rw [← hB]; positivity
  have heq : flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w = min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) := by
    rw [← hB, ← hR, ← hK, hN]
    simp only [flowEpsilonBound]
    rw [← rootDiscriminant_eq_rpow]
  rw [heq]
  refine ⟨lt_min one_pos (div_pos (by positivity) (mul_pos hB0 hR0)), min_le_left _ _, fun ε hε hεlt => ?_⟩
  have hle : min 1 ((fdeg E : ℝ) ^ 2 / (B * R2)) ≤ (fdeg E : ℝ) ^ 2 / (B * R2) := min_le_right _ _
  have h1 := (le_div_iff₀ (mul_pos hB0 hR0)).1 (le_of_lt (lt_of_lt_of_le hεlt hle))
  rw [lt_div_iff₀ (mul_pos hB0 hε)]
  have hε' : ε * (B * R2) < (fdeg E : ℝ) ^ 2 := by
    have h2 := (lt_div_iff₀ (mul_pos hB0 hR0)).1 (lt_of_lt_of_le hεlt hle)
    exact h2
  calc R2 * (B * ε) = ε * (B * R2) := by ring
    _ < (fdeg E : ℝ) ^ 2 := hε'

set_option maxHeartbeats 1000000 in
theorem unipotent_vector_eq_smul_component {r : ℕ} (X : DataX E r) (z0 : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) (K : ℂ)
    (a : X.Ψ → Fin 2 → ℂ) (ha : a τ = ![-(K * (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
        X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ))), K / (X.NC : ℂ)]) :
    X.uvec ![ξ, (X.NC : E) • x] a τ = K • X.ucomp z0 ξ (X.embV x) τ := by
  have hNCc : (X.NC : ℂ) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
  rw [X.toData.orthogonal_component_apply]
  funext j
  simp only [Data.uvec, ha, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Data.emb, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul, map_natCast]
  generalize X.Hf z0 τ (fun a => τ.1 (x a)) (fun a => τ.1 (ξ a)) /
    X.Hf z0 τ (fun a => τ.1 (ξ a)) (fun a => τ.1 (ξ a)) = q
  field_simp
  ring

set_option maxHeartbeats 1000000 in
theorem short_vector_setting_exists {r : ℕ} (X : DataX E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} {ξ : Fin r → E}
    {ν : X.Ψ → ℝ} {c1 w : ℝ} {z0 : Frame X.Ψ r} (hH : ShortVectorHypotheses X la P ξ ν c1 w z0) {x : Fin r → E}
    (hxL : x ∈ X.L') (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    ∃ a, IsotropicFlowSetting X la P ξ ν c1 w z0 x a := by
  have hξ0 : ξ ≠ 0 := hH.2.2.1.2.2
  have hune : ∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0 := X.toData.orthogonal_component_ne_zero z0 hξ0 hxE
  obtain ⟨K, hK⟩ : ∃ K : X.Ψ → ℂ, ∀ τ,
      K τ = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) := ⟨_, fun _ => rfl⟩
  refine ⟨fun τ => ![-(K τ * (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ))), K τ / (X.NC : ℂ)],
    hH, hxL, hxξ, hxx, hxE, hune, fun τ => ?_⟩
  rw [← hK τ]
  exact unipotent_vector_eq_smul_component X z0 ξ x τ (K τ) _ rfl

theorem isotropic_pair_in_lattice {r : ℕ} (X : DataX E r) {ξ x : Fin r → E} (hiso : X.IsIso ξ) (hxL : x ∈ X.L')
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) (hxE : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] ∧ ∀ i, ![ξ, (X.NC : E) • x] i ∈ X.Λ := by
  have hξ0 : ξ ≠ 0 := hiso.2.2
  have hξx : herm X.Gm ξ x = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm x ξ, hxξ, HermitianTraceFormVanishing.cc_zero]
  refine ⟨⟨fun i k => ?_, ?_⟩, fun i => ?_⟩
  · fin_cases i <;> fin_cases k <;>
      simp [hiso.2.1, HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_right, hxξ, hξx, hxx]
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right hξ0, rfl⟩
    · exfalso
      have hNCE : (X.NC : E) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
      have htN : t * (X.NC : E) ≠ 0 := mul_ne_zero ht hNCE
      have h1 : (t * (X.NC : E)) • x = -(s • ξ) := by
        rw [mul_smul]; exact eq_neg_of_add_eq_zero_right hst
      apply hxE (-(s / (t * (X.NC : E))))
      calc x = (t * (X.NC : E))⁻¹ • ((t * (X.NC : E)) • x) := by
            rw [smul_smul, inv_mul_cancel₀ htN, one_smul]
        _ = -(s / (t * (X.NC : E))) • ξ := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  · fin_cases i
    · exact hiso.1
    · exact X.NC_sub x hxL

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pointwise_sum_bound {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ)
    (F : (X.Ψ → Fin 2 → Fin 2 → ℂ) → Frame X.Ψ r → ℂ) (T : (X.Ψ → Fin 2 → Fin 2 → ℂ) → ℝ)
    (w S1 : ℝ) (hS10 : 0 ≤ S1) (z0 : Frame X.Ψ r)
    (hexp : ∀ z ∈ X.dom, Summable (fun χ => ‖F χ z‖) → HasSum (fun χ => F χ z) (Q z))
    (hpt : ∀ χ, ∀ z ∈ X.dom, X.SameFlag z0 z →
      X.pnorm la (F χ) z ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * T χ) * S1)
    (hsum : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} => Real.exp (-Real.pi * T j.1))) :
    ∀ z ∈ X.dom, X.SameFlag z0 z → X.pnorm la Q z ≤
      2 ^ (w / 2) * (∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1)) * S1 := by
  intro z hz hfl
  have hN := X.pointNorm_nonneg la (fun _ => (1 : ℂ)) z
  have hC : 0 ≤ (2 : ℝ) ^ (w / 2) := by positivity
  have htn : 0 ≤ ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  rw [X.pointNorm_eq_norm_mul la Q z]
  rcases hN.eq_or_lt with hN0 | hNpos
  · rw [← hN0, mul_zero]
    exact mul_nonneg (mul_nonneg hC htn) hS10
  have hpt' : ∀ χ, ‖F χ z‖ * X.pnorm la (fun _ => (1 : ℂ)) z ≤
      2 ^ (w / 2) * Real.exp (-Real.pi * T χ) * S1 := fun χ => by
    rw [← X.pointNorm_eq_norm_mul la (F χ) z]; exact hpt χ z hz hfl
  have hb : ∀ χ, ‖F χ z‖ ≤
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z * Real.exp (-Real.pi * T χ) := by
    intro χ
    rw [div_mul_eq_mul_div, le_div_iff₀ hNpos]
    linarith [hpt' χ]
  have hzero : ∀ χ, χ ∉ {χ | ∃ y ∈ X.dom, F χ y ≠ 0} → F χ z = 0 := fun χ hχ => by
    by_contra h; exact hχ ⟨z, hz, h⟩
  have hsupp : Function.support (fun χ => ‖F χ z‖) ⊆ {χ | ∃ y ∈ X.dom, F χ y ≠ 0} := by
    intro χ hχ
    by_contra h
    exact hχ (by simp only [hzero χ h, norm_zero])
  have hsumS : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} => ‖F j.1 z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hb j.1) (hsum.mul_left _)
  have hsumAll : Summable (fun χ => ‖F χ z‖) := by
    refine (Function.Injective.summable_iff Subtype.val_injective fun χ hχ => ?_).1 hsumS
    rw [norm_eq_zero]
    exact hzero χ fun h => hχ ⟨⟨χ, h⟩, rfl⟩
  have hQ := hexp z hz hsumAll
  have hnorm : ‖Q z‖ ≤ ∑' χ, ‖F χ z‖ := by
    rw [← hQ.tsum_eq]; exact norm_tsum_le_tsum_norm hsumAll
  rw [← tsum_subtype_eq_of_support_subset hsupp] at hnorm
  have hsum2 : Summable (fun j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0} =>
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z * Real.exp (-Real.pi * T j.1)) :=
    hsum.mul_left _
  have hle : ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, ‖F j.1 z‖ ≤
      2 ^ (w / 2) * S1 / X.pnorm la (fun _ => (1 : ℂ)) z *
        ∑' j : ↥{χ | ∃ y ∈ X.dom, F χ y ≠ 0}, Real.exp (-Real.pi * T j.1) := by
    rw [← tsum_mul_left]
    exact hsumS.tsum_le_tsum (fun j => hb j.1) hsum2
  have hm := mul_le_mul_of_nonneg_right (hnorm.trans hle) hN
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self hNpos.ne', mul_one] at hm
  linarith

private theorem herm_swap_eq_cc_of_conj_symm {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (x y : Fin r → E) : herm G y x = cc (herm G x y) := by
  have hG' : ∀ a b, IsCMField.complexConj E (G a b) = G b a := hG
  simp only [herm, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hG' a b]
  ring

private theorem herm_add_smul_self_expand {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) (c : E) :
    herm G (x + c • y) (x + c • y) =
      herm G x x + c * herm G y x + cc c * herm G x y + c * cc c * herm G y y := by
  simp only [herm, cc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem shortVectorBound_of_coefficient_bounds (h3 : FourierCoefficientProperties (E := E)) (h3q : CuspCoefficientBound (E := E)) (h6p : FlowCoefficientDecay (E := E))
    (h7 : CoefficientIndexLowerBound (E := E)) (h8 : CoefficientHeightBound (E := E)) (h9 : CountingExponentialSum)
    (h10 : IsotropicOutsideLine (E := E)) : ShortVectorBound (E := E) := by
  intro r X la P ξ ν c1 w z0 hH x hxL hxξ hxE
  have hH0 := hH
  obtain ⟨-, hSS, hiso, hc1, -, -, hw1, -, hχ, hz0, hsup⟩ := hH
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  obtain ⟨hep_pos, hep_le, hep_spec⟩ := epsilonZero_spec X c1 w hc1 hw1
  obtain ⟨hxx, α, hx'L, hx'ξ, hucomp, -, hmajNC⟩ :=
    h10 r X ξ hiso z0 hz0 x hxL hxξ hxE fun τ => lt_of_lt_of_le (hcon τ) hep_le
  set x' := x + ((X.NA : E) * (α : E)) • ξ with hx'
  have hx'E : ∀ e : E, x' ≠ e • ξ := by
    intro e he
    exact hxE (e - (X.NA : E) * (α : E)) (by rw [sub_smul, ← he, hx']; abel)
  have hx'x' : herm X.Gm x' x' = 0 := by
    rw [hx', herm_add_smul_self_expand, herm_swap_eq_cc_of_conj_symm X.Gm X.Gm_herm x ξ, hxξ, hiso.2.1, hxx]
    simp [cc]
  obtain ⟨a, hset⟩ := short_vector_setting_exists X hH0 hx'L hx'ξ hx'x' hx'E
  obtain ⟨hpair, hmem⟩ := isotropic_pair_in_lattice X hiso hx'L hx'ξ hx'x' hx'E
  obtain ⟨ε, hε0, hεlt, hεmaj⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧
      ∀ τ, X.maj z0 τ (X.ucomp z0 ξ (X.embV x') τ) ≤ ε := by
    let s : Finset ℝ := (Finset.univ.image fun τ => X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ∪
      {flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w / 2}
    have hs : s.Nonempty := ⟨_, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
    refine ⟨s.max' hs, lt_of_lt_of_le (half_pos hep_pos)
      (s.le_max' _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))), ?_, fun τ => ?_⟩
    · have hm := s.max'_mem hs
      rcases Finset.mem_union.1 hm with h | h
      · obtain ⟨τ, -, hτ⟩ := Finset.mem_image.1 h
        rw [← hτ]; exact hcon τ
      · rw [Finset.mem_singleton.1 h]; linarith
    · rw [hucomp]
      exact s.le_max' _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ τ)))
  obtain ⟨hQd, hQb, hQz⟩ := h3q r X ![ξ, (X.NC : E) • x'] hpair hmem la P hSS hχ ν
  have hL3 := h3 r X.toData ![ξ, (X.NC : E) • x'] X.g hpair X.g_pos la (X.fj la ξ ν P) hQd hQb hQz
  have hK : 1 ≤ 1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
      (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := by
    have h1 : 0 < 2 * c1 + 1 := by linarith
    have h2 : 0 ≤ (X.g : ℝ) * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
      (X.NA : ℝ) ^ 2)) * (2 * c1 + 1) := mul_nonneg (by positivity) h1.le
    linarith
  have hN : (1 : ℝ) ≤ ((4 * fdeg E : ℕ) : ℝ) := by
    have := one_le_field_half_degree (E := E)
    push_cast
    linarith
  have hlow : ∀ j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
      X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0},
      w + ((4 * fdeg E : ℕ) : ℝ) * Real.log (2 * (1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 *
        (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) *
        ((4 * fdeg E : ℕ) : ℝ)) + ((4 * fdeg E : ℕ) : ℝ) + 2 <
      2 * ∑ τ, (X.chiAt j.1 a τ).re := fun j =>
    lt_of_lt_of_le (hep_spec ε hε0 hεlt) (h7 r X la P ξ ν c1 w z0 x' a ε hset hε0 hεmaj j.1 j.2)
  have hcount : ∀ t0 : ℝ, 1 ≤ t0 →
      {j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} |
          2 * ∑ τ, (X.chiAt j.1 a τ).re ≤ t0}.Finite ∧
      ({j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} |
          2 * ∑ τ, (X.chiAt j.1 a τ).re ≤ t0}.ncard : ℝ) ≤
        ((1 + X.g * dE E ^ 2 * ((X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 *
          (X.NA : ℝ) ^ 2)) * (2 * c1 + 1)) * t0) ^ ((4 * fdeg E : ℕ) : ℝ) := by
    intro t0 ht0
    obtain ⟨hfin, hcard⟩ := h8 r X la P ξ ν c1 w z0 x' a hset hmajNC t0 ht0
    have hpre : {j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0} |
          2 * ∑ τ, (X.chiAt j.1 a τ).re ≤ t0} =
        Subtype.val ⁻¹' {χ | (∃ y ∈ X.dom, X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0) ∧
          2 * ∑ τ, (X.chiAt χ a τ).re ≤ t0} := by
      ext j
      exact ⟨fun h => ⟨j.2, h⟩, fun h => h.2⟩
    rw [hpre]
    refine ⟨hfin.preimage Subtype.val_injective.injOn, ?_⟩
    rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
      (fun χ hχ => ⟨⟨χ, hχ.1⟩, rfl⟩), Real.rpow_natCast]
    exact hcard
  have hw0 : 0 ≤ w := le_trans zero_le_one hw1
  obtain ⟨hsumT, hlt⟩ := h9 _ _ w hK hN hw0 ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
      X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0}
    (fun j => 2 * ∑ τ, (X.chiAt j.1 a τ).re) hlow hcount
  have hS10 : 0 ≤ sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} :=
    Real.sSup_nonneg fun t ⟨y, _, ht⟩ => ht ▸ X.hatNorm_nonneg la _ y
  have hbound := pointwise_sum_bound X.toData la (X.fj la ξ ν P)
    (fun χ => X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P))
    (fun χ => 2 * ∑ τ, (X.chiAt χ a τ).re) w _ hS10 z0 (hL3 0).2.2
    (fun χ z hz hfl => h6p r X la P ξ ν c1 w z0 x' a hset χ z hz hfl) hsumT
  have hhat : X.hatN la (X.fj la ξ ν P) z0 ≤ 2 ^ (w / 2) *
      (∑' j : ↥{χ : X.Ψ → Fin 2 → Fin 2 → ℂ | ∃ y ∈ X.dom,
        X.fz ![ξ, (X.NC : E) • x'] X.g χ (X.fj la ξ ν P) y ≠ 0},
        Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt j.1 a τ).re))) *
      sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} := by
    unfold Data.hatN
    refine csSup_le ⟨_, z0, hz0.1, fun τ => rfl, rfl⟩ ?_
    rintro t ⟨z, hz, hfl, rfl⟩
    exact hbound z hz hfl
  have hm := mul_le_mul_of_nonneg_right hlt.le hS10
  linarith only [hsup, hhat, hm]

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cusp_coefficient_bound_of_unipotent_lattice_lift (hL2 : UnipotentLatticeLift (E := E)) : CuspCoefficientBound (E := E) := by
  intro r X u hu huΛ la P hP hchi ν
  have hiso : X.IsIso (u 0) := ⟨huΛ 0, hu.1 0 0, hu.2.ne_zero 0⟩
  refine ⟨CuspCoefficientFlow.fj_diffOn X.toData la P hP.1 hiso ν, ?_, ?_⟩
  · intro x hx b hb
    have hfl : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b) =
        rmul (X.flow (u 0) (fun τ => (s τ : ℂ)) x) b := fun s => by
      funext τ
      show X.flowMat (u 0) τ (s τ : ℂ) * (mat x τ * mat b τ) =
        (X.flowMat (u 0) τ (s τ : ℂ) * mat x τ) * mat b τ
      rw [Matrix.mul_assoc]
    have hPb : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b)) =
        bchar la b * P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl]
      exact hP.1.1.2.1 _ (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1 b hb
    unfold Data.fj
    split_ifs with h1 h2
    · simp_rw [hPb, mul_assoc]
      rw [integral_const_mul]
      ring
    · simp
    · simp
  · intro b hb x hx
    let a0 : X.Ψ → Fin 2 → ℂ := fun _ => ![1, 0]
    have hemb : X.embV (u 0) = X.uvec u a0 := by
      funext τ
      simp [Data.uvec, a0, Fin.sum_univ_two, Data.embV]
    have hfl : ∀ (s : X.Ψ → ℝ) y, X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.Zb u (fun τ i k => (s τ : ℂ) * a0 τ i * conj (a0 τ k)) y := fun s y => by
      rw [show X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.flowV (X.embV (u 0)) (fun τ => (s τ : ℂ)) y from rfl, hemb, Data.flowV_uvec]
    have hZ : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x) =
        X.Zb u b (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl, hfl, Data.Zb_Zb X.toData u hu.1, Data.Zb_Zb X.toData u hu.1, add_comm]
    have hPZ : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x)) =
        P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hZ]
      exact (hL2 r X u hu huΛ).2.1 la P hP.1.1 hchi b hb _
        (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1
    unfold Data.fj
    simp_rw [hPZ]

end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem cusp_coefficient_quantitative_holds : CuspCoefficientBound (E := E) := CuspCoefficientQuantitative.cusp_coefficient_bound_of_unipotent_lattice_lift unipotent_lattice_lift

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem flow_coefficient_decay_holds (h1 : UnipotentVectorGroup (E := E)) (h2 : UnipotentLatticeLift (E := E))
    (h3 : FourierCoefficientProperties (E := E)) (h3d : FourierCoefficientSupport (E := E)) (h4 : HolomorphicPeriodicityExtension (E := E)) :
    FlowCoefficientDecay (E := E) := by
  intro r X la P ξ ν c1 w z0 x a hS χ z hz hf
  obtain ⟨hH, hxL, hxξ, hxx, hne, hxp0, hua⟩ := hS
  obtain ⟨-, hSS, hξ, -, -, -, -, hw, hχ, hz0, -⟩ := hH
  set u : Fin 2 → Fin r → E := ![ξ, (X.NC : E) • x] with hu
  set e := X.uvec u a with he
  set Q := X.fj la ξ ν P with hQ
  set S1 := sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la Q y} with hS1
  have hpair := FlowIsotropicPairs.isIsoPair_of X hξ hxξ hxx hne
  have hmem := FlowIsotropicPairs.mem_pair X hξ hxL
  obtain ⟨hiso, heξ, hHe, hce⟩ :=
    FlowIsotropicPairs.e_facts X.toData hξ.2.1 hξ.2.2 hxξ hxx hz0.1 e hxp0 hua
  obtain ⟨httv, hTD1⟩ := FlowIsotropicPairs.flow_facts X.toData hz0 e hiso heξ hHe hce hz hf
  have hTdom : X.flowV e (fun _ => -(I / 2)) z ∈ X.dom := hTD1.1

  obtain ⟨CP, hCP⟩ := hSS.1.2
  have hQb : ∀ y ∈ X.dom, X.pnorm la Q y ≤ CP := fun y hy =>
    FlowCoefficientBounds.fj_bound X.toData la P CP hCP hξ ν hy
  have hCP0 : 0 ≤ CP :=
    le_trans (mul_nonneg (norm_nonneg _) (FlowCoefficientBounds.nfac_pos X.toData hz la).le) (hQb z hz)
  have hhat : ∀ y ∈ X.dom, X.hatN la Q y ≤ CP := fun y _ =>
    Real.sSup_le (by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy') hCP0
  have hle_hat : ∀ y ∈ X.dom, X.pnorm la Q y ≤ X.hatN la Q y := fun y hy =>
    le_csSup ⟨CP, by rintro t ⟨y', hy', -, rfl⟩; exact hQb y' hy'⟩ ⟨y, hy, fun τ => rfl, rfl⟩
  have hle_S1 : ∀ y ∈ X.FramesOverBasis ξ, X.hatN la Q y ≤ S1 := fun y hy =>
    le_csSup ⟨CP, by rintro t ⟨y', hy', rfl⟩; exact hhat y' hy'.1⟩ ⟨y, hy, rfl⟩
  have hS10 : 0 ≤ S1 := le_trans (le_trans (mul_nonneg (norm_nonneg _)
    (FlowCoefficientBounds.nfac_pos X.toData hz0.1 la).le) (hle_hat z0 hz0.1)) (hle_S1 z0 hz0)

  obtain ⟨-, hL1⟩ := h1 r X.toData u hpair
  have hT1 : X.pnorm la (X.fz u X.g χ Q) (X.flowV e (fun _ => -(I / 2)) z) ≤ S1 := by
    refine FlowCoefficientBounds.fz_bound X.toData u X.g χ Q la hTdom S1 hS10 fun b hb => ?_
    obtain ⟨-, -, -, -, -, hnfZ, -, hD1Z, -, -⟩ := hL1 b hb
    have hZ : X.Zb u b (X.flowV e (fun _ => -(I / 2)) z) ∈ X.FramesOverBasis ξ := hD1Z _ hTD1
    rw [← hnfZ la _ hTdom]
    exact (hle_hat _ hZ.1).trans (hle_S1 _ hZ)
  have hRHS : 0 ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * S1 :=
    mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) hS10

  have hL3d : ∀ y ∈ X.dom, X.fz u X.g χ Q y =
      if (∀ τ, χ τ 0 0 = (ν τ : ℂ)) then X.fz u X.g χ P y else 0 := fun y hy =>
    h3d r X u hpair hmem la P hSS.1.1 hχ ν χ y hy
  by_cases hc : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
  swap
  · have h0 : X.fz u X.g χ Q z = 0 := by rw [hL3d z hz, if_neg hc]
    show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _
    rw [h0, norm_zero, zero_mul]
    exact hRHS
  have hGP : ∀ y ∈ X.dom, X.fz u X.g χ Q y = X.fz u X.g χ P y := fun y hy => by
    rw [hL3d y hy, if_pos hc]

  have hper := (h2 r X u hpair hmem).2.1 la P hSS.1.1 hχ
  obtain ⟨⟨hdiff, -, hcov⟩, -, -⟩ :=
    h3 r X.toData u X.g hpair X.g_pos la P hSS.1.1.1 hSS.1.1.2.1 hper χ

  obtain ⟨-, -, -, -, -, -, -, -, -, hRF⟩ := hL1 0 (fun τ i k => by simp)
  have hreal : ∀ s : X.Ψ → ℝ, X.fz u X.g χ P (X.flowV e (fun τ => (s τ : ℂ)) z) =
      cexp (4 * Real.pi * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * s τ) * X.fz u X.g χ P z := by
    intro s
    have hb : IsHermFam (fun τ (i k : Fin 2) => (s τ : ℂ) * a τ i * conj (a τ k)) := by
      intro τ i k
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    have hRF' : X.flowV e (fun τ => (s τ : ℂ)) z =
        X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) z := hRF a s z
    have hpr : X.pairR χ (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) =
        ∑ τ, (X.chiAt χ a τ).re * s τ := by
      unfold Data.pairR Data.chiAt
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      have : ∑ i, ∑ k, χ τ i k * ((s τ : ℂ) * a τ i * conj (a τ k)) =
          (s τ : ℂ) * ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      rw [this, Complex.re_ofReal_mul, mul_comm]
    rw [hRF', hcov _ hb z hz, hpr, Complex.ofReal_sum]
    simp only [Complex.ofReal_mul]
  have hL4 := h4 r X.toData e hiso (X.fz u X.g χ P) hdiff
    (fun τ => ((X.chiAt χ a τ).re : ℂ)) z hz hreal (fun _ => -(I / 2)) hTdom
  have hexp : 4 * (Real.pi : ℂ) * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * -(I / 2) =
      ((2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re : ℝ) : ℂ) := by
    rw [← Finset.sum_mul]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * ∑ τ, ((X.chiAt χ a τ).re : ℂ)) * Complex.I_sq
  rw [hexp] at hL4
  have hnorm : ‖X.fz u X.g χ P z‖ = Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
      ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ := by
    rw [hL4, norm_mul, Complex.norm_exp_ofReal, ← mul_assoc, ← Real.exp_add,
      show -Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re) + 2 * Real.pi * ∑ τ, (X.chiAt χ a τ).re = 0 by
        ring, Real.exp_zero, one_mul]

  have hq := m3bNorm_holds r X.toData e hiso la z hz (fun _ => -(I / 2)) hTdom
  have hq2 : X.nfac la z / X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤
      ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2) := by
    refine hq.2.trans (le_of_eq (Finset.prod_congr rfl fun τ _ => ?_))
    simp only [httv τ]
    norm_num [max_def]
  have hprod : ∏ τ, (2 : ℝ) ^ (X.spread la τ / 2) ≤ 2 ^ (w / 2) := by
    rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [← Finset.sum_div]
    linarith
  have hnT := FlowCoefficientBounds.nfac_pos X.toData hTdom la
  have hnf : X.nfac la z ≤ 2 ^ (w / 2) * X.nfac la (X.flowV e (fun _ => -(I / 2)) z) := by
    rw [div_le_iff₀ hnT] at hq2
    exact hq2.trans (mul_le_mul_of_nonneg_right hprod hnT.le)

  have hT1' : ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
      X.nfac la (X.flowV e (fun _ => -(I / 2)) z) ≤ S1 := by
    rw [← hGP _ hTdom]
    exact hT1
  show ‖X.fz u X.g χ Q z‖ * X.nfac la z ≤ _
  rw [hGP z hz, hnorm]
  calc Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ * X.nfac la z
      ≤ Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        ‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
          (2 ^ (w / 2) * X.nfac la (X.flowV e (fun _ => -(I / 2)) z)) := by gcongr
    _ = 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) *
        (‖X.fz u X.g χ P (X.flowV e (fun _ => -(I / 2)) z)‖ *
          X.nfac la (X.flowV e (fun _ => -(I / 2)) z)) := by ring
    _ ≤ 2 ^ (w / 2) * Real.exp (-Real.pi * (2 * ∑ τ, (X.chiAt χ a τ).re)) * S1 := by gcongr

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Finset

theorem pow_le_exp_of_log_bound {K N w m : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hw : 0 ≤ w)
    (hm : w + N * Real.log (2 * K * N) + N + 2 ≤ m) :
    (K * m) ^ N ≤ Real.exp (2 * m - w - 2) := by
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log (2 * K * N) := Real.log_nonneg (by nlinarith)
  have hNL : 0 ≤ N * Real.log (2 * K * N) := mul_nonneg hN0.le hL
  have hm0 : 0 < m := by linarith
  have hKm : 0 < K * m := mul_pos hK0 hm0
  have h1 : Real.log (K * m) = Real.log (2 * K * N) + Real.log (m / (2 * N)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (m / (2 * N)) ≤ m / (2 * N) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : N * (m / (2 * N)) = m / 2 := by
    field_simp
  have h4 := mul_le_mul_of_nonneg_left h2 hN0.le
  rw [Real.rpow_def_of_pos hKm]
  apply Real.exp_le_exp.mpr
  rw [h1]
  nlinarith

theorem counting_exponential_sum_holds : CountingExponentialSum := by
  intro K N w hK hN hw ι t ht hcount
  classical
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log (2 * K * N) := Real.log_nonneg (by nlinarith)
  have hNL : 0 ≤ N * Real.log (2 * K * N) := mul_nonneg hN0.le hL
  have ht3 : ∀ j, 3 < t j := fun j => by linarith [ht j]
  have hpi := Real.pi_gt_three
  set q : ℝ := Real.exp (2 - Real.pi) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < Real.exp (-1) := Real.exp_lt_exp.mpr (by linarith)
  have he1 : Real.exp (-1) < 1 / 2 := by
    have h2 : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
    rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hq12 : q < 1 / 2 := lt_trans hq1 he1
  have hbound : ∀ s : Finset ι, ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤
      Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) := by
    intro s
    obtain ⟨mj, hmj⟩ : ∃ mj : ι → ℕ, mj = fun j => ⌈t j⌉₊ := ⟨_, rfl⟩
    have hmj_ge : ∀ j, t j ≤ (mj j : ℝ) := fun j => by rw [hmj]; exact Nat.le_ceil _
    have hmj_lt : ∀ j, (mj j : ℝ) < t j + 1 := fun j => by
      rw [hmj]; exact Nat.ceil_lt_add_one (by linarith [ht3 j])
    have hmj4 : ∀ j, 4 ≤ mj j := fun j => by
      have h1 : (3 : ℝ) < mj j := lt_of_lt_of_le (ht3 j) (hmj_ge j)
      have h2 : (3 : ℕ) < mj j := by exact_mod_cast h1
      omega
    have step1 : ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ ∑ j ∈ s, Real.exp (-Real.pi * ((mj j : ℝ) - 1)) :=
      Finset.sum_le_sum (fun j _ => Real.exp_le_exp.mpr (by have := hmj_lt j; nlinarith [Real.pi_pos]))
    have step2 : ∀ y ∈ s.image mj, ∑ j ∈ s.filter (fun j => mj j = y),
        Real.exp (-Real.pi * ((mj j : ℝ) - 1)) ≤ Real.exp (Real.pi - w - 2) * q ^ y := by
      intro y hy
      obtain ⟨j0, _, hj0y⟩ := Finset.mem_image.mp hy
      have hyT : w + N * Real.log (2 * K * N) + N + 2 ≤ (y : ℝ) := by
        rw [← hj0y]; linarith [ht j0, hmj_ge j0]
      have hy1 : (1 : ℝ) ≤ y := by linarith
      have hsum : ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) =
          ((s.filter (fun j => mj j = y)).card : ℝ) * Real.exp (-Real.pi * ((y : ℝ) - 1)) := by
        rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]), Finset.sum_const,
          nsmul_eq_mul]
      have hcard : ((s.filter (fun j => mj j = y)).card : ℝ) ≤ Real.exp (2 * y - w - 2) := by
        obtain ⟨hfin, hle⟩ := hcount y hy1
        have hsub : ((s.filter (fun j => mj j = y) : Finset ι) : Set ι) ⊆ {j | t j ≤ (y : ℝ)} := by
          intro j hj
          have hj' := Finset.mem_filter.mp hj
          show t j ≤ (y : ℝ)
          rw [← hj'.2]
          exact hmj_ge j
        have h1 : (s.filter (fun j => mj j = y)).card ≤ {j | t j ≤ (y : ℝ)}.ncard := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard hsub hfin
        calc ((s.filter (fun j => mj j = y)).card : ℝ) ≤ ({j | t j ≤ (y : ℝ)}.ncard : ℝ) := by
              exact_mod_cast h1
          _ ≤ (K * y) ^ N := hle
          _ ≤ Real.exp (2 * y - w - 2) := pow_le_exp_of_log_bound hK hN hw hyT
      rw [hsum]
      calc ((s.filter (fun j => mj j = y)).card : ℝ) * Real.exp (-Real.pi * ((y : ℝ) - 1))
          ≤ Real.exp (2 * y - w - 2) * Real.exp (-Real.pi * ((y : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
        _ = Real.exp (Real.pi - w - 2) * q ^ y := by
            rw [hq, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
    have step3 : ∑ y ∈ s.image mj, Real.exp (Real.pi - w - 2) * q ^ y ≤
        Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      calc ∑ y ∈ s.image mj, q ^ y ≤ ∑ y ∈ Finset.Ico 4 (s.sup mj + 1), q ^ y := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro y hy
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
              rw [Finset.mem_Ico]
              exact ⟨hmj4 j, Nat.lt_succ_of_le (Finset.le_sup hj)⟩
            · intro y _ _
              exact pow_nonneg hq0 y
        _ ≤ q ^ 4 / (1 - q) := geom_sum_Ico_le_of_lt_one hq0 (by linarith)
    calc ∑ j ∈ s, Real.exp (-Real.pi * t j) ≤ ∑ j ∈ s, Real.exp (-Real.pi * ((mj j : ℝ) - 1)) := step1
      _ = ∑ y ∈ s.image mj, ∑ j ∈ s.filter (fun j => mj j = y), Real.exp (-Real.pi * ((mj j : ℝ) - 1)) :=
          (Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem mj hj) _).symm
      _ ≤ ∑ y ∈ s.image mj, Real.exp (Real.pi - w - 2) * q ^ y := Finset.sum_le_sum step2
      _ ≤ _ := step3
  have hnn : ∀ j, 0 ≤ Real.exp (-Real.pi * t j) := fun j => (Real.exp_pos _).le
  have hsumm : Summable (fun j => Real.exp (-Real.pi * t j)) := summable_of_sum_le hnn hbound
  refine ⟨hsumm, ?_⟩
  have htsum : ∑' j, Real.exp (-Real.pi * t j) ≤ Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q)) :=
    hsumm.tsum_le_of_sum_le hbound
  have h2w : (2 : ℝ) ^ (w / 2) ≤ Real.exp w := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have h1 : Real.log 2 < 2 := by linarith [Real.log_two_lt_d9]
    nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  have hq4 : q ^ 4 = Real.exp (8 - 4 * Real.pi) := by
    rw [hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hpos : 0 < 1 - q := by linarith
  calc (2 : ℝ) ^ (w / 2) * ∑' j, Real.exp (-Real.pi * t j)
      ≤ Real.exp w * (Real.exp (Real.pi - w - 2) * (q ^ 4 / (1 - q))) :=
        mul_le_mul h2w htsum (tsum_nonneg hnn) (Real.exp_pos _).le
    _ = Real.exp (6 - 3 * Real.pi) / (1 - q) := by
        rw [hq4, show Real.exp (6 - 3 * Real.pi) =
          Real.exp w * (Real.exp (Real.pi - w - 2) * Real.exp (8 - 4 * Real.pi)) by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring]
        ring
    _ < 1 / 2 := by
        have h4 : Real.exp (6 - 3 * Real.pi) < Real.exp (-3) := Real.exp_lt_exp.mpr (by linarith)
        have h5 : 4 < Real.exp 3 := by linarith [Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)]
        have h7 : Real.exp (-3) < 1 / 4 := by
          rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 3) (by norm_num)]
          linarith
        rw [div_lt_div_iff₀ hpos (by norm_num)]
        linarith

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem isotropic_outside_line_of_covering (hD3 : IntegerApproximationCount (E := E)) : IsotropicOutsideLine (E := E) := by
  intro r X ξ hξ z0 hz0 x hxL hxξ _hxne hsmall
  obtain ⟨hξΛ, hξξ, -⟩ := hξ
  obtain ⟨hzdom, hzD⟩ := hz0
  have hmaj_ne : ∀ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 ξ) ≠ 0 := fun τ h => by
    have h1 := hzD τ
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := fun τ => by
    rw [X.Hf_self hzdom τ]
    exact_mod_cast hmaj_ne τ
  have hu : ∀ (v : Fin r → E) (τ : X.Ψ), X.ucomp z0 ξ (X.embV v) τ = Data.emb τ.1 v -
      (X.Hf z0 τ (Data.emb τ.1 v) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := fun v τ => rfl
  have hxx : herm X.Gm x x = 0 := by
    apply UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int x hxL x hxL)
    have hΨ : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm x x)‖ < 1 := by
      intro τ
      have h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hxξ, map_zero]
      have h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0 := by
        rw [← hermC_conj τ.1 X.Gm_herm, h1, map_zero]
      have h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hξξ, map_zero]
      have hww : hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) =
          τ.1 (herm X.Gm x x) := by
        rw [hu x τ]
        simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right]
        rw [h1, h2, h3, hermC_emb]
        ring
      rw [← hww]
      exact lt_of_le_of_lt (UnipotentCoefficientShift.norm_hermC_le_maj hzdom τ _) (hsmall τ)
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact hΨ ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
          RingHom.ext fun a => by simp
        rw [X.cmType, hcc]
        exact hσ
      have h := hΨ ⟨_, hc⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  refine ⟨hxx, ?_⟩
  obtain ⟨α, hα⟩ := (hD3 r X.toData).1 (fun τ => -(X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) / (X.NA : ℂ))
  refine ⟨α, ?_⟩
  intro x'
  have hemb : ∀ τ : X.Ψ, Data.emb τ.1 x' =
      Data.emb τ.1 x + τ.1 ((X.NA : E) * α) • Data.emb τ.1 ξ := by
    intro τ
    funext a
    simp [x', Data.emb]
  have hx'L : x' ∈ X.L' := by
    apply X.L'.add_mem hxL
    have h1 : (X.NA : E) • ξ ∈ X.L' := X.NA_sub ξ hξΛ
    have h2 := X.L'.smul_mem α h1
    have h3 : α • ((X.NA : E) • ξ) = ((X.NA : E) * (α : E)) • ξ := by
      rw [← algebraMap_smul E α ((X.NA : E) • ξ), smul_smul]
      congr 1
      exact mul_comm _ _
    rwa [h3] at h2
  have hx'ξ : herm X.Gm x' ξ = 0 := by
    simp only [x']
    rw [HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hxξ, hξξ, mul_zero, add_zero]
  have hucomp : X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x) := by
    funext τ
    rw [hu x' τ, hu x τ, hemb τ, UnipotentCoefficientShift.ucomp_shift _ _ _ _ _ (hHne τ)]
  have hcoef : ∀ τ : X.Ψ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by
    intro τ
    rw [hemb τ, UnipotentCoefficientShift.coef_shift _ _ _ _ _ (hHne τ)]
    have hNA : (X.NA : ℂ) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
    set k := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hkdef
    have hk : (X.NA : ℂ) * (k / X.NA) = k := by field_simp
    have e : k + τ.1 ((X.NA : E) * α) = (X.NA : ℂ) * (τ.1 (α : E) - -k / X.NA) := by
      rw [map_mul, map_natCast]
      linear_combination (-1 : ℂ) * hk
    rw [e, norm_mul, Complex.norm_natCast]
    have hb : ‖τ.1 (α : E) - -k / X.NA‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := hα τ
    calc (X.NA : ℝ) * ‖τ.1 (α : E) - -k / X.NA‖ ≤ X.NA * (2 * (fdeg E : ℝ) ^ 2 * rdE E) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by ring
  refine ⟨hx'L, hx'ξ, hucomp, hcoef, ?_⟩
  intro τ
  have hembNC : Data.emb τ.1 ((X.NC : E) • x') = ((X.NC : ℝ) : ℂ) • Data.emb τ.1 x' := by
    funext a
    simp [Data.emb]
  rw [hembNC, UnipotentCoefficientShift.maj_smul hzdom, UnipotentCoefficientShift.maj_decomp hzdom τ _ _ (hHne τ)]
  have hw : Data.emb τ.1 x' - (X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ =
        X.ucomp z0 ξ (X.embV x) τ := by
    rw [← hucomp, hu x' τ]
  rw [hw]
  have hK := hcoef τ
  set K := ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ with hKdef
  set m := X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) with hmdef
  have hc2 : X.c τ ≤ 2 := by
    unfold Data.c
    rw [X.ξ0_abs τ]
    linarith [X.k0_le]
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hD := hzD τ
  have hm : m < 1 := hsmall τ
  have hK0 : 0 ≤ K := norm_nonneg _
  have h1 : X.c τ * m ≤ 2 := by nlinarith
  have h2 : K ^ 2 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hK hK hK0 (le_trans hK0 hK)]
  have h3 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) = X.c τ * m + K ^ 2 := by
    linear_combination K ^ 2 * hD
  have h4 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) ≤
      2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    rw [h3]
    linarith
  calc X.c τ * ((X.NC : ℝ) ^ 2 * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)))
      = (X.NC : ℝ) ^ 2 * (X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem isotropic_outside_line : IsotropicOutsideLine (E := E) := isotropic_outside_line_of_covering integerApproximationCount_holds

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private lemma card_le_sum_of_one_le_prod {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → ℝ) (hz : ∀ i, 0 < z i)
    (h1 : 1 ≤ ∏ i, z i) : (Fintype.card ι : ℝ) ≤ ∑ i, z i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have key := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Fintype.card ι : ℝ)) z
    (fun i _ => by positivity) hw (fun i _ => (hz i).le)
  rw [Real.finset_prod_rpow _ _ (fun i _ => (hz i).le), ← Finset.mul_sum] at key
  have h2 : 1 ≤ (∏ i, z i) ^ (1 / (Fintype.card ι : ℝ)) := Real.one_le_rpow h1 (by positivity)
  have h3 := h2.trans key
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hn] at h3
  linarith

private lemma prod_le_one_of_sum_le_card {ι : Type} [Fintype ι] [Nonempty ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hs : ∑ i, v i ≤ Fintype.card ι) : ∏ i, v i ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : ∑ _i : ι, (1 / (Fintype.card ι : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have key := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (Fintype.card ι : ℝ)) v
    (fun i _ => by positivity) hw (fun i _ => (hv i).le)
  rw [Real.finset_prod_rpow _ _ (fun i _ => (hv i).le), ← Finset.mul_sum] at key
  have h3 : 1 / (Fintype.card ι : ℝ) * ∑ i, v i ≤ 1 := by
    rw [one_div, inv_mul_le_iff₀ hn]; linarith
  by_contra hgt
  push_neg at hgt
  have := Real.one_lt_rpow hgt (by positivity : (0 : ℝ) < 1 / (Fintype.card ι : ℝ))
  linarith

private lemma card_sq_div_le_two_mul_sum_of_bounds {ι : Type} [Fintype ι] [Nonempty ι] (d ν A R : ι → ℝ) (N NC k0 c1 ε : ℝ)
    (hN : 0 < N) (hNC : 0 < NC) (hk0 : 0 < k0) (hk2 : k0 ≤ 2) (hε : 0 < ε) (hc1 : 0 < c1)
    (hd : ∀ i, 0 < d i) (hν : ∀ i, 0 < ν i) (hνs : ∑ i, ν i ≤ c1)
    (hprod : 1 ≤ ∏ i, (N ^ 2 * d i))
    (hA : ∀ i, 1 / (NC ^ 2 * k0 * ε) ≤ A i)
    (hq : ∀ i, d i * A i ≤ ν i * R i) :
    (Fintype.card ι : ℝ) ^ 2 / (N ^ 2 * NC ^ 2 * c1 * ε) ≤ 2 * ∑ i, R i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  set K : ℝ := 1 / (NC ^ 2 * k0 * ε) with hK
  have hKpos : 0 < K := by positivity
  have hR : ∀ i, d i / ν i * K ≤ R i := by
    intro i
    rw [div_mul_eq_mul_div, div_le_iff₀ (hν i)]
    calc d i * K ≤ d i * A i := mul_le_mul_of_nonneg_left (hA i) (hd i).le
      _ ≤ ν i * R i := hq i
      _ = R i * ν i := mul_comm _ _
  have hv : ∏ i, (n * ν i / c1) ≤ 1 := by
    apply prod_le_one_of_sum_le_card (fun i => n * ν i / c1) (fun i => by have := hν i; positivity)
    rw [← Finset.sum_div, ← Finset.mul_sum, div_le_iff₀ hc1]
    exact mul_le_mul_of_nonneg_left hνs hn.le
  have hvpos : 0 < ∏ i, (n * ν i / c1) :=
    Finset.prod_pos fun i _ => by have := hν i; positivity
  have hz : n ≤ ∑ i, (N ^ 2 * d i) / (n * ν i / c1) := by
    apply card_le_sum_of_one_le_prod _ (fun i => by have := hν i; have := hd i; positivity)
    rw [Finset.prod_div_distrib]
    exact (one_le_div hvpos).mpr (hv.trans hprod)
  have hsum : ∑ i, (N ^ 2 * d i) / (n * ν i / c1) = (N ^ 2 * c1 / n) * ∑ i, d i / ν i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hν i
    field_simp
  rw [hsum] at hz
  have hdν : n ^ 2 / (N ^ 2 * c1) ≤ ∑ i, d i / ν i := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hn] at hz
    nlinarith
  have h2K : 1 / (NC ^ 2 * ε) ≤ 2 * K := by
    rw [hK, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < NC ^ 2 * ε := by positivity
    nlinarith
  calc n ^ 2 / (N ^ 2 * NC ^ 2 * c1 * ε) = (1 / (NC ^ 2 * ε)) * (n ^ 2 / (N ^ 2 * c1)) := by
        field_simp
    _ ≤ (2 * K) * (n ^ 2 / (N ^ 2 * c1)) := mul_le_mul_of_nonneg_right h2K (by positivity)
    _ ≤ (2 * K) * ∑ i, d i / ν i := mul_le_mul_of_nonneg_left hdν (by positivity)
    _ = 2 * ∑ i, d i / ν i * K := by rw [← Finset.sum_mul]; ring
    _ ≤ 2 * ∑ i, R i := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hR i) (by norm_num)

theorem coefficient_index_lower_bound (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) : CoefficientIndexLowerBound (E := E) := by
  intro r X la P ξ ν c1 w z0 x a ε hS hε hmaj χ hy
  obtain ⟨hH, hxL, hxξ, hxx, hne, hu0, hu⟩ := hS
  obtain ⟨_, hSS, hIso, hc1, hνc1, _, _, _, hchar, hz0, _⟩ := hH
  have hpair := FlowIsotropicPairs.isIsoPair_of X hIso hxξ hxx hne
  have hmem := FlowIsotropicPairs.mem_pair X hIso hxL
  obtain ⟨y, hyd, hy⟩ := hy
  have hHF : IsHermFam χ ∧ X.IsFreqZ X.g χ := by
    by_contra hn
    apply hy
    unfold Data.fz
    rw [if_neg hn]
  have hSS' : X.IsBddSec la P ∧ _ := hSS
  have h3 := h3d r X ![ξ, (X.NC : E) • x] hpair hmem la P hSS'.1.1 hchar ν χ y hyd
  have hy' : X.fz ![ξ, (X.NC : E) • x] X.g χ
      (X.fj la ((![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) 0) ν P) y ≠ 0 := hy
  rw [h3] at hy'
  by_cases hcond : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
  swap
  · rw [if_neg hcond] at hy'
    exact absurd rfl hy'
  rw [if_pos hcond] at hy'
  have hPD := h5 r X ![ξ, (X.NC : E) • x] hpair hmem la P hSS hchar χ ⟨y, hyd, hy'⟩
  obtain ⟨β, -, hβ, hβint⟩ := (h2 r X ![ξ, (X.NC : E) • x] hpair hmem).2.2 χ hHF.1 hHF.2
  have hne0 : Nonempty X.Ψ := Fintype.card_pos_iff.mp (QuadraticCoefficientForms.card_Psi_pos (X := X.toData))

  have hz0dom : z0 ∈ X.dom := hz0.1
  have hmpos : ∀ τ, 0 < X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) :=
    fun τ => X.maj_pos hz0dom τ (hu0 τ)
  have hck : ∀ τ, X.c τ = X.k0 := by
    intro τ
    show 2 * ‖τ.1 X.ξ0‖ = X.k0
    rw [X.ξ0_abs τ]
    ring

  have ha1 : ∀ τ, Complex.normSq (a τ 1) *
      ((X.NC : ℝ) ^ 2 * X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) = 1 := by
    intro τ
    obtain ⟨T, hT, h⟩ : ∃ T : ℂ,
        T = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) ∧
        X.uvec ![ξ, (X.NC : E) • x] a τ = T • X.ucomp z0 ξ (X.embV x) τ := ⟨_, rfl, hu τ⟩
    have hV : X.ucomp z0 ξ (X.embV x) τ = Data.emb τ.1 x -
        (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
          Data.emb τ.1 ξ := rfl
    have hU : X.uvec ![ξ, (X.NC : E) • x] a τ =
        a τ 0 • Data.emb τ.1 ξ + a τ 1 • ((X.NC : ℂ) • Data.emb τ.1 x) := by
      ext i
      simp [Data.uvec, Data.emb, Fin.sum_univ_two, smul_eq_mul, map_mul, map_natCast]
    rw [hU, hV] at h
    set S := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)
    have h0 : (a τ 0 + T * S) • Data.emb τ.1 ξ + (a τ 1 * X.NC - T) • Data.emb τ.1 x = 0 := by
      ext i
      have hi := congrFun h i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      linear_combination hi
    have hq := QuadraticCoefficientForms.coef_zero hIso.2.2 hne τ.1 _ _ h0
    have hTa : a τ 1 * X.NC = T := sub_eq_zero.mp hq
    have hpos : 0 < X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) := by
      rw [hck τ]; exact mul_pos X.minWeight_pos (hmpos τ)
    have hT2 : Complex.normSq T = (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))⁻¹ := by
      rw [hT, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hpos.le]
    have h4 : Complex.normSq (a τ 1) * (X.NC : ℝ) ^ 2 =
        (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))⁻¹ := by
      rw [← hT2, ← hTa, Complex.normSq_mul, Complex.normSq_natCast]
      ring
    rw [hck τ] at h4 hpos
    rw [show Complex.normSq (a τ 1) * ((X.NC : ℝ) ^ 2 * X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))
        = (Complex.normSq (a τ 1) * (X.NC : ℝ) ^ 2) * (X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ))
        by ring, h4]
    exact inv_mul_cancel₀ hpos.ne'

  have hχβ : ∀ (τ : X.Ψ) i k, χ τ i k = τ.1 (β i k) := by
    intro τ i k; rw [hβ]; rfl
  have hdpos : ∀ τ, 0 < (Matrix.of (χ τ)).det.re ∧ (Matrix.of (χ τ)).det.im = 0 := by
    intro τ
    have h := (hPD τ).det_pos
    rw [Complex.lt_def] at h
    exact ⟨by simpa using h.1, by simpa using h.2.symm⟩
  have hνpos : ∀ τ, 0 < ν τ := by
    intro τ
    have h := (hPD τ).diag_pos (i := 0)
    rw [Matrix.of_apply, hcond τ] at h
    exact_mod_cast h

  set Nn : ℕ := X.g * dEnat E ^ 2 with hNn
  have hdE : dE E = (dEnat E : ℝ) := by
    unfold dE dEnat
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hNpos : 0 < (X.g : ℝ) * dE E ^ 2 := by
    rw [hdE]
    have h1 : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
    have h2 := X.g_pos
    positivity
  have hNcast : ((Nn : ℕ) : ℝ) = (X.g : ℝ) * dE E ^ 2 := by
    rw [hNn, hdE]; push_cast; ring
  set γ : E := (((X.g * dEnat E ^ 2 : ℕ) : E) * β 0 0) * (((X.g * dEnat E ^ 2 : ℕ) : E) * β 1 1) -
      (((X.g * dEnat E ^ 2 : ℕ) : E) * β 0 1) * (((X.g * dEnat E ^ 2 : ℕ) : E) * β 1 0) with hγ
  have hint : IsIntegral ℤ γ :=
    ((hβint 0 0).mul (hβint 1 1)).sub ((hβint 0 1).mul (hβint 1 0))
  have hγτ : ∀ τ : X.Ψ, τ.1 γ = ((Nn : ℂ)) ^ 2 * (Matrix.of (χ τ)).det := by
    intro τ
    rw [Matrix.det_fin_two, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply,
      hχβ, hχβ, hχβ, hχβ, hγ]
    simp only [map_sub, map_mul, map_natCast, hNn]
    push_cast
    ring
  have hnorm : ∀ τ : X.Ψ, ‖τ.1 γ‖ = ((X.g : ℝ) * dE E ^ 2) ^ 2 * (Matrix.of (χ τ)).det.re := by
    intro τ
    have hdet : (Matrix.of (χ τ)).det = (((Matrix.of (χ τ)).det.re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [(hdpos τ).2])
    rw [hγτ τ, norm_mul, norm_pow, Complex.norm_natCast, hNcast]
    congr 1
    conv_lhs => rw [hdet]
    rw [Complex.norm_real, Real.norm_of_nonneg (hdpos τ).1.le]
  have hγ0 : γ ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := hne0
    have := hnorm τ
    rw [h0, map_zero, norm_zero] at this
    have := (hdpos τ).1
    have := hNpos
    nlinarith [mul_pos (pow_pos hNpos 2) (hdpos τ).1]
  have hp := QuadraticCoefficientForms.one_le_prod_norm (X := X.toData) γ hint hγ0
  simp_rw [hnorm] at hp
  rw [Finset.prod_pow] at hp
  have hprod : 1 ≤ ∏ τ : X.Ψ, (((X.g : ℝ) * dE E ^ 2) ^ 2 * (Matrix.of (χ τ)).det.re) := by
    have hnn : 0 ≤ ∏ τ : X.Ψ, (((X.g : ℝ) * dE E ^ 2) ^ 2 * (Matrix.of (χ τ)).det.re) :=
      Finset.prod_nonneg fun τ _ => by have := (hdpos τ).1; positivity
    by_contra hlt
    push_neg at hlt
    have := pow_lt_one₀ hnn hlt (two_ne_zero)
    linarith

  have hq : ∀ τ : X.Ψ, (Matrix.of (χ τ)).det.re * Complex.normSq (a τ 1) ≤
      ν τ * (X.chiAt χ a τ).re := by
    intro τ
    have h := QuadraticCoefficientForms.quad2 (Matrix.of (χ τ)) (hPD τ).1 (a τ)
    simp only [Matrix.of_apply] at h
    rw [hcond τ, Complex.ofReal_re] at h
    exact h
  have hA : ∀ τ : X.Ψ, 1 / ((X.NC : ℝ) ^ 2 * X.k0 * ε) ≤ Complex.normSq (a τ 1) := by
    intro τ
    have h := ha1 τ
    have hm := hmpos τ
    have hme := hmaj τ
    have hNC : (0 : ℝ) < X.NC := by exact_mod_cast X.NC_pos
    have hk := X.minWeight_pos
    rw [div_le_iff₀ (by positivity)]
    have hns := Complex.normSq_nonneg (a τ 1)
    have : Complex.normSq (a τ 1) * ((X.NC : ℝ) ^ 2 * X.k0 * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ≤
        Complex.normSq (a τ 1) * ((X.NC : ℝ) ^ 2 * X.k0 * ε) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hme (by positivity)) hns
    linarith
  have key := card_sq_div_le_two_mul_sum_of_bounds (fun τ : X.Ψ => (Matrix.of (χ τ)).det.re) ν (fun τ => Complex.normSq (a τ 1))
    (fun τ => (X.chiAt χ a τ).re) ((X.g : ℝ) * dE E ^ 2) (X.NC : ℝ) X.k0 c1 ε hNpos
    (by exact_mod_cast X.NC_pos) X.minWeight_pos X.k0_le hε hc1 (fun τ => (hdpos τ).1) hνpos hνc1 hprod hA hq
  rw [QuadraticCoefficientForms.card_Psi (X := X.toData)] at key
  exact key

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace QuadraticOffDiagonalBounds

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quad_nonneg {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (v : Fin 2 → ℂ) :
    0 ≤ (∑ i, ∑ k, M i k * v i * conj (v k)).re := by
  have h := hM.dotProduct_mulVec_nonneg (star v)
  have e : dotProduct (star (star v)) ((Matrix.of M).mulVec (star v)) = ∑ i, ∑ k, M i k * v i * conj (v k) := by
    simp only [star_star, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.star_apply, ← starRingEnd_apply]
    ring
  rw [e] at h
  simpa using (Complex.le_def.mp h).1

theorem quad_comb {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (α β : ℂ)
    (v w : Fin 2 → ℂ) :
    (∑ i, ∑ k, M i k * (α • v + β • w) i * conj ((α • v + β • w) k)).re ≤
      (‖α‖ ^ 2 + ‖β‖ ^ 2) * ((∑ i, ∑ k, M i k * v i * conj (v k)).re +
        (∑ i, ∑ k, M i k * w i * conj (w k)).re) := by
  have hid : (∑ i, ∑ k, M i k * (α • v + β • w) i * conj ((α • v + β • w) k)) +
      (∑ i, ∑ k, M i k * (conj β • v - conj α • w) i * conj ((conj β • v - conj α • w) k)) =
      (α * conj α + β * conj β) * ((∑ i, ∑ k, M i k * v i * conj (v k)) +
        (∑ i, ∑ k, M i k * w i * conj (w k))) := by
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add,
      map_sub, map_mul, Complex.conj_conj]
    ring
  have h0 := quad_nonneg hM (conj β • v - conj α • w)
  have hαβ : α * conj α + β * conj β = ((‖α‖ ^ 2 + ‖β‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hre := congrArg Complex.re hid
  rw [Complex.add_re, hαβ, Complex.re_ofReal_mul, Complex.add_re] at hre
  linarith

theorem offdiag_le {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef)
    (h10 : M 1 0 = conj (M 0 1)) : 2 * ‖M 0 1‖ ≤ (M 0 0).re + (M 1 1).re := by
  have d0 := quad_nonneg hM ![1, 0]
  have d1 := quad_nonneg hM ![0, 1]
  simp [Fin.sum_univ_two] at d0 d1
  rcases eq_or_ne (M 0 1) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    linarith
  · have hn : 0 < ‖M 0 1‖ := norm_pos_iff.mpr h0
    have hs : M 0 1 * conj (M 0 1) = ((‖M 0 1‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have h := quad_nonneg hM ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)]
    have e : (∑ i, ∑ k, M i k * ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] i *
        conj (![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] k)) =
        ((‖M 0 1‖ ^ 2 : ℝ) : ℂ) * (M 0 0 + M 1 1) - ((2 * ‖M 0 1‖ ^ 3 : ℝ) : ℂ) := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        map_neg, Complex.conj_conj, Complex.conj_ofReal, h10]
      push_cast
      linear_combination (M 0 0 - 2 * ((‖M 0 1‖ : ℝ) : ℂ)) * hs
    rw [e] at h
    have h' := h
    simp only [Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re,
      Complex.ofReal_re] at h'
    by_contra hlt
    push_neg at hlt
    have hm := mul_lt_mul_of_pos_left hlt (pow_pos hn 2)
    nlinarith

variable {r : ℕ} {X : Data E r}

private theorem Hf_smul_add_smul_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) (a b : ℂ) :
    X.Hf z τ u (a • v + b • w) = conj a * X.Hf z τ u v + conj b * X.Hf z τ u w := by
  simp only [Data.Hf, hermC, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

theorem coord {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (f1 f2 e : Fin r → ℂ) (a0 a1 : ℂ)
    (c : ℝ) (he : e = a0 • f1 + a1 • f2) (h1 : c * (X.Hf z τ f1 f1).re = 1)
    (h2 : X.Hf z τ e f1 = 0) (h3 : c * (X.Hf z τ e e).re = 1) :
    ∃ p q : ℂ, q * a0 + p = 0 ∧ q * a1 = 1 ∧ ‖p‖ ^ 2 + ‖q‖ ^ 2 = c * (X.Hf z τ f2 f2).re := by
  have hc : ∀ u w, conj (X.Hf z τ u w) = X.Hf z τ w u := fun u w => UnipotentCoefficientShift.Hf_conj hz τ u w
  have hL : ∀ w, X.Hf z τ e w = a0 * X.Hf z τ f1 w + a1 * X.Hf z τ f2 w := by
    intro w
    rw [← hc w e, he, Hf_smul_add_smul_right, map_add, map_mul, map_mul, Complex.conj_conj, Complex.conj_conj,
      hc, hc]
  have h2' : a0 * X.Hf z τ f1 f1 + a1 * X.Hf z τ f2 f1 = 0 := by rw [← hL, h2]
  have hee : X.Hf z τ e e = conj a0 * X.Hf z τ e f1 + conj a1 * X.Hf z τ e f2 := by
    have := Hf_smul_add_smul_right z τ e f1 f2 a0 a1
    rwa [← he] at this
  rw [h2, mul_zero, zero_add, hL f2, ← hc f2 f1] at hee
  have hA : conj (X.Hf z τ f1 f1) = X.Hf z τ f1 f1 := hc f1 f1
  have hD : conj (X.Hf z τ f2 f2) = X.Hf z τ f2 f2 := hc f2 f2
  have hB : conj a1 * conj (X.Hf z τ f2 f1) = -(conj a0 * X.Hf z τ f1 f1) := by
    rw [← map_mul, show a1 * X.Hf z τ f2 f1 = -(a0 * X.Hf z τ f1 f1) by linear_combination h2',
      map_neg, map_mul, hA]
  have hee2 : X.Hf z τ e e = -(a0 * conj a0) * X.Hf z τ f1 f1 + (a1 * conj a1) * X.Hf z τ f2 f2 := by
    rw [hee]
    linear_combination a0 * hB
  have hAr : ((X.Hf z τ f1 f1).re : ℂ) = X.Hf z τ f1 f1 := Complex.conj_eq_iff_re.mp hA
  have hDr : ((X.Hf z τ f2 f2).re : ℂ) = X.Hf z τ f2 f2 := Complex.conj_eq_iff_re.mp hD
  have hre : (X.Hf z τ e e).re =
      -(‖a0‖ ^ 2) * (X.Hf z τ f1 f1).re + ‖a1‖ ^ 2 * (X.Hf z τ f2 f2).re := by
    rw [hee2, ← hAr, ← hDr, Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [hre] at h3
  have key : ‖a1‖ ^ 2 * (c * (X.Hf z τ f2 f2).re) = 1 + ‖a0‖ ^ 2 := by
    linear_combination h3 + ‖a0‖ ^ 2 * h1
  have ha1 : a1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at key
    nlinarith [sq_nonneg ‖a0‖]
  have hn : 0 < ‖a1‖ := norm_pos_iff.mpr ha1
  have hcd : c * (X.Hf z τ f2 f2).re = (1 + ‖a0‖ ^ 2) / ‖a1‖ ^ 2 := by
    rw [eq_div_iff (by positivity)]
    linear_combination key
  refine ⟨-a0 * a1⁻¹, a1⁻¹, by ring, inv_mul_cancel₀ ha1, ?_⟩
  rw [hcd, norm_mul, norm_neg, norm_inv]
  field_simp
  ring

end QuadraticOffDiagonalBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem coefficient_height_bound_of (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) (hD3 : IntegerApproximationCount (E := E)) : CoefficientHeightBound (E := E) := by
  intro r X la P ξ ν c1 w z0 x a hS hHmax t ht K2 S
  classical
  obtain ⟨hHyp, hxL, hxξ, hxx, hxne, hw0, hua⟩ := hS
  obtain ⟨-, hPSS, hξ, hc1, hνsum, -, -, -, hchar, hz0, -⟩ := hHyp
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  obtain ⟨hzdom, hzD⟩ := hz0
  have hNC : (X.NC : E) ≠ 0 := by exact_mod_cast X.NC_pos.ne'
  have hξx : herm X.Gm ξ x = 0 := by
    rw [← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm x ξ, hxξ]
    simp
  have hIso : IsIsoPair X.Gm ![ξ, (X.NC : E) • x] := by
    refine ⟨?_, ?_⟩
    · intro i k
      fin_cases i <;> fin_cases k <;>
        simp [HermitianTraceFormVanishing.herm_smul_left, HermitianTraceFormVanishing.herm_smul_right, hξξ, hxξ, hξx, hxx]
    · rw [LinearIndependent.pair_iff]
      intro s s' hst
      by_cases hs0 : s' = 0
      · subst hs0
        refine ⟨?_, rfl⟩
        simpa [hξ0] using hst
      · exfalso
        have hsn : s' * (X.NC : E) ≠ 0 := mul_ne_zero hs0 hNC
        apply hxne (-(s / (s' * (X.NC : E))))
        have h' : (s' * (X.NC : E)) • x = -(s • ξ) := by
          rw [mul_smul]
          exact eq_neg_of_add_eq_zero_right hst
        calc x = (s' * (X.NC : E))⁻¹ • ((s' * (X.NC : E)) • x) := by
              rw [smul_smul, inv_mul_cancel₀ hsn, one_smul]
          _ = -(s / (s' * (X.NC : E))) • ξ := by
              rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hΛ : ∀ i, (![ξ, (X.NC : E) • x] : Fin 2 → Fin r → E) i ∈ X.Λ := by
    intro i
    fin_cases i
    · simpa using hξΛ
    · simpa using X.NC_sub x hxL

  have hmem : ∀ χ ∈ S, IsHermFam χ ∧ X.IsFreqZ X.g χ ∧ (∀ τ, χ τ 0 0 = (ν τ : ℂ)) ∧
      (∀ τ, (Matrix.of (χ τ)).PosSemidef) := by
    intro χ hχ
    obtain ⟨⟨y, hy, hfz⟩, -⟩ := hχ
    have hHF : IsHermFam χ ∧ X.IsFreqZ X.g χ := by
      by_contra hn
      apply hfz
      unfold Data.fz
      rw [if_neg hn]
    have e := h3d r X ![ξ, (X.NC : E) • x] hIso hΛ la P hPSS.1.1 hchar ν χ y hy
    by_cases hν : ∀ τ, χ τ 0 0 = (ν τ : ℂ)
    · rw [if_pos hν] at e
      have hP : X.fz ![ξ, (X.NC : E) • x] X.g χ P y ≠ 0 := fun h0 => hfz (e.trans h0)
      exact ⟨hHF.1, hHF.2, hν,
        fun τ => (h5 r X _ hIso hΛ la P hPSS hchar χ ⟨y, hy, hP⟩ τ).posSemidef⟩
    · exfalso
      rw [if_neg hν] at e
      exact hfz e

  have hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := fun τ h => by
    have h1 := hzD τ
    rw [X.Hf_self hzdom τ] at h
    rw [Complex.ofReal_eq_zero.mp h, mul_zero] at h1
    exact zero_ne_one h1
  have hcoord : ∀ τ : X.Ψ, ∃ p q : ℂ, q * a τ 0 + p = 0 ∧ q * a τ 1 = 1 ∧
      ‖p‖ ^ 2 + ‖q‖ ^ 2 ≤ (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2) := by
    intro τ
    have hcpos : 0 < X.c τ := by
      unfold Data.c
      rw [X.ξ0_abs τ]
      linarith [X.minWeight_pos]
    have hmw : 0 < X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) := X.maj_pos hzdom τ (hw0 τ)
    have hc0 : X.c τ ≠ 0 := hcpos.ne'
    have hm0 : X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) ≠ 0 := hmw.ne'
    have hs : Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) ^ 2 =
        X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) := Real.sq_sqrt (mul_pos hcpos hmw).le
    have hcast : ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) =
        (((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℝ) : ℂ) := by
      simp
    have hua' : X.uvec ![ξ, (X.NC : E) • x] a τ =
        (((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℝ) : ℂ) •
          X.ucomp z0 ξ (X.embV x) τ := by
      rw [hua τ, hcast]
    have he : X.uvec ![ξ, (X.NC : E) • x] a τ =
        a τ 0 • Data.emb τ.1 ξ + a τ 1 • Data.emb τ.1 ((X.NC : E) • x) := by
      simp [Data.uvec, Fin.sum_univ_two]
    have h1 : X.c τ * (X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)).re = 1 := by
      rw [X.Hf_self hzdom, Complex.ofReal_re]
      exact hzD τ
    have hwf : X.Hf z0 τ (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 := by
      show X.Hf z0 τ (Data.emb τ.1 x - (X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
        X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0
      rw [UnipotentCoefficientShift.Hf_sub_left, UnipotentCoefficientShift.Hf_smul_left, div_mul_cancel₀ _ (hHne τ), sub_self]
    have h2e : X.Hf z0 τ (X.uvec ![ξ, (X.NC : E) • x] a τ) (Data.emb τ.1 ξ) = 0 := by
      rw [hua', UnipotentCoefficientShift.Hf_smul_left, hwf, mul_zero]
    have h3 : X.c τ * (X.Hf z0 τ (X.uvec ![ξ, (X.NC : E) • x] a τ)
        (X.uvec ![ξ, (X.NC : E) • x] a τ)).re = 1 := by
      rw [hua', X.Hf_self hzdom, Complex.ofReal_re, UnipotentCoefficientShift.maj_smul hzdom, inv_pow, hs]
      field_simp
    obtain ⟨p, q, hp1, hp2, hpq⟩ :=
      QuadraticOffDiagonalBounds.coord hzdom τ _ _ _ (a τ 0) (a τ 1) (X.c τ) he h1 h2e h3
    refine ⟨p, q, hp1, hp2, ?_⟩
    rw [hpq, X.Hf_self hzdom, Complex.ofReal_re]
    exact hHmax τ

  set Hm : ℝ := (X.NC : ℝ) ^ 2 * (2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2) with hHm
  have hHm1 : 1 ≤ Hm := by
    have h1 : (1 : ℝ) ≤ X.NC := by exact_mod_cast X.NC_pos
    have h2 : 0 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by positivity
    rw [hHm]
    nlinarith
  set B : ℝ := Hm * (c1 + t / 2) with hB
  have hB0 : 0 ≤ B := mul_nonneg (by linarith) (by linarith)
  have hent : ∀ χ ∈ S, ∀ τ : X.Ψ, ‖χ τ 0 1‖ ≤ B ∧ ‖χ τ 1 1‖ ≤ B := by
    intro χ hχ τ
    obtain ⟨hH, -, hν, hpsd⟩ := hmem χ hχ
    have hχt : 2 * ∑ τ, (X.chiAt χ a τ).re ≤ t := hχ.2
    have q00 : ∀ τ', (∑ i, ∑ k, χ τ' i k * (![1, 0] : Fin 2 → ℂ) i *
        conj ((![1, 0] : Fin 2 → ℂ) k)) = χ τ' 0 0 := by
      intro τ'
      simp [Fin.sum_univ_two]
    have q11 : (∑ i, ∑ k, χ τ i k * (![0, 1] : Fin 2 → ℂ) i * conj ((![0, 1] : Fin 2 → ℂ) k)) =
        χ τ 1 1 := by
      simp [Fin.sum_univ_two]
    have hνnn : ∀ τ', 0 ≤ ν τ' := by
      intro τ'
      have h := QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ') ![1, 0]
      rw [q00, hν τ', Complex.ofReal_re] at h
      exact h
    have hchinn : ∀ τ', 0 ≤ (X.chiAt χ a τ').re := fun τ' => QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ') (a τ')
    have hντ : ν τ ≤ c1 :=
      le_trans (Finset.single_le_sum (fun τ' _ => hνnn τ') (Finset.mem_univ τ)) hνsum
    have hchτ : (X.chiAt χ a τ).re ≤ t / 2 := by
      have := Finset.single_le_sum (fun τ' _ => hchinn τ') (Finset.mem_univ τ)
      linarith
    obtain ⟨p, q, hp1, hp2, hpq⟩ := hcoord τ
    have hvec : q • a τ + p • (![1, 0] : Fin 2 → ℂ) = ![0, 1] := by
      funext i
      fin_cases i
      · simp
        linear_combination hp1
      · simp
        linear_combination hp2
    have hc := QuadraticOffDiagonalBounds.quad_comb (hpsd τ) q p (a τ) ![1, 0]
    rw [hvec, q11, q00 τ, hν τ, Complex.ofReal_re] at hc
    have hchi : (∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)).re = (X.chiAt χ a τ).re := rfl
    rw [hchi] at hc
    have hre11 : (χ τ 1 1).re ≤ B := by
      calc (χ τ 1 1).re ≤ (‖q‖ ^ 2 + ‖p‖ ^ 2) * ((X.chiAt χ a τ).re + ν τ) := hc
        _ ≤ Hm * (c1 + t / 2) := by
            apply mul_le_mul (by linarith) (by linarith) (by linarith [hchinn τ, hνnn τ])
              (by linarith)
    have hnn11 : 0 ≤ (χ τ 1 1).re := by
      have h := QuadraticOffDiagonalBounds.quad_nonneg (hpsd τ) ![0, 1]
      rwa [q11] at h
    have hreal11 : χ τ 1 1 = ((χ τ 1 1).re : ℂ) :=
      (Complex.conj_eq_iff_re.mp (hH τ 1 1).symm).symm
    have hn11 : ‖χ τ 1 1‖ ≤ B := by
      rw [hreal11, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn11]
      exact hre11
    have hoff := QuadraticOffDiagonalBounds.offdiag_le (hpsd τ) (hH τ 0 1)
    rw [hν τ, Complex.ofReal_re] at hoff
    have hcB : c1 ≤ B := by
      have : c1 + t / 2 ≤ Hm * (c1 + t / 2) := by nlinarith
      linarith
    exact ⟨by linarith, hn11⟩

  have hdisc : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  obtain ⟨N0, hN0⟩ : ∃ n : ℕ, n = X.g * dEnat E ^ 2 := ⟨_, rfl⟩
  have hN0E : (N0 : E) ≠ 0 := by
    rw [hN0]
    exact_mod_cast (Nat.mul_pos X.g_pos (pow_pos hdisc 2)).ne'
  have hN0r : (N0 : ℝ) = X.g * dE E ^ 2 := by
    simp only [hN0, dEnat, dE, Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs]
  have hβ : ∀ χ ∈ S, ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧
      χ = X.embH β ∧ ∀ i k, IsIntegral ℤ ((N0 : E) * β i k) := by
    intro χ hχ
    obtain ⟨hH, hF, -, -⟩ := hmem χ hχ
    obtain ⟨β, hβ1, hβ2, hβ3⟩ := (h2 r X _ hIso hΛ).2.2 χ hH hF
    exact ⟨β, hβ1, hβ2, fun i k => by rw [hN0]; exact hβ3 i k⟩
  choose! β hβh hβe hβi using hβ
  have hent' : ∀ χ ∈ S, ∀ (τ : X.Ψ) (i k : Fin 2), χ τ i k = τ.1 (β χ i k) := fun χ hχ τ i k =>
    congrFun (congrFun (congrFun (hβe χ hχ) τ) i) k
  have hσ : ∀ χ ∈ S, ∀ i k : Fin 2, (∀ τ : X.Ψ, ‖χ τ i k‖ ≤ B) →
      ∀ σ : E →+* ℂ, ‖σ ((N0 : E) * β χ i k)‖ ≤ (N0 : ℝ) * B := by
    intro χ hχ i k hb σ
    rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    by_cases hs : σ ∈ X.Ψ
    · have h := hb ⟨σ, hs⟩
      rw [hent' χ hχ] at h
      exact h
    · have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
        RingHom.ext fun a => by simp
      have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        rw [X.cmType, hcc]
        exact hs
      have h := hb ⟨_, hc⟩
      rw [hent' χ hχ] at h
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  obtain ⟨hAfin, hAcard⟩ := (hD3 r X.toData).2 ((N0 : ℝ) * B) (mul_nonneg (Nat.cast_nonneg _) hB0)
  set A := {α : 𝓞 E | ∀ σ : E →+* ℂ, ‖σ (α : E)‖ ≤ (N0 : ℝ) * B} with hA
  let φ : (X.Ψ → Fin 2 → Fin 2 → ℂ) → E × E := fun χ => ((N0 : E) * β χ 0 1, (N0 : E) * β χ 1 1)
  have hmaps : ∀ χ ∈ S, φ χ ∈ (Subtype.val '' A) ×ˢ (Subtype.val '' A) := by
    intro χ hχ
    exact ⟨⟨⟨(N0 : E) * β χ 0 1, hβi χ hχ 0 1⟩, hσ χ hχ 0 1 (fun τ => (hent χ hχ τ).1), rfl⟩,
      ⟨⟨(N0 : E) * β χ 1 1, hβi χ hχ 1 1⟩, hσ χ hχ 1 1 (fun τ => (hent χ hχ τ).2), rfl⟩⟩
  have hinj : Set.InjOn φ S := by
    intro χ hχ χ' hχ' hφ
    obtain ⟨h01', h11'⟩ := Prod.mk.inj (hφ : ((N0 : E) * β χ 0 1, (N0 : E) * β χ 1 1) =
      ((N0 : E) * β χ' 0 1, (N0 : E) * β χ' 1 1))
    have h01 : β χ 0 1 = β χ' 0 1 := mul_left_cancel₀ hN0E h01'
    have h11 : β χ 1 1 = β χ' 1 1 := mul_left_cancel₀ hN0E h11'
    obtain ⟨hH, -, hν, -⟩ := hmem χ hχ
    obtain ⟨hH', -, hν', -⟩ := hmem χ' hχ'
    have e01 : ∀ τ, χ τ 0 1 = χ' τ 0 1 := fun τ => by
      rw [hent' χ hχ, hent' χ' hχ', h01]
    have e11 : ∀ τ, χ τ 1 1 = χ' τ 1 1 := fun τ => by
      rw [hent' χ hχ, hent' χ' hχ', h11]
    funext τ i k
    fin_cases i <;> fin_cases k
    · exact (hν τ).trans (hν' τ).symm
    · exact e01 τ
    · exact (hH τ 0 1).trans ((congrArg conj (e01 τ)).trans (hH' τ 0 1).symm)
    · exact e11 τ
  have hTfin : ((Subtype.val '' A) ×ˢ (Subtype.val '' A)).Finite :=
    (hAfin.image _).prod (hAfin.image _)
  have hSfin : S.Finite := Set.Finite.of_finite_image
    (hTfin.subset (by rintro _ ⟨χ, hχ, rfl⟩; exact hmaps χ hχ)) hinj
  have hcard := Set.ncard_le_ncard_of_injOn φ hmaps hinj hTfin
  rw [Set.ncard_prod] at hcard
  have himA : (Subtype.val '' A).ncard ≤ A.ncard := Set.ncard_image_le hAfin
  have hcard' : S.ncard ≤ A.ncard * A.ncard := hcard.trans (Nat.mul_le_mul himA himA)
  refine ⟨hSfin, ?_⟩
  have hR0 : 0 ≤ (N0 : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB0
  have hNH : 0 ≤ (N0 : ℝ) * Hm := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hR1 : 1 + 2 * ((N0 : ℝ) * B) ≤ K2 * t := by
    simp only [K2, ← hHm]
    rw [← hN0r, hB]
    nlinarith [mul_nonneg (mul_nonneg hNH hc1.le) (sub_nonneg.mpr ht)]
  calc (S.ncard : ℝ) ≤ (A.ncard : ℝ) * A.ncard := by exact_mod_cast hcard'
    _ ≤ (1 + 2 * ((N0 : ℝ) * B)) ^ (2 * fdeg E) * (1 + 2 * ((N0 : ℝ) * B)) ^ (2 * fdeg E) :=
        mul_le_mul hAcard hAcard (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
    _ = (1 + 2 * ((N0 : ℝ) * B)) ^ (4 * fdeg E) := by
        rw [← pow_add]
        congr 1
        ring
    _ ≤ (K2 * t) ^ (4 * fdeg E) := pow_le_pow_left₀ (by linarith) hR1 _

theorem coefficient_height_bound_of_lift_support_positivity (h2 : UnipotentLatticeLift (E := E)) (h3d : FourierCoefficientSupport (E := E))
    (h5 : NonvanishingCoefficientPositivity (E := E)) : CoefficientHeightBound (E := E) :=
  coefficient_height_bound_of h2 h3d h5 integerApproximationCount_holds

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem flowCoefficientDecay : FlowCoefficientDecay (E := E) :=
  flow_coefficient_decay_holds unipotent_vector_group unipotent_lattice_lift fourier_coefficients_holds fourier_coefficient_support_holds holomorphic_periodicity_extension

theorem coefficientIndex_lowerBound : CoefficientIndexLowerBound (E := E) :=
  coefficient_index_lower_bound unipotent_lattice_lift fourier_coefficient_support_holds nonvanishing_coefficient_positivity

theorem coefficientHeight_bound : CoefficientHeightBound (E := E) :=
  coefficient_height_bound_of_lift_support_positivity unipotent_lattice_lift fourier_coefficient_support_holds nonvanishing_coefficient_positivity

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem shortVectorBound : ShortVectorBound (E := E) :=
  shortVectorBound_of_coefficient_bounds fourier_coefficients_holds cusp_coefficient_quantitative_holds flowCoefficientDecay coefficientIndex_lowerBound coefficientHeight_bound counting_exponential_sum_holds isotropic_outside_line

end ReciprocityTheory.ChartRestriction.G.FD
end
