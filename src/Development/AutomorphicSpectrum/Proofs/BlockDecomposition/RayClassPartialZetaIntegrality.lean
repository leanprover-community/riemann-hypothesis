import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedSumDecompositionDenominators

section
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem DL_int_valued {r : ℕ} (g : (Fin r → ℕ) → ℂ) (hg : ∀ m, ∃ z : ℤ, g m = (z : ℂ))
    (cs : List (Fin r)) : ∀ m, ∃ z : ℤ, DL cs g m = (z : ℂ) := by
  induction cs with
  | nil => exact hg
  | cons c cs ih =>
    intro m
    obtain ⟨z1, h1⟩ := ih (m + Pi.single c 1)
    obtain ⟨z2, h2⟩ := ih m
    refine ⟨z1 - z2, ?_⟩
    show DL cs g (m + Pi.single c 1) - DL cs g m = ((z1 - z2 : ℤ) : ℂ)
    rw [h1, h2]
    push_cast
    ring

theorem coneTerm_neg_nat {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ)
    (m : Fin r → ℕ) :
    coneTerm a b (-(p : ℂ)) m = ((∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p : ℝ) : ℂ) := by
  unfold coneTerm
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [neg_neg, Complex.cpow_natCast, Complex.ofReal_pow]

theorem tsum_mem_of_denominator {α : Type} (f : α → ℂ) (K l : ℕ) (hl : 0 < l)
    (hf : ∀ m, ∃ x : ℤ, ((l : ℂ) ^ K) * f m = (x : ℂ)) :
    ∃ (q : ℚ) (z : ℤ), ∑' m, f m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  have hmem : ((l : ℂ) ^ K) * ∑' m, f m ∈ Set.range (Int.cast : ℤ → ℂ) := by
    by_cases hs : Summable f
    · rw [← tsum_mul_left]
      have hs' : Summable (fun m => (l : ℂ) ^ K * f m) := hs.mul_left _
      apply Complex.isClosed_range_intCast.mem_of_tendsto hs'.hasSum
      refine Filter.Eventually.of_forall (fun S => ?_)
      choose x hx using hf
      exact ⟨∑ b ∈ S, x b, by push_cast; exact Finset.sum_congr rfl (fun b _ => (hx b).symm)⟩
    · rw [tsum_eq_zero_of_not_summable hs, mul_zero]
      exact ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := hmem
  have hlC : ((l : ℂ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  have hlQ : ((l : ℚ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  refine ⟨(z : ℚ) / (l : ℚ) ^ K, z, ?_, ?_⟩
  · push_cast
    rw [hz]
    exact (mul_div_cancel_left₀ (∑' m, f m) hlC).symm
  · rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hlQ

theorem value_neg_nat_mem : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (p K l : ℕ), 0 < l → (∀ m, ∃ z : ℤ, (l : ℚ) ^ K * u m = z) → (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (z : ℤ), ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r a b u cs p K l hl hu hprod
  apply tsum_mem_of_denominator _ K l hl
  intro m
  obtain ⟨z2, h2⟩ := DL_int_valued (coneTerm a b (-(p : ℂ))) (fun m' => by
      obtain ⟨z, hz⟩ := hprod m'
      exact ⟨z, by rw [coneTerm_neg_nat, hz, Complex.ofReal_intCast]⟩) cs m
  obtain ⟨z1, h1⟩ := hu m
  refine ⟨z1 * z2, ?_⟩
  rw [h2, ← mul_assoc]
  have h1' : ((l : ℂ) ^ K) * (u m : ℂ) = (z1 : ℂ) := by exact_mod_cast h1
  rw [h1']
  push_cast
  ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_special_value_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (p K l : ℕ), 0 < l → (∀ m, ∃ z : ℤ, (l : ℚ) ^ K * u m = z) → (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (z : ℤ), ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.value_neg_nat_mem
end

section
section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem eq_at_neg_of_eq_right (k p : ℕ) (hp : p < k) (T G : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ) (hG : DifferentiableOn ℂ G {s | -(k : ℝ) < s.re})
    (h : ∀ s : ℂ, 1 < s.re → T s = G s) : T (-(p : ℂ)) = G (-(p : ℂ)) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le p) hp)
  have hpk : (p : ℝ) < k := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set C₁ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | 0 < s.im} with hC₁
  set C₂ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | s.re < 1} with hC₂
  have hO₁ : IsOpen C₁ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hO₂ : IsOpen C₂ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hV₁ : Convex ℝ C₁ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)
  have hV₂ : Convex ℝ C₂ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hs₁ : C₁ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hs₂ : C₂ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hAT₁ : AnalyticOnNhd ℂ T C₁ := (hT.mono hs₁).analyticOnNhd hO₁
  have hAG₁ : AnalyticOnNhd ℂ G C₁ := (hG.mono fun s hs => hs.1).analyticOnNhd hO₁
  have hAT₂ : AnalyticOnNhd ℂ T C₂ := (hT.mono hs₂).analyticOnNhd hO₂
  have hAG₂ : AnalyticOnNhd ℂ G C₂ := (hG.mono fun s hs => hs.1).analyticOnNhd hO₂
  have hz₁ : (2 + Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₁ : T =ᶠ[nhds (2 + Complex.I : ℂ)] G := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (2 + Complex.I : ℂ) ∈ {s : ℂ | 1 < s.re})] with s hs
    exact h s hs
  have hE₁ : Set.EqOn T G C₁ :=
    hAT₁.eqOn_of_preconnected_of_eventuallyEq hAG₁ hV₁.isPreconnected hz₁ hev₁
  have hz₂ : (Complex.I : ℂ) ∈ C₂ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hz₂' : (Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₂ : T =ᶠ[nhds (Complex.I : ℂ)] G := by
    filter_upwards [hO₁.mem_nhds hz₂'] with s hs
    exact hE₁ hs
  have hE₂ : Set.EqOn T G C₂ :=
    hAT₂.eqOn_of_preconnected_of_eventuallyEq hAG₂ hV₂.isPreconnected hz₂ hev₂
  refine hE₂ ?_
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith

theorem abelValue_mem_zInv (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (w : (Fin r → ℕ) → ℚ) (hr : r ≤ Fintype.card ι) (hl : 0 < l) (ha : ∀ j i, 0 < a j i)
    (hb : ∀ j, 0 < b j) (hw : GoodWeight l w) (hz : ∀ m, ∃ z : ℤ, w m = z) (T : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ)
    (hS : ∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) (p : ℕ)
    (hp : ∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) :
    ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  obtain ⟨Q, _, cs, u, K, hu, hc, hK, hid⟩ :=
    GlobalTheory.T.weighted_sum_decomposition_denominators r l (Fintype.card ι * (p + 1) + 2) w hl hw hz
  set G : ℂ → ℂ := fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m with hGdef
  have hG : DifferentiableOn ℂ G {s | -((p + 1 : ℕ) : ℝ) < s.re} := by
    refine DifferentiableOn.fun_sum fun q _ => ?_
    exact GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb (p + 1) _ (cs q) (u q) le_rfl (hu q) (hc q)
  have hTG : ∀ s : ℂ, 1 < s.re → T s = G s := by
    intro s hs
    rw [← (hS s hs).tsum_eq]
    exact hid _ (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)
  have hval := eq_at_neg_of_eq_right (p + 1) p (Nat.lt_succ_self p) T G hT hG hTG
  choose ρ ζ hρ hζ using fun q => GlobalTheory.T.cone_series_special_value_rational ι r a b (u q) (cs q) p K l hl (hK q) hp
  refine ⟨∑ q, ρ q, K, ∑ q, ζ q, ?_, ?_⟩
  · rw [hval, hGdef]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hρ q
  · rw [Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hζ q

theorem abelValue_mem_zInv' : ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ), r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) → ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r l a b w hr hl ha hb hw hz T hT hS p hp
  exact abelValue_mem_zInv ι r l a b w hr hl ha hb hw hz T hT hS p hp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_zeta_special_value_denominator_bound : ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ), r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) → ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv'
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality

theorem eqOn_compl_one {H R : ℂ → ℂ} (hH : DifferentiableOn ℂ H {1}ᶜ) (hR : DifferentiableOn ℂ R {1}ᶜ)
    (h : ∀ s : ℂ, 1 < s.re → H s = R s) : Set.EqOn H R {1}ᶜ := by
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; first | exact Cardinal.one_lt_two | norm_num | exact_mod_cast (show (1:ℕ) < 2 by norm_num)) 1).isPreconnected
  have hmem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff]; norm_num
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hnhds : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) := hopen.mem_nhds (by norm_num)
  exact (hH.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd isOpen_compl_singleton) hconn hmem (Filter.eventually_of_mem hnhds fun s hs => h s hs)

theorem coneWeight_int {F : Type} [Field F] [NumberField F] {r : ℕ} (l : ℕ) (A : Ideal (𝓞 F)) (y : 𝓞 F)
    (v : Fin r → 𝓞 F) (m : Fin r → ℕ) : ∃ z : ℤ, coneWeight l A y v m = z := by
  unfold coneWeight
  split_ifs
  · exact ⟨(l : ℤ) - 1, by push_cast; ring⟩
  · exact ⟨-1, by push_cast; ring⟩

theorem exists_pow_mul_sum {J : Type} (S : Finset J) (l : ℕ) (q : J → ℚ) (K : J → ℕ) (z : J → ℤ)
    (h : ∀ j, (l : ℚ) ^ K j * q j = z j) : ∃ (K' : ℕ) (Z : ℤ), (l : ℚ) ^ K' * ∑ j ∈ S, q j = Z := by
  refine ⟨∑ j ∈ S, K j, ∑ j ∈ S, (l : ℤ) ^ (∑ i ∈ S, K i - K j) * z j, ?_⟩
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hle : K j ≤ ∑ i ∈ S, K i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
  rw [← h j, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem padicValRat_int_div_nonneg (l : ℕ) [Fact l.Prime] (Z : ℤ) (D : ℕ) (hD : D ≠ 0) (h : ¬ l ∣ D) :
    0 ≤ padicValRat l ((Z : ℚ) / (D : ℚ)) := by
  rcases eq_or_ne Z 0 with rfl | hZ
  · simp
  have hZ' : (Z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hZ
  have hD' : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  rw [padicValRat.div hZ' hD', padicValRat.of_int, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  simp

theorem classTwist_value_int : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J] (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) → ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧ ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := by
  intro F _ _ _ 𝔣 𝔞 𝔟 𝔠 J _ r y v hP h𝔠 hN hv T hT hS k hk
  obtain ⟨hb, hy, hvv, hr, e, he⟩ := hP
  letI : Fintype (F →+* ℝ) := Fintype.ofEquiv (F →+* ℂ) (realEmbeddingsEquiv F).symm
  set l := Ideal.absNorm 𝔠 with hl_def
  have hl0 : 0 < l := hN.pos
  have hcard : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [Fintype.card_congr (realEmbeddingsEquiv F)]
    convert NumberField.Embeddings.card F ℂ
  have hNb : Ideal.absNorm 𝔟 ≠ 0 := fun h => hb (Ideal.absNorm_eq_zero_iff.mp h)
  have hNbC : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNb
  have hw : ∀ j, GoodWeight l (coneWeight l (𝔠 * 𝔟) (y j) (v j)) := fun j =>
    goodWeight_coneWeight hb hN (hy j).1 (fun i => (hvv j i).1) (hv j)
  have hcont : ∀ j, ∃ Tj : ℂ → ℂ, Differentiable ℂ Tj ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun m => (coneWeight l (𝔠 * 𝔟) (y j) (v j) m : ℂ) *
        coneTerm (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) s m) (Tj s)) := by
    intro j
    obtain ⟨Tj, hd, hs, -⟩ := abelContinuation (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F))
      (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0
      (fun σ i => (hvv j i).2 σ) (fun σ => (hy j).2 σ) (hw j)
    exact ⟨Tj, hd, hs⟩
  choose Tc hTcd hTcs using hcont
  have key : ∀ (s : ℂ) (p : (j : J) × (Fin (r j) → ℕ)),
      (classWeight l 𝔠 (e p).1 : ℂ) * ((Ideal.absNorm (e p).1 : ℕ) : ℂ) ^ (-s) =
        ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2) := by
    rintro s ⟨j, m⟩
    dsimp only
    have hx : (e ⟨j, m⟩).1 * 𝔟 = Ideal.span {conePt (y j) (v j) m} := he ⟨j, m⟩
    have hwt : classWeight l 𝔠 (e ⟨j, m⟩).1 = coneWeight l (𝔠 * 𝔟) (y j) (v j) m := by
      unfold classWeight coneWeight
      rw [le_iff_mem_mul_of_span (𝔠 := 𝔠) hb hx]
    have hnorm : Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) =
        Ideal.absNorm (e ⟨j, m⟩).1 * Ideal.absNorm 𝔟 := by rw [← hx, map_mul]
    rw [hwt, coneTerm_eq_absNorm_cpow (hy j).2 (fun i => (hvv j i).2) s m, hnorm, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s),
      mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s), ← Complex.cpow_add _ _ hNbC, add_neg_cancel,
      Complex.cpow_zero, mul_one]
  have hRs : ∀ s : ℂ, 1 < s.re → T s = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s := by
    intro s hs
    have h1 := (e.hasSum_iff.mpr (hS s hs))
    have h2 : HasSum (fun p : (j : J) × (Fin (r j) → ℕ) => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s *
        ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2)) (T s) := by
      convert h1 using 1
      funext p
      exact (key s p).symm
    have h3 := h2.sigma (fun j => (hTcs j s hs).mul_left (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s))
    rw [Finset.mul_sum]
    exact h3.unique (hasSum_fintype _)
  have hRd : DifferentiableOn ℂ (fun s => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s) {1}ᶜ := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · exact differentiableAt_id.const_cpow (Or.inl hNbC)
    · have hsd := DifferentiableAt.sum (u := Finset.univ) (fun j _ => hTcd j s)
      have hfun : (fun t => ∑ j, Tc j t) = ∑ j, Tc j := by
        funext t
        simp [Finset.sum_apply]
      rw [hfun]
      exact hsd
  have heq := eqOn_compl_one hT hRd (fun s hs => hRs s hs)
  have hint : ∀ j, ∃ (qj : ℚ) (K : ℕ) (z : ℤ), Tc j (-((k - 1 : ℕ) : ℂ)) = qj ∧ (l : ℚ) ^ K * qj = z := by
    intro j
    refine GlobalTheory.T.cone_zeta_special_value_denominator_bound (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F))
      (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0 (fun σ i => (hvv j i).2 σ)
      (fun σ => (hy j).2 σ) (hw j) (fun m => coneWeight_int l _ _ _ m) (Tc j) (hTcd j).differentiableOn
      (hTcs j) (k - 1) (fun m => ?_)
    have h1 : ∏ σ : F →+* ℝ, (σ ((y j : 𝓞 F) : F) + ∑ i, σ ((v j i : 𝓞 F) : F) * (m i : ℝ)) =
        ((Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) : ℕ) : ℝ) := by
      rw [← prod_real_embeddings_eq_absNorm _ (totPos_conePt (hy j).2 (fun i => (hvv j i).2) m)]
      exact Finset.prod_congr rfl fun σ _ => (embedding_conePt σ (y j) (v j) m).symm
    refine ⟨(Ideal.absNorm (Ideal.span {conePt (y j) (v j) m})) ^ (k - 1), ?_⟩
    try beta_reduce
    rw [Finset.prod_pow, h1]
    first | norm_cast | (push_cast; ring) | simp
  choose qj Kj zj hqj hzj using hint
  obtain ⟨K', Z, hZ⟩ := exists_pow_mul_sum Finset.univ l qj Kj zj hzj
  have hs0 : (1 - (k : ℂ)) = -(((k - 1 : ℕ)) : ℂ) := by rw [Nat.cast_sub hk]; push_cast; ring
  have hmem : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff, Ne, sub_eq_self]; exact_mod_cast (by omega : k ≠ 0)
  have hval : T (1 - (k : ℂ)) = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ (1 - (k : ℂ)) * ∑ j, (qj j : ℂ) := by
    rw [heq hmem]
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs0]; exact hqj j
  have hlK : (l : ℚ) ^ K' ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl0.ne')
  have hsum : ∑ j, qj j = (Z : ℚ) / (l : ℚ) ^ K' := by
    rw [eq_div_iff hlK, mul_comm]; exact hZ
  have hD : l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hl0.ne') (pow_ne_zero _ hNb)
  refine ⟨(Z : ℚ) / ((l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) : ℕ) : ℚ), ?_, ?_⟩
  · rw [hval, hs0, Complex.cpow_neg, Complex.cpow_natCast, ← Rat.cast_sum, hsum]
    push_cast
    ring
  · intro l' hl' hne hndvd
    haveI := Fact.mk hl'
    apply padicValRat_int_div_nonneg l' Z _ hD
    intro hdvd
    rcases (Nat.Prime.dvd_mul hl').mp hdvd with h | h
    · exact hne ((Nat.prime_dvd_prime_iff_eq hl' hN).mp (hl'.dvd_of_dvd_pow h))
    · exact hndvd (hl'.dvd_of_dvd_pow h)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality
end
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_partial_zeta_integrality : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J] (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) → ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧ ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int
end
