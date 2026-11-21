import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassPartialZetaContinuationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_L_series_euler_product : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → LSeriesSummable (D.coef χ) s ∧ Summable (fun v : D.Pr => ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖) ∧ LSeries (D.coef χ) s = Complex.exp (∑' v : D.Pr, -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  first | exact @GlobalTheory.Mem.RayData.lseries_eq_exp_tsum | exact GlobalTheory.Mem.RayData.lseries_eq_exp_tsum | (intros; apply GlobalTheory.Mem.RayData.lseries_eq_exp_tsum <;> assumption)
end

section
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

namespace GlobalTheory.Mem

def PosDirichlet (F : ℂ → ℂ) : Prop :=
  ∃ (ι : Type) (w : ι → ℝ) (N : ι → ℕ), (∀ i, 0 ≤ w i) ∧ (∀ i, N i ≠ 0) ∧
    ∀ s : ℂ, 1 < s.re → HasSum (fun i => (w i : ℂ) * (N i : ℂ) ^ (-s)) (F s)

namespace PosDirichlet

lemma congr {F G : ℂ → ℂ} (h : PosDirichlet F) (e : ∀ s : ℂ, 1 < s.re → F s = G s) :
    PosDirichlet G := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := h
  exact ⟨ι, w, N, hw, hN, fun s hs => e s hs ▸ h s hs⟩

lemma const {c : ℝ} (hc : 0 ≤ c) : PosDirichlet (fun _ => (c : ℂ)) :=
  ⟨Unit, fun _ => c, fun _ => 1, fun _ => hc, fun _ => one_ne_zero, fun s _ => by
    simpa using hasSum_unique (fun _ : Unit => (c : ℂ))⟩

lemma hasSum_mul_of_norm_summable {ι κ : Type} {f : ι → ℂ} {g : κ → ℂ} {a b : ℂ} (hf : HasSum f a)
    (hg : HasSum g b) : HasSum (fun p : ι × κ => f p.1 * g p.2) (a * b) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

lemma mul {F G : ℂ → ℂ} (hF : PosDirichlet F) (hG : PosDirichlet G) :
    PosDirichlet (fun s => F s * G s) := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := hF
  obtain ⟨κ, w', N', hw', hN', h'⟩ := hG
  refine ⟨ι × κ, fun p => w p.1 * w' p.2, fun p => N p.1 * N' p.2,
    fun p => mul_nonneg (hw _) (hw' _), fun p => mul_ne_zero (hN _) (hN' _), fun s hs => ?_⟩
  have e : ∀ p : ι × κ, ((w p.1 * w' p.2 : ℝ) : ℂ) * ((N p.1 * N' p.2 : ℕ) : ℂ) ^ (-s) =
      ((w p.1 : ℂ) * (N p.1 : ℂ) ^ (-s)) * ((w' p.2 : ℂ) * (N' p.2 : ℂ) ^ (-s)) := by
    intro p
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  have h1 := hasSum_mul_of_norm_summable (h s hs) (h' s hs)
  beta_reduce at h1 ⊢
  rw [funext e]
  exact h1

lemma pow {F : ℂ → ℂ} (hF : PosDirichlet F) (j : ℕ) : PosDirichlet (fun s => F s ^ j) := by
  induction j with
  | zero => simpa using const zero_le_one
  | succ j ih => simpa only [pow_succ] using ih.mul hF

lemma norm_term {w : ℝ} (hw : 0 ≤ w) {N : ℕ} (hN : N ≠ 0) (s : ℂ) :
    ‖(w : ℂ) * (N : ℂ) ^ (-s)‖ = ((w : ℂ) * (N : ℂ) ^ (-(s.re : ℂ))).re := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN), Complex.norm_real,
    Real.norm_of_nonneg hw, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg N), ← Complex.ofReal_mul, Complex.ofReal_re, neg_re]

lemma tsum {J : Type} {F : J → ℂ → ℂ} (hF : ∀ j, PosDirichlet (F j))
    (hs : ∀ s : ℂ, 1 < s.re → Summable (fun j => F j s)) :
    PosDirichlet (fun s => ∑' j, F j s) := by
  choose ι w N hw hN h using hF
  refine ⟨Σ j, ι j, fun p => w p.1 p.2, fun p => N p.1 p.2, fun p => hw _ _, fun p => hN _ _,
    fun s hs' => ?_⟩
  have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs'
  have key : ∀ j, HasSum (fun i => ‖(w j i : ℂ) * (N j i : ℂ) ^ (-s)‖) (F j s.re).re := by
    intro j
    simp only [norm_term (hw _ _) (hN _ _)]
    exact Complex.hasSum_re (h j _ hσ)
  have hsum : Summable (fun p : Σ j, ι j => (w p.1 p.2 : ℂ) * (N p.1 p.2 : ℂ) ^ (-s)) := by
    apply Summable.of_norm
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun j => (key j).summable, ?_⟩
    simp only [fun j => (key j).tsum_eq]
    exact (Complex.hasSum_re (hs _ hσ).hasSum).summable
  have h2 := hsum.hasSum.sigma (fun j => h j s hs')
  show HasSum _ (∑' j, F j s)
  rw [h2.tsum_eq]
  exact hsum.hasSum

lemma exists_LSeries {F : ℂ → ℂ} (hF : PosDirichlet F) :
    ∃ b : ℕ → ℂ, 0 ≤ b ∧ ∀ s : ℂ, 1 < s.re → LSeriesHasSum b s (F s) := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := hF
  refine ⟨fun n => ∑' i : N ⁻¹' {n}, (w i : ℂ), fun n => tsum_nonneg fun i =>
    Complex.zero_le_real.2 (hw i.1), fun s hs => ?_⟩
  have h1 := (h s hs).tsum_fiberwise N
  unfold LSeriesHasSum
  suffices e : ∀ n, LSeries.term (fun n => ∑' i : N ⁻¹' {n}, (w i : ℂ)) s n =
      ∑' i : N ⁻¹' {n}, (w i : ℂ) * (N i : ℂ) ^ (-s) by
    rw [funext e]; exact h1
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · haveI : IsEmpty (N ⁻¹' {0}) := ⟨fun i => hN i i.2⟩
    simp
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    have : N i = n := i.2
    rw [this]

lemma exp_sub_one {F : ℂ → ℂ} (hF : PosDirichlet F) :
    PosDirichlet (fun s => Complex.exp (F s) - 1) := by
  have h1 : ∀ z : ℂ, HasSum (fun j : ℕ => z ^ (j + 1) / ((j + 1).factorial : ℂ))
      (Complex.exp z - 1) := by
    intro z
    have := NormedSpace.expSeries_div_hasSum_exp z
    rw [← Complex.exp_eq_exp_ℂ, ← hasSum_nat_add_iff' 1] at this
    simpa using this
  refine (tsum (F := fun (j : ℕ) s => F s ^ (j + 1) / ((j + 1).factorial : ℂ)) (fun j => ?_)
    (fun s _ => (h1 _).summable)).congr fun s _ => (h1 _).tsum_eq
  refine ((hF.pow (j + 1)).mul (const (c := ((j + 1).factorial : ℝ)⁻¹) (by positivity))).congr
    fun s _ => ?_
  push_cast
  rw [div_eq_mul_inv]

lemma exists_LSeries_exp {F : ℂ → ℂ} (hF : PosDirichlet F) :
    ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧
      ∀ s : ℂ, 1 < s.re → LSeries b s = Complex.exp (F s) := by
  obtain ⟨b, hb, h⟩ := hF.exp_sub_one.exists_LSeries
  have hδ : (0 : ℕ → ℂ) ≤ LSeries.delta := fun n => by
    by_cases hn : n = 1 <;> simp [LSeries.delta, hn]
  have h2 : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (LSeries.delta + b) s (Complex.exp (F s)) := by
    intro s hs
    have h0 : LSeriesHasSum LSeries.delta s 1 := by
      unfold LSeriesHasSum
      have := hasSum_ite_eq (1 : ℕ) (1 : ℂ)
      convert this using 2 with n
      rw [LSeries.term_delta]
    simpa using h0.add (h s hs)
  refine ⟨LSeries.delta + b, add_nonneg hδ hb, ?_, ?_, fun s hs => (h2 s hs).LSeries_eq⟩
  · have : LSeries.delta 1 = 1 := by simp [LSeries.delta]
    rw [Pi.add_apply, this]
    exact add_pos_of_pos_of_nonneg one_pos (hb 1)
  · refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) fun y hy => ?_
    exact (h2 y (by simpa using hy)).LSeriesSummable

end PosDirichlet

lemma sum_characters_nonneg {G : Type} [CommGroup G] [Fintype (G →* ℂˣ)] (g : G) :
    0 ≤ ∑ χ : G →* ℂˣ, (χ g : ℂ) := by
  by_cases h : ∀ χ : G →* ℂˣ, χ g = 1
  · exact Finset.sum_nonneg fun χ _ => by simp [h χ]
  · push_neg at h
    obtain ⟨ψ, hψ⟩ := h
    have h1 : ∑ χ : G →* ℂˣ, (χ g : ℂ) = (ψ g : ℂ) * ∑ χ : G →* ℂˣ, (χ g : ℂ) := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft ψ)]
      simp
    have h2 : (1 - (ψ g : ℂ)) * ∑ χ : G →* ℂˣ, (χ g : ℂ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (Units.ext (sub_eq_zero.1 h3).symm) hψ
    · exact h3.ge

lemma norm_character {G : Type} [CommGroup G] [Fintype G] (χ : G →* ℂˣ) (g : G) :
    ‖(χ g : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G) _ Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

lemma natCast_pow_cpow_comm (q k : ℕ) (z : ℂ) : ((q : ℂ) ^ k) ^ z = ((q : ℂ) ^ z) ^ k := by
  rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

lemma posDirichlet_local {G : Type} [CommGroup G] [Fintype G] [Fintype (G →* ℂˣ)] (g : G)
    {q : ℕ} (hq : 2 ≤ q) :
    PosDirichlet (fun s => ∑ χ : G →* ℂˣ, -Complex.log (1 - (χ g : ℂ) * (q : ℂ) ^ (-s))) := by
  refine ⟨ℕ, fun k => (∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ)).re / k, fun k => q ^ k,
    fun k => div_nonneg (Complex.nonneg_iff.1 (sum_characters_nonneg _)).1 (Nat.cast_nonneg _),
    fun k => pow_ne_zero _ (by omega), fun s hs => ?_⟩
  have h1 : ∀ χ : G →* ℂˣ, ‖(χ g : ℂ) * (q : ℂ) ^ (-s)‖ < 1 := by
    intro χ
    rw [norm_mul, norm_character, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hq
    · simp only [neg_re]; linarith
  have h2 := hasSum_sum (s := Finset.univ)
    (fun χ _ => Complex.hasSum_taylorSeries_neg_log (h1 χ))
  convert h2 using 2 with k
  have h3 : (((∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ)).re : ℝ) : ℂ) = ∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ) :=
    (Complex.eq_re_of_ofReal_le (r := 0) (by simpa using sum_characters_nonneg (g ^ k))).symm
  rw [Complex.ofReal_div, h3, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Nat.cast_pow, natCast_pow_cpow_comm, mul_pow, map_pow, Units.val_pow_eq_pow_val]
  push_cast
  ring

theorem ray_prod_LSeries_nonneg : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) [Fintype (D.G →* ℂˣ)], ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧ ∀ s : ℂ, 1 < s.re → LSeries b s = ∏ χ : D.G →* ℂˣ, LSeries (D.coef χ) s := by
  intro K _ _ M hM D _
  have hsum : ∀ (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → Summable (fun v : D.Pr =>
      -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    intro χ s hs
    refine (Summable.clog_one_sub (Summable.of_norm ?_)).neg
    simpa only [norm_mul, norm_character, one_mul] using (GlobalTheory.T.ray_L_series_euler_product K M hM D χ s hs).2.1
  have hq : ∀ v : D.Pr, 2 ≤ Ideal.absNorm v.1.asIdeal := fun v =>
    NumberField.HeightOneSpectrum.one_lt_absNorm v.1
  obtain ⟨b, h0, h1, h2, h3⟩ := (PosDirichlet.tsum
    (fun v : D.Pr => posDirichlet_local (D.cls v.1.asIdeal) (hq v))
    (fun s hs => summable_sum fun χ _ => hsum χ s hs)).exists_LSeries_exp
  refine ⟨b, h0, h1, h2, fun s hs => ?_⟩
  rw [h3 s hs, Summable.tsum_finsetSum (fun χ _ => hsum χ s hs), Complex.exp_sum]
  exact Finset.prod_congr rfl fun χ _ => (GlobalTheory.T.ray_L_series_euler_product K M hM D χ s hs).2.2.symm

end GlobalTheory.Mem
end

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_zeta_factorization_ray : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) [Fintype (D.G →* ℂˣ)], ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧ ∀ s : ℂ, 1 < s.re → LSeries b s = ∏ χ : D.G →* ℂˣ, LSeries (D.coef χ) s := by
  atlas_forward_decl GlobalTheory.Mem.ray_prod_LSeries_nonneg
end

section
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

namespace GlobalTheory.Mem

lemma exists_entire_div_sub_one {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h1 : f 1 = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s, f s = (s - 1) * g s := by
  refine ⟨dslope f 1, ?_, fun s => ?_⟩
  · rw [← differentiableOn_univ] at hf ⊢
    exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hf
  · have := sub_smul_dslope f 1 s
    rw [h1, sub_zero, smul_eq_mul] at this
    exact this.symm

lemma RayData.LSeries_coef_eq_sum {K : Type} [Field K] [NumberField K] {M : ℕ} (D : RayData K M)
    (χ : D.G →* ℂˣ) (s : ℂ) (h : ∀ c, LSeriesSummable (D.cnt c) s) :
    LSeries (D.coef χ) s = ∑ c, (χ c : ℂ) * LSeries (D.cnt c) s := by
  have e : D.coef χ = ∑ c, (χ c : ℂ) • D.cnt c := by
    funext n
    simp [RayData.coef, Finset.sum_apply]
  rw [e, LSeries_sum (fun c _ => (h c).smul _)]
  simp [LSeries_smul]

theorem rayLSeries_entire_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ), χ ≠ 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ L 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
  intro K _ _ _ hK M hM D χ₀ hχ₀
  classical
  obtain ⟨ρ, -, hZ⟩ := GlobalTheory.T.ray_class_partial_zeta_continuation K hK M hM D
  choose Z hZd hZ1 hZm hZs using hZ
  let Y : (D.G →* ℂˣ) → ℂ → ℂ := fun χ s => ∑ c, (χ c : ℂ) * Z c s
  have hYd : ∀ χ, Differentiable ℂ (Y χ) := fun χ =>
    Differentiable.fun_sum fun c _ => (hZd c).const_mul _
  have hYm : ∀ χ, Y χ (-1) = 0 := fun χ => by simp [Y, hZm]
  have hYs : ∀ χ s, 1 < s.re → Y χ s = (s - 1) * LSeries (D.coef χ) s := by
    intro χ s hs
    rw [D.LSeries_coef_eq_sum χ s fun c => (hZs c s hs).1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [(hZs c s hs).2]; ring
  have hY1 : ∀ χ, χ ≠ 1 → Y χ 1 = 0 := by
    intro χ hχ
    have h0 : ∑ c, (χ c : ℂ) = 0 := by
      have := sum_hom_units_eq_zero ((Units.coeHom ℂ).comp χ) (by
        intro h
        apply hχ
        ext c
        simpa using DFunLike.congr_fun h c)
      simpa using this
    simp only [Y, hZ1]
    rw [← Finset.sum_mul, h0, zero_mul]
  have hL : ∀ χ : D.G →* ℂˣ, ∃ L : ℂ → ℂ, χ ≠ 1 →
      Differentiable ℂ L ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, fun h => absurd hχ h⟩
    obtain ⟨g, hg, hg'⟩ := exists_entire_div_sub_one (hYd χ) (hY1 χ hχ)
    refine ⟨g, fun _ => ⟨hg, fun s hs => ?_⟩⟩
    have hs1 : s - 1 ≠ 0 := by
      rw [sub_ne_zero]; rintro rfl; simp at hs
    exact mul_left_cancel₀ hs1 ((hg' s).symm.trans (hYs χ s hs))
  choose L hL using hL
  refine ⟨L χ₀, (hL χ₀ hχ₀).1, fun h0 => ?_, (hL χ₀ hχ₀).2⟩
  obtain ⟨g, hg, hg'⟩ := exists_entire_div_sub_one (hL χ₀ hχ₀).1 h0
  haveI : NeZero ((Monoid.exponent D.G : ℕ) : ℂ) := ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  haveI : Finite (D.G →* ℂˣ) := by
    obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity D.G ℂ
    exact Finite.of_equiv _ e.toEquiv.symm
  haveI : Fintype (D.G →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨b, hb0, hb1, hba, hbs⟩ := GlobalTheory.T.dedekind_zeta_factorization_ray K M hM D
  let F : ℂ → ℂ := fun s => Y 1 s * (g s * ∏ χ ∈ (Finset.univ.erase 1).erase χ₀, L χ s)
  have hFd : Differentiable ℂ F := by
    refine (hYd 1).mul (hg.mul ?_)
    refine Differentiable.fun_finset_prod fun χ hχ => (hL χ ?_).1
    exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ)
  have hFs : {s : ℂ | (1 : ℝ) < s.re}.EqOn F (LSeries b) := by
    intro s hs
    have hs' : 1 < s.re := hs
    rw [hbs s hs', ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : D.G →* ℂˣ)),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hχ₀, Finset.mem_univ χ₀⟩),
      ← (hL χ₀ hχ₀).2 s hs', hg' s]
    simp only [F]
    rw [hYs 1 s hs', Finset.prod_congr rfl fun χ hχ =>
      (hL χ (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hχ))).2 s hs']
    ring
  have hpos := LSeries.positive_of_differentiable_of_eqOn hb0 hb1 hFd (x := 1)
    (by exact_mod_cast hba) hFs (-1)
  have : F ((-1 : ℝ) : ℂ) = 0 := by
    simp [F, hYm]
  rw [this] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.Mem
end

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_L_nonvanishing_at_one : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ), χ ≠ 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ L 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
  atlas_forward_decl GlobalTheory.Mem.rayLSeries_entire_ne_zero_one
end

section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set

namespace GlobalTheory.Mem.RayPrimes

theorem log_bounded (g : ℝ → ℂ) (L : ℂ → ℂ) (hL : Continuous L) (h1 : L 1 ≠ 0)
    (hg : ContinuousOn g (Ioi 1)) (he : ∀ s : ℝ, 1 < s → cexp (g s) = L s) :
    g =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hc : Continuous (fun s : ℝ => L s / L 1 - 1) := by fun_prop (disch := exact h1)
  have ht : ∀ᶠ s : ℝ in 𝓝 1, ‖L s / L 1 - 1‖ < 1 / 2 := by
    have := (hc.norm.tendsto 1)
    simp only [ofReal_one, div_self h1, sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 ht
  have hb' : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), ‖L s / L 1 - 1‖ < 1 / 2 := fun s hs => hb (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  have hslit : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), 1 + (L s / L 1 - 1) ∈ slitPlane := fun s hs =>
    mem_slitPlane_of_norm_lt_one (by linarith [hb' s hs])
  set k : ℝ → ℂ := fun s => g s - log (1 + (L s / L 1 - 1)) with hk
  have hkc : ContinuousOn k (Ioo 1 (1 + δ)) :=
    (hg.mono Ioo_subset_Ioi_self).sub
      (ContinuousOn.clog (continuous_const.add hc).continuousOn hslit)
  have hke : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), cexp (k s) = L 1 := fun s hs => by
    have hne : L s ≠ 0 := by rw [← he s hs.1]; exact exp_ne_zero _
    simp only [hk]
    rw [exp_sub, exp_log (slitPlane_ne_zero (hslit s hs)), he s hs.1, add_sub_cancel]
    field_simp
  have hconst : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), k s = k (1 + δ / 2) := fun s hs =>
    Complex.isCoveringMap_exp.constOn_of_comp isPreconnected_Ioo hkc
      (fun a ha b hb => Subtype.ext (by simp only; rw [hke a ha, hke b hb])) hs
      ⟨by linarith, by linarith⟩
  refine IsBigO.of_bound (‖k (1 + δ / 2)‖ + 1) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ by linarith)] with s hs
  have h2 : g s = k (1 + δ / 2) + log (1 + (L s / L 1 - 1)) := by
    rw [← hconst s hs]; simp [hk]
  have h3 := norm_log_one_add_half_le_self (hb' s hs).le
  rw [h2, norm_one, mul_one]
  refine (norm_add_le _ _).trans ?_
  linarith [hb' s hs]

section series

variable {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (a : ι → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
include hn ha

theorem norm_term_le (v : ι) {s t : ℝ} (hst : t ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ) ^ (-t) := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  rw [norm_mul, norm_natCast_cpow_of_pos (by linarith [hn v])]
  simp only [neg_re, ofReal_re]
  calc ‖a v‖ * (n v : ℝ) ^ (-s) ≤ 1 * (n v : ℝ) ^ (-t) := by
        gcongr
        · exact ha v
        · linarith
    _ = _ := one_mul _

theorem norm_term_le_inv (v : ι) {s : ℝ} (hs : 1 ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ)⁻¹ := by
  have := norm_term_le n hn a ha v hs
  rwa [Real.rpow_neg_one] at this

theorem norm_term_le_half (v : ι) {s : ℝ} (hs : 1 ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  refine (norm_term_le_inv n hn a ha v hs).trans ?_
  rw [one_div]; gcongr

theorem continuousOn_logSum (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) :
    ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi 1) := by
  intro s hs1
  obtain ⟨t, ht1, hts⟩ := exists_between (show (1 : ℝ) < s from hs1)
  have : ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi t) := by
    refine continuousOn_tsum (u := fun v => 3 / 2 * (n v : ℝ) ^ (-t)) ?_ ((hs t ht1).mul_left _) ?_
    · intro v
      refine ContinuousOn.neg (ContinuousOn.clog ?_ ?_)
      · have h0 : (n v : ℂ) ≠ 0 := by
          have := hn v
          exact_mod_cast (by omega : n v ≠ 0)
        refine (continuous_const.sub (continuous_const.mul ?_)).continuousOn
        exact Continuous.const_cpow (by fun_prop) (Or.inl h0)
      · intro x hx
        rw [sub_eq_add_neg]
        refine mem_slitPlane_of_norm_lt_one ?_
        rw [norm_neg]
        linarith [norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx))]
    · intro v x hx
      rw [norm_neg, sub_eq_add_neg]
      have h := norm_log_one_add_half_le_self (z := -(a v * (n v : ℂ) ^ (-(x : ℂ))))
        (by rw [norm_neg]; exact norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx)))
      rw [norm_neg] at h
      linarith [norm_term_le n hn a ha v (le_of_lt hx)]
  exact (this.continuousAt (Ioi_mem_nhds hts)).continuousWithinAt

theorem summable_term (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) {s : ℝ} (h : 1 < s) :
    Summable fun v => a v * (n v : ℂ) ^ (-(s : ℂ)) :=
  Summable.of_norm_bounded (hs s h) fun v => norm_term_le n hn a ha v le_rfl

theorem logSum_sub_bounded (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) :
    (fun s : ℝ => (∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) - ∑' v, a v * (n v : ℂ) ^ (-(s : ℂ)))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  refine IsBigO.of_bound (∑' v, (n v : ℝ) ^ (-(2 : ℝ))) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs1
  have hs1 : 1 < s := hs1
  have hb : ∀ v, ‖-log (1 - a v * (n v : ℂ) ^ (-(s : ℂ))) - a v * (n v : ℂ) ^ (-(s : ℂ))‖
      ≤ (n v : ℝ) ^ (-(2 : ℝ)) := by
    intro v
    set z := a v * (n v : ℂ) ^ (-(s : ℂ)) with hz
    have h1 : ‖z‖ ≤ 1 / 2 := norm_term_le_half n hn a ha v hs1.le
    have h2 : ‖z‖ ≤ (n v : ℝ)⁻¹ := norm_term_le_inv n hn a ha v hs1.le
    have h3 := norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]; linarith)
    have h4 : -log (1 - z) - z = -(log (1 + -z) - -z) := by rw [← sub_eq_add_neg 1 z]; ring
    rw [h4, norm_neg]
    refine h3.trans ?_
    rw [norm_neg, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, ← inv_pow]
    have h5 : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h6 : ‖z‖ ^ 2 ≤ ((n v : ℝ)⁻¹) ^ 2 := by gcongr
    have h7 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ 2 * 2 := by gcongr
    linarith
  have hsum := summable_term n hn a ha hs hs1
  have hd := Summable.of_norm_bounded (hs 2 (by norm_num)) hb
  have hl : Summable fun v => -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ))) := by
    simpa using hd.add hsum
  rw [← hl.tsum_sub hsum, norm_one, mul_one]
  exact tsum_of_norm_bounded (hs 2 (by norm_num)).hasSum hb

end series

section orth

variable {G : Type} [CommGroup G] [Fintype G]

theorem norm_char (χ : G →* ℂˣ) (x : G) : ‖(χ x : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G) ?_ Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

theorem sum_char_eq_zero [Fintype (G →* ℂˣ)] {x : G} (hx : x ≠ 1) :
    ∑ χ : G →* ℂˣ, (χ x : ℂ) = 0 := by
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hx
  let f : (G →* ℂˣ) →* ℂ :=
    { toFun := fun χ => (χ x : ℂ), map_one' := by simp, map_mul' := by simp }
  refine sum_hom_units_eq_zero f ?_
  intro h
  apply hφ
  have := DFunLike.congr_fun h φ
  simpa [f] using this

theorem not_summable_class {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (cl : ι → G)
    (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s))
    (hχ : ∀ χ : G →* ℂˣ, χ ≠ 1 → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s →
      cexp (∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))) = L s)
    (Z : ℂ → ℂ) (hZ : Continuous Z) (hZ1 : Z 1 ≠ 0)
    (h1 : ∀ s : ℝ, 1 < s → Z s = (s - 1) *
      cexp (∑' v, -log (1 - ((1 : G →* ℂˣ) (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))))
    (c : G) : ¬ Summable fun v : {v // cl v = c} => (n v : ℝ)⁻¹ := by
  classical
  intro hc
  have : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  let g : (G →* ℂˣ) → ℝ → ℂ := fun χ s => ∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))
  let P : (G →* ℂˣ) → ℝ → ℂ := fun χ s => ∑' v, (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ))
  have hgP : ∀ χ, (fun s => g χ s - P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := fun χ =>
    logSum_sub_bounded n hn _ (fun v => (norm_char χ _).le) hs
  have hP : ∀ χ, χ ≠ 1 → P χ =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    intro χ h
    obtain ⟨L, hL, hL1, hL2⟩ := hχ χ h
    have := log_bounded (g χ) L hL hL1
      (continuousOn_logSum n hn _ (fun v => (norm_char χ _).le) hs) hL2
    simpa using this.sub (hgP χ)
  have hS : (fun s => ∑ χ, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have hc' := (summable_subtype_iff_indicator (f := fun v => (n v : ℝ)⁻¹)
      (s := {v | cl v = c})).1 hc
    have hc'' := hc'.mul_left (Fintype.card (G →* ℂˣ) : ℝ)
    refine IsBigO.of_bound (∑' v, (Fintype.card (G →* ℂˣ) : ℝ) *
      ({v | cl v = c}).indicator (fun v => (n v : ℝ)⁻¹) v) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs1
    have hs1 : 1 < s := hs1
    have hsum : ∀ χ : G →* ℂˣ, Summable fun v =>
        (χ c⁻¹ : ℂ) * ((χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ))) := fun χ =>
      (summable_term n hn _ (fun v => (norm_char χ _).le) hs hs1).mul_left _
    simp only [P, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun χ _ => hsum χ), norm_one, mul_one]
    refine tsum_of_norm_bounded hc''.hasSum fun v => ?_
    by_cases hv : cl v = c
    · rw [indicator_of_mem (by exact hv)]
      refine (norm_sum_le _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.card_univ]
      refine Finset.sum_le_card_nsmul _ _ _ fun χ _ => ?_
      rw [norm_mul, norm_char, one_mul]
      exact norm_term_le_inv n hn (fun v => (χ (cl v) : ℂ)) (fun v => (norm_char χ _).le) v hs1.le
    · rw [indicator_of_notMem (by exact hv)]
      have : c⁻¹ * cl v ≠ 1 := fun h => hv (inv_mul_eq_one.1 h).symm
      have h0 := sum_char_eq_zero this
      simp only [map_mul, Units.val_mul] at h0
      simp only [← mul_assoc, ← Finset.sum_mul, h0]
      simp
  have hP1 : P 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have h2 : (fun s => ∑ χ ∈ Finset.univ.erase 1, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1]
        (fun _ => (1 : ℝ)) :=
      (IsBigO.sum fun χ hχ => (hP χ (Finset.ne_of_mem_erase hχ)).const_mul_left
        (χ c⁻¹ : ℂ)).congr_left fun s => Finset.sum_apply _ _ _
    refine (hS.sub h2).congr_left fun s => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G →* ℂˣ))]
    simp
  have hg1 : g 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    simpa using (hgP 1).add hP1
  obtain ⟨B, hB⟩ := hg1.bound
  have hlim : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1)) := by
    have : Continuous fun s : ℝ => Z s := by fun_prop
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B) ?_ ?_
    · filter_upwards [hB, self_mem_nhdsWithin] with s h hs1
      rw [h1 s hs1, norm_mul, norm_exp]
      gcongr
      rw [norm_one, mul_one] at h
      exact (re_le_norm _).trans h
    · have : Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B := by fun_prop
      simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  exact hZ1 (tendsto_nhds_unique hlim hlim0)

end orth

section field

variable {K : Type} [Field K] [NumberField K]

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem eq_span_of_not_prime (h2 : Module.finrank ℚ K = 2) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ∃ p : ℕ, v.asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm v.asIdeal = p ^ 2 := by
  have hP := v.isPrime
  have h2' := two_le_absNorm v
  have hm := Ideal.absNorm_mem v.asIdeal
  obtain ⟨p, hp, hpv⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal := by
    rw [← Nat.prod_primeFactorsList (n := Ideal.absNorm v.asIdeal) (by omega), Nat.cast_list_prod] at hm
    obtain ⟨x, hx, hxv⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem hP
      (((Ideal.absNorm v.asIdeal).primeFactorsList.map Nat.cast : List (𝓞 K)) : Multiset (𝓞 K))).1
      (by simpa using hm)
    simp only [Multiset.mem_coe, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hxv⟩
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.dvd_span_singleton]; exact hpv
  have hmul : p ^ 2 = Ideal.absNorm v.asIdeal * Ideal.absNorm J := by rw [← hN, hJ, map_mul]
  obtain ⟨i, hi, hiv⟩ := (Nat.dvd_prime_pow hp).1 ⟨_, hmul⟩
  have hi2 : i = 2 := by
    interval_cases i
    · rw [pow_zero] at hiv; omega
    · rw [pow_one] at hiv; exact absurd (hiv ▸ hp) hv
    · rfl
  subst hi2
  refine ⟨p, ?_, hiv⟩
  have hJ1 : Ideal.absNorm J = 1 := by
    rw [hiv] at hmul
    exact (Nat.mul_eq_left (pow_ne_zero _ hp.ne_zero)).1 hmul.symm
  rw [Ideal.absNorm_eq_one_iff] at hJ1
  rw [hJ, hJ1, Ideal.mul_top]

theorem summable_of_not_prime_or_le (h2 : Module.finrank ℚ K = 2) (N : ℕ) {ι : Type}
    (f : ι → HeightOneSpectrum (𝓞 K)) (hf : Function.Injective f)
    (h : ∀ i, (Ideal.absNorm (f i).asIdeal).Prime → Ideal.absNorm (f i).asIdeal ≤ N) :
    Summable fun i => ((Ideal.absNorm (f i).asIdeal : ℕ) : ℝ)⁻¹ := by
  have hfin : {i | Ideal.absNorm (f i).asIdeal ≤ N}.Finite := by
    have h1 : {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ N}.Finite := Ideal.finite_setOfPred_absNorm_le N
    refine Set.Finite.preimage (f := fun i => (f i).asIdeal) ?_ h1
    intro i _ j _ hij
    exact hf (HeightOneSpectrum.ext hij)
  rw [← hfin.summable_compl_iff]
  have hex : ∀ i : ↥({i | Ideal.absNorm (f i).asIdeal ≤ N}ᶜ : Set ι), ∃ p : ℕ,
      (f i).asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm (f i).asIdeal = p ^ 2 :=
    fun i => eq_span_of_not_prime h2 _ fun hp => i.2 (h i hp)
  choose p hp1 hp2 using hex
  have hinj : Function.Injective p := fun i j hij =>
    Subtype.ext (hf (HeightOneSpectrum.ext (by rw [hp1, hp1, hij])))
  have := (Real.summable_nat_pow_inv.2 one_lt_two).comp_injective hinj
  refine this.congr fun i => ?_
  simp [hp2]

end field

theorem exists_prime_in_class : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (c : D.G) (N : ℕ), ∃ v : D.Pr, D.cls v.1.asIdeal = c ∧ (Ideal.absNorm v.1.asIdeal).Prime ∧ N < Ideal.absNorm v.1.asIdeal := by
  intro K _ _ _ h2 M hM D c N
  by_contra hcon
  push Not at hcon
  obtain ⟨ρ, hρ, hZ⟩ := GlobalTheory.T.ray_class_partial_zeta_continuation K h2 M hM D
  choose Z hZd hZ1 _ hZs using hZ
  have hre : ∀ s : ℝ, 1 < s → 1 < (s : ℂ).re := fun s h => by simpa using h
  refine not_summable_class (fun v : D.Pr => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun v => D.cls v.1.asIdeal) ?_ ?_ (fun s => ∑ x, Z x s)
    (continuous_finsetSum _ fun x _ => (hZd x).continuous) ?_ ?_ c ?_
  · intro s hs
    refine (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D 1 s (hre s hs)).2.1.congr fun v => ?_
    rw [norm_natCast_cpow_of_pos (by linarith [two_le_absNorm v.1])]
    simp
  · intro χ hχ
    obtain ⟨L, hL, hL1, hL2⟩ := GlobalTheory.T.ray_L_nonvanishing_at_one K h2 M hM D χ hχ
    exact ⟨L, hL.continuous, hL1, fun s hs => by
      rw [hL2 s (hre s hs), (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D χ s (hre s hs)).2.2]⟩
  · simp only [hZ1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (by exact_mod_cast hρ.ne')
  · intro s hs
    rw [← (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D 1 s (hre s hs)).2.2]
    have hco : D.coef 1 = ∑ x, D.cnt x := by
      funext m
      simp [RayData.coef]
    rw [hco, LSeries_sum fun x _ => (hZs x s (hre s hs)).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => (hZs x s (hre s hs)).2
  · exact summable_of_not_prime_or_le h2 N (fun v : {v : D.Pr // D.cls v.1.asIdeal = c} => v.1.1)
      (fun i j hij => Subtype.ext (Subtype.ext hij)) fun i hi => hcon i.1 i.2 hi

end GlobalTheory.Mem.RayPrimes
end
