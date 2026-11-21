import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PFlagWeightLevi
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PHermitianDetMono
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PMongeAmpereCompactChange
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PMongeAmpereComparison
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsFSDensity
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsChartPartition
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsCoverInt
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsClosedPointGenericFibre
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPointAlgebraic
import GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPoint
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsKrullHeightOne
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviFormGbPotOne
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.NormLeOneIffIsIntegralElemOfEquiv

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

theorem FlagRootProduct.rootPairing_eq_abs {N p : ℕ} {lam : Fin N → ℝ}
    (hd : IsSplitDominant N p lam) (q : LowerPair N) :
    rootPairing N p lam q = |lam q.1.1 - lam q.1.2| := by
  obtain ⟨⟨a, b⟩, hba⟩ := q
  have hba' : b.val < a.val := hba
  have ha := a.isLt
  have hb := b.isLt
  unfold rootPairing
  dsimp only
  by_cases h : b.val < p ∧ p ≤ a.val
  · rw [if_pos h]
    have hle : lam b ≤ lam a := hd a b (by
      unfold splitRank
      rw [if_pos h.2, if_neg (by omega)]
      omega)
    rw [abs_of_nonneg (by linarith)]
  · rw [if_neg h]
    have hle : lam a ≤ lam b := hd b a (by
      unfold splitRank
      split_ifs <;> omega)
    rw [abs_of_nonpos (by linarith)]
    ring

theorem FlagRootProduct.proof : FlagRootProduct.Statement := by
  intro N p lam hd
  have h := fun q => FlagRootProduct.rootPairing_eq_abs (N := N) (p := p) hd q
  exact ⟨h, Finset.prod_congr rfl fun q _ => h q⟩

end GroundTheory.Heights₂.Heights.FourB
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

theorem one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (g h : ι → ℝ)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1) (hgh : ∀ i, 1 - g i ≤ h i) :
    1 - ∏ i ∈ s, g i ≤ ∑ i ∈ s, h i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hP0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i _ => hg0 i
    have hP1 : ∏ i ∈ s, g i ≤ 1 := Finset.prod_le_one (fun i _ => hg0 i) fun i _ => hg1 i
    have key : 1 - g a * ∏ i ∈ s, g i = (1 - ∏ i ∈ s, g i) + (1 - g a) * ∏ i ∈ s, g i := by ring
    have h1 : (1 - g a) * ∏ i ∈ s, g i ≤ 1 - g a :=
      mul_le_of_le_one_right (by linarith [hg1 a]) hP1
    linarith [hgh a]

theorem raiseSmall_factor {f : ℕ} (N j' : ℕ) (x : Fin f → Fin N → ℝ) (δ : ℝ)
    (hx : ∀ τ (i l : Fin N), i < l → x τ l < x τ i) (τ : Fin f) (i l : Fin N) :
    (if i < l then raiseSmall N j' δ x τ i - raiseSmall N j' δ x τ l else 1) =
      (if i < l then x τ i - x τ l else 1) *
        (if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1) := by
  by_cases hil : i < l
  · have hpos : 0 < x τ i - x τ l := sub_pos.mpr (hx τ i l hil)
    have hlt : i.val < l.val := hil
    simp only [if_pos hil, raiseSmall]
    by_cases hA : Across N j' i l
    · obtain ⟨h1, h2⟩ := hA
      have hi : ¬ N - j' ≤ i.val := by omega
      rw [if_neg hi, if_pos h2, if_pos (show Across N j' i l from ⟨h1, h2⟩)]
      field_simp
      ring
    · rw [if_neg hA, mul_one]
      simp only [Across, not_and, not_le] at hA
      by_cases hi : N - j' ≤ i.val
      · rw [if_pos hi, if_pos (show N - j' ≤ l.val by omega)]; ring
      · have hl := hA (by omega)
        rw [if_neg hi, if_neg (show ¬ N - j' ≤ l.val by omega)]
  · have hA : ¬ Across N j' i l := by
      rintro ⟨h1, h2⟩
      exact hil (Fin.lt_def.mpr (by omega))
    simp [hil, hA]

theorem DegreeRatio.proof : DegreeRatio.Statement := by
  intro f N j' x δ ⟨hδ, hx, hacross⟩
  set P : Fin f → Fin N → Fin N → ℝ :=
    fun τ i l => if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1 with hPdef
  set H : Fin f → Fin N → Fin N → ℝ :=
    fun τ i l => if Across N j' i l then δ / (x τ i - x τ l) else 0 with hHdef

  have hfac : ∀ τ (i l : Fin N), 0 < (if i < l then x τ i - x τ l else 1) := by
    intro τ i l
    split_ifs with h
    · exact sub_pos.mpr (hx τ i l h)
    · exact one_pos
  have hdeg : 0 < weightDegree x :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => hfac τ i l

  have hP0 : ∀ τ i l, 0 < P τ i l := by
    intro τ i l
    simp only [hPdef]
    split_ifs with hA
    · have hd := hacross τ i l hA
      have hpos : 0 < x τ i - x τ l := by linarith
      have : δ / (x τ i - x τ l) < 1 := (div_lt_one hpos).mpr hd
      linarith
    · exact one_pos
  have hP1 : ∀ τ i l, P τ i l ≤ 1 := by
    intro τ i l
    simp only [hPdef]
    split_ifs with hA
    · have hd := hacross τ i l hA
      have : 0 ≤ δ / (x τ i - x τ l) := div_nonneg hδ (by linarith)
      linarith
    · exact le_rfl
  have hPH : ∀ τ i l, 1 - P τ i l ≤ H τ i l := by
    intro τ i l
    simp only [hPdef, hHdef]
    split_ifs <;> simp

  have hratio : weightDegree (raiseSmall N j' δ x) / weightDegree x = ∏ τ, ∏ i, ∏ l, P τ i l := by
    rw [div_eq_iff hdeg.ne']
    simp only [weightDegree, raiseSmall_factor N j' x δ hx, Finset.prod_mul_distrib, hPdef]
    ring
  rw [hratio]
  have hin0 : ∀ τ i, 0 ≤ ∏ l, P τ i l := fun τ i => Finset.prod_nonneg fun l _ => (hP0 τ i l).le
  have hin1 : ∀ τ i, ∏ l, P τ i l ≤ 1 :=
    fun τ i => Finset.prod_le_one (fun l _ => (hP0 τ i l).le) fun l _ => hP1 τ i l
  have hmid0 : ∀ τ, 0 ≤ ∏ i, ∏ l, P τ i l := fun τ => Finset.prod_nonneg fun i _ => hin0 τ i
  have hmid1 : ∀ τ, ∏ i, ∏ l, P τ i l ≤ 1 :=
    fun τ => Finset.prod_le_one (fun i _ => hin0 τ i) fun i _ => hin1 τ i
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => hP0 τ i l
  · exact Finset.prod_le_one (fun τ _ => hmid0 τ) fun τ _ => hmid1 τ
  · refine one_sub_prod_le_sum _ _ _ hmid0 hmid1 fun τ => ?_
    refine one_sub_prod_le_sum _ _ _ (hin0 τ) (hin1 τ) fun i => ?_
    exact one_sub_prod_le_sum _ _ _ (fun l => (hP0 τ i l).le) (hP1 τ i) (hPH τ i)

end GroundTheory.Heights₂.Heights.FourB
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Finset

theorem card_window_fin (n a b : ℕ) (hb : b ≤ n) :
    ∑ i : Fin n, (if a ≤ i.val ∧ i.val < b then (1 : ℝ) else 0) = ((b - a : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if a ≤ i ∧ i < b then (1 : ℝ) else 0) n,
    Finset.sum_boole]
  congr 2
  have : (Finset.range n).filter (fun i => a ≤ i ∧ i < b) = Finset.Ico a b := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]

theorem RhoBound.proof (h : DegreeRatio.Statement) : RhoBound.Statement := by
  intro f k j j' x g₁ T w hH
  obtain ⟨hk, hg, hT, hw, hdec, hacr, hcloud⟩ := hH
  intro N ρ
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hg0 : 0 < g₁ := lt_of_le_of_lt (by positivity) hg
  have hδ : DegreeRatio.Hyp (k + j + j' - 1) j' x (3 * N) :=
    ⟨by positivity, hdec, fun τ i l hil => lt_of_lt_of_le hg (hacr τ i l hil)⟩
  obtain ⟨-, -, hle1, hsum⟩ := h f (k + j + j' - 1) j' x (3 * N) hδ

  have key : ∀ τ, ∑ i : Fin (k + j + j' - 1), ∑ l : Fin (k + j + j' - 1),
      (if Across (k + j + j' - 1) j' i l then 3 * N / (x τ i - x τ l) else 0) ≤
      3 * N * ((j : ℝ) * j' / g₁ + 2 * ((k : ℝ) - 1) * j' * T / w τ) := by
    intro τ
    set A : Fin (k + j + j' - 1) → ℝ := fun i => if 0 ≤ i.val ∧ i.val < k - 1 then 1 else 0
    set C : Fin (k + j + j' - 1) → ℝ := fun i => if k - 1 ≤ i.val ∧ i.val < k + j - 1 then 1 else 0
    set B : Fin (k + j + j' - 1) → ℝ :=
      fun l => if k + j - 1 ≤ l.val ∧ l.val < k + j + j' - 1 then 1 else 0
    have hterm : ∀ i l : Fin (k + j + j' - 1),
        (if Across (k + j + j' - 1) j' i l then 3 * N / (x τ i - x τ l) else 0) ≤
          3 * N * (2 * T / w τ) * (A i * B l) + 3 * N * (1 / g₁) * (C i * B l) := by
      intro i l
      have hT' : 0 ≤ 3 * N * (2 * T / w τ) := by have := hw τ; positivity
      have hg' : 0 ≤ 3 * N * (1 / g₁) := by positivity
      have hA0 : 0 ≤ A i := by simp only [A]; split_ifs <;> norm_num
      have hB0 : 0 ≤ B l := by simp only [B]; split_ifs <;> norm_num
      have hC0 : 0 ≤ C i := by simp only [C]; split_ifs <;> norm_num
      by_cases hA : Across (k + j + j' - 1) j' i l
      · rw [if_pos hA]
        have hd : g₁ ≤ x τ i - x τ l := hacr τ i l hA
        have hdpos : 0 < x τ i - x τ l := lt_of_lt_of_le hg0 hd
        have hB1 : B l = 1 := by
          simp only [B]; rw [if_pos]; unfold Across at hA; have := l.isLt; omega
        by_cases hc : i.val < k - 1
        · have hA1 : A i = 1 := by simp only [A]; rw [if_pos]; omega
          have hC1 : C i = 0 := by simp only [C]; rw [if_neg]; omega
          rw [hA1, hB1, hC1]
          have hwd : w τ / (2 * T) ≤ x τ i - x τ l := hcloud τ i l hc hA
          have hwpos : 0 < w τ / (2 * T) := by have := hw τ; positivity
          have : 1 / (x τ i - x τ l) ≤ 2 * T / w τ := by
            rw [div_le_div_iff₀ hdpos (hw τ)]
            rw [div_le_iff₀ (by positivity)] at hwd
            linarith
          calc 3 * N / (x τ i - x τ l) = 3 * N * (1 / (x τ i - x τ l)) := by ring
            _ ≤ 3 * N * (2 * T / w τ) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
        · have hA1 : A i = 0 := by simp only [A]; rw [if_neg]; omega
          have hC1 : C i = 1 := by
            simp only [C]; rw [if_pos]; unfold Across at hA; omega
          rw [hA1, hB1, hC1]
          have : 1 / (x τ i - x τ l) ≤ 1 / g₁ := one_div_le_one_div_of_le hg0 hd
          calc 3 * N / (x τ i - x τ l) = 3 * N * (1 / (x τ i - x τ l)) := by ring
            _ ≤ 3 * N * (1 / g₁) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
      · rw [if_neg hA]; positivity
    have hAs : ∑ i, A i = ((k - 1 - 0 : ℕ) : ℝ) := card_window_fin _ 0 (k - 1) (by omega)
    have hCs : ∑ i, C i = ((k + j - 1 - (k - 1) : ℕ) : ℝ) := card_window_fin _ _ _ (by omega)
    have hBs : ∑ l, B l = ((k + j + j' - 1 - (k + j - 1) : ℕ) : ℝ) :=
      card_window_fin _ _ _ le_rfl
    have e1 : k - 1 - 0 = k - 1 := by omega
    have e2 : k + j - 1 - (k - 1) = j := by omega
    have e3 : k + j + j' - 1 - (k + j - 1) = j' := by omega
    rw [e1] at hAs; rw [e2] at hCs; rw [e3] at hBs
    calc _ ≤ ∑ i : Fin (k + j + j' - 1), ∑ l : Fin (k + j + j' - 1),
          (3 * N * (2 * T / w τ) * (A i * B l) + 3 * N * (1 / g₁) * (C i * B l)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hterm i l
      _ = 3 * N * (2 * T / w τ) * ((∑ i, A i) * ∑ l, B l) +
            3 * N * (1 / g₁) * ((∑ i, C i) * ∑ l, B l) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul_sum]
      _ = _ := by
          rw [hAs, hBs, hCs, Nat.cast_sub hk]
          have := hw τ
          field_simp
          ring
  refine ⟨by simp only [ρ]; linarith, ?_, ?_⟩
  · calc ρ ≤ ∑ τ, ∑ i : Fin (k + j + j' - 1), ∑ l : Fin (k + j + j' - 1),
          (if Across (k + j + j' - 1) j' i l then 3 * N / (x τ i - x τ l) else 0) := hsum
      _ ≤ ∑ τ, 3 * N * ((j : ℝ) * j' / g₁ + 2 * ((k : ℝ) - 1) * j' * T / w τ) :=
          Finset.sum_le_sum fun τ _ => key τ
      _ = _ := by rw [Finset.mul_sum]
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    have hwτ := hw τ
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hj' : (0 : ℝ) ≤ j' := Nat.cast_nonneg _
    have h1 : (j : ℝ) * j' / g₁ ≤ 2 * (((j : ℝ) + j') ^ 2 / g₁) := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hg0]; nlinarith
    have h2 : 2 * ((k : ℝ) - 1) * j' * T / w τ ≤ 2 * (((j : ℝ) + j') * k * T / w τ) := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hwτ]
      have : ((k : ℝ) - 1) * j' ≤ ((j : ℝ) + j') * k := by nlinarith
      nlinarith
    nlinarith

end GroundTheory.Heights₂.Heights.FourB
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

abbrev coverFSPot (e : ℕ) (z : Fin e → ℂ) : ℝ := (1 / 2) * Real.log (1 + ∑ i, ‖z i‖ ^ 2)

theorem coverFSPot_contDiff (e : ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (coverFSPot e) := by
  unfold coverFSPot
  refine contDiff_const.mul (ContDiff.log (contDiff_const.add
    (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))) fun z => ?_)
  positivity

theorem coverFS_local {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)} {d : ℕ}
    (hH : FubiniStudyCoverMass.Hyp A P q M₀ Δ d) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x)
    (hm : (A.chart j).symm y ∈ M₀) :
    AnalyticAt ℂ (q ∘ (A.chart j).symm) y ∧ ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G y ∧
      P.φ x ∘ (A.chart j).symm =ᶠ[𝓝 y]
        fun y' => (coverFSPot e ∘ (q ∘ (A.chart j).symm)) y' + (G y').re := by
  obtain ⟨-, hM, -, -, hq, -, -, -, -, hloc⟩ := hH
  refine ⟨analyticAt_pi_iff.2 fun i => hq i j y ⟨hy, hm⟩, ?_⟩
  obtain ⟨W, hWo, hyW, G, hG, heq⟩ := hloc x _ ⟨hx, hm⟩
  refine ⟨G ∘ (A.chart j).symm, hG j y ⟨hy, hyW⟩, ?_⟩
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (W ∩ P.U x ∩ M₀)) :=
    (A.chart j).isOpen_inter_preimage_symm ((hWo.inter (P.isOpen_U x)).inter hM)
  filter_upwards [hO.mem_nhds ⟨hy, ⟨hyW, hx⟩, hm⟩] with y' hy'
  exact heq _ hy'.2

theorem coverFS_contDiffAt {e : ℕ} {τ : (Fin e → ℂ) → (Fin e → ℂ)} {y : Fin e → ℂ}
    (hτ : AnalyticAt ℂ τ y) : ContDiffAt ℝ 2 (coverFSPot e ∘ τ) y :=
  (coverFSPot_contDiff e).contDiffAt.comp y hτ.restrictScalars.contDiffAt

theorem fubiniStudyCover_levi_nonneg (hFS : FubiniStudyChartDensity.Statement) {e : ℕ} {X : Type}
    [TopologicalSpace X] {A : FinHolAtlas e X} {P : LocPot X} {q : X → Fin e → ℂ} {M₀ : Set X}
    {Δ : Set (Fin e → ℂ)} {d : ℕ} (hH : FubiniStudyCoverMass.Hyp A P q M₀ Δ d) (x : X)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hx : (A.chart j).symm y ∈ P.U x) (hm : (A.chart j).symm y ∈ M₀) (w : Fin e → ℂ) :
    0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w := by
  obtain ⟨hτ, G, hG, hev⟩ := coverFS_local hH x j hy hx hm
  have hg : ContDiffAt ℝ 2 (fun y' => (G y').re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y hG.restrictScalars.contDiffAt
  have hsum : (fun y' => (coverFSPot e ∘ (q ∘ (A.chart j).symm)) y' + (G y').re) =
      fun y' => (coverFSPot e ∘ (q ∘ (A.chart j).symm)) y' + 1 * (G y').re := by
    funext y'; rw [one_mul]
  rw [levi_congr hev, hsum, levi_add_smul 1 (coverFS_contDiffAt hτ) hg, levi_re_analytic hG,
    mul_zero, add_zero, levi_comp w hτ (coverFSPot_contDiff e).contDiffAt]
  exact (hFS e _ _).1

theorem coverFS_locDens (hFS : FubiniStudyChartDensity.Statement) {e : ℕ} {X : Type}
    [TopologicalSpace X] {A : FinHolAtlas e X} {P : LocPot X} {q : X → Fin e → ℂ} {M₀ : Set X}
    {Δ : Set (Fin e → ℂ)} {d : ℕ} (hH : FubiniStudyCoverMass.Hyp A P q M₀ Δ d) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hm : (A.chart j).symm y ∈ M₀) :
    locDens A (fun _ => P) j y =
      (e.factorial : ℝ) / (Real.pi ^ e * (1 + ∑ i, ‖q ((A.chart j).symm y) i‖ ^ 2) ^ (e + 1)) *
        ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  obtain ⟨hτ, G, hG, hev⟩ := coverFS_local hH ((A.chart j).symm y) j hy (P.mem_U _) hm
  have h1 : locDens A (fun _ => P) j y =
      maDens (fun _ => P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y := rfl
  have h2 : maDens (fun _ => P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y =
      maDens (fun _ => coverFSPot e ∘ (q ∘ (A.chart j).symm)) y := by
    rw [maDens_congr_eventuallyEq (fun _ => hev)]
    exact maDens_congr_hessC _ _ y fun _ =>
      ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ G y (coverFS_contDiffAt hτ) hG
  have h3 := ReciprocityTheory.AnForm.A.maDens_comp (fun _ => coverFSPot e) (q ∘ (A.chart j).symm) y hτ
    fun _ => (coverFSPot_contDiff e).contDiffAt
  rw [h1, h2, h3, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq]
  congr 1
  exact (hFS e _ 0).2

theorem FubiniStudyCoverMass.proof (hFS : FubiniStudyChartDensity.Statement)
    (hPart : ChartPartitionExists.Statement) (hCov : CoverChartLIntegral.Statement) :
    FubiniStudyCoverMass.Statement := by
  intro e X _ _ _ _ A P q M₀ Δ d hH
  have hH' := hH
  obtain ⟨hP, hM, hAn, hInt, hq, hΔc, hΔ0, hcov, hdeg, -⟩ := hH'
  refine ⟨?_, ?_⟩
  ·
    intro x j y hy w
    by_contra hneg
    have hneg' := not_le.1 hneg
    have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
      (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
    have hc : ContinuousAt (fun y' => levi (P.φ x ∘ (A.chart j).symm) y' w) y := by
      have h := (continuousOn_levi hU (potSmoothOn A P hP x j)).continuousAt
        ((hU.prod isOpen_univ).mem_nhds (Set.mk_mem_prod hy (Set.mem_univ w)))
      have hpair : ContinuousAt (fun y' : Fin e → ℂ => (y', w)) y :=
        continuousAt_id.prodMk continuousAt_const
      exact ContinuousAt.comp (f := fun y' : Fin e → ℂ => (y', w)) h hpair
    have hev : ∀ᶠ y' in 𝓝 y, levi (P.φ x ∘ (A.chart j).symm) y' w < 0 ∧
        y' ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
      (hc.eventually (gt_mem_nhds hneg')).and (hU.mem_nhds hy)
    have hfr : ∃ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ M₀ := by
      intro hno
      obtain ⟨N, hNsub, hNo, hyN⟩ := mem_nhds_iff.1 (hno.and ((A.chart j).open_target.mem_nhds hy.1))
      have himg : IsOpen ((A.chart j).symm '' N) :=
        (A.chart j).isOpen_image_symm_of_subset_target hNo fun z hz => (hNsub hz).2
      have hsub : (A.chart j).symm '' N ⊆ interior M₀ᶜ :=
        interior_maximal (by rintro _ ⟨z, hz, rfl⟩; exact (hNsub hz).1) himg
      rw [hInt] at hsub
      exact hsub ⟨y, hyN, rfl⟩
    obtain ⟨y', hm, hlt, hyU⟩ := (hfr.and_eventually hev).exists
    exact absurd (fubiniStudyCover_levi_nonneg hFS hH x j hyU.1 hyU.2 hm w) (not_le.2 hlt)
  ·
    have hχ : Nonempty (ChartPartition A) := hPart A
    set χ := hχ.some with hχdef
    have hmass : maMeasure A (fun _ => P) Set.univ = ∑ j, ∫⁻ y in (A.chart j).target,
        ENNReal.ofReal (χ.χ j ((A.chart j).symm y) * locDens A (fun _ => P) j y) := by
      rw [maMeasure, dif_pos hχ, Measure.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Measure.map_apply_of_aemeasurable ?_ MeasurableSet.univ, Set.preimage_univ,
        withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact ((A.chart j).continuousOn_symm.aemeasurable
        (A.chart j).open_target.measurableSet).mono_ac (withDensity_absolutelyContinuous _ _)
    have hpiece : ∀ j, ∫⁻ y in (A.chart j).target,
        ENNReal.ofReal (χ.χ j ((A.chart j).symm y) * locDens A (fun _ => P) j y) =
        ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀,
          ENNReal.ofReal (χ.χ j ((A.chart j).symm y)) *
            ENNReal.ofReal (‖LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) y :
              (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2) *
            (fun z => ENNReal.ofReal (CP.fsVolumeDensity (N := e) 0 z)) (q ((A.chart j).symm y)) := by
      intro j
      have hae : ((A.chart j).target : Set (Fin e → ℂ)) =ᵐ[volume]
          ((A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀ : Set (Fin e → ℂ)) := by
        refine ae_eq_set.2 ⟨measure_mono_null ?_ (analyticNull A M₀ᶜ hAn hInt j), ?_⟩
        · rintro y ⟨hy, hyV⟩
          exact ⟨(A.chart j).symm y, ⟨fun hm => hyV ⟨hy, hm⟩, (A.chart j).map_target hy⟩,
            (A.chart j).right_inv hy⟩
        · rw [Set.sdiff_eq_empty.2 Set.inter_subset_left, measure_empty]
      rw [setLIntegral_congr hae]
      refine setLIntegral_congr_fun ((A.chart j).isOpen_inter_preimage_symm hM).measurableSet
        fun y hy => ?_
      rw [coverFS_locDens hFS hH j hy.1 hy.2]
      beta_reduce
      rw [CP.fsVolumeDensity_eq,
        ENNReal.ofReal_mul (χ.nonneg j _), ENNReal.ofReal_mul (by positivity)]
      simp only [normSqSum]
      ring
    have hmeas : Measurable fun z => ENNReal.ofReal (CP.fsVolumeDensity (N := e) 0 z) :=
      (CP.measurable_fsVolumeDensity 0).ennreal_ofReal
    rw [hmass, Finset.sum_congr rfl fun j _ => hpiece j,
      hCov A χ q M₀ Δ d ⟨hM, hq, hΔc, hcov, hdeg⟩ _ hmeas,
      setLIntegral_congr (ae_eq_univ.2 (by rwa [compl_compl])), Measure.restrict_univ,
      CP.lintegral_fsVolumeDensity, mul_one]

end

end GroundTheory.Heights₂.Heights.FourB
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

theorem exists_maximal_of_fibre (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (v : HeightOneSpectrum (𝓞 F)) (P : Ideal R)
    (u : R) (hP : P.IsPrime) (hPv : P.comap (algebraMap (𝓞 F) R) = v.asIdeal) (hu : u ∉ P) :
    ∃ M : Ideal R, M.IsMaximal ∧ P ≤ M ∧ u ∉ M := by
  have hc : (P.comap (algebraMap (𝓞 F) R)).IsMaximal := hPv ▸ v.isMaximal
  let : Field (𝓞 F ⧸ P.comap (algebraMap (𝓞 F) R)) := Ideal.Quotient.field _
  have : Algebra.FiniteType (𝓞 F) (R ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (𝓞 F) P)
      (Ideal.Quotient.mkₐ_surjective (𝓞 F) P)
  have : Algebra.FiniteType (𝓞 F ⧸ P.comap (algebraMap (𝓞 F) R)) (R ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (𝓞 F) _ _
  have : IsJacobsonRing (R ⧸ P) :=
    isJacobsonRing_of_finiteType (A := 𝓞 F ⧸ P.comap (algebraMap (𝓞 F) R))
  have hbot : (⊥ : Ideal (R ⧸ P)).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.1 inferInstance ⊥ Ideal.isPrime_bot
  have hu' : Ideal.Quotient.mk P u ∉ (⊥ : Ideal (R ⧸ P)).jacobson := by
    rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact hu
  rw [Ideal.jacobson, Ideal.mem_sInf] at hu'
  push Not at hu'
  obtain ⟨J, ⟨-, hJ⟩, huJ⟩ := hu'
  refine ⟨J.comap (Ideal.Quotient.mk P),
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective, ?_, huJ⟩
  intro a ha
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  exact J.zero_mem

theorem IntegralPointThroughPrime.proof (h₁ : ClosedPointOfGenericFibre.Statement)
    (h₂ : IntegralPointOfAlgebraicDomain.Statement) : IntegralPointThroughPrime.Statement := by
  intro F _ _ R _ _ _ _ _ v P u g ⟨hP, hPv, hu, hg⟩
  obtain ⟨M, hM, hPM, huM⟩ := exists_maximal_of_fibre F R v P u hP hPv hu
  have hMv : M.comap (algebraMap (𝓞 F) R) = v.asIdeal :=
    ((v.isMaximal.eq_of_le (Ideal.IsPrime.comap (algebraMap (𝓞 F) R) (hK := hM.isPrime)).ne_top
      (hPv ▸ Ideal.comap_mono hPM))).symm
  obtain ⟨Q, hQ, hQM, hQ0, hgQ, hQalg⟩ := h₁ F R M g ⟨hM, hg⟩
  have := hQ
  have : Algebra.FiniteType (𝓞 F) (R ⧸ Q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ (𝓞 F) Q)
      (Ideal.Quotient.mkₐ_surjective (𝓞 F) Q)
  set M' : Ideal (R ⧸ Q) := M.map (Ideal.Quotient.mk Q)
  have hcomap : M'.comap (Ideal.Quotient.mk Q) = M := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.2 hQM]
  have hM' : M'.IsMaximal := hM.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hQM)
  have hq : algebraMap (𝓞 F) (R ⧸ Q) = (Ideal.Quotient.mk Q).comp (algebraMap (𝓞 F) R) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 F) (R ⧸ Q)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hq, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.mem_comap, hQ0, Ideal.mem_bot] at hx
    exact hx
  have hM'v : M'.comap (algebraMap (𝓞 F) (R ⧸ Q)) = v.asIdeal := by
    rw [hq, ← Ideal.comap_comap, hcomap, hMv]
  obtain ⟨L, iL, aL, fL, y, hy, hyinj, hint, hunit, hnon⟩ :=
    h₂ F (R ⧸ Q) v M' ⟨hinj, hQalg, hM', hM'v⟩
  refine ⟨L, iL, aL, fL, y.comp (Ideal.Quotient.mk Q), ?_, fun a => hint _, ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, ← hq, hy]
  · intro h
    apply hgQ
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hyinj (by rw [map_zero]; exact h)
  · refine hunit _ fun h => huM ?_
    rw [← hcomap]
    exact h
  · intro a ha
    exact hnon _ (Ideal.mem_map_of_mem _ (hPM ha))

end GroundTheory.Heights₂.Heights.FourB
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

theorem exists_prime_mul_eq_of_not_dvd {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a b : A} (hab : ¬ b ∣ a) :
    ∃ P : Ideal A, P.IsPrime ∧ ∃ w ∉ P, ∃ c ∈ P, w * b = c * a := by
  classical
  by_cases hb : b = 0
  · refine ⟨⊥, Ideal.isPrime_bot, 1, ?_, 0, (⊥ : Ideal A).zero_mem, by simp [hb]⟩
    rw [Submodule.mem_bot]
    exact one_ne_zero
  let N : Submodule A (A ⧸ Ideal.span {b}) := Submodule.span A {Ideal.Quotient.mk _ a}
  let n₀ : N := ⟨Ideal.Quotient.mk _ a, Submodule.subset_span rfl⟩
  have hn₀ : n₀ ≠ 0 := by
    intro h
    apply hab
    have : Ideal.Quotient.mk (Ideal.span {b}) a = 0 := congrArg Subtype.val h
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A n₀ hn₀
  obtain ⟨hPp, ⟨m, hm⟩, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.1 hm
  obtain ⟨y, hy⟩ : ∃ y, y = x * a := ⟨_, rfl⟩
  have hmem : ∀ r, r ∈ P ↔ b ∣ r * y := by
    intro r
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.coe_inj]
    show r • (x • Ideal.Quotient.mk (Ideal.span {b}) a) = 0 ↔ b ∣ r * y
    rw [smul_smul, GroundTheory.Arith.Toric.smul_mk_eq_zero_iff, hy, mul_assoc]
  have hbP : b ∈ P := (hmem b).2 (dvd_mul_right b y)
  by_cases hcase : ∀ r s : A, r ∈ P → r * y = b * s → s ∈ P
  · exfalso
    let K := FractionRing A
    have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
    let M : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hMfg : M.FG := (IsNoetherian.noetherian P).map _
    have hM0 : M ≠ ⊥ := by
      intro h
      have : algebraMap A K b ∈ M := Submodule.mem_map.2 ⟨b, hbP, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hb (hinj (by rw [this, map_zero]))
    have hbK : algebraMap A K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hint : IsIntegral A (algebraMap A K y / algebraMap A K b) := by
      refine isIntegral_of_smul_mem_submodule M hM0 hMfg _ ?_
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      refine Submodule.mem_map.2 ⟨s, hcase r s hr hs, ?_⟩
      change algebraMap A K s = (algebraMap A K y / algebraMap A K b) * algebraMap A K r
      rw [div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul, mul_comm y r, hs, mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hyz : y = b * z := by
      apply hinj
      rw [map_mul, hz, mul_div_cancel₀ _ hbK]
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, hmem, one_mul, hyz]
    exact dvd_mul_right b z
  · push Not at hcase
    obtain ⟨r₀, s₀, hr₀, hrs, hs₀⟩ := hcase
    refine ⟨P, hPp, s₀, hs₀, r₀ * x, P.mul_mem_right x hr₀, ?_⟩
    rw [mul_assoc, ← hy, hrs, mul_comm]

theorem IntegralOnModel.proof (hpt : IntegralPointThroughPrime.Statement) :
    IntegralOnModel.Statement := by
  intro F _ _ R _ _ _ _ _ _ r g s ⟨hs, hg, hpts⟩
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (𝓞 F) R
  by_contra hndvd
  have hnd : ¬ algebraMap (𝓞 F) R s ∣ r := fun ⟨r', h⟩ => hndvd ⟨r', h⟩
  obtain ⟨P, hP, w, hw, c, hc, hwc⟩ := exists_prime_mul_eq_of_not_dvd hnd
  have hsP : algebraMap (𝓞 F) R s ∈ P := by
    have : w * algebraMap (𝓞 F) R s ∈ P := hwc ▸ P.mul_mem_right r hc
    exact (hP.mem_or_mem this).resolve_left hw
  have hpP : (P.comap (algebraMap (𝓞 F) R)).IsPrime := Ideal.comap_isPrime _ P
  have hp0 : P.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
    intro h
    have : s ∈ P.comap (algebraMap (𝓞 F) R) := hsP
    rw [h, Submodule.mem_bot] at this
    exact hs this
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.comap (algebraMap (𝓞 F) R), hpP, hp0⟩
  obtain ⟨L, _, _, _, y, hcomp, hint, hyg, ⟨bw, hbw, hbwint⟩, hPnon⟩ :=
    hpt F R v P w g ⟨hP, rfl, hw, hg⟩
  have hys : y (algebraMap (𝓞 F) R s) ≠ 0 := by
    rw [← RingHom.comp_apply, hcomp]
    simp only [RingHom.comp_apply, ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hs
  have hyr := hpts v L y hcomp hint hyg
  apply hPnon c hc (y r / y (algebraMap (𝓞 F) R s) * bw) _ (RingHom.IsIntegralElem.mul _ hyr hbwint)
  have h1 : y w * y (algebraMap (𝓞 F) R s) = y c * y r := by rw [← map_mul, ← map_mul, hwc]
  calc y r / y (algebraMap (𝓞 F) R s) * bw * y c
      = bw * y w * ((y c * y r) / (y w * y (algebraMap (𝓞 F) R s))) := by
        have hyw : y w ≠ 0 := fun h0 => by simp [h0] at hbw
        field_simp
    _ = 1 := by rw [hbw, ← h1, div_self (mul_ne_zero (fun h0 => by simp [h0] at hbw) hys), one_mul]

end GroundTheory.Heights₂.Heights.FourB
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open Ideal

theorem KrullHeightOne.exists_prime_colon {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p q : A) (hqp : ¬ q ∣ p) :
    ∃ (a : A) (P : Ideal A), P.IsPrime ∧ ¬ q ∣ a * p ∧ ∀ x, x ∈ P ↔ q ∣ x * (a * p) := by
  let mk := Ideal.Quotient.mk (Ideal.span {q})
  let M := Submodule.span A {mk p}
  have hx : (⟨mk p, Submodule.mem_span_singleton_self _⟩ : M) ≠ 0 := by
    intro h
    apply hqp
    have : mk p = 0 := congrArg Subtype.val h
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hx
  obtain ⟨hPp, y, hy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 y.2
  have key : ∀ x, x ∈ P ↔ q ∣ x * (a * p) := by
    intro x
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.val_inj]
    change x • (y : A ⧸ Ideal.span {q}) = 0 ↔ _
    rw [← ha, smul_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, mul_assoc]
  refine ⟨a, P, hPp, fun h => hPp.ne_top ?_, key⟩
  rw [Ideal.eq_top_iff_one, key, one_mul]
  exact h

theorem KrullHeightOne.proof : KrullHeightOne.Statement := by
  intro A _ _ _ _ p q hpq
  obtain ⟨hq, hqp⟩ := hpq
  obtain ⟨a, P, hPp, hb, hP⟩ := KrullHeightOne.exists_prime_colon p q hqp
  have hqP : q ∈ P := (hP q).2 (dvd_mul_right q _)
  have hPbot : P ≠ ⊥ := fun h => hq (by rw [h, Ideal.mem_bot] at hqP; exact hqP)

  have hex : ∃ u ∈ P, ∃ w ∉ P, u * (a * p) = q * w := by
    by_contra hne
    have hne' : ∀ u ∈ P, ∀ w, u * (a * p) = q * w → w ∈ P := by
      intro u hu w huw
      by_contra hw
      exact hne ⟨u, hu, w, hw, huw⟩
    have hqK : algebraMap A (FractionRing A) q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hq
    let N : Submodule A (FractionRing A) := Submodule.map (Algebra.linearMap A (FractionRing A)) P
    have hN : N ≠ ⊥ := by
      intro h
      have : algebraMap A (FractionRing A) q ∈ N := Submodule.mem_map_of_mem hqP
      rw [h, Submodule.mem_bot] at this
      exact hqK this
    have hNfg : N.FG := (IsNoetherian.noetherian P).map _
    have hy : IsIntegral A (algebraMap A (FractionRing A) (a * p) / algebraMap A (FractionRing A) q) := by
      refine isIntegral_of_smul_mem_submodule N hN hNfg _ ?_
      intro n hn
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨w, hw⟩ := (hP x).1 hx
      have hwP : w ∈ P := hne' x hx w hw
      refine Submodule.mem_map.2 ⟨w, hwP, ?_⟩
      show algebraMap A (FractionRing A) w =
        algebraMap A (FractionRing A) (a * p) / algebraMap A (FractionRing A) q *
          algebraMap A (FractionRing A) x
      rw [div_mul_eq_mul_div, eq_div_iff hqK, ← map_mul, ← map_mul, mul_comm (a * p) x, hw,
        mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hy
    apply hb
    refine ⟨z, IsFractionRing.injective A (FractionRing A) ?_⟩
    rw [map_mul _ q z, hz]
    exact (mul_div_cancel₀ _ hqK).symm
  obtain ⟨u, hu, w, hw, huw⟩ := hex

  have hmin : P ∈ (Ideal.span {u}).minimalPrimes := by
    refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 hu⟩, ?_⟩
    rintro Q ⟨hQ, huQ⟩ hQP x hx
    obtain ⟨v, hv⟩ := (hP x).1 hx
    have h1 : x * w = u * v := by
      apply mul_left_cancel₀ hq
      linear_combination (-x) * huw + u * hv
    have h2 : x * w ∈ Q := by
      rw [h1]
      exact Q.mul_mem_right v ((Ideal.span_singleton_le_iff_mem _).1 huQ)
    rcases hQ.mem_or_mem h2 with h | h
    · exact h
    · exact absurd (hQP h) hw
  have : (Ideal.span {u}).IsPrincipal := ⟨⟨u, rfl⟩⟩
  have := hPp
  have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
  have hge : 1 ≤ P.height :=
    Order.one_le_iff_ne_zero.2 fun h => hPbot (Ideal.height_eq_zero_iff_eq_bot.1 h)
  refine ⟨P, hPp, le_antisymm hle hge, w, hw, u * a, P.mul_mem_right a hu, ?_⟩
  linear_combination -huw

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

def ZariskiDense.Hyp (A : Type*) [CommRing A] [Algebra ℂ A] (g : A) : Prop :=
  Algebra.FiniteType ℂ A ∧ IsDomain A ∧ g ≠ 0

def ZariskiDense.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℂ A] (g : A), ZariskiDense.Hyp A g →
    ∀ (x : A →ₐ[ℂ] ℂ) (s : Finset A) (ε : ℝ), 0 < ε →
      ∃ y : A →ₐ[ℂ] ℂ, (∀ a ∈ s, ‖y a - x a‖ < ε) ∧ y g ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

theorem RiemannExt.exists_point {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (P : Ideal A) [P.IsPrime] (c : A) (hc : c ∉ P) :
    ∃ x : A →ₐ[ℂ] ℂ, (∀ a ∈ P, x a = 0) ∧ x c ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hJ : P.jacobson = P := IsJacobsonRing.out ‹_› (Ideal.IsPrime.isRadical ‹_›)
  rw [← hJ, Ideal.jacobson, Submodule.mem_sInf] at hc
  push Not at hc
  obtain ⟨m, ⟨hPm, hm⟩, hcm⟩ := hc
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  let e : ℂ ≃ₐ[ℂ] A ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), fun a ha => ?_, ?_⟩
  · simp [Ideal.Quotient.eq_zero_iff_mem.2 (hPm ha)]
  · simpa [Ideal.Quotient.eq_zero_iff_mem] using hcm

theorem RiemannExt.proof (hK : KrullHeightOne.Statement) (hZ : ZariskiDense.Statement) :
    RiemannExt.Statement := by
  classical
  intro A _ _ p q ⟨hft, hdom, hic, hq, hbdd⟩
  by_contra hne
  have hdvd : ¬ q ∣ p := fun ⟨r, hr⟩ => hne ⟨r, hr⟩
  have := hdom
  have := hft
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hp : p ≠ 0 := by rintro rfl; exact hdvd (dvd_zero q)
  obtain ⟨P, hP, -, c, hc, t, ht, hct⟩ := hK A p q ⟨hq, hdvd⟩
  obtain ⟨x, hxP, hxc⟩ := RiemannExt.exists_point P c hc
  obtain ⟨s, ε, hε, M, hM⟩ := hbdd x
  have hδ : 0 < ‖x c‖ := norm_pos_iff.2 hxc
  have hxt : x t = 0 := hxP t ht
  have hM1 : 0 < |M| + 1 := by positivity
  obtain ⟨y, hy, hyg⟩ := hZ A (p * q) ⟨hft, hdom, mul_ne_zero hp hq⟩ x (insert c (insert t s))
    (min ε (min (‖x c‖ / 2) (‖x c‖ / (2 * (|M| + 1))))) (by positivity)
  have hyp : y p ≠ 0 := fun h => hyg (by rw [map_mul, h, zero_mul])
  have hyq : y q ≠ 0 := fun h => hyg (by rw [map_mul, h, mul_zero])
  have h1 := hM y (fun a ha => (hy a (by simp [ha])).trans_le (min_le_left _ _)) hyq
  have hyc : ‖y c - x c‖ < ‖x c‖ / 2 :=
    (hy c (by simp)).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hyt : ‖y t‖ < ‖x c‖ / (2 * (|M| + 1)) := by
    have := (hy t (by simp)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rwa [hxt, sub_zero] at this
  have hrel : ‖y c‖ * ‖y q‖ = ‖y t‖ * ‖y p‖ := by
    rw [← norm_mul, ← norm_mul, ← map_mul, ← map_mul, hct]
  have hc' : ‖x c‖ / 2 < ‖y c‖ := by
    have := norm_sub_norm_le (x c) (y c)
    rw [norm_sub_rev] at this
    linarith
  have key : ‖y c‖ ≤ |M| * ‖y t‖ := by
    have hle : ‖y c‖ * ‖y q‖ ≤ (|M| * ‖y t‖) * ‖y q‖ := by
      rw [hrel]
      calc ‖y t‖ * ‖y p‖ ≤ ‖y t‖ * (M * ‖y q‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ ‖y t‖ * (|M| * ‖y q‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)) (norm_nonneg _)
        _ = (|M| * ‖y t‖) * ‖y q‖ := by ring
    exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hyq)
  have hsmall : |M| * ‖y t‖ < ‖x c‖ / 2 := by
    calc |M| * ‖y t‖ ≤ (|M| + 1) * ‖y t‖ := by nlinarith [norm_nonneg (y t)]
      _ < (|M| + 1) * (‖x c‖ / (2 * (|M| + 1))) := mul_lt_mul_of_pos_left hyt hM1
      _ = ‖x c‖ / 2 := by field_simp
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem DetMono.equiv :
    FourB.HermitianDetMono.Statement ↔ IndefiniteRowSideFullHecke.FourB.DetMono.Statement := by
  constructor
  · intro h n A A' hA
    exact h n A A' hA.1 hA.2
  · intro h n A B hB hAB
    exact h n A B ⟨hB, hAB⟩

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

namespace MACompact

variable {D : ℕ} {Ω : Set (Fin D → ℂ)}

theorem maDens_eq_topDens (f ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : f =ᶠ[𝓝 z] fun y => ψ y / 2) : maDens (fun _ : Fin D => f) z = topDens ψ z := by
  have h2 : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ fun y => ψ y / 2) z :=
    h.fderiv.fderiv_eq
  have h3 : hessC f z = cxHessian (fun y => ψ y / 2) z := by
    unfold hessC cxHessian
    rw [h2]
  simp only [maDens, topDens, maDensity, mdisc, mixedDisc, h3]

theorem topDens_congr {ψ ψ' : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : ψ =ᶠ[𝓝 z] ψ') :
    topDens ψ z = topDens ψ' z := by
  have h1 : (fun y => ψ y / 2) =ᶠ[𝓝 z] fun y => ψ' y / 2 := h.fun_comp (· / 2)
  exact (maDens_eq_topDens _ ψ z EventuallyEq.rfl).symm.trans (maDens_eq_topDens _ ψ' z h1)

theorem topDens_continuousOn {ψ : (Fin D → ℂ) → ℝ} (hΩ : IsOpen Ω) (hψ : ContDiffOn ℝ ∞ ψ Ω) :
    ContinuousOn (topDens ψ) Ω := by
  have e : topDens ψ = maDens (fun _ : Fin D => fun y => ψ y / 2) :=
    funext fun z => (maDens_eq_topDens _ ψ z EventuallyEq.rfl).symm
  rw [e]
  exact maDens_continuousOn _ Ω hΩ fun _ => (hψ.div_const 2).of_le (WithTop.coe_le_coe.2 le_top)

def inclChart (hΩ : IsOpen Ω) [Nonempty Ω] : OpenPartialHomeomorph Ω (Fin D → ℂ) :=
  hΩ.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

theorem inclChart_source (hΩ : IsOpen Ω) [Nonempty Ω] : (inclChart hΩ).source = Set.univ := by
  simp [inclChart]

theorem inclChart_target (hΩ : IsOpen Ω) [Nonempty Ω] : (inclChart hΩ).target = Ω := by
  simp [inclChart]

theorem inclChart_symm (hΩ : IsOpen Ω) [Nonempty Ω] (y : Fin D → ℂ) (hy : y ∈ Ω) :
    (((inclChart hΩ).symm y : Ω) : Fin D → ℂ) = y := by
  have h := (inclChart hΩ).right_inv (by rw [inclChart_target]; exact hy)
  simpa [inclChart] using h

def oneChartAtlas (hΩ : IsOpen Ω) [Nonempty Ω] : FinHolAtlas D Ω where
  n := 1
  chart _ := inclChart hΩ
  cover x := ⟨⟨0, Nat.one_pos⟩, by rw [inclChart_source]; trivial⟩
  holo := by
    intro _ _ y hy
    have hyΩ : y ∈ Ω := by rw [← inclChart_target hΩ]; exact hy.1
    refine analyticAt_id.congr ?_
    filter_upwards [hΩ.mem_nhds hyΩ] with z hz
    exact ((inclChart hΩ).right_inv (by rw [inclChart_target]; exact hz)).symm

def j0 (hΩ : IsOpen Ω) [Nonempty Ω] : Fin (oneChartAtlas hΩ).n := ⟨0, Nat.one_pos⟩

theorem oneChartAtlas_index_eq (hΩ : IsOpen Ω) [Nonempty Ω] (j : Fin (oneChartAtlas hΩ).n) : j = j0 hΩ :=
  Fin.ext (by have h1 : j.val < 1 := j.isLt; show j.val = 0; omega)

theorem oneChartAtlas_smooth (hΩ : IsOpen Ω) [Nonempty Ω] {f : (Fin D → ℂ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) : (oneChartAtlas hΩ).Smooth (fun x : Ω => f x) := by
  intro j
  have hs : (inclChart hΩ).target ∩ (inclChart hΩ).symm ⁻¹' Set.univ = Ω := by
    simp [inclChart_target]
  show ContDiffOn ℝ ∞ ((fun x : Ω => f x) ∘ (inclChart hΩ).symm)
    ((inclChart hΩ).target ∩ (inclChart hΩ).symm ⁻¹' Set.univ)
  rw [hs]
  exact hf.congr fun y hy => by simp only [Function.comp_apply, inclChart_symm hΩ y hy]

theorem oneChartAtlas_mInt (hΩ : IsOpen Ω) [Nonempty Ω] (Φ : Fin D → LocPot Ω) (g : Ω → ℝ) :
    mInt (oneChartAtlas hΩ) Φ g =
      ∫ y in Ω, g ((inclChart hΩ).symm y) * locDens (oneChartAtlas hΩ) Φ (j0 hΩ) y := by
  have hne : Nonempty (ChartPartition (oneChartAtlas hΩ)) :=
    ⟨{ χ := fun _ _ => 1
       smooth := fun _ _ => contDiffOn_const
       nonneg := fun _ _ => zero_le_one
       tsupport_subset := fun _ => by
         show _ ⊆ (inclChart hΩ).source
         rw [inclChart_source]; exact Set.subset_univ _
       sum_eq_one := fun _ => by show ∑ _j : Fin 1, (1 : ℝ) = 1; simp }⟩
  rw [mInt, dif_pos hne, integralWith]
  have hχ : ∀ j x, hne.some.χ j x = 1 := by
    intro j x
    have h := hne.some.sum_eq_one x
    rwa [Finset.sum_eq_single j (fun b _ hb => absurd ((oneChartAtlas_index_eq hΩ b).trans (oneChartAtlas_index_eq hΩ j).symm) hb)
      (by simp)] at h
  have hterm : ∀ j : Fin (oneChartAtlas hΩ).n,
      (∫ y in ((oneChartAtlas hΩ).chart j).target,
        hne.some.χ j (((oneChartAtlas hΩ).chart j).symm y) * g (((oneChartAtlas hΩ).chart j).symm y) *
          locDens (oneChartAtlas hΩ) Φ j y) =
      ∫ y in Ω, g ((inclChart hΩ).symm y) * locDens (oneChartAtlas hΩ) Φ (j0 hΩ) y := by
    intro j
    rw [oneChartAtlas_index_eq hΩ j]
    simp only [hχ, one_mul]
    show (∫ y in (inclChart hΩ).target, _) = _
    rw [inclChart_target]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  exact one_smul _ _

theorem oneChartAtlas_locDens (hΩ : IsOpen Ω) [Nonempty Ω] (L : LocPot Ω) (ψ : (Fin D → ℂ) → ℝ)
    (hL : ∀ x x', L.φ x x' = ψ x' / 2) (y : Fin D → ℂ) (hy : y ∈ Ω) :
    locDens (oneChartAtlas hΩ) (fun _ => L) (j0 hΩ) y = topDens ψ y := by
  unfold locDens
  simp only [hL]
  apply maDens_eq_topDens
  filter_upwards [hΩ.mem_nhds hy] with z hz
  show ψ ((inclChart hΩ).symm z : Fin D → ℂ) / 2 = ψ z / 2
  rw [inclChart_symm hΩ z hz]

end MACompact

open MACompact in

theorem MACompact.of_manifold
    (hA : GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange.Statement) :
    MACompact.Statement := by
  rintro D Ω φ v ⟨hΩ, hφ, hv, hvc, hvΩ⟩
  rcases Ω.eq_empty_or_nonempty with rfl | hne
  · simp
  have : Nonempty Ω := hne.to_subtype
  set T := tsupport v with hT
  let P : LocPot Ω := LocPot.ofFun fun x => φ x / 2
  let w : Ω → ℝ := fun x => v x / 2
  let K : Set Ω := Subtype.val ⁻¹' T
  have hKc : IsCompact K := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.2 hvΩ]
    exact hvc
  have hwK : tsupport w ⊆ K := by
    refine closure_minimal ?_ ((isClosed_tsupport v).preimage continuous_subtype_val)
    intro x hx
    exact subset_tsupport v fun h0 => hx (by simp [w, h0])
  have hmain := hA (oneChartAtlas hΩ) P w K
    ⟨isPotential_ofFun _ _ (oneChartAtlas_smooth hΩ (hφ.div_const 2)),
      oneChartAtlas_smooth hΩ (hv.div_const 2),
      hKc.of_isClosed_subset (isClosed_tsupport w) hwK, hKc, hwK⟩
  rw [oneChartAtlas_mInt, oneChartAtlas_mInt] at hmain
  have hind : ∀ y ∈ Ω, K.indicator (1 : Ω → ℝ) ((inclChart hΩ).symm y) =
      T.indicator (1 : (Fin D → ℂ) → ℝ) y := by
    intro y hy
    have hm : (inclChart hΩ).symm y ∈ K ↔ y ∈ T := by
      show (((inclChart hΩ).symm y : Ω) : Fin D → ℂ) ∈ T ↔ y ∈ T
      rw [inclChart_symm hΩ y hy]
    by_cases h : y ∈ T
    · rw [Set.indicator_of_mem (hm.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (mt hm.1 h), Set.indicator_of_notMem h]
  have hL1 : Set.EqOn (fun y => K.indicator 1 ((inclChart hΩ).symm y) *
      locDens (oneChartAtlas hΩ) (fun _ => P + LocPot.ofFun w) (j0 hΩ) y)
      (T.indicator (topDens (φ + v))) Ω := by
    intro y hy
    simp only
    rw [hind y hy, oneChartAtlas_locDens hΩ _ (φ + v) (fun x x' => by
      show φ x' / 2 + v x' / 2 = (φ + v) x' / 2
      rw [Pi.add_apply, add_div]) y hy]
    by_cases h : y ∈ T <;> simp [h]
  have hL2 : Set.EqOn (fun y => K.indicator 1 ((inclChart hΩ).symm y) *
      locDens (oneChartAtlas hΩ) (fun _ => P) (j0 hΩ) y) (T.indicator (topDens φ)) Ω := by
    intro y hy
    simp only
    rw [hind y hy, oneChartAtlas_locDens hΩ _ φ (fun x x' => rfl) y hy]
    by_cases h : y ∈ T <;> simp [h]
  rw [setIntegral_congr_fun hΩ.measurableSet hL1, setIntegral_congr_fun hΩ.measurableSet hL2]
    at hmain
  have hint : ∀ ψ : (Fin D → ℂ) → ℝ, ContDiffOn ℝ ∞ ψ Ω →
      IntegrableOn (T.indicator (topDens ψ)) Ω := fun ψ hψ =>
    (((topDens_continuousOn hΩ hψ).mono hvΩ).integrableOn_compact hvc).integrable_indicator
      (isClosed_tsupport v).measurableSet |>.integrableOn
  have heq : Set.EqOn (fun z => topDens (φ + v) z - topDens φ z)
      (fun z => T.indicator (topDens (φ + v)) z - T.indicator (topDens φ) z) Ω := by
    intro z _
    by_cases hz : z ∈ T
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, sub_zero, sub_eq_zero]
      exact topDens_congr ((notMem_tsupport_iff_eventuallyEq.1 hz).mono fun y hy => by
        simp only [Pi.add_apply, hy, Pi.zero_apply, add_zero])
  rw [setIntegral_congr_fun hΩ.measurableSet heq, integral_sub (hint (φ + v) (hφ.add hv)) (hint φ hφ),
    hmain, sub_self]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

def openAtlas {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    FinHolAtlas D Ω where
  n := 1
  chart _ := Ω.openPartialHomeomorphSubtypeCoe hΩ
  cover _ := ⟨0, by simp⟩
  holo _ _ := by
    intro y hy
    have hy' : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target := hy.1
    have hev : (Ω.openPartialHomeomorphSubtypeCoe hΩ ∘ (Ω.openPartialHomeomorphSubtypeCoe hΩ).symm)
        =ᶠ[𝓝 y] id := by
      filter_upwards [(Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target.mem_nhds hy'] with z hz
      exact (Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hz
    exact analyticAt_id.congr hev.symm

theorem openAtlas_symm_eventuallyEq {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ))
    (hΩ : Nonempty Ω) (j : Fin (openAtlas Ω hΩ).n) (F : (Fin D → ℂ) → ℝ) {y : Fin D → ℂ}
    (hy : y ∈ Ω) :
    (fun z => F (((openAtlas Ω hΩ).chart j).symm z : Fin D → ℂ)) =ᶠ[𝓝 y] F := by
  have hy' : y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target := by simpa using hy
  filter_upwards [(Ω.openPartialHomeomorphSubtypeCoe hΩ).open_target.mem_nhds hy'] with z hz
  have h := (Ω.openPartialHomeomorphSubtypeCoe hΩ).right_inv hz
  simp only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_coe] at h
  change F ((Ω.openPartialHomeomorphSubtypeCoe hΩ).symm z : Fin D → ℂ) = F z
  rw [h]

def openAtlasPartition {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    ChartPartition (openAtlas Ω hΩ) where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := by
    change _ ⊆ (Ω.openPartialHomeomorphSubtypeCoe hΩ).source
    simp
  sum_eq_one _ := by
    change ∑ _ : Fin 1, (1 : ℝ) = 1
    simp

instance {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω) :
    Subsingleton (Fin (openAtlas Ω hΩ).n) :=
  (inferInstance : Subsingleton (Fin 1))

theorem openAtlas_mass {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (Q : LocPot Ω) (F : (Fin D → ℂ) → ℝ) (hQ : ∀ x z, Q.φ x z = F z / 2) :
    maMeasure (openAtlas Ω hΩ) (fun _ => Q) Set.univ =
      ∫⁻ z in (Ω : Set (Fin D → ℂ)), ENNReal.ofReal (topDens F z) := by
  have hne : Nonempty (ChartPartition (openAtlas Ω hΩ)) := ⟨openAtlasPartition Ω hΩ⟩
  let j : Fin (openAtlas Ω hΩ).n := ⟨0, Nat.one_pos⟩
  have hχ : ∀ x, hne.some.χ j x = 1 := by
    intro x
    have h := hne.some.sum_eq_one x
    rwa [Fintype.sum_subsingleton _ j] at h
  have hT : ((openAtlas Ω hΩ).chart j).target = (Ω : Set (Fin D → ℂ)) := by
    change (Ω.openPartialHomeomorphSubtypeCoe hΩ).target = _
    simp
  have hmeas : AEMeasurable ((openAtlas Ω hΩ).chart j).symm
      (volume.restrict ((openAtlas Ω hΩ).chart j).target) :=
    ((openAtlas Ω hΩ).chart j).continuousOn_symm.aemeasurable
      ((openAtlas Ω hΩ).chart j).open_target.measurableSet
  rw [maMeasure, dif_pos hne, Measure.finsetSum_apply, Fintype.sum_subsingleton _ j,
    Measure.map_apply_of_aemeasurable (hmeas.mono_ac (withDensity_absolutelyContinuous _ _))
      MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hT]
  refine setLIntegral_congr_fun Ω.isOpen.measurableSet fun y hy => ?_
  rw [hχ, one_mul]
  congr 1
  have hev : (fun z => Q.φ (((openAtlas Ω hΩ).chart j).symm y)
      (((openAtlas Ω hΩ).chart j).symm z)) =ᶠ[𝓝 y] fun z => F z / 2 := by
    filter_upwards [openAtlas_symm_eventuallyEq Ω hΩ j F hy] with z hz
    rw [hQ, hz]
  have hH := (hev.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  unfold locDens topDens maDens maDensity mdisc mixedDisc hessC cxHessian
  simp only [hH]

theorem openAtlas_smooth {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (F : (Fin D → ℂ) → ℝ) (hF : ContDiffOn ℝ ∞ F Ω) :
    (openAtlas Ω hΩ).Smooth fun x => F x := by
  intro j
  have hsub : ((openAtlas Ω hΩ).chart j).target ∩ ((openAtlas Ω hΩ).chart j).symm ⁻¹' Set.univ ⊆
      (Ω : Set (Fin D → ℂ)) := by
    intro y hy
    have h := hy.1
    change y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target at h
    simpa using h
  exact (hF.mono hsub).congr fun y hy =>
    (openAtlas_symm_eventuallyEq Ω hΩ j F (hsub hy)).eq_of_nhds

theorem openAtlas_isPsh {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (Q : LocPot Ω) (F : (Fin D → ℂ) → ℝ) (hQ : ∀ x z, Q.φ x z = F z / 2)
    (hF : ContDiffOn ℝ ∞ F Ω) (hL : ∀ z ∈ (Ω : Set (Fin D → ℂ)), ∀ w, 0 ≤ leviForm F z w) :
    IsPsh (openAtlas Ω hΩ) Q := by
  intro x j y hy w
  have hyΩ : y ∈ (Ω : Set (Fin D → ℂ)) := by
    have h := hy.1
    change y ∈ (Ω.openPartialHomeomorphSubtypeCoe hΩ).target at h
    simpa using h
  have hev : (Q.φ x ∘ ((openAtlas Ω hΩ).chart j).symm) =ᶠ[𝓝 y]
      fun z => (fun _ => (0 : ℝ)) z + (1 / 2 : ℝ) * F z := by
    filter_upwards [openAtlas_symm_eventuallyEq Ω hΩ j F hyΩ] with z hz
    simp only [Function.comp_apply, hQ, hz]
    ring
  have hC : ContDiffAt ℝ 2 F y :=
    (hF.contDiffAt (Ω.isOpen.mem_nhds hyΩ)).of_le (WithTop.coe_le_coe.2 le_top)
  rw [levi_congr hev, levi_add_smul (f := fun _ => (0 : ℝ)) (1 / 2) contDiffAt_const hC]
  have h0 : levi (fun _ : Fin D → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
  have h1 : levi F y w = leviForm F y w := rfl
  have h2 := hL y hyΩ w
  rw [h0, h1]
  linarith

theorem MAComparison.of_manifold :
    GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison.Statement → MAComparison.Statement := by
  intro hA D Ω φ a b hyp
  obtain ⟨hΩo, hφ, ha, hb, hpa, hpb, hK⟩ := hyp
  rcases Set.eq_empty_or_nonempty Ω with h0 | hne
  · simp [h0]
  let U : TopologicalSpace.Opens (Fin D → ℂ) := ⟨Ω, hΩo⟩
  have hU : Nonempty U := hne.to_subtype
  let P : LocPot U := LocPot.ofFun fun x => φ x / 2
  have hsum : ∀ c : (Fin D → ℂ) → ℝ, ∀ x z,
      (P + LocPot.ofFun fun x : U => c x / 2).φ x z = (φ + c) z / 2 := by
    intro c x z
    change φ z / 2 + c z / 2 = _
    rw [Pi.add_apply, add_div]
  have key := hA (openAtlas U hU) P (fun x => a x / 2) (fun x => b x / 2)
    ⟨isPotential_ofFun _ _ (openAtlas_smooth U hU (fun z => φ z / 2) (hφ.div_const 2)),
     openAtlas_smooth U hU (fun z => a z / 2) (ha.div_const 2),
     openAtlas_smooth U hU (fun z => b z / 2) (hb.div_const 2),
     openAtlas_isPsh U hU _ (φ + a) (hsum a) (hφ.add ha) hpa,
     openAtlas_isPsh U hU _ (φ + b) (hsum b) (hφ.add hb) hpb, fun k => ?_⟩
  · rw [openAtlas_mass U hU _ _ (hsum b), openAtlas_mass U hU _ _ (hsum a)] at key
    exact key
  · rw [Subtype.isCompact_iff]
    convert hK (2 * k) using 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq] at hx
      exact ⟨x.2, by linarith⟩
    · rintro ⟨hz, h⟩
      exact ⟨⟨z, hz⟩, by simp only [Set.mem_ofPred_eq]; linarith, rfl⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def CoverMass2.Hyp {D : ℕ} (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ) :
    Prop :=
  IsOpen M ∧ volume Z = 0 ∧ DifferentiableOn ℂ z M ∧ Set.MapsTo z M Zᶜ ∧
    IsCoveringMapOn (fun x : M => z x) Zᶜ ∧ ∀ w ∉ Z, Set.encard {x | x ∈ M ∧ z x = w} = δ

def CoverMass2.Statement : Prop :=
  ∀ (D : ℕ) (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ),
    CoverMass2.Hyp M Z z δ →
      ∫⁻ x in M, ENNReal.ofReal (topDens (fun y => Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) x) = δ

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.FourB

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

namespace OpenSetChart

variable {D : ℕ} {M : Set (Fin D → ℂ)}

open scoped Classical in

def retract (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (y : Fin D → ℂ) : M :=
  ⟨if y ∈ M then y else x₀, by split_ifs with h; exacts [h, hx₀]⟩

theorem retract_of_mem {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ} (hy : y ∈ M) :
    (retract x₀ hx₀ y : Fin D → ℂ) = y := by
  simp [retract, hy]

theorem measurable_retract (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) :
    Measurable (retract x₀ hx₀) := by
  classical
  unfold retract
  exact (Measurable.ite hM.measurableSet measurable_id measurable_const).subtype_mk

def chart (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : OpenPartialHomeomorph M (Fin D → ℂ) where
  toFun := Subtype.val
  invFun := retract x₀ hx₀
  source := Set.univ
  target := M
  map_source' x _ := x.2
  map_target' _ _ := Set.mem_univ _
  left_inv' x _ := Subtype.ext (retract_of_mem hx₀ x.2)
  right_inv' _ hy := retract_of_mem hx₀ hy
  open_source := isOpen_univ
  open_target := hM
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert (continuous_id : Continuous (id : M → M)) using 1
    funext y
    exact Subtype.ext (retract_of_mem hx₀ y.2)

theorem eventuallyEq_retract (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ}
    (hy : y ∈ M) : (fun y' => (retract x₀ hx₀ y' : Fin D → ℂ)) =ᶠ[𝓝 y] id :=
  Filter.eventually_of_mem (hM.mem_nhds hy) fun _ hy' => retract_of_mem hx₀ hy'

def atlas (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : FinHolAtlas D M where
  n := 1
  chart _ := chart hM x₀ hx₀
  cover _ := ⟨0, Set.mem_univ _⟩
  holo _ _ := fun _ hy => analyticAt_id.congr (eventuallyEq_retract hM hx₀ hy.1).symm

def partition (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) :
    ChartPartition (atlas hM x₀ hx₀) where
  χ _ _ := 1
  smooth _ := fun _ => contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun _ _ => Set.mem_univ _
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp

theorem maMeasure_univ (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (u : M → ℝ) :
    maMeasure (atlas hM x₀ hx₀) (fun _ => LocPot.ofFun u) Set.univ =
      ∫⁻ y in M, ENNReal.ofReal (maDens (fun _ y' => u (retract x₀ hx₀ y')) y) := by
  have hne : Nonempty (ChartPartition (atlas hM x₀ hx₀)) := ⟨partition hM x₀ hx₀⟩
  have : Subsingleton (Fin (atlas hM x₀ hx₀).n) := (inferInstance : Subsingleton (Fin 1))
  have hχ : ∀ j x, hne.some.χ j x = 1 := by
    intro j x
    have h := hne.some.sum_eq_one x
    rwa [Fintype.sum_subsingleton _ j] at h
  let j0 : Fin (atlas hM x₀ hx₀).n := ⟨0, Nat.zero_lt_one⟩
  have ht : ((atlas hM x₀ hx₀).chart j0).target = M := rfl
  have hm : Measurable ((atlas hM x₀ hx₀).chart j0).symm := measurable_retract hM hx₀
  rw [maMeasure, dif_pos hne, Fintype.sum_subsingleton _ j0,
    Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ht]
  refine lintegral_congr fun y => ?_
  rw [hχ, one_mul]
  rfl

end OpenSetChart

open OpenSetChart

theorem maDens_congr_germ' {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  have hH : ∀ i, hessC (φ i) y = hessC (ψ i) y := by
    intro i
    have h1 : fderiv ℝ (φ i) =ᶠ[𝓝 y] fderiv ℝ (ψ i) := (h i).fderiv
    unfold hessC
    rw [h1.fderiv_eq]
  unfold maDens
  simp only [hH]

theorem CoverMass2.of_fubiniStudyCoverMass (hA : FubiniStudyCoverMass.Statement) :
    IndefiniteRowSideFullHecke.FourB.CoverMass2.Statement := by
  intro D M Z z δ hB
  obtain ⟨hM, hZ, hz, hmaps, hcov, hfib⟩ := hB
  rcases M.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hZc : Zᶜ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      rw [h, Measure.measure_univ_eq_zero] at hZ
      exact NeZero.ne (volume : Measure (Fin D → ℂ)) hZ
    obtain ⟨w, hw⟩ := hZc
    have h1 := hfib w hw
    have h0 : {x | x ∈ (∅ : Set (Fin D → ℂ)) ∧ z x = w} = ∅ := by simp
    rw [h0, Set.encard_empty] at h1
    have hδ : δ = 0 := by exact_mod_cast h1.symm
    subst hδ
    simp
  ·
    have hδ : δ ≠ 0 := by
      intro h0
      have h1 := hfib (z x₀) (hmaps hx₀)
      have hmem : x₀ ∈ {x | x ∈ M ∧ z x = z x₀} := ⟨hx₀, rfl⟩
      rw [h0, Nat.cast_zero, Set.encard_eq_zero] at h1
      rw [h1] at hmem
      exact hmem

    have hZcl : IsClosed Z := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro w hw
      obtain ⟨-, U, hwU, hU, -, H, hH⟩ := hcov w hw
      obtain ⟨x, hxM, hxw⟩ : {x | x ∈ M ∧ z x = w}.Nonempty := by
        rw [← Set.encard_pos, hfib w hw]
        exact_mod_cast Nat.pos_of_ne_zero hδ
      let i : (fun x : M => z x) ⁻¹' {w} := ⟨⟨x, hxM⟩, hxw⟩
      refine ⟨U, fun v hv => ?_, hU, hwU⟩
      have h1 : v = z (H.symm (⟨v, hv⟩, i)).1 := by
        simpa using hH (H.symm (⟨v, hv⟩, i))
      rw [h1]
      exact hmaps (H.symm (⟨v, hv⟩, i)).1.2

    have han : ∀ i, AnalyticOnNhd ℂ (fun y => z y i) M := fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood D M _ hM (differentiableOn_pi.1 hz i)
    let A := atlas hM x₀ hx₀
    let q : M → Fin D → ℂ := fun x => z x
    let u : M → ℝ := fun x => (1 / 2) * Real.log (1 + ∑ i, ‖q x i‖ ^ 2)
    have hsm : ContDiffOn ℝ ∞ (fun y => (1 / 2) * Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) M := by
      refine contDiffOn_const.mul (ContDiffOn.log (contDiffOn_const.add (ContDiffOn.sum
        fun i _ => (contDiff_norm_sq ℝ).comp_contDiffOn
          (((han i).contDiffOn hM.uniqueDiffOn).restrict_scalars ℝ))) fun y _ => ?_)
      positivity
    have hu : A.Smooth u := by
      intro j
      refine (hsm.mono Set.inter_subset_left).congr fun y hy => ?_
      show u (retract x₀ hx₀ y) = _
      simp only [u, q, retract_of_mem hx₀ hy.1]
    have hHyp : FubiniStudyCoverMass.Hyp A (LocPot.ofFun u) q Set.univ Z δ := by
      refine ⟨isPotential_ofFun A u hu, isOpen_univ, ?_, ?_, ?_, hZcl, hZ,
        ⟨fun x _ => hmaps x.2, ?_⟩, ?_, ?_⟩
      · intro x
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, fun _ _ => 1,
          fun _ _ => analyticOnNhd_const, ?_⟩
        ext y
        simp
      · simp
      · intro i j y hy
        exact ((han i) y hy.1).congr
          (((eventuallyEq_retract hM hx₀ hy.1).fun_comp fun y' => z y' i).symm)
      · have hpre : (Set.univ : Set M) = (fun x : M => z x) ⁻¹' Zᶜ := by
          ext x
          simpa using hmaps x.2
        exact hcov.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr hpre)
      · intro w hw
        rw [← hfib w hw, ← Subtype.val_injective.encard_image]
        congr 1
        ext y
        simp [q, and_comm]
      · intro x y _
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, fun _ _ _ => analyticAt_const, ?_⟩
        intro v _
        simp [LocPot.ofFun, u]
    have key := (hA A (LocPot.ofFun u) q Set.univ Z δ hHyp).2
    rw [maMeasure_univ] at key
    rw [← key]
    refine setLIntegral_congr_fun hM.measurableSet fun y hy => ?_
    show ENNReal.ofReal (maDens _ y) = ENNReal.ofReal (maDens _ y)
    congr 1
    refine maDens_congr_germ' fun _ => ?_
    filter_upwards [hM.mem_nhds hy] with y' hy'
    simp only [u, q, retract_of_mem hx₀ hy']
    ring

end GroundTheory.Heights₂.Heights.FourB
end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

theorem FlagWeightLevi.full : FlagWeightLevi.Statement :=
  FlagWeightLevi.proof

theorem FlagRootProduct.full : FlagRootProduct.Statement :=
  FlagRootProduct.proof

theorem DegreeRatio.full : DegreeRatio.Statement :=
  DegreeRatio.proof

theorem RhoBound.full : RhoBound.Statement :=
  RhoBound.proof DegreeRatio.full

theorem HermitianDetMono.full : HermitianDetMono.Statement :=
  HermitianDetMono.proof

theorem MongeAmpereCompactChange.full : MongeAmpereCompactChange.Statement :=
  MongeAmpereCompactChange.proof

theorem MongeAmpereComparison.full : MongeAmpereComparison.Statement :=
  MongeAmpereComparison.proof MongeAmpereCompactChange.full

theorem FubiniStudyCoverMass.of_open (hFS : FubiniStudyChartDensity.Statement)
    (hPart : ChartPartitionExists.Statement) (hCov : CoverChartLIntegral.Statement) :
    FubiniStudyCoverMass.Statement :=
  FubiniStudyCoverMass.proof hFS hPart hCov

theorem CoverMass2.of_open (hFS : FubiniStudyChartDensity.Statement)
    (hPart : ChartPartitionExists.Statement) (hCov : CoverChartLIntegral.Statement) :
    IndefiniteRowSideFullHecke.FourB.CoverMass2.Statement :=
  CoverMass2.of_fubiniStudyCoverMass (FubiniStudyCoverMass.proof hFS hPart hCov)

theorem IntegralOnModel.of_open (h₁ : ClosedPointOfGenericFibre.Statement)
    (h₂ : IntegralPointOfAlgebraicDomain.Statement) : IntegralOnModel.Statement :=
  IntegralOnModel.proof (IntegralPointThroughPrime.proof h₁ h₂)

end GroundTheory.Heights₂.Heights.FourB

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

theorem KrullHeightOne.full : KrullHeightOne.Statement :=
  KrullHeightOne.proof

theorem DetMono.full : DetMono.Statement :=
  GroundTheory.Heights₂.Heights.DetMono.equiv.mp _root_.GroundTheory.Heights₂.Heights.FourB.HermitianDetMono.full

theorem MACompact.full : MACompact.Statement :=
  MACompact.of_manifold _root_.GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange.full

theorem MAComparison.full : MAComparison.Statement :=
  MAComparison.of_manifold _root_.GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison.full

theorem RiemannExt.of_open (hZ : ZariskiDense.Statement) : RiemannExt.Statement :=
  RiemannExt.proof KrullHeightOne.full hZ

theorem Normality.of_open
    (h₁ : _root_.GroundTheory.Heights₂.Heights.FourB.ClosedPointOfGenericFibre.Statement)
    (h₂ : _root_.GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain.Statement) :
    Normality.Statement :=
  Normality.of_integralOnModel (_root_.GroundTheory.Heights₂.Heights.FourB.IntegralOnModel.of_open h₁ h₂)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
