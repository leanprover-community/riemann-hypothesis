import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneRegularSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω}

omit [Fintype K] in

theorem shift_succ_sub_one (b : K → ℤ) (j : ℕ) :
    (b + fun _ => ((j + 1 : ℕ) : ℤ)) - 1 = b + fun _ => (j : ℤ) := by
  funext k
  simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply]
  push_cast
  ring

omit [∀ k, Fintype (ι k)] in

theorem pow_mul_mem_chartLatQ (c : ∀ k, ι k) (b : K → ℤ) {s : Ω} (hs : s ∈ chartLatQ y b 1) (j : ℕ) :
    (∏ k, y ⟨k, c k⟩) ^ j * s ∈ chartLatQ y (b + fun _ => (j : ℤ)) 1 := by
  induction j with
  | zero =>
    rw [pow_zero, one_mul]
    convert hs using 2
    funext k
    simp
  | succ j ih =>
    rw [← shift_succ_sub_one] at ih
    have h := mul_mem_chartLatQ (c := c) (b + fun _ => ((j + 1 : ℕ) : ℤ)) ih
    rwa [← mul_assoc, ← pow_succ'] at h

theorem finiteDimensional_chartLatQ (hfin : SectionLatticeFinite.Statement) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (b : K → ℤ) : FiniteDimensional ℚ (chartLatQ y b 1) := by
  obtain ⟨S, hS⟩ := hfin K ι Ω y b 1 hy
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ (S : Set Ω)) fun s hs => ?_
  obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y b 1 s hs
  rw [← hS] at hNs
  have hZ : (N : Ω) * s ∈ Submodule.span ℤ (S : Set Ω) :=
    (AddSubgroup.closure_le (K := (Submodule.span ℤ (S : Set Ω)).toAddSubgroup)).mpr
      Submodule.subset_span hNs
  have hQ : (N : Ω) * s ∈ Submodule.span ℚ (S : Set Ω) := Submodule.span_le_restrictScalars ℤ ℚ _ hZ
  have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
    rw [Rat.smul_def]
    push_cast
    field_simp
  rw [hs']
  exact Submodule.smul_mem _ _ hQ

theorem finrank_shift_le (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) (j : ℕ) :
    Module.finrank ℚ (chartLatQ y (b + fun _ => (j : ℤ)) 1) ≤ Module.finrank ℚ (chartLatQ y b 1) +
      ∑ i ∈ Finset.range j, Module.finrank ℚ (chartLatQ y (b + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
        chartDivSec y c (b + fun _ => ((i + 1 : ℕ) : ℤ))) := by
  induction j with
  | zero =>
    have h0 : (b + fun _ => ((0 : ℕ) : ℤ)) = b := by funext k; simp
    rw [h0]
    simp
  | succ j ih =>
    have h := finrank_chartLatQ_le hc (b + fun _ => ((j + 1 : ℕ) : ℤ))
    rw [shift_succ_sub_one] at h
    rw [Finset.sum_range_succ]
    omega

end Shift

theorem ShiftSectionBound.proof (hfin : SectionLatticeFinite.Statement) (hQ : ShiftQuotientBound.Statement) :
    ShiftSectionBound.Statement := by
  intro K _ ι _ Ω _ _ y D a m hD hV hB
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  choose c hc using hy
  have hC := fun i : ℕ => hQ K ι Ω y D a (fun _ => ((i + 1 : ℕ) : ℤ)) c hD hV hB hc
  choose C hC using hC
  refine ⟨∑ i ∈ Finset.range m, C i,
    ((Filter.eventually_all_finset (Finset.range m)).mpr fun i _ => hC i).mono fun n hn => ⟨?_, ?_⟩⟩
  ·
    have := finiteDimensional_chartLatQ hfin (fun k => ⟨c k, hc k⟩) ((n : ℤ) • a + fun _ => (m : ℤ))
    have hh : (∏ k, y ⟨k, c k⟩) ^ m ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)
    let φ : chartLatQ y ((n : ℤ) • a) 1 →ₗ[ℚ] chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1 :=
      { toFun := fun s => ⟨(∏ k, y ⟨k, c k⟩) ^ m * s, pow_mul_mem_chartLatQ c _ s.2 m⟩
        map_add' := fun s t => Subtype.ext (mul_add _ _ _)
        map_smul' := fun r s => Subtype.ext (mul_smul_comm r _ (s : Ω)) }
    have hinj : Function.Injective φ := fun s t hst =>
      Subtype.ext (mul_left_cancel₀ hh (congrArg Subtype.val hst))
    exact_mod_cast LinearMap.finrank_le_finrank_of_injective hinj
  · have h := finrank_shift_le c hc ((n : ℤ) • a) m
    have h' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ≤
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) +
          ∑ i ∈ Finset.range m, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
            chartDivSec y c ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ))) : ℝ) := by
      exact_mod_cast h
    have hs : ∑ i ∈ Finset.range m, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
          chartDivSec y c ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ))) : ℝ) ≤
        (∑ i ∈ Finset.range m, C i) * (n : ℝ) ^ (D - 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => hn i hi
    linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Mul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}

omit [∀ k, Fintype (ι k)] in

theorem mul_mem_chartLatQ_add {B γ : K → ℤ} {g s : Ω} (hg : g ∈ chartLatQ y γ 1) (hs : s ∈ chartLatQ y B 1) :
    g * s ∈ chartLatQ y (B + γ) 1 := by
  intro c' hc'
  have hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (B + γ) k)) =
      y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * γ k)) * y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * B k)) := by
    intro k
    rw [← zpow_add₀ (hc' k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  have heq : g * s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (B + γ) k)) =
      (g * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * γ k))) * (s * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * B k))) := by
    simp only [hk, Finset.prod_mul_distrib]
    ring
  rw [heq]
  exact Subalgebra.mul_mem _ (hg c' hc') (hs c' hc')

theorem finrank_quot_le_of_regular {B γ : K → ℤ} {g : Ω} [FiniteDimensional ℚ (chartLatQ y (B + γ) 1)]
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hg : g ∈ chartLatQ y γ 1)
    (hreg : ∀ s : Ω, s ∈ chartLatQ y B 1 → g * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (B + γ - 1) 1 →
      s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (B - 1) 1) :
    Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) ≤
      Module.finrank ℚ (chartLatQ y (B + γ) 1 ⧸ chartDivSec y c (B + γ)) := by
  let φ : chartLatQ y B 1 →ₗ[ℚ] chartLatQ y (B + γ) 1 :=
    { toFun := fun s => ⟨g * s, mul_mem_chartLatQ_add hg s.2⟩
      map_add' := fun s t => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm r g (s : Ω)) }
  have hle : chartDivSec y c B ≤ (chartDivSec y c (B + γ)).comap φ := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hs)
    refine Submodule.mem_comap.mpr (Submodule.mem_comap.mpr (Submodule.mem_map.mpr
      ⟨g * t, ?_, ?_⟩))
    · have h := mul_mem_chartLatQ_add hg ht
      rwa [show B - 1 + γ = B + γ - 1 by abel] at h
    · change (∏ k, y ⟨k, c k⟩) * (g * t) = g * (s : Ω)
      have hts' : (∏ k, y ⟨k, c k⟩) * t = (s : Ω) := hts
      rw [← hts']
      ring
  refine LinearMap.finrank_le_finrank_of_injective (f := Submodule.mapQ _ _ φ hle) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.Quotient.mk_eq_zero]
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
  have hts' : (∏ k, y ⟨k, c k⟩) * t = g * (s : Ω) := hts
  have hu := hreg s s.2 (by rwa [← hts', mul_div_cancel_left₀ _ hm0])
  refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨_, hu, ?_⟩)
  change (∏ k, y ⟨k, c k⟩) * ((s : Ω) / ∏ k, y ⟨k, c k⟩) = (s : Ω)
  exact mul_div_cancel₀ _ hm0

end Mul

theorem ShiftQuotientBound.proof (hfin : SectionLatticeFinite.Statement) (hQ : HyperplaneQuotientBound.Statement)
    (hR : HyperplaneRegularSection.Statement) : ShiftQuotientBound.Statement := by
  intro K _ ι _ Ω _ _ y D a b c hD hV hB hc
  obtain ⟨C₀, hC₀⟩ := hQ K ι Ω y D (fun _ => 1) c hD hV hB hc
  set N : ℕ := 1 + ∑ k, (a k).natAbs with hN
  set M : ℕ := ∑ k, (b k).natAbs with hM
  have hN1 : 1 ≤ N := by omega
  have ht : Tendsto (fun n : ℕ => n * N + M) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; nlinarith [Nat.zero_le n, hN1]) tendsto_id
  refine ⟨|C₀| * ((N + M : ℕ) : ℝ) ^ (D - 1),
    ((ht.eventually hC₀).and (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_⟩
  set B : K → ℤ := (n : ℤ) • a + b with hBdef
  set γ : K → ℤ := (((n * N + M : ℕ) : ℤ) • fun _ => (1 : ℤ)) - B with hγdef
  have hγ : ∀ k, 0 ≤ γ k := by
    intro k
    have ha : (a k).natAbs ≤ ∑ j, (a j).natAbs :=
      Finset.single_le_sum (f := fun j => (a j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hb : (b k).natAbs ≤ ∑ j, (b j).natAbs :=
      Finset.single_le_sum (f := fun j => (b j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have ha' : a k < (N : ℤ) :=
      calc a k ≤ (a k).natAbs := Int.le_natAbs
        _ ≤ ((∑ j, (a j).natAbs : ℕ) : ℤ) := by exact_mod_cast ha
        _ < (N : ℤ) := by rw [hN]; exact_mod_cast (by omega : ∑ j, (a j).natAbs < 1 + ∑ j, (a j).natAbs)
    have hb' : b k ≤ (M : ℤ) :=
      calc b k ≤ (b k).natAbs := Int.le_natAbs
        _ ≤ (M : ℤ) := by rw [hM]; exact_mod_cast hb
    simp only [hγdef, hBdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ha'.le (Int.natCast_nonneg n)]
  obtain ⟨g, -, hg, hreg⟩ := hR K ι Ω y c (fun k => (γ k).toNat) hc
  have he : (fun k => ((γ k).toNat : ℤ)) = γ := funext fun k => Int.toNat_of_nonneg (hγ k)
  rw [he] at hg hreg
  have := finiteDimensional_chartLatQ hfin (fun k => ⟨c k, hc k⟩) (B + γ)
  have h1 := finrank_quot_le_of_regular hc hg (hreg B)
  rw [show B + γ = ((n * N + M : ℕ) : ℤ) • fun _ => (1 : ℤ) by rw [hγdef]; abel] at h1
  have h2 : (Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) : ℝ) ≤ C₀ * ((n * N + M : ℕ) : ℝ) ^ (D - 1) :=
    le_trans (by exact_mod_cast h1) hn
  have h3 : ((n * N + M : ℕ) : ℝ) ≤ ((N + M : ℕ) : ℝ) * (n : ℝ) := by
    have : n * N + M ≤ (N + M) * n := by nlinarith
    exact_mod_cast this
  calc (Module.finrank ℚ (chartLatQ y B 1 ⧸ chartDivSec y c B) : ℝ)
      ≤ |C₀| * ((n * N + M : ℕ) : ℝ) ^ (D - 1) :=
        h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    _ ≤ |C₀| * (((N + M : ℕ) : ℝ) * (n : ℝ)) ^ (D - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 _) (abs_nonneg _)
    _ = |C₀| * ((N + M : ℕ) : ℝ) ^ (D - 1) * (n : ℝ) ^ (D - 1) := by rw [mul_pow, mul_assoc]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
