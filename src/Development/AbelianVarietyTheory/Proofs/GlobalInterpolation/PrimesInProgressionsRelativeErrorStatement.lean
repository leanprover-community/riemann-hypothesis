import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExceptionalDirichletZeroUniqueZeroFreeRegion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogFreeZeroDensityDirichletOneModulus
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Repulsion
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaClosed
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLZerosEqPrimitiveCharacterZeros
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDirichletLFunctionZeroGapNearOne
import BuildAid.ForwardExisting

section
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.ZeroSum

theorem mem_disc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {T : ℝ} {ρ : ℂ}
    (h : ρ ∈ zerosBox χ (1 / 2) T) :
    ⌊ρ.im⌋ ∈ Finset.Icc (-⌈T⌉) ⌈T⌉ ∧ ρ ∈ zerosDisc χ (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I) 3 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [abs_le] at h3
  have a1 := Int.floor_le ρ.im
  have a2 := Int.lt_floor_add_one ρ.im
  have a3 := Int.le_ceil T
  refine ⟨?_, ?_, Or.inr ?_, h4⟩
  · rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast; linarith
    · have : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ (⌈T⌉ : ℤ) := by linarith
      exact_mod_cast this
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have b1 : |(ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).re| ≤ 2 := by
      rw [abs_le]; simp; constructor <;> linarith
    have b2 : |(ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).im| ≤ 1 := by
      have : (ρ - (2 + ((⌊ρ.im⌋ : ℝ) : ℂ) * I)).im = ρ.im - ⌊ρ.im⌋ := by simp
      rw [this, abs_le]; constructor <;> linarith
    linarith
  · rintro rfl
    simp at h2

theorem total_count : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ),
    2 ≤ T → ∃ h : (zerosBox χ (1 / 2) T).Finite,
      ∑ ρ ∈ h.toFinset, (ord χ ρ : ℝ) ≤ C * (q * T ^ 2) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.T.iteratedDeriv_logDeriv_dirichletL_via_nearby_zeros
  refine ⟨12 * C, by positivity, fun q _ χ T hT => ?_⟩
  have hf : ∀ n : ℤ, (zerosDisc χ (2 + ((n : ℝ) : ℂ) * I) 3).Finite :=
    fun n => (H q χ 2 n 0 (by norm_num) le_rfl).1
  have hfin : (zerosBox χ (1 / 2) T).Finite := by
    refine ((Finset.Icc (-⌈T⌉) ⌈T⌉).finite_toSet.biUnion (fun n _ => hf n)).subset ?_
    intro ρ hρ
    simp only [Set.mem_iUnion]
    exact ⟨_, (mem_disc χ hρ).1, (mem_disc χ hρ).2⟩
  refine ⟨hfin, ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have a3 := Int.ceil_lt_add_one T
  have a4 := Int.le_ceil T
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc (-⌈T⌉) ⌈T⌉) (g := fun ρ : ℂ => ⌊ρ.im⌋)
    (fun ρ hρ => (mem_disc χ (hfin.mem_toFinset.1 hρ)).1)]
  have key : ∀ n ∈ Finset.Icc (-⌈T⌉) ⌈T⌉,
      ∑ ρ ∈ hfin.toFinset with ⌊ρ.im⌋ = n, (ord χ ρ : ℝ) ≤ C * (q * (3 * T)) := by
    intro n hn
    have h2 := (H q χ 2 n 0 (by norm_num) le_rfl).2.1
    rw [finsum_mem_eq_finite_toFinset_sum _ (hf n)] at h2
    have hn' : |(n : ℝ)| ≤ T + 1 := by
      rw [Finset.mem_Icc] at hn
      have c1 : ((-⌈T⌉ : ℤ) : ℝ) ≤ n := by exact_mod_cast hn.1
      have c2 : (n : ℝ) ≤ (⌈T⌉ : ℤ) := by exact_mod_cast hn.2
      push_cast at c1
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ ∑ ρ ∈ (hf n).toFinset, (ord χ ρ : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
          intro ρ hρ
          rw [Finset.mem_filter] at hρ
          rw [Set.Finite.mem_toFinset, ← hρ.2]
          exact (mem_disc χ (hfin.mem_toFinset.1 hρ.1)).2
      _ ≤ _ := h2
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hC.le
          refine (Real.log_le_self (by positivity)).trans ?_
          refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  refine (Finset.sum_le_card_nsmul _ _ _ key).trans ?_
  rw [nsmul_eq_mul]
  have hc : ((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℝ) ≤ 4 * T := by
    have h0 : (0 : ℤ) ≤ ⌈T⌉ + 1 - -⌈T⌉ := by
      have : (0 : ℤ) ≤ ⌈T⌉ := Int.ceil_nonneg (by linarith)
      omega
    have : (((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℤ) : ℝ) = ((⌈T⌉ + 1 - -⌈T⌉ : ℤ) : ℝ) := by
      rw [Int.card_Icc, Int.toNat_of_nonneg h0]
    push_cast at this
    rw [this]; linarith
  calc _ ≤ (4 * T) * (C * (q * (3 * T))) := by gcongr
    _ = _ := by ring

theorem layers {ι : Type*} (s : Finset ι) (w δ : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {L η e : ℝ}
    (hL : 0 < L) (J : ℕ) (hJ : L * e < J) (hη : 0 ≤ η) :
    ∑ i ∈ s with η ≤ δ i, w i * Real.exp (-(L * δ i)) ≤
      ∑ j ∈ Finset.range J, Real.exp (-(L * η) - j) *
        (∑ i ∈ s with δ i ≤ min (η + (j + 1) / L) e, w i) + Real.exp (-(L * e)) * ∑ i ∈ s, w i := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hwi := hw i
  have hnn : ∀ j ∈ Finset.range J, 0 ≤ Real.exp (-(L * η) - j) *
      (if δ i ≤ min (η + (j + 1) / L) e then w i else 0) := by
    intro j _
    split_ifs <;> positivity
  have hs := Finset.sum_nonneg hnn
  have he : 0 ≤ Real.exp (-(L * e)) * w i := by positivity
  split_ifs with h
  · by_cases h2 : δ i ≤ e
    · have h0 : 0 ≤ L * (δ i - η) := mul_nonneg hL.le (by linarith)
      have a1 := Nat.floor_le h0
      have a2 := Nat.lt_floor_add_one (L * (δ i - η))
      have hm : ⌊L * (δ i - η)⌋₊ ∈ Finset.range J := by
        rw [Finset.mem_range, Nat.floor_lt h0]
        nlinarith
      have := Finset.single_le_sum hnn hm
      rw [if_pos] at this
      · have h3 : Real.exp (-(L * δ i)) ≤ Real.exp (-(L * η) - ⌊L * (δ i - η)⌋₊) :=
          Real.exp_le_exp.2 (by linarith)
        nlinarith
      · refine le_min ?_ h2
        have : δ i - η ≤ (⌊L * (δ i - η)⌋₊ + 1) / L := by
          rw [le_div_iff₀ hL]; linarith
        linarith
    · have h3 : Real.exp (-(L * δ i)) ≤ Real.exp (-(L * e)) :=
        Real.exp_le_exp.2 (by nlinarith)
      nlinarith
  · linarith

theorem sum_rpow_zeros_le : ∃ A C η₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < η₀ ∧ ∀ (q : ℕ) [NeZero q] (T u η : ℝ), 2 ≤ T → ((q : ℝ) * T) ^ A ≤ u → 0 ≤ η → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤ C * (u ^ (-η / 2) + u ^ (-η₀)) := by
  obtain ⟨A₁, C₁, η₁, hA₁, hC₁, hη₁, H₁⟩ := GlobalTheory.T.logFree_zeroDensity_dirichlet_one_modulus
  obtain ⟨C₂, hC₂, H₂⟩ := total_count
  obtain ⟨e, he0, he1, he2⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ η₁ ∧ e ≤ 1 / 2 :=
    ⟨min η₁ (1 / 2), by positivity, min_le_left _ _, min_le_right _ _⟩
  have hr : Real.exp (-1 / 2) < 1 := by
    simpa using Real.exp_lt_exp.2 (show (-1 / 2 : ℝ) < 0 by norm_num)
  have hsum := summable_geometric_of_lt_one (Real.exp_pos (-1 / 2)).le hr
  set K := ∑' j : ℕ, Real.exp (-1 / 2) ^ j with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => by positivity
  refine ⟨2 * A₁ + 4 / e, C₁ * Real.exp (1 / 2) * K + C₂, e / 2, by positivity, by positivity,
    by positivity, fun q _ T u η hT hu hη => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hqT : (1 : ℝ) < q * T := by nlinarith
  have hu1 : 1 < u := (Real.one_lt_rpow hqT (by positivity)).trans_le hu
  have hu0 : 0 < u := by linarith
  have hL : 0 < Real.log u := Real.log_pos hu1
  have hM : 0 < Real.log (q * T) := Real.log_pos hqT
  have hLM : (2 * A₁ + 4 / e) * Real.log (q * T) ≤ Real.log u := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log (by positivity) hu
  set L := Real.log u with hLdef
  set M := Real.log (q * T) with hMdef
  have h4 : 0 < 4 / e := by positivity
  have hLM1 : 2 * A₁ * M ≤ L := by nlinarith
  have hLM2 : 4 * M ≤ e * L := by
    have : 4 / e * M ≤ L := by nlinarith [mul_pos hA₁ hM]
    rw [div_mul_eq_mul_div, div_le_iff₀ he0] at this
    linarith
  choose hfin hcount using fun χ : DirichletCharacter ℂ q => H₂ q χ T hT
  obtain ⟨J, hJ⟩ := exists_nat_gt (L * e)
  have step1 : ∀ χ : DirichletCharacter ℂ q,
      (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤
      ∑ j ∈ Finset.range J, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) +
        Real.exp (-(L * e)) * (C₂ * (q * T ^ 2)) := by
    intro χ
    have h := layers (hfin χ).toFinset (fun ρ => (ord χ ρ : ℝ)) (fun ρ => 1 - ρ.re)
      (fun _ => Nat.cast_nonneg _) hL J hJ hη
    have e1 : zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η} =
        ((hfin χ).toFinset.filter (fun ρ : ℂ => η ≤ 1 - ρ.re) : Finset ℂ) := by
      ext ρ
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
      exact and_congr_right fun _ => ⟨fun _ => by linarith, fun _ => by linarith⟩
    have e2 : ∀ x : ℝ, x ≤ e → zerosBox χ (1 - x) T =
        ((hfin χ).toFinset.filter (fun ρ : ℂ => 1 - ρ.re ≤ x) : Finset ℂ) := by
      intro x hx
      ext ρ
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, zerosBox]
      constructor
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨by linarith, b, c, d⟩, by linarith⟩
      · rintro ⟨⟨a, b, c, d⟩, f⟩
        exact ⟨by linarith, b, c, d⟩
    rw [e1, finsum_mem_coe_finset]
    calc _ = _ := by
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [Real.rpow_def_of_pos hu0, show Real.log u * (ρ.re - 1) = -(L * (1 - ρ.re)) by ring]
      _ ≤ _ := h
      _ ≤ _ := by
          refine add_le_add (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
            (mul_le_mul_of_nonneg_left (hcount χ) (Real.exp_pos _).le)
          rw [e2 _ (min_le_right _ _), finsum_mem_coe_finset]
  refine (Finset.sum_le_sum fun χ _ => step1 χ).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hA : ∑ j ∈ Finset.range J, ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) ≤
        C₁ * Real.exp (1 / 2) * K * u ^ (-η / 2) := by
    have : ∀ j ∈ Finset.range J, ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * η) - j) *
        (∑ᶠ ρ ∈ zerosBox χ (1 - min (η + (j + 1) / L) e) T, (ord χ ρ : ℝ)) ≤
        C₁ * Real.exp (1 / 2) * u ^ (-η / 2) * Real.exp (-1 / 2) ^ j := by
      intro j _
      rw [← Finset.mul_sum]
      have hx0 : 0 ≤ min (η + (j + 1) / L) e := by positivity
      have hx1 := min_le_left (η + (j + 1) / L) e
      have hx2 := min_le_right (η + (j + 1) / L) e
      generalize min (η + (j + 1) / L) e = x at hx0 hx1 hx2 ⊢
      have h := H₁ q T (1 - x) hT (by linarith) (by linarith)
      refine (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans ?_
      rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos (by linarith), ← Real.exp_nat_mul,
        mul_left_comm, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
      rw [← hLdef, ← hMdef]
      have hx3 : L * x ≤ L * η + (j + 1) := by
        have := mul_le_mul_of_nonneg_left hx1 hL.le
        rwa [mul_add, mul_div_cancel₀ _ hL.ne'] at this
      nlinarith [mul_le_mul_of_nonneg_right hLM1 hx0]
    refine (Finset.sum_le_sum this).trans ?_
    rw [← Finset.mul_sum]
    have := hsum.sum_le_tsum (Finset.range J) (fun _ _ => by positivity)
    calc _ ≤ C₁ * Real.exp (1 / 2) * u ^ (-η / 2) * K := by gcongr
      _ = _ := by ring
  have hB : ∑ χ : DirichletCharacter ℂ q, Real.exp (-(L * e)) * (C₂ * (q * T ^ 2)) ≤
      C₂ * u ^ (-(e / 2)) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    have ht : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    have hE : Real.exp (2 * M) = (q * T) ^ 2 := by
      rw [show 2 * M = M + M by ring, Real.exp_add, hMdef, Real.exp_log (by linarith), sq]
    calc _ ≤ (q : ℝ) * (Real.exp (-(L * e)) * (C₂ * (q * T ^ 2))) := by gcongr
      _ = C₂ * (Real.exp (-(L * e)) * Real.exp (2 * M)) := by rw [hE]; ring
      _ ≤ _ := by
        rw [← Real.exp_add, Real.rpow_def_of_pos hu0, ← hLdef]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₂.le
        linarith
  have p1 : 0 ≤ u ^ (-η / 2) := by positivity
  have p2 : 0 ≤ u ^ (-(e / 2)) := by positivity
  have p3 : 0 ≤ C₁ * Real.exp (1 / 2) * K := by positivity
  nlinarith [mul_nonneg p3 p2, mul_nonneg hC₂.le p1]

end GlobalTheory.Lin.ZeroSum
end

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_characters_finsum_zeros_rpow_re_sub_one_le : ∃ A C η₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 < η₀ ∧ ∀ (q : ℕ) [NeZero q] (T u η : ℝ), 2 ≤ T → ((q : ℝ) * T) ^ A ≤ u → 0 ≤ η → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η}, (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) ≤ C * (u ^ (-η / 2) + u ^ (-η₀)) := by
  atlas_forward_decl GlobalTheory.Lin.ZeroSum.sum_rpow_zeros_le
end

section
namespace GlobalTheory.Mem.An

theorem zeroCount_holds : GlobalTheory.Mem.An.ZeroCount := by
  obtain ⟨C, -, H⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨C, fun q _ χ hχ t => ?_⟩
  have h := (H q χ hχ t).2
  simpa only [zsumR, zerosIn, zmult, mul_one] using h

end GlobalTheory.Mem.An
end

section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_psi0_add_zsum_le : ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  first | exact @GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed | exact GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed | (intros; apply GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed <;> assumption)
end

section
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.ExplicitFormulaRight

open GlobalTheory.Mem.An

theorem zfin {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) :
    (zerosIn χ t T).Finite := (ZeroWindow.finite_and_one_le_zmult q χ t T).1

theorem zsumR_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ) :
    zsumR χ t T f = ∑ ρ ∈ (zfin χ t T).toFinset, (zmult χ ρ : ℝ) * f ρ :=
  finsum_mem_eq_finite_toFinset_sum _ _

theorem recip_bound : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
      zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ C * ((q : ℝ) ^ 2 * Real.log (3 * q) ^ 2) ∧
      zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤
        C * ((q : ℝ) ^ 2 * Real.log (3 * q) ^ 2) + C * Real.log (q * T) ^ 2 := by
  obtain ⟨C₁, H₁⟩ := zsumR_recip_le zeroCount_holds
  obtain ⟨c, hc, H₂⟩ := GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one
  refine ⟨|C₁| / c + |C₁| + 1, by positivity, fun q _ χ hχ T hT => ?_⟩
  obtain ⟨h1, h2⟩ := H₁ q χ hχ T hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hl : 0 < Real.log (3 * q) := Real.log_pos (by linarith)
  have hK : 0 < (q : ℝ) ^ 2 * Real.log (3 * q) := by positivity
  have hA : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤
      (|C₁| / c + |C₁| + 1) * ((q : ℝ) ^ 2 * Real.log (3 * q) ^ 2) := by
    have a1 : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤
        ((q : ℝ) ^ 2 * Real.log (3 * q) / c) * zsumR χ 0 1 (fun _ => 1) := by
      rw [zsumR_eq, zsumR_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      obtain ⟨r0, r1, ri, rz⟩ := (zfin χ 0 1).mem_toFinset.mp hρ
      have hz := ((zeros_symm_one_sub q χ hχ ρ r0 r1).1).mp rz
      have hne : (1 - ρ) ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hb := H₂ q χ⁻¹ (1 - ρ) (Or.inr hne) hz (by simpa using ri)
      have hre : c / ((q : ℝ) ^ 2 * Real.log (3 * q)) ≤ ‖ρ‖ := by
        have := Complex.re_le_norm ρ
        simp only [Complex.sub_re, Complex.one_re] at hb
        linarith
      have : 1 / ‖ρ‖ ≤ (q : ℝ) ^ 2 * Real.log (3 * q) / c := by
        have := one_div_le_one_div_of_le (div_pos hc hK) hre
        rwa [one_div_div] at this
      calc (zmult χ ρ : ℝ) * (1 / ‖ρ‖) ≤ (zmult χ ρ : ℝ) * ((q : ℝ) ^ 2 * Real.log (3 * q) / c) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have a2 : zsumR χ 0 1 (fun _ => 1) ≤ |C₁| * Real.log (3 * q) :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hl.le)
    calc _ ≤ ((q : ℝ) ^ 2 * Real.log (3 * q) / c) * (|C₁| * Real.log (3 * q)) :=
          a1.trans (mul_le_mul_of_nonneg_left a2 (by positivity))
      _ = (|C₁| / c) * ((q : ℝ) ^ 2 * Real.log (3 * q) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C₁]) (by positivity)
  refine ⟨hA, ?_⟩
  have hB : zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) +
      zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) := by
    rw [zsumR_eq, zsumR_eq, zsumR_eq]
    have e : (zfin χ 0 1).toFinset = (zfin χ 0 T).toFinset.filter (fun ρ => ¬ 1 < |ρ.im|) := by
      ext ρ
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter, zerosIn, Set.mem_setOf_eq, sub_zero,
        not_lt]
      constructor
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨a, b, by linarith, d⟩, c⟩
      · rintro ⟨⟨a, b, _, d⟩, c⟩
        exact ⟨a, b, c, d⟩
    rw [e, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ρ _ => ?_
    by_cases h : 1 < |ρ.im| <;> simp [h]
  have hC : C₁ * Real.log (q * T) ^ 2 ≤ (|C₁| / c + |C₁| + 1) * Real.log (q * T) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ |C₁| / c := by positivity
    linarith [le_abs_self C₁]
  linarith

theorem box_subset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    zerosBox χ (1 / 2) T ⊆ zerosIn χ 0 T := by
  rintro ρ ⟨a, b, c, d⟩
  exact ⟨by linarith, b, by simpa using c, d⟩

theorem left_zeros {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u T : ℝ) (hu : 1 ≤ u) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ) -
      ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
      Real.sqrt u * zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) := by
  have hf := (zfin χ 0 T).subset (box_subset χ T)
  have e : hf.toFinset = (zfin χ 0 T).toFinset.filter (fun ρ => 1 / 2 ≤ ρ.re) := by
    ext ρ
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨box_subset χ T h, h.1⟩
    · rintro ⟨⟨_, b, c, d⟩, a⟩
      exact ⟨a, b, by simpa using c, d⟩
  rw [zsumR_eq, zsum, finsum_mem_eq_finite_toFinset_sum _ (zfin χ 0 T),
    finsum_mem_eq_finite_toFinset_sum _ hf, e, Finset.sum_filter, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine norm_sum_le_of_le _ fun ρ _ => ?_
  have hu0 : 0 < u := by linarith
  by_cases h : 1 / 2 ≤ ρ.re
  · rw [if_pos h]
    have : (ord χ ρ : ℂ) = zmult χ ρ := rfl
    rw [this, sub_self, norm_zero]
    positivity
  · rw [if_neg h, sub_zero, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
      Complex.norm_natCast, Real.sqrt_eq_rpow]
    have h1 : u ^ ρ.re ≤ u ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu (not_le.mp h).le
    calc (zmult χ ρ : ℝ) * (u ^ ρ.re / ‖ρ‖) = u ^ ρ.re * ((zmult χ ρ : ℝ) * (1 / ‖ρ‖)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

theorem logs {N q u T : ℝ} (hN : 1 ≤ N) (hq : N ≤ q) (hT : 2 ≤ T) (hu : T ≤ u) {L : ℝ}
    (hL : L = Real.log (q * u * T)) :
    1 ≤ L ∧ Real.log (N * u * T) ^ 2 ≤ L ^ 2 ∧ Real.log (N * u) ≤ L ^ 2 ∧
      Real.log (3 * N) ^ 2 ≤ L ^ 2 ∧ Real.log (N * T) ^ 2 ≤ L ^ 2 ∧
      (Nat.log 2 ⌊u⌋₊ : ℝ) * Real.log q ≤ 2 * L ^ 2 := by
  have hq1 : 1 ≤ q := hN.trans hq
  have hu2 : 2 ≤ u := hT.trans hu
  have huT : 4 ≤ u * T := by nlinarith
  have hlog : ∀ x : ℝ, 0 < x → x ≤ q * u * T → Real.log x ≤ L := fun x hx h =>
    hL ▸ Real.log_le_log hx h
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ q → 0 ≤ b → b ≤ u * T → a * b ≤ q * u * T := by
    intro a b ha haq hb hbu
    rw [mul_assoc]
    exact mul_le_mul haq hbu hb (by linarith)
  have h2 := Real.log_two_gt_d9
  have hL1 : 1 ≤ L := by
    have := hlog 4 (by norm_num) (by simpa using key 1 4 (by norm_num) hq1 (by norm_num) huT)
    have h2' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have sq_le : ∀ x : ℝ, 1 ≤ x → x ≤ q * u * T → Real.log x ^ 2 ≤ L ^ 2 := fun x hx hc =>
    pow_le_pow_left₀ (Real.log_nonneg hx) (hlog x (by linarith) hc) 2
  have huu : u ≤ u * T := by nlinarith
  have hTT : T ≤ u * T := by nlinarith
  refine ⟨hL1, sq_le _ ?_ ?_, ?_, sq_le _ (by linarith) ?_, sq_le _ (by nlinarith) ?_, ?_⟩
  · rw [mul_assoc]; nlinarith
  · rw [mul_assoc]; exact key _ _ (by linarith) hq (by linarith) le_rfl
  · have := hlog (N * u) (by positivity) (key _ _ (by linarith) hq (by linarith) huu)
    nlinarith
  · rw [mul_comm]; exact key _ _ (by linarith) hq (by linarith) (by linarith)
  · exact key _ _ (by linarith) hq (by linarith) hTT
  · have a1 : Real.log q ≤ L :=
      hlog q (by linarith) (by simpa using key q 1 (by linarith) le_rfl (by norm_num) (by linarith))
    have a2 : Real.log u ≤ L :=
      hlog u (by linarith) (by simpa using key 1 u (by linarith) hq1 (by linarith) huu)
    have hfl : ⌊u⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega
    have a3 : (Nat.log 2 ⌊u⌋₊ : ℝ) * Real.log 2 ≤ Real.log u := by
      rw [← Real.log_pow]
      refine Real.log_le_log (by positivity) (le_trans ?_ (Nat.floor_le (by linarith)))
      exact_mod_cast Nat.pow_log_le_self 2 hfl
    have a4 : (Nat.log 2 ⌊u⌋₊ : ℝ) ≤ 2 * L := by
      have : (0 : ℝ) ≤ Nat.log 2 ⌊u⌋₊ := by positivity
      nlinarith
    calc _ ≤ (2 * L) * L := mul_le_mul a4 a1 (Real.log_nonneg hq1) (by linarith)
      _ = _ := by ring

theorem combine {A B S s x K E P D Z₁ Z t₁ t₂ l₃ l₄ N q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 1 ≤ s) (hx : 0 ≤ x) (hK : 0 ≤ K) (hN : 1 ≤ N) (hq : N ≤ q)
    (hS : S ≤ P + E + D) (hP : P ≤ 2 * K) (hE : E ≤ A * (t₁ + t₂ + Z₁)) (hD : D ≤ s * Z)
    (h1 : t₁ ≤ x * K) (h2 : t₂ ≤ K) (hl₃ : l₃ ≤ K) (hl₄ : l₄ ≤ K)
    (hZ₁ : Z₁ ≤ B * (N ^ 2 * l₃)) (hZ : Z ≤ B * (N ^ 2 * l₃) + B * l₄) :
    S ≤ (2 + A * (2 + B) + 2 * B) * (x + s * q ^ 3) * K := by
  have hq1 : 1 ≤ q := hN.trans hq
  have hq3 : 1 ≤ q ^ 3 := one_le_pow₀ hq1
  have hN2 : N ^ 2 ≤ q ^ 3 :=
    (pow_le_pow_left₀ (by linarith) hq 2).trans (pow_le_pow_right₀ hq1 (by norm_num))
  obtain ⟨M, hM⟩ : ∃ M, M = (x + s * q ^ 3) * K := ⟨_, rfl⟩
  have m0 : 0 ≤ x * K := by positivity
  have k1 : K ≤ q ^ 3 * K := le_mul_of_one_le_left hK hq3
  have k2 : q ^ 3 * K ≤ s * (q ^ 3 * K) := le_mul_of_one_le_left (by positivity) hs
  have m1 : s * (q ^ 3 * K) ≤ M := by rw [hM]; linarith
  have m2 : x * K ≤ M := by rw [hM]; linarith
  have n1 : N ^ 2 * l₃ ≤ q ^ 3 * K :=
    (mul_le_mul_of_nonneg_left hl₃ (by positivity)).trans (mul_le_mul_of_nonneg_right hN2 hK)
  have z1 : Z₁ ≤ B * M := hZ₁.trans (mul_le_mul_of_nonneg_left (by linarith) hB)
  have z2 : Z ≤ 2 * B * (q ^ 3 * K) := by
    have b1 := mul_le_mul_of_nonneg_left n1 hB
    have b2 := mul_le_mul_of_nonneg_left (hl₄.trans k1) hB
    linarith
  have z3 : D ≤ 2 * B * M := by
    calc D ≤ s * (2 * B * (q ^ 3 * K)) := hD.trans (mul_le_mul_of_nonneg_left z2 (by linarith))
      _ = 2 * B * (s * (q ^ 3 * K)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left m1 (by positivity)
  have z4 : E ≤ A * (M + M + B * M) := hE.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
  rw [mul_assoc, ← hM]
  linarith

theorem explicit_formula_right : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u T : ℝ), 2 ≤ T → T ≤ u → (zerosBox χ (1 / 2) T).Finite ∧ ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) - (if χ = 1 then (u : ℂ) else 0) + ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u / T + Real.sqrt u * (q : ℝ) ^ 3) * Real.log (q * u * T) ^ 2 := by
  obtain ⟨A, HA⟩ := GlobalTheory.T.norm_psi0_add_zsum_le
  obtain ⟨B, hB, HB⟩ := recip_bound
  refine ⟨2 + |A| * (2 + B) + 2 * B, by positivity, fun q _ χ u T hT hu => ?_⟩
  refine ⟨(zfin χ 0 T).subset (box_subset χ T), ?_⟩
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hN : (1 : ℝ) ≤ χ.conductor := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hq : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hone : χ.primitiveCharacter = 1 ↔ χ = 1 := by
    constructor
    · intro h
      rw [← χ.changeLevel_primitiveCharacter, h, map_one]
    · rintro rfl
      exact primitiveCharacter_one
  have hcmp : ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → ρ.re < 1 →
      (LFunction χ ρ = 0 ↔ LFunction χ.primitiveCharacter ρ = 0) ∧
        ord χ ρ = ord χ.primitiveCharacter ρ := fun ρ a b =>
    GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros q χ ρ (by linarith) (Or.inr (by rintro rfl; simp at b))
  have hbox : zerosBox χ (1 / 2) T = zerosBox χ.primitiveCharacter (1 / 2) T := by
    ext ρ
    constructor
    · rintro ⟨a, b, c, d⟩
      exact ⟨a, b, c, (hcmp ρ a b).1.mp d⟩
    · rintro ⟨a, b, c, d⟩
      exact ⟨a, b, c, (hcmp ρ a b).1.mpr d⟩
  have hsum : ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) =
      ∑ᶠ ρ ∈ zerosBox χ.primitiveCharacter (1 / 2) T,
        (ord χ.primitiveCharacter ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) :=
    finsum_mem_congr hbox fun ρ hρ => by rw [(hcmp ρ hρ.1 hρ.2.1).2]
  have hE := HA χ.conductor χ.primitiveCharacter hprim u T hT hu
  obtain ⟨hZ₁, hZ⟩ := HB χ.conductor χ.primitiveCharacter hprim T hT
  have hD := left_zeros χ.primitiveCharacter u T (by linarith)
  have hP := GlobalTheory.MangoldtSeries.norm_sub_primitive_le χ ⌊u⌋₊
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := logs hN hq hT hu rfl
  have hpsi : Formalism.MainNotions.GlobalTheoryTheory.psi0 χ.primitiveCharacter u =
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)) -
        (if χ = 1 then (u : ℂ) else 0) := by
    unfold Formalism.MainNotions.GlobalTheoryTheory.psi0
    congr 1
    by_cases h : χ = 1
    · rw [if_pos h, if_pos (hone.mpr h)]
    · rw [if_neg h, if_neg (mt hone.mp h)]
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hZ0 : 0 ≤ zsumR χ.primitiveCharacter 0 1 (fun ρ => 1 / ‖ρ‖) := by
    rw [zsumR_eq]
    exact Finset.sum_nonneg fun ρ _ => by positivity
  have hl0 : 0 ≤ Real.log (χ.conductor * u) := Real.log_nonneg (by nlinarith)
  have hE' := hE.trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
  refine combine (abs_nonneg A) hB.le (Real.one_le_sqrt.mpr (by linarith)) (by positivity)
    (by positivity) hN hq ?_ (hP.trans l5) hE' hD ?_ l2 l3 l4 hZ₁ hZ
  · rw [hsum, hpsi]
    refine le_trans (le_of_eq ?_) ((norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
    congr 1
    ring
  · rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left l1 (by positivity)

end GlobalTheory.ExplicitFormulaRight
end

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicit_formula_dirichlet_zeros_right_half : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u T : ℝ), 2 ≤ T → T ≤ u → (zerosBox χ (1 / 2) T).Finite ∧ ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) - (if χ = 1 then (u : ℂ) else 0) + ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u / T + Real.sqrt u * (q : ℝ) ^ 3) * Real.log (q * u * T) ^ 2 := by
  atlas_forward_decl GlobalTheory.ExplicitFormulaRight.explicit_formula_right
end

section
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.PsiRel

lemma orth (M : ℕ) [NeZero M] (b : ℕ) (hb : Nat.Coprime b M) (u : ℝ) :
    (((M.totient : ℝ) * psiAP M b u : ℝ) : ℂ) = ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ *
      ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod M) := by
  have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold psiAP
  rw [Finset.sum_filter, Finset.mul_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod M)
  have h2 : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ * (((Λ n : ℝ) : ℂ) * χ (n : ZMod M)) =
      ((Λ n : ℝ) : ℂ) * ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ * χ (n : ZMod M) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun χ _ => by ring
  rw [h2, h]
  by_cases hn : n ≡ b [MOD M]
  · have : (b : ZMod M) = n := (ZMod.natCast_eq_natCast_iff _ _ _).2 hn.symm
    rw [if_pos hn, if_pos this]; push_cast; ring
  · have : ¬ (b : ZMod M) = n := fun h => hn ((ZMod.natCast_eq_natCast_iff _ _ _).1 h).symm
    rw [if_neg hn, if_neg this]; simp

lemma zsum (s t : Set ℂ) (ht : t.Finite) (hst : s ⊆ t) (o : ℂ → ℕ) (u : ℝ) (hu : 0 < u)
    (h : ∀ ρ ∈ s, 1 / 2 ≤ ρ.re) :
    ‖∑ᶠ ρ ∈ s, (o ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ 2 * u * ∑ᶠ ρ ∈ t, (o ρ : ℝ) * u ^ (ρ.re - 1) := by
  have hs := ht.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, finsum_mem_eq_finite_toFinset_sum _ ht, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (g := fun ρ : ℂ => 2 * u * ((o ρ : ℝ) * u ^ (ρ.re - 1))) ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (by simpa using hst) fun ρ _ _ => by positivity)
  intro ρ hρ
  have h1 := h ρ (by simpa using hρ)
  have h2 : 1 / 2 ≤ ‖ρ‖ := h1.trans (Complex.re_le_norm ρ)
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu,
    Real.rpow_sub_one hu.ne']
  have h3 : 0 < u ^ ρ.re := Real.rpow_pos_of_pos hu _
  have h4 : u ^ ρ.re / ‖ρ‖ ≤ 2 * u ^ ρ.re := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  calc (o ρ : ℝ) * (u ^ ρ.re / ‖ρ‖) ≤ (o ρ : ℝ) * (2 * u ^ ρ.re) := by gcongr
    _ = _ := by field_simp

lemma combine (M : ℕ) [NeZero M] (b : ℕ) (hb : Nat.Coprime b M) (u E x : ℝ) (hE : 0 ≤ E)
    (Z e : DirichletCharacter ℂ M → ℂ) (B : DirichletCharacter ℂ M → ℝ)
    (h1 : ∀ χ : DirichletCharacter ℂ M, ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod M)) -
      (if χ = 1 then (u : ℂ) else 0) + Z χ‖ ≤ E)
    (h2 : ∀ χ, ‖Z χ - e χ‖ ≤ B χ)
    (h3 : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ * e χ = (x : ℂ)) :
    |(M.totient : ℝ) * psiAP M b u - (u - x)| ≤ M * E + ∑ χ, B χ := by
  have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  have hui : IsUnit (b : ZMod M)⁻¹ :=
    IsUnit.of_mul_eq_one (b : ZMod M) (ZMod.inv_mul_of_unit _ hu)
  have h4 : ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ * (if χ = 1 then (u : ℂ) else 0) = u := by
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), MulChar.one_apply hui, one_mul]
  have key : (((M.totient : ℝ) * psiAP M b u - (u - x) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ M, χ (b : ZMod M)⁻¹ *
        (((∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod M)) -
          (if χ = 1 then (u : ℂ) else 0) + Z χ) - (Z χ - e χ)) := by
    rw [Complex.ofReal_sub, orth M b hb u, Complex.ofReal_sub, ← h3]
    conv_lhs => rw [← h4]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun χ _ => by ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, key]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun χ => E + B χ) fun χ _ => ?_).trans ?_
  · rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans ?_
    exact (norm_sub_le _ _).trans (add_le_add (h1 χ) (h2 χ))
  · rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      ← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    have : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
    gcongr

lemma struct (M : ℕ) [NeZero M] (b : ℕ) (hb : Nat.Coprime b M) (θ : ℤ) (β u T η E : ℝ) (hu : 0 < u) (hE : 0 ≤ E)
    (h1 : ∀ χ : DirichletCharacter ℂ M, (zerosBox χ (1 / 2) T).Finite ∧
      ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod M)) - (if χ = 1 then (u : ℂ) else 0) +
        ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ E)
    (h2 : (θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T, ρ.re ≤ 1 - η) ∨
      ∃ χ₁ : DirichletCharacter ℂ M, χ₁ ^ 2 = 1 ∧ χ₁ (b : ZMod M) = θ ∧ (β : ℂ) ∈ zerosBox χ₁ (1 / 2) T ∧
        ord χ₁ β = 1 ∧ ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T,
          (χ = χ₁ ∧ ρ = β) ∨ ρ.re ≤ 1 - η) :
    |(M.totient : ℝ) * psiAP M b u - (u - θ * (u ^ β / β))| ≤ M * E + 2 * u *
      ∑ χ : DirichletCharacter ℂ M, (∑ᶠ ρ ∈ zerosBox χ (1 / 2) T ∩ {ρ | ρ.re ≤ 1 - η},
        (ord χ ρ : ℝ) * u ^ (ρ.re - 1)) := by
  have hbu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  rw [Finset.mul_sum]
  rcases h2 with ⟨h0, h2⟩ | ⟨χ₁, hsq, hθ, hβ, ho, h2⟩
  · refine combine M b hb u E _ hE _ (fun _ => 0) _ (fun χ => (h1 χ).2) (fun χ => ?_) (by simp [h0])
    rw [sub_zero]
    exact zsum _ _ ((h1 χ).1.inter_of_left _) (fun ρ hρ => ⟨hρ, h2 χ ρ hρ⟩) _ u hu fun ρ hρ => hρ.1
  · refine combine M b hb u E _ hE _ (fun χ => if χ = χ₁ then (u : ℂ) ^ (β : ℂ) / β else 0) _
      (fun χ => (h1 χ).2) (fun χ => ?_) ?_
    · by_cases hχ : χ = χ₁
      · subst hχ
        have hi : zerosBox χ (1 / 2) T = insert (β : ℂ) (zerosBox χ (1 / 2) T \ {(β : ℂ)}) := by
          rw [Set.insert_diff_singleton, Set.insert_eq_of_mem hβ]
        have : ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) =
            (u : ℂ) ^ (β : ℂ) / β +
            ∑ᶠ ρ ∈ zerosBox χ (1 / 2) T \ {(β : ℂ)}, (ord χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) := by
          conv_lhs => rw [hi]
          rw [finsum_mem_insert _ (by simp) ((h1 χ).1.diff), ho]; simp
        simp only [if_true]
        rw [this, add_sub_cancel_left]
        refine zsum _ _ ((h1 χ).1.inter_of_left _) (fun ρ hρ => ⟨hρ.1, ?_⟩) _ u hu fun ρ hρ => hρ.1.1
        rcases h2 χ ρ hρ.1 with h | h
        · exact absurd h.2 hρ.2
        · exact h
      · simp only [if_neg hχ]
        rw [sub_zero]
        refine zsum _ _ ((h1 χ).1.inter_of_left _) (fun ρ hρ => ⟨hρ, ?_⟩) _ u hu fun ρ hρ => hρ.1
        rcases h2 χ ρ hρ with h | h
        · exact absurd h.1 hχ
        · exact h
    · simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
      have ha : χ₁ (b : ZMod M) * χ₁ (b : ZMod M) = 1 := by
        have := congrArg (fun ψ : DirichletCharacter ℂ M => ψ (b : ZMod M)) hsq
        simp only [pow_two, MulChar.mul_apply, MulChar.one_apply hbu] at this
        exact this
      have hb' : χ₁ (b : ZMod M)⁻¹ * χ₁ (b : ZMod M) = 1 := by
        rw [← map_mul, ZMod.inv_mul_of_unit _ hbu, map_one]
      have hc : χ₁ (b : ZMod M)⁻¹ = θ := by
        rw [← hθ]; linear_combination (-(χ₁ (b : ZMod M)⁻¹)) * ha + χ₁ (b : ZMod M) * hb'
      rw [hc]; push_cast; rw [Complex.ofReal_cpow hu.le]

lemma mainLower (θ β V : ℝ) (hθ : θ ≤ 1) (h1 : 7 / 8 ≤ β) (h2 : β < 1) (hV : 8 ≤ V) :
    Real.exp V * min 1 ((1 - β) * V) / 4 ≤ Real.exp V - θ * ((Real.exp V) ^ β / β) := by
  set x := (1 - β) * V with hx
  have hx0 : 0 < x := by positivity
  have hb : 0 < β := by linarith
  have e1 : (Real.exp V) ^ β = Real.exp V * Real.exp (-x) := by
    rw [← Real.exp_mul, ← Real.exp_add]; congr 1; rw [hx]; ring
  have e2 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, one_div]; exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp x])
  have e3 : 8 * (1 - β) ≤ x := by rw [hx]; nlinarith
  have e4 : Real.exp (-x) / β ≤ 1 - min 1 x / 4 := by
    rw [div_le_iff₀ hb]; refine e2.trans ?_
    rw [div_le_iff₀ (by linarith)]
    rcases le_total 1 x with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]
      have : 0 ≤ (1 - x / 4) * (1 + x) := by apply mul_nonneg <;> linarith
      have h5 : (1 - x / 4) * (1 + x) * (1 - x / 8) ≤ (1 - x / 4) * (1 + x) * β := by
        gcongr; linarith
      nlinarith [mul_nonneg hx0.le (sub_nonneg.2 h), mul_nonneg hx0.le (mul_nonneg hx0.le hx0.le)]
  have hu := Real.exp_pos V
  have e5 : 0 < Real.exp (-x) / β := by positivity
  rw [e1, mul_div_assoc (Real.exp V) (Real.exp (-x))]
  have : θ * (Real.exp V * (Real.exp (-x) / β)) ≤ 1 * (Real.exp V * (1 - min 1 x / 4)) := by
    refine (mul_le_mul_of_nonneg_right hθ (by positivity)).trans ?_
    gcongr
  linarith

lemma realEnd (Ce Ca η₀ c' K cw R₀ : ℝ) (hCe : 0 < Ce) (hCa : 0 < Ca) (hη : 0 < η₀) (hc : 0 < c') (hK : 0 < K)
    (hcw : 0 < cw) :
    ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∀ m V w : ℝ, 1 ≤ m → c₂ * m ≤ V →
      0 < V ∧ R₀ * (10 * m + √V) ≤ V ∧ (cw * Real.exp (-(3 * m)) ≤ w →
      Real.exp m * (Ce * (Real.exp (-(8 * m + √V)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
        (m + V + (8 * m + √V)) ^ 2) + 2 * (Ca * (K * w * Real.exp (-(c' * (V / (10 * m + √V)))) +
          Real.exp (-(η₀ * V)))) ≤
        C * (Real.exp (-c₃ * V / m) + Real.exp (-√(c₃ * V))) * (w / 4)) := by
  set R := max (max R₀ 2) (1 / η₀) with hR
  have hR2 : 2 ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR0 : R₀ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRη : 1 ≤ η₀ * R := by
    have : 1 / η₀ ≤ R := le_max_right _ _
    rw [div_le_iff₀ hη] at this; linarith
  set c₃ := min (min (1 / 4) (c' / 20)) (c' ^ 2 / 4) with hc₃
  have hc3 : 0 < c₃ := by positivity
  have hc3a : c₃ ≤ 1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hc3b : c₃ ≤ c' / 20 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3c : c₃ ≤ c' ^ 2 / 4 := min_le_right _ _
  refine ⟨20 * R + 4 * R ^ 2, c₃, 4 * ((3072 * Ce + 2 * Ca) / cw + 2 * Ca * K), by positivity, hc3,
    by positivity, fun m V w hm hV => ?_⟩
  have hV1 : 20 * R * m ≤ V := by nlinarith [sq_nonneg R]
  have hV2 : 4 * R ^ 2 ≤ V := by nlinarith [sq_nonneg R]
  have hV0 : 0 < V := by nlinarith
  set s := √V with hs
  have hs2 : s * s = V := Real.mul_self_sqrt hV0.le
  have hsR : 2 * R ≤ s := Real.le_sqrt_of_sq_le (by linarith)
  have hL : R * (10 * m + s) ≤ V := by nlinarith
  have hL0 : 0 < 10 * m + s := by linarith
  refine ⟨hV0, le_trans (by gcongr) hL, fun hw => ?_⟩
  have hL2 : 2 * (10 * m + s) ≤ V := le_trans (by gcongr) hL
  have hLη : 10 * m + s ≤ η₀ * V := by
    have := mul_le_mul_of_nonneg_left hL hη.le
    nlinarith
  set P := Real.exp (-c₃ * V / m) + Real.exp (-√(c₃ * V)) with hP
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hsq : ∀ a : ℝ, 0 ≤ a → c₃ ≤ a ^ 2 → √(c₃ * V) ≤ a * s := fun a ha h => by
    apply Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, pow_two s, hs2]; gcongr
  have p1 : Real.exp (-(s / 2)) ≤ P := by
    have := hsq (1 / 2) (by norm_num) (by linarith)
    have h : Real.exp (-(s / 2)) ≤ Real.exp (-√(c₃ * V)) := by gcongr; linarith
    linarith [Real.exp_pos (-c₃ * V / m)]
  have p2 : Real.exp (-(c' * (V / (10 * m + s)))) ≤ P := by
    rcases le_total s (10 * m) with h | h
    · have h1 : V / (20 * m) ≤ V / (10 * m + s) := by gcongr; linarith
      have h2 : c₃ * V / m ≤ c' * (V / (20 * m)) := by
        have : c' * (V / (20 * m)) = c' / 20 * V / m := by field_simp
        rw [this]; gcongr
      have h3 : Real.exp (-(c' * (V / (10 * m + s)))) ≤ Real.exp (-c₃ * V / m) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left h1 hc.le
        rw [neg_mul, neg_div]; linarith
      linarith [Real.exp_pos (-√(c₃ * V))]
    · have h1 : s / 2 ≤ V / (10 * m + s) := by
        rw [le_div_iff₀ hL0]; nlinarith
      have h2 := hsq (c' / 2) (by positivity) (by linarith)
      have h3 : Real.exp (-(c' * (V / (10 * m + s)))) ≤ Real.exp (-√(c₃ * V)) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left h1 hc.le
        linarith
      linarith [Real.exp_pos (-c₃ * V / m)]
  have hs0 : 0 ≤ s := by linarith
  have q1 : (m + V + (8 * m + s)) ^ 2 ≤ 1536 * Real.exp (s / 2) := by
    have h1 : (m + V + (8 * m + s)) ^ 2 ≤ (2 * V) ^ 2 := by gcongr; linarith
    have h2 := Real.pow_div_factorial_le_exp (s / 2) (by linarith) 4
    have h3 : (s / 2) ^ 4 / ((Nat.factorial 4 : ℕ) : ℝ) = V ^ 2 / 384 := by
      rw [← hs2]; norm_num [Nat.factorial]; ring
    rw [h3] at h2; linarith
  set X := Real.exp (-(3 * m)) with hX
  have q2 : Real.exp m * (Real.exp (-(8 * m + s)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
      Real.exp (s / 2) ≤ 2 * (X * Real.exp (-(s / 2))) := by
    rw [mul_add, add_mul, hX]
    simp only [← Real.exp_add]
    rw [two_mul]; exact add_le_add (Real.exp_le_exp.2 (by linarith)) (Real.exp_le_exp.2 (by linarith))
  have q3 : Real.exp (-(η₀ * V)) ≤ X * Real.exp (-(s / 2)) := by
    rw [hX, ← Real.exp_add]; gcongr; linarith
  have q4 : X * Real.exp (-(s / 2)) ≤ w / cw * P := by
    have : X ≤ w / cw := by rw [le_div_iff₀ hcw]; linarith
    gcongr
  have q5 : Real.exp m * (Ce * (Real.exp (-(8 * m + s)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
        (m + V + (8 * m + s)) ^ 2) ≤ 3072 * Ce * (w / cw * P) := by
    calc _ ≤ Real.exp m * (Ce * (Real.exp (-(8 * m + s)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
        (1536 * Real.exp (s / 2))) := by gcongr
      _ = 1536 * Ce * (Real.exp m * (Real.exp (-(8 * m + s)) + Real.exp (-(V / 2)) * Real.exp (3 * m)) *
        Real.exp (s / 2)) := by ring
      _ ≤ 1536 * Ce * (2 * (w / cw * P)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  calc _ ≤ 3072 * Ce * (w / cw * P) + 2 * (Ca * (K * w * P + w / cw * P)) := by
        gcongr; exact q3.trans q4
    _ = _ := by field_simp; ring

lemma etaChoice (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    ∃ c' K R₁ : ℝ, 0 < c' ∧ c' ≤ c / 2 ∧ 1 ≤ K ∧ ∀ δ R : ℝ, 0 < δ → 0 ≤ R → R₁ ≤ R → ∃ a : ℝ, 0 ≤ a ∧
      (a = c ∨ a = d * Real.log (d / δ)) ∧
      Real.exp (-(a * R / 2)) ≤ K * min 1 δ * Real.exp (-(c' * R)) := by
  set d₀ := min 1 (d / Real.exp 1) with hd₀
  have h0 : 0 < d₀ := by positivity
  have h1 : d₀ ≤ 1 := min_le_left _ _
  have h2 : d₀ * Real.exp 1 ≤ d := by
    have : d₀ ≤ d / Real.exp 1 := min_le_right _ _
    rwa [le_div_iff₀ (Real.exp_pos 1)] at this
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have ha : min (c / 2) (d / 4) ≤ c / 2 := min_le_left _ _
  have hb : min (c / 2) (d / 4) ≤ d / 4 := min_le_right _ _
  refine ⟨min (c / 2) (d / 4), 1 / d₀, 4 / d, by positivity, ha, by rwa [le_div_iff₀ h0, one_mul],
    fun δ R hδ hR0 hR => ?_⟩
  rcases le_total d₀ δ with h | h
  · refine ⟨c, hc.le, Or.inl rfl, ?_⟩
    have h3 : 1 ≤ 1 / d₀ * min 1 δ := by
      rw [one_div_mul_eq_div, le_div_iff₀ h0, one_mul]; exact le_min h1 h
    refine le_trans ?_ (le_mul_of_one_le_left (Real.exp_pos _).le h3)
    apply Real.exp_le_exp.2
    nlinarith
  · have hl : 1 ≤ Real.log (d / δ) := by
      rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hδ]; nlinarith
    refine ⟨d * Real.log (d / δ), by positivity, Or.inr rfl, ?_⟩
    have h4 : 4 ≤ d * R := by rw [div_le_iff₀ hd] at hR; linarith
    rw [min_eq_right (h.trans h1)]
    have h5 : Real.exp (-Real.log (d / δ)) ≤ 1 / d₀ * δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div, one_div_mul_eq_div]
      gcongr; nlinarith
    refine le_trans ?_ (mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hb hR0
    nlinarith [mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hl)]

set_option maxHeartbeats 1000000 in

theorem psiAP_relative : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∀ (M : ℕ) [NeZero M] (b : ℕ) (θ : ℤ) (β u : ℝ), 3 ≤ M → Nat.Coprime b M → ExcData c₁ M b θ β → (M : ℝ) ^ c₂ ≤ u → |(M.totient : ℝ) * psiAP M b u - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log M) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β)) := by
  obtain ⟨c₀, hc₀, hX⟩ := GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion
  refine ⟨c₀, hc₀, fun c₁ hc₁ hc₁' => ?_⟩
  obtain ⟨c, hc, hX⟩ := hX c₁ hc₁ hc₁'
  obtain ⟨d, hd, hD⟩ := GlobalTheory.T.one_sub_re_ge_of_exceptional_zero_repulsion
  obtain ⟨Ce, hCe, hE⟩ := GlobalTheory.T.explicit_formula_dirichlet_zeros_right_half
  obtain ⟨A, Ca, η₀, hA, hCa, hη₀, hZ⟩ := GlobalTheory.T.exists_sum_characters_finsum_zeros_rpow_re_sub_one_le
  obtain ⟨c', K, R₁, hc', hc'', hK, hη⟩ := etaChoice c d hc hd
  obtain ⟨c₂, c₃, C, hc₂, hc₃, hC, hR⟩ := realEnd Ce Ca η₀ c' K (min 1 c) (max (max R₁ A) 8) hCe hCa hη₀ hc'
    (by linarith) (by positivity)
  refine ⟨c₂, c₃, C, hc₂, hc₃, hC, fun M _ b θ β u hM hb hexc hu => ?_⟩
  obtain ⟨hX1, hX2, hX3⟩ := hX M hM
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hu0 : 0 < u := lt_of_lt_of_le (Real.rpow_pos_of_pos hM0 _) hu
  obtain ⟨V, rfl⟩ : ∃ V, u = Real.exp V := ⟨Real.log u, (Real.exp_log hu0).symm⟩
  rw [Real.log_exp]
  set m := Real.log M with hm
  have hMm : (M : ℝ) = Real.exp m := (Real.exp_log hM0).symm
  have hm1 : 1 ≤ m := by
    rw [hm, Real.le_log_iff_exp_le hM0]; linarith [Real.exp_one_lt_d9]
  have hV : c₂ * m ≤ V := by
    rw [hMm, ← Real.exp_mul, Real.exp_le_exp] at hu; linarith
  have hs0 : 0 ≤ √V := Real.sqrt_nonneg V
  have hL : max (max R₁ A) 8 * (10 * m + √V) ≤ V := (hR m V 1 hm1 hV).2.1
  have hV0 : 0 < V := (hR m V 1 hm1 hV).1
  have hfin := fun w => (hR m V w hm1 hV).2.2
  clear hR
  set L := 10 * m + √V with hLd
  have hL1 : 10 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hL8 : 8 * L ≤ V := le_trans (by gcongr; exact le_max_right _ _) hL
  have hLA : A * L ≤ V := le_trans (by gcongr; exact (le_max_right _ _).trans (le_max_left _ _)) hL
  have hLR : R₁ ≤ V / L := by
    rw [le_div_iff₀ hL0]
    exact le_trans (by gcongr; exact (le_max_left _ _).trans (le_max_left _ _)) hL
  set T := Real.exp (8 * m + √V) with hT
  have hT2 : 2 ≤ T := by linarith [Real.add_one_le_exp (8 * m + √V)]
  have hTu : T ≤ Real.exp V := Real.exp_le_exp.2 (by linarith)
  have hTA : ((M : ℝ) * T) ^ A ≤ Real.exp V := by
    rw [hMm, hT, ← Real.exp_add, ← Real.exp_mul, Real.exp_le_exp]; nlinarith
  have hlog : ∀ ρ : ℂ, |ρ.im| ≤ T → 0 < Real.log (M * (|ρ.im| + 2)) ∧ Real.log (M * (|ρ.im| + 2)) ≤ L := by
    intro ρ hρ
    have h0 := abs_nonneg ρ.im
    refine ⟨Real.log_pos (by nlinarith), ?_⟩
    rw [Real.log_le_iff_le_exp (by positivity)]
    have : Real.exp L = M * (M * T) := by
      rw [hMm, hT, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hLd]; ring
    rw [this]; gcongr; nlinarith
  have hzf : ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T,
      (ρ.im = 0 ∧ IsExc c₁ χ ρ.re) ∨ ρ.re ≤ 1 - c / L := by
    intro χ ρ hρ
    refine (hX3 χ ρ hρ.2.1 hρ.2.2.2).imp_right fun h => h.trans ?_
    obtain ⟨h1, h2⟩ := hlog ρ hρ.2.2.1
    gcongr
  have core : ∀ a w : ℝ, 0 ≤ a → min 1 c * Real.exp (-(3 * m)) ≤ w →
      Real.exp (-(a * (V / L) / 2)) ≤ K * w * Real.exp (-(c' * (V / L))) →
      Real.exp V * w / 4 ≤ Real.exp V - θ * (Real.exp V ^ β / β) →
      ((θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T, ρ.re ≤ 1 - a / L) ∨
      ∃ χ₁ : DirichletCharacter ℂ M, χ₁ ^ 2 = 1 ∧ χ₁ (b : ZMod M) = θ ∧ (β : ℂ) ∈ zerosBox χ₁ (1 / 2) T ∧
        ord χ₁ β = 1 ∧ ∀ (χ : DirichletCharacter ℂ M), ∀ ρ ∈ zerosBox χ (1 / 2) T,
          (χ = χ₁ ∧ ρ = β) ∨ ρ.re ≤ 1 - a / L) →
      |(M.totient : ℝ) * psiAP M b (Real.exp V) - (Real.exp V - θ * (Real.exp V ^ β / β))| ≤
        C * (Real.exp (-c₃ * V / m) + Real.exp (-√(c₃ * V))) * (Real.exp V - θ * (Real.exp V ^ β / β)) := by
    intro a w ha hw h1 h2 h3
    have s1 := struct M b hb θ β (Real.exp V) T (a / L) _ hu0 (by positivity)
      (fun χ => hE M χ (Real.exp V) T hT2 hTu) h3
    have s2 := hZ M T (Real.exp V) (a / L) hT2 hTA (by positivity)
    have s3 := hfin w hw
    have e1 : Real.log (M * Real.exp V * T) = m + V + (8 * m + √V) := by
      rw [hMm, hT, ← Real.exp_add, ← Real.exp_add, Real.log_exp]
    have e2 : Real.exp V / T = Real.exp V * Real.exp (-(8 * m + √V)) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    have e3 : √(Real.exp V) * (M : ℝ) ^ 3 = Real.exp V * (Real.exp (-(V / 2)) * Real.exp (3 * m)) := by
      rw [← Real.exp_half, hMm, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]; congr 1; push_cast; ring
    have e4 : Real.exp V ^ (-(a / L) / 2) = Real.exp (-(a * (V / L) / 2)) := by
      rw [← Real.exp_mul]; congr 1; ring
    have e5 : Real.exp V ^ (-η₀) = Real.exp (-(η₀ * V)) := by
      rw [← Real.exp_mul]; congr 1; ring
    rw [e1, e2, e3] at s1
    rw [e4, e5] at s2
    have s4 := s2.trans (mul_le_mul_of_nonneg_left (add_le_add h1 le_rfl) hCa.le)
    have s5 := mul_le_mul_of_nonneg_left s4 (show 0 ≤ 2 * Real.exp V by positivity)
    have s6 := mul_le_mul_of_nonneg_left s3 hu0.le
    have s7 := mul_le_mul_of_nonneg_left h2
      (show 0 ≤ C * (Real.exp (-c₃ * V / m) + Real.exp (-√(c₃ * V))) by positivity)
    rw [← hMm] at s6
    linarith
  have hx3 : Real.exp (-(3 * m)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hmin1 : min 1 c * Real.exp (-(3 * m)) ≤ 1 :=
    mul_le_one₀ (min_le_left _ _) (Real.exp_pos _).le hx3
  have hVL : 0 ≤ V / L := by positivity
  rcases hexc with ⟨h0, hno⟩ | ⟨χ₁, hχ₁, hθ⟩
  · refine core c 1 hc.le hmin1 ?_ ?_ (Or.inl ⟨h0, fun χ ρ hρ => (hzf χ ρ hρ).resolve_left fun h => hno _ _ h.2⟩)
    · rw [mul_one]
      refine le_trans ?_ (le_mul_of_one_le_left (Real.exp_pos _).le hK)
      apply Real.exp_le_exp.2; nlinarith
    · rw [h0]; simp only [Int.cast_zero, zero_mul]; linarith
  · obtain ⟨hne, hβ1, hz, ho, hlow⟩ := hX2 χ₁ β hχ₁
    have hβ2 : β < 1 := hχ₁.2.2.1
    obtain ⟨a, ha, hor, hexp⟩ := hη ((1 - β) * L) (V / L) (mul_pos (by linarith) hL0) hVL hLR
    have hθ1 : (θ : ℝ) ≤ 1 := by
      have := χ₁.norm_le_one (b : ZMod M)
      rw [hθ, Complex.norm_intCast] at this
      exact (le_abs_self _).trans this
    refine core a _ ha (le_min hmin1 ?_) hexp ?_ (Or.inr ⟨χ₁, hχ₁.1, hθ, ⟨?_, ?_, ?_, hz⟩, ho, ?_⟩)
    · have h1 : Real.exp (-(3 * m)) = 1 / (M : ℝ) ^ 3 := by
        rw [hMm, ← Real.exp_nat_mul, Real.exp_neg, one_div]; norm_num
      have h2 : m ≤ M := by rw [hMm]; linarith [Real.add_one_le_exp m]
      have h3 : c / (M : ℝ) ^ 3 ≤ c / ((M : ℝ) ^ 2 * m) := by
        rw [pow_succ (M : ℝ) 2]; gcongr
      have h4 : min 1 c * (1 / (M : ℝ) ^ 3) ≤ c / (M : ℝ) ^ 3 := by
        rw [mul_one_div]; gcongr; exact min_le_right _ _
      rw [h1]; nlinarith
    · refine le_trans ?_ (mainLower θ β V hθ1 hβ1 hβ2 (by linarith))
      gcongr; linarith
    · simp only [Complex.ofReal_re]; linarith
    · simpa using hβ2
    · simp only [Complex.ofReal_im, abs_zero]; linarith
    · intro χ ρ hρ
      rcases hor with rfl | rfl
      · refine (hzf χ ρ hρ).imp_left fun h => ?_
        obtain ⟨h1, h2⟩ := hX1 χ χ₁ _ _ h.2 hχ₁
        exact ⟨h1, Complex.ext (by simpa using h2) (by simpa using h.1)⟩
      · by_cases h : χ = χ₁ ∧ ρ = β
        · exact Or.inl h
        · right
          have := hD M χ₁ χ β L ρ hne hχ₁.1 hβ2 (by linarith) hz hρ.2.2.2 hρ.1 hρ.2.1
            (by tauto) (hlog ρ hρ.2.2.1).2
          linarith

end GlobalTheory.Lin.PsiRel
end

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebyshevPsiProgression_relative_error : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₀ → ∃ c₂ c₃ C : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < C ∧ ∀ (M : ℕ) [NeZero M] (b : ℕ) (θ : ℤ) (β u : ℝ), 3 ≤ M → Nat.Coprime b M → ExcData c₁ M b θ β → (M : ℝ) ^ c₂ ≤ u → |(M.totient : ℝ) * psiAP M b u - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log M) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β)) := by
  atlas_forward_decl GlobalTheory.Lin.PsiRel.psiAP_relative
end

section
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.PsiToPi

open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)

noncomputable def mainPsi (θ : ℤ) (β u : ℝ) : ℝ := u - θ * (u ^ β / β)

noncomputable def wt (P : ℕ → Prop) (n : ℕ) : ℝ := if n.Prime ∧ P n then Real.log n else 0

noncomputable def cnt (P : ℕ → Prop) (u : ℝ) : ℝ := (((Finset.Icc 1 ⌊u⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ)

theorem contOn_inv_log : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ioi 1) := fun t ht =>
  (continuousAt_const.div (Real.continuousAt_log (by have : 1 < t := ht; linarith))
    (Real.log_pos ht).ne').continuousWithinAt

theorem intInt_inv_log {x : ℝ} (hx : 1 < x) : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume 2 x := by
  apply ContinuousOn.intervalIntegrable
  refine contOn_inv_log.mono fun t ht => ?_
  have := ht.1
  have h2 : (1 : ℝ) < min 2 x := lt_min (by norm_num) hx
  exact lt_of_lt_of_le h2 this

theorem hasDerivAt_Li {x : ℝ} (hx : 1 < x) : HasDerivAt Li (1 / Real.log x) x :=
  intervalIntegral.integral_hasDerivAt_right (intInt_inv_log hx)
    (contOn_inv_log.stronglyMeasurableAtFilter isOpen_Ioi x hx)
    (contOn_inv_log.continuousAt (Ioi_mem_nhds hx))

theorem li_bounds {x : ℝ} (hx : 2 ≤ x) : 0 ≤ Li x ∧ Li x ≤ 3 / 2 * x := by
  have h2 := Real.log_two_gt_d9
  constructor
  · exact intervalIntegral.integral_nonneg hx fun t ht =>
      div_nonneg zero_le_one (Real.log_nonneg (by linarith [ht.1]))
  · have h := intervalIntegral.integral_mono_on hx (intInt_inv_log (by linarith))
      (intervalIntegrable_const (c := (3 / 2 : ℝ))) (fun t ht => by
        have := Real.log_le_log (by norm_num) ht.1
        rw [div_le_iff₀ (by linarith)]; linarith)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    unfold Li; linarith

theorem hasDerivAt_diff (θ : ℤ) {β u : ℝ} (hβ : 0 < β) (hu : 1 < u) :
    HasDerivAt (fun u => Emain θ β u - mainPsi θ β u / Real.log u) (mainPsi θ β u / (u * Real.log u ^ 2)) u := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < Real.log u := Real.log_pos hu
  have h1 : HasDerivAt (fun u : ℝ => u ^ β) (β * u ^ (β - 1)) u := Real.hasDerivAt_rpow_const (Or.inl hu0.ne')
  have h2 := (hasDerivAt_Li (Real.one_lt_rpow hu hβ)).comp u h1
  have h3 := (hasDerivAt_Li hu).sub (h2.const_mul (θ : ℝ))
  have h4 := ((hasDerivAt_id u).sub ((h1.div_const β).const_mul (θ : ℝ))).div (Real.hasDerivAt_log hu0.ne') hl.ne'
  have h5 := h3.sub h4
  refine HasDerivAt.congr_deriv (f := fun u => Emain θ β u - mainPsi θ β u / Real.log u) h5 ?_
  simp only [mainPsi, id, Pi.sub_apply]
  rw [Real.log_rpow hu0]
  field_simp
  ring

theorem contOn_w {Y X : ℝ} (hY : 1 < Y) : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2)) (Set.Icc Y X) := by
  intro t ht
  have h1 : 1 < t := lt_of_lt_of_le hY ht.1
  have hl := Real.log_pos h1
  exact (continuousAt_const.div (continuousAt_id.mul ((Real.continuousAt_log (by linarith)).pow 2))
    (mul_ne_zero (by show t ≠ 0; linarith) (pow_ne_zero 2 hl.ne'))).continuousWithinAt

theorem contOn_main (θ : ℤ) (β : ℝ) {Y X : ℝ} (hY : 1 < Y) :
    ContinuousOn (fun t : ℝ => 1 / (t * Real.log t ^ 2) * mainPsi θ β t) (Set.Icc Y X) := by
  refine (contOn_w hY).mul fun t ht => ?_
  have h1 : 1 < t := lt_of_lt_of_le hY ht.1
  exact (continuousAt_id.sub (continuousAt_const.mul
    ((Real.continuousAt_rpow_const t β (Or.inl (by linarith))).div_const β))).continuousWithinAt

theorem integral_main (θ : ℤ) {β Y X : ℝ} (hβ : 0 < β) (hY : 1 < Y) (hYX : Y ≤ X) :
    ∫ t in Y..X, 1 / (t * Real.log t ^ 2) * mainPsi θ β t =
      (Emain θ β X - mainPsi θ β X / Real.log X) - (Emain θ β Y - mainPsi θ β Y / Real.log Y) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => Emain θ β u - mainPsi θ β u / Real.log u)
  · intro t ht
    rw [Set.uIcc_of_le hYX] at ht
    exact (hasDerivAt_diff θ hβ (lt_of_lt_of_le hY ht.1)).congr_deriv (by ring)
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hYX]; exact contOn_main θ β hY

theorem cnt_eq (P : ℕ → Prop) (u : ℝ) :
    cnt P u = ∑ k ∈ Finset.Ioc 0 ⌊u⌋₊, 1 / Real.log k * wt P k := by
  unfold cnt
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold wt
  split_ifs with h
  · have : 0 < Real.log k := Real.log_pos (by exact_mod_cast h.1.one_lt)
    field_simp; simp
  · simp

theorem abel (P : ℕ → Prop) {Y X : ℝ} (hY : 1 < Y) (hYX : Y ≤ X) :
    cnt P X - cnt P Y = (∑ k ∈ Finset.Icc 0 ⌊X⌋₊, wt P k) / Real.log X - (∑ k ∈ Finset.Icc 0 ⌊Y⌋₊, wt P k) / Real.log Y +
      ∫ t in Y..X, 1 / (t * Real.log t ^ 2) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, wt P k := by
  have hd : ∀ t ∈ Set.Icc Y X, HasDerivAt (fun t : ℝ => 1 / Real.log t) (-(1 / (t * Real.log t ^ 2))) t := by
    intro t ht
    have h1 : 1 < t := lt_of_lt_of_le hY ht.1
    have hl := Real.log_pos h1
    refine HasDerivAt.congr_deriv (f := fun t : ℝ => 1 / Real.log t)
      ((hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_log (by linarith : t ≠ 0)) hl.ne') ?_
    field_simp; ring
  have hint : IntegrableOn (deriv fun t : ℝ => 1 / Real.log t) (Set.Icc Y X) :=
    ((contOn_w hY).neg.congr fun t ht => (hd t ht).deriv).integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (wt P) (f := fun t : ℝ => 1 / Real.log t) (by linarith) hYX
    (fun t ht => (hd t ht).differentiableAt) hint
  rw [cnt_eq, cnt_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊Y⌋₊) (Nat.floor_le_floor hYX),
    add_sub_cancel_left, h, intervalIntegral.integral_of_le hYX, sub_eq_add_neg _ (∫ t in _, _), ← integral_neg]
  congr 1
  · ring
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hd t (Set.Ioc_subset_Icc_self ht)).deriv]; ring

theorem core (P : ℕ → Prop) (θ : ℤ) {β φ ρ Y X : ℝ} (hβ : 0 < β) (hY : 1 < Y) (hYX : Y ≤ X)
    (h : ∀ u ∈ Set.Icc Y X, |φ * (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k) - mainPsi θ β u| ≤ ρ * mainPsi θ β u) :
    |φ * (cnt P X - cnt P Y) - (Emain θ β X - Emain θ β Y)| ≤
      ρ * (Emain θ β X - Emain θ β Y + 2 * (mainPsi θ β Y / Real.log Y)) := by
  have hlY := Real.log_pos hY
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have iA : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t ^ 2) * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, wt P k) volume Y X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hYX).2
      (integrableOn_mul_sum_Icc (wt P) (by linarith) (contOn_w hY).integrableOn_Icc)
  have iB : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.log t ^ 2) * mainPsi θ β t) volume Y X :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hYX).2 (contOn_main θ β hY).integrableOn_Icc
  have hw : ∀ t ∈ Set.Icc Y X, 0 ≤ 1 / (t * Real.log t ^ 2) := fun t ht => by
    have : 0 < t := by linarith [ht.1]
    positivity
  have u1 := intervalIntegral.integral_mono_on hYX (iA.const_mul φ) (iB.const_mul (1 + ρ)) fun t ht => by
    have := mul_le_mul_of_nonneg_left (abs_le.1 (h t ht)).2 (hw t ht)
    linarith
  have u2 := intervalIntegral.integral_mono_on hYX (iB.const_mul (1 - ρ)) (iA.const_mul φ) fun t ht => by
    have := mul_le_mul_of_nonneg_left (abs_le.1 (h t ht)).1 (hw t ht)
    linarith
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_main θ hβ hY hYX] at u1 u2
  obtain ⟨x1, x2⟩ := abs_le.1 (h X ⟨hYX, le_rfl⟩)
  obtain ⟨y1, y2⟩ := abs_le.1 (h Y ⟨le_rfl, hYX⟩)
  have x1 := mul_le_mul_of_nonneg_left x1 (inv_pos.2 hlX).le
  have x2 := mul_le_mul_of_nonneg_left x2 (inv_pos.2 hlX).le
  have y1 := mul_le_mul_of_nonneg_left y1 (inv_pos.2 hlY).le
  have y2 := mul_le_mul_of_nonneg_left y2 (inv_pos.2 hlY).le
  rw [abel P hY hYX, abs_le]
  simp only [div_eq_mul_inv] at *
  constructor <;> linarith

theorem psi_sub_wt (P : ℕ → Prop) {u : ℝ} (hu : 1 ≤ u) :
    |(∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k| ≤ 2 * √u * Real.log u := by
  refine le_trans ?_ (Chebyshev.psi_sub_theta_le hu)
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), show wt P 0 = 0 by simp [wt], zero_add,
    show Finset.Icc 1 ⌊u⌋₊ = Finset.Ioc 0 ⌊u⌋₊ from rfl, Finset.sum_filter, ← Finset.sum_sub_distrib,
    Chebyshev.psi, Chebyshev.theta, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have h0 : 0 ≤ Λ n := vonMangoldt_nonneg
  unfold wt
  by_cases hp : n.Prime <;> by_cases hP : P n <;> simp [hp, hP, vonMangoldt_apply_prime, abs_of_nonneg h0, h0]

theorem main_bounds {θ : ℤ} {β δ u : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hδ : 0 < δ) (hδβ : δ ≤ 1 - β)
    (hu : 1 ≤ u) (hl : 4 ≤ Real.log u) : δ * u ≤ mainPsi θ β u ∧ mainPsi θ β u ≤ 3 * u := by
  have hu0 : 0 < u := by linarith
  have hp : 0 < u ^ β := Real.rpow_pos_of_pos hu0 β
  have h1 : u ^ β ≤ u := by
    simpa using Real.rpow_le_rpow_of_exponent_le hu (show β ≤ 1 by linarith)
  have h2 : 0 < u ^ β / β := by positivity
  have h3 : u ^ β / β ≤ 2 * u := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h4 : δ * u ≤ u := by nlinarith
  unfold mainPsi
  rcases hθ with rfl | rfl | rfl
  · simp; constructor <;> linarith
  · have e : u = u ^ β * Real.exp ((1 - β) * Real.log u) := by
      rw [Real.rpow_def_of_pos hu0, ← Real.exp_add]
      rw [show Real.log u * β + (1 - β) * Real.log u = Real.log u by ring, Real.exp_log hu0]
    have h5 : 1 + 4 * (1 - β) ≤ Real.exp ((1 - β) * Real.log u) := by
      have := Real.add_one_le_exp ((1 - β) * Real.log u)
      nlinarith
    have h6 : u ^ β * (1 + 4 * (1 - β)) ≤ u := by
      have := mul_le_mul_of_nonneg_left h5 hp.le
      linarith
    have h7 : u ^ β / β ≤ β * u := by
      rw [div_le_iff₀ (by linarith)]
      have h8 : 1 ≤ (1 + 4 * (1 - β)) * (β * β) := by
        have : 0 ≤ 1 - β := by linarith
        have h9 : 3 / 4 ≤ β * β := by nlinarith
        nlinarith
      have := mul_le_mul_of_nonneg_left h8 hp.le
      have := mul_le_mul_of_nonneg_right h6 (show 0 ≤ β * β by positivity)
      nlinarith
    push_cast
    constructor <;> nlinarith
  · push_cast
    constructor <;> linarith

theorem abs_emain_le {θ : ℤ} {β u : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hβ1 : β ≤ 1)
    (hu : 4 ≤ u) : |Emain θ β u| ≤ 3 * u := by
  have h1 : u ^ β ≤ u := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show 1 ≤ u by linarith) hβ1
  have h2 : 2 ≤ u ^ β := by
    have h3 : u ^ (1 / 2 : ℝ) ≤ u ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have e : (2 : ℝ) ≤ u ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; apply Real.le_sqrt_of_sq_le; linarith
    linarith
  obtain ⟨a1, a2⟩ := li_bounds (x := u) (by linarith)
  obtain ⟨b1, b2⟩ := li_bounds h2
  unfold Emain
  rw [abs_le]
  rcases hθ with rfl | rfl | rfl <;> push_cast <;> constructor <;> linarith

theorem cnt_bounds (P : ℕ → Prop) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ cnt P u ∧ cnt P u ≤ u := by
  refine ⟨Nat.cast_nonneg _, le_trans ?_ (Nat.floor_le hu)⟩
  have := Finset.card_filter_le (Finset.Icc 1 ⌊u⌋₊) (fun p => p.Prime ∧ P p)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  unfold cnt
  exact_mod_cast this

theorem step (P : ℕ → Prop) {θ : ℤ} {β δ φ B ρ s : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hδ : 0 < δ)
    (hδβ : δ ≤ 1 - β) (hB : 3 ≤ B) (hφ : 0 ≤ φ) (hφB : φ ≤ B) (hρ : 0 ≤ ρ) (hs : 64 * B ≤ δ * s)
    (h : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - mainPsi θ β u| ≤ ρ * mainPsi θ β u) :
    0 ≤ Emain θ β (s ^ 16) ∧
      |φ * cnt P (s ^ 16) - Emain θ β (s ^ 16)| ≤ (3 * ρ + 4 / s) * Emain θ β (s ^ 16) := by
  have hs0 : 0 < s := by
    by_contra hc
    nlinarith
  have hsB : 64 * B ≤ s := by nlinarith
  have hs1 : 1 ≤ s := by linarith
  have hls : 1 ≤ Real.log s := by
    rw [Real.le_log_iff_exp_le hs0]; linarith [Real.exp_one_lt_d9]
  have hY : s ≤ s ^ 8 := le_self_pow₀ hs1 (by norm_num)
  have hYX : s ^ 8 ≤ s ^ 16 := pow_le_pow_right₀ hs1 (by norm_num)
  have hlY : 4 ≤ Real.log (s ^ 8) := by rw [Real.log_pow]; push_cast; linarith
  have hm : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16), δ * u ≤ mainPsi θ β u ∧ mainPsi θ β u ≤ 3 * u := fun u hu =>
    main_bounds hθ hβ hδ hδβ (by linarith [hu.1]) (hlY.trans (Real.log_le_log (by positivity) hu.1))
  have h' : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      |φ * (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k) - mainPsi θ β u| ≤ (ρ + 1 / s) * mainPsi θ β u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have k1 := psi_sub_wt P (u := u) (by linarith [hu.1])
    obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ u = r ^ 4 :=
      ⟨√(√u), by positivity, by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by positivity), Real.sq_sqrt hu0.le]⟩
    have hsr : s ^ 2 ≤ r := by
      apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hr0.le
      rw [← hr, ← pow_mul]; exact hu.1
    have k2 : √u = r ^ 2 := by
      rw [hr, show r ^ 4 = (r ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have k3 : Real.log u ≤ 4 * r := by
      rw [hr, Real.log_pow]; push_cast; linarith [Real.log_le_sub_one_of_pos hr0]
    have k4 : 2 * √u * Real.log u ≤ 8 * r ^ 3 := by
      rw [k2]
      have := mul_le_mul_of_nonneg_left k3 (show 0 ≤ 2 * r ^ 2 by positivity)
      linarith
    have k5 : B * (8 * r ^ 3) ≤ 1 / s * (δ * u) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs0, hr]
      have a1 : 8 * B * s ≤ δ * r := by nlinarith
      have := mul_le_mul_of_nonneg_left a1 (show 0 ≤ r ^ 3 by positivity)
      linarith
    have k6 : 1 / s * (δ * u) ≤ 1 / s * mainPsi θ β u := mul_le_mul_of_nonneg_left (hm u hu).1 (by positivity)
    have k7 : |φ * ((∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - ∑ k ∈ Finset.Icc 0 ⌊u⌋₊, wt P k)| ≤ B * (8 * r ^ 3) := by
      rw [abs_mul, abs_of_nonneg hφ]
      exact mul_le_mul hφB (k1.trans k4) (abs_nonneg _) (by linarith)
    have k8 := abs_le.1 (h u hu)
    rw [abs_le] at k7 ⊢
    constructor <;> linarith [k7.1, k7.2, k8.1, k8.2]
  have hc := core P θ (φ := φ) (by linarith : 0 < β) (by linarith) hYX h'
  have hI : 0 ≤ ∫ t in s ^ 8..s ^ 16, 1 / (t * Real.log t ^ 2) * mainPsi θ β t :=
    intervalIntegral.integral_nonneg hYX fun t ht => by
      have : 0 < t := by linarith [ht.1]
      exact mul_nonneg (by positivity) (le_trans (by positivity) (hm t ht).1)
  rw [integral_main θ (by linarith) (by linarith) hYX] at hI
  have e1 := abs_le.1 (abs_emain_le (u := s ^ 8) hθ hβ (by linarith) (by linarith))
  have e2 : mainPsi θ β (s ^ 8) / Real.log (s ^ 8) ≤ s ^ 8 := by
    rw [div_le_iff₀ (by linarith)]
    have := (hm _ ⟨le_rfl, hYX⟩).2
    nlinarith
  have e3 : 8 * s ^ 14 ≤ mainPsi θ β (s ^ 16) / Real.log (s ^ 16) := by
    rw [le_div_iff₀ (Real.log_pos (by linarith)), Real.log_pow]
    have a1 := (hm _ ⟨hYX, le_rfl⟩).1
    have a2 : Real.log s ≤ s := by linarith [Real.log_le_sub_one_of_pos hs0]
    have a3 := mul_le_mul_of_nonneg_left a2 (show 0 ≤ s ^ 14 by positivity)
    have a4 := mul_le_mul_of_nonneg_left (show 128 ≤ δ * s by linarith) (show 0 ≤ s ^ 15 by positivity)
    push_cast
    nlinarith
  have e4 : s ^ 8 ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
  have e5 : s ^ 10 ≤ s ^ 14 := pow_le_pow_right₀ hs1 (by norm_num)
  have e6 : 4 * s ^ 10 ≤ Emain θ β (s ^ 16) := by linarith [e1.1]
  have hY0 : 0 < s ^ 8 := by positivity
  refine ⟨by linarith, ?_⟩
  have e7 : (ρ + 1 / s) * (Emain θ β (s ^ 16) - Emain θ β (s ^ 8) + 2 * (mainPsi θ β (s ^ 8) / Real.log (s ^ 8))) ≤
      (ρ + 1 / s) * (3 * Emain θ β (s ^ 16)) := mul_le_mul_of_nonneg_left (by linarith [e1.1]) (by positivity)
  obtain ⟨c1, c2⟩ := cnt_bounds P hY0.le
  have e8 : φ * cnt P (s ^ 8) ≤ B * s ^ 8 := mul_le_mul hφB c2 c1 (by linarith)
  have e9 : 0 ≤ φ * cnt P (s ^ 8) := mul_nonneg hφ c1
  have e10 : B * s ^ 8 + 3 * s ^ 8 ≤ 1 / s * Emain θ β (s ^ 16) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hs0]
    have := mul_le_mul_of_nonneg_left (show B + 3 ≤ s by linarith) (show 0 ≤ s ^ 9 by positivity)
    have : 0 < s ^ 10 := by positivity
    nlinarith
  have e11 := abs_le.1 (hc.trans e7)
  have e12 : 0 ≤ B * s ^ 8 := by positivity
  rw [abs_le, show 4 / s = 4 * (1 / s) by ring]
  constructor <;> linarith [e11.1, e11.2, e1.1, e1.2]

end GlobalTheory.Lin.PsiToPi

namespace GlobalTheory.Lin

open PsiToPi

theorem pi_rel_of_psi_rel : ∀ c₂ c₃ C cS : ℝ, 0 < c₂ → 0 < c₃ → 0 < C → 0 < cS → ∃ c₂' c₃' C' : ℝ, 0 < c₂' ∧ 0 < c₃' ∧ 0 < C' ∧ ∀ (B φ β : ℝ) (θ : ℤ) (P : ℕ → Prop), 3 ≤ B → 1 ≤ φ → φ ≤ B → (θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ cS / B ^ 3 ≤ 1 - β)) → (∀ u : ℝ, B ^ c₂ ≤ u → |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log B) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β))) → ∀ X : ℝ, B ^ c₂' ≤ X → |φ * (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤ C' * (Real.exp (-c₃' * Real.log X / Real.log B) + Real.exp (-Real.sqrt (c₃' * Real.log X))) * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X := by
  intro c₂ c₃ C cS h2 h3 hC hS
  set c := min cS 1 with hc
  have hc0 : 0 < c := lt_min hS one_pos
  set d := min (c₃ / 2) (1 / 16) with hd
  have hd0 : 0 < d := lt_min (by positivity) (by norm_num)
  have hd1 : d ≤ c₃ / 2 := min_le_left _ _
  have hd2 : d ≤ 1 / 16 := min_le_right _ _
  refine ⟨16 * (c₂ + 4 + 64 / c), d, 3 * C + 4, by positivity, hd0, by positivity, ?_⟩
  intro B φ β θ P hB hφ hφB hθ h X hX
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hlB : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]; linarith [Real.exp_one_lt_d9]
  have hX1 : 1 ≤ X := le_trans (Real.one_le_rpow hB1 (by positivity)) hX
  have hX0 : 0 < X := by linarith
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ X = s ^ 16 :=
    ⟨X ^ ((16 : ℕ) : ℝ)⁻¹, by positivity, (Real.rpow_inv_natCast_pow hX0.le (by norm_num)).symm⟩
  have hs : B ^ (c₂ + 4 + 64 / c) ≤ s := by
    apply le_of_pow_le_pow_left₀ (n := 16) (by norm_num) hs0.le
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0.le, mul_comm]
    exact_mod_cast hX
  have hs1 : 1 ≤ s := le_trans (Real.one_le_rpow hB1 (by positivity)) hs
  have hs2 : B ^ c₂ ≤ s := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 (by
    have : 0 < 64 / c := by positivity
    linarith)) hs
  have hs3 : 64 * B ≤ c / B ^ 3 * s := by
    have a1 : B ^ (4 + 64 / c) ≤ s := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)) hs
    have a2 : 64 / c ≤ B ^ (64 / c) := by
      rw [Real.rpow_def_of_pos hB0]
      have := Real.add_one_le_exp (Real.log B * (64 / c))
      have : 0 < 64 / c := by positivity
      nlinarith
    rw [Real.rpow_add hB0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at a1
    have a3 : B ^ 4 * (64 / c) ≤ s := le_trans (by gcongr) a1
    calc 64 * B = c / B ^ 3 * (B ^ 4 * (64 / c)) := by field_simp
      _ ≤ _ := by gcongr
  have hls : 0 ≤ Real.log s := Real.log_nonneg hs1
  set e := Real.exp (-d * Real.log (s ^ 16) / Real.log B) + Real.exp (-Real.sqrt (d * Real.log (s ^ 16))) with he
  have he0 : 0 < e := by positivity
  have herr : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      Real.exp (-c₃ * Real.log u / Real.log B) + Real.exp (-Real.sqrt (c₃ * Real.log u)) ≤ e := by
    intro u hu
    have a1 : d * Real.log (s ^ 16) ≤ c₃ * Real.log u := by
      have := Real.log_le_log (by positivity) hu.1
      rw [Real.log_pow] at this ⊢
      push_cast at this ⊢
      nlinarith
    refine add_le_add (Real.exp_le_exp.2 ?_) (Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt a1)))
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hse : 1 / s ≤ e := by
    have a1 : 1 / s ≤ Real.exp (-d * Real.log (s ^ 16) / Real.log B) := by
      rw [one_div, ← Real.exp_log hs0, ← Real.exp_neg, Real.exp_log hs0]
      apply Real.exp_le_exp.2
      rw [le_div_iff₀ (by linarith), Real.log_pow]
      push_cast
      nlinarith
    exact a1.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  have key : ∀ β' : ℝ, (θ = 0 ∨ θ = 1 ∨ θ = -1) → 7 / 8 ≤ β' → c / B ^ 3 ≤ 1 - β' →
      (∀ u, mainPsi θ β' u = u - θ * (u ^ β / β)) →
      |φ * cnt P (s ^ 16) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β' (s ^ 16)| ≤ (3 * C + 4) * e * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β' (s ^ 16) := by
    intro β' t1 t2 t3 t4
    have hY : s ≤ s ^ 8 := le_self_pow₀ hs1 (by norm_num)
    obtain ⟨r1, r2⟩ := step P (ρ := C * e) t1 t2 (by positivity) t3 hB (by linarith) hφB (by positivity) hs3 (fun u hu => by
      have hh := h u (by linarith [hu.1])
      rw [← t4 u] at hh
      have h0 : 0 ≤ mainPsi θ β' u := (mul_nonneg_iff_of_pos_left (by positivity)).1 (le_trans (abs_nonneg _) hh)
      exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (herr u hu) hC.le) h0))
    refine r2.trans (mul_le_mul_of_nonneg_right ?_ r1)
    rw [show 4 / s = 4 * (1 / s) by ring]
    linarith
  rcases hθ with rfl | ⟨t1, t2, t3⟩
  · have := key (7 / 8) (Or.inl rfl) le_rfl (by
      rw [div_le_iff₀ (by positivity)]
      have a1 : (3 : ℝ) ^ 3 ≤ B ^ 3 := by gcongr
      have a2 : c ≤ 1 := min_le_right _ _
      linarith) (fun u => by simp [mainPsi])
    simpa [Formalism.HermitianLattices.GL2PrimeSums.Emain, cnt] using this
  · exact key β (Or.inr t1) t2 (le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) t3)
      (fun u => rfl)

end GlobalTheory.Lin
end

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeCount_relative_error_of_psi_relative_error : ∀ c₂ c₃ C cS : ℝ, 0 < c₂ → 0 < c₃ → 0 < C → 0 < cS → ∃ c₂' c₃' C' : ℝ, 0 < c₂' ∧ 0 < c₃' ∧ 0 < C' ∧ ∀ (B φ β : ℝ) (θ : ℤ) (P : ℕ → Prop), 3 ≤ B → 1 ≤ φ → φ ≤ B → (θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ cS / B ^ 3 ≤ 1 - β)) → (∀ u : ℝ, B ^ c₂ ≤ u → |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log B) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β))) → ∀ X : ℝ, B ^ c₂' ≤ X → |φ * (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤ C' * (Real.exp (-c₃' * Real.log X / Real.log B) + Real.exp (-Real.sqrt (c₃' * Real.log X))) * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X := by
  atlas_forward_decl GlobalTheory.Lin.pi_rel_of_psi_rel
end

section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem sign_of_sq_eq_one {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (h : χ ^ 2 = 1) (b : ℕ)
    (hb : Nat.Coprime b M) (θ : ℤ) (hθ : χ (b : ZMod M) = (θ : ℂ)) : θ = 1 ∨ θ = -1 := by
  have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  have h1 : (χ ^ 2) (b : ZMod M) = 1 := by rw [h]; exact MulChar.one_apply hu
  rw [MulChar.pow_apply' χ (by norm_num), hθ] at h1
  have h2 : θ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : (θ - 1) * (θ + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · left; omega
  · right; omega

theorem primesRel_holds : GlobalTheory.Lin.PrimesRel := by
  obtain ⟨a, ha, hA⟩ := GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion
  obtain ⟨a', ha', hA'⟩ := GlobalTheory.T.chebyshevPsiProgression_relative_error
  have hc₁ : 0 < min (1 / 8 : ℝ) (min a a') := lt_min (by norm_num) (lt_min ha ha')
  obtain ⟨c, hc, hE⟩ := hA _ hc₁ ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨c₂, c₃, C, h₂, h₃, hC, hP⟩ := hA' _ hc₁ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨c₂', c₃', C', h₂', h₃', hC', hQ⟩ := GlobalTheory.T.primeCount_relative_error_of_psi_relative_error c₂ c₃ C c h₂ h₃ hC hc
  refine ⟨_, c₂', c₃', C', c, hc₁, min_le_left _ _, h₂', h₃', hC', hc, fun M _ hM => ?_⟩
  obtain ⟨hU, hB, -⟩ := hE M hM
  refine ⟨hU, fun χ β h => (hB χ β h).2.2.2.2, fun b θ β hb hD X hX => ?_⟩
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hφ1 : (1 : ℝ) ≤ (M.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (by omega)
  have hφ2 : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hθ : θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ c / (M : ℝ) ^ 3 ≤ 1 - β) := by
    rcases hD with h | ⟨χ, hχ, hb'⟩
    · exact Or.inl h.1
    · obtain ⟨-, h78, -, -, hS⟩ := hB χ β hχ
      refine Or.inr ⟨sign_of_sq_eq_one χ hχ.1 b hb θ hb', h78, le_trans ?_ hS⟩
      have hl : 0 < Real.log M := Real.log_pos (by linarith)
      have hl2 : Real.log M ≤ M := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      apply div_le_div_of_nonneg_left hc.le (by positivity)
      calc (M : ℝ) ^ 2 * Real.log M ≤ (M : ℝ) ^ 2 * M := by gcongr
        _ = (M : ℝ) ^ 3 := by ring
  have := hQ M M.totient β θ (fun n => n ≡ b [MOD M]) hM3 hφ1 hφ2 hθ
    (fun u hu => by
      have := hP M b θ β u hM hb hD hu
      unfold psiAP at this
      convert this) X hX
  convert this

end GlobalTheory.Lin
end

section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primesInProgressions_relativeError : GlobalTheory.Lin.PrimesRel := by
  first | exact @GlobalTheory.Lin.primesRel_holds | exact GlobalTheory.Lin.primesRel_holds | (intros; apply GlobalTheory.Lin.primesRel_holds <;> assumption)
end
