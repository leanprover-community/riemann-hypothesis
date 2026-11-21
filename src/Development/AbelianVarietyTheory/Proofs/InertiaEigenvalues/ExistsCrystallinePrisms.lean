import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemPPSetCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGenerat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialMulCoeffMemDividedPowerSeriesSubring
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineEvalRingHomFrobeniusTaylor

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem frobTot_mem_SdSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∀ F ∈ SdSet t K e, frobTot K a l F ∈ SdSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF
  obtain ⟨w, hw, hF⟩ := hF
  have hpos : 0 < l := (Fact.out : l.Prime).pos
  refine ⟨fun n => if l ∣ n then
      ((((n / e).factorial / ((n / l) / e).factorial : ℕ) : Wq l a) * sigma l a (w (n / l))) else 0, ?_, ?_⟩
  · intro r
    have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    refine (h.image fun m => l * m).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    split_ifs at hn with hd
    · refine ⟨n / l, ?_, Nat.mul_div_cancel' hd⟩
      intro hr
      apply hn
      obtain ⟨c, hc⟩ := hr
      exact Dvd.dvd.mul_left ⟨sigma l a c, by rw [hc, map_mul, map_pow, map_natCast]⟩ _
    · exact absurd (dvd_zero _) hn
  · intro τ n
    show _ = algebraMap O K (emb t τ (if l ∣ n then _ else 0))
    rw [frobTot_apply, coeff_frob]
    by_cases hd : l ∣ n
    · rw [if_pos hd, if_pos hd]
      obtain ⟨m, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left m hpos]
      have hdiv : (m / e).factorial ∣ (l * m / e).factorial :=
        Nat.factorial_dvd_factorial (Nat.div_le_div_right (Nat.le_mul_of_pos_left m hpos))
      rw [map_mul, map_natCast, emb_sigma, map_mul, map_natCast, ← hF (τ - 1) m, ← mul_assoc, ← Nat.cast_mul,
        Nat.div_mul_cancel hdiv]
    · rw [if_neg hd, if_neg hd]; simp

end GlobalTheory.CrysPrism
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, frobTot K a l F ∈ SdSet t K e := by
  atlas_forward_decl GlobalTheory.CrysPrism.frobTot_mem_SdSet
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.FrobCong

theorem sigma_eq_pow_add (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  have h0 : sigma l a w - w ^ l ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow]
    simp [WittVector.constantCoeff_apply, coeff_sigma]
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 h0
  exact ⟨x, by rw [mul_comm, hx]; ring⟩

end GlobalTheory.FrobCong
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a), ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  atlas_forward_decl GlobalTheory.FrobCong.sigma_eq_pow_add
end

section
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.DpGood

theorem factorial_pow_mul (q : ℕ) : ∀ j : ℕ, ∃ D : ℕ, (j * q).factorial = q.factorial ^ j * D
  | 0 => ⟨1, by simp⟩
  | j + 1 => by
    obtain ⟨D, hD⟩ := factorial_pow_mul q j
    refine ⟨((j + 1) * q).choose q * D, ?_⟩
    have h := Nat.choose_mul_factorial_mul_factorial (show q ≤ (j + 1) * q by nlinarith)
    have h2 : (j + 1) * q - q = j * q := by rw [add_mul, one_mul, Nat.add_sub_cancel]
    rw [h2, hD] at h
    rw [← h]; ring

theorem choose_eq (l q : ℕ) (hl : 1 ≤ l) (hq : 1 ≤ q) :
    (l * q).choose q = l * (l * q - 1).choose (q - 1) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hpos : 0 < l * (q' + 1) := by positivity
  have hn : l * (q' + 1) = (l * (q' + 1) - 1) + 1 := (Nat.succ_pred_eq_of_pos hpos).symm
  have h := Nat.add_one_mul_choose_eq (l * (q' + 1) - 1) q'
  rw [← hn] at h
  simp only [Nat.add_sub_cancel]
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos q')
    (show (l * (q' + 1)).choose (q' + 1) * (q' + 1) = l * (l * (q' + 1) - 1).choose q' * (q' + 1) by
      rw [← h]; ring)

theorem fact_dvd (l q M : ℕ) (hl : 1 ≤ l) (hq : 1 ≤ q) (hM : l * q ≤ M) :
    ∃ G : ℕ, M.factorial = q.factorial ^ l * l * G := by
  obtain ⟨D, hD⟩ := factorial_pow_mul q (l - 1)
  obtain ⟨R, hR⟩ := Nat.factorial_dvd_factorial hM
  have h := Nat.choose_mul_factorial_mul_factorial (show q ≤ l * q by nlinarith)
  have h2 : l * q - q = (l - 1) * q := by rw [Nat.sub_mul, one_mul]
  rw [h2, hD, choose_eq l q hl hq] at h
  refine ⟨(l * q - 1).choose (q - 1) * D * R, ?_⟩
  have hl' : q.factorial ^ l = q.factorial ^ (l - 1) * q.factorial := by
    rw [← pow_succ]; congr 1; omega
  rw [hR, ← h, hl']; ring

theorem key (K : Type) [Field K] [CharZero K] (l : ℕ) (hl : 1 ≤ l) (q M : ℕ) (hM : l * q ≤ M) :
    ∃ c' : K, ∃ k : ℕ, (q.factorial : K)⁻¹ = (q.factorial : K)⁻¹ ^ l + (l : K) * c' ∧
      (M.factorial : K) * c' = k := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact ⟨0, 0, by simp, by simp⟩
  obtain ⟨G, hG⟩ := fact_dvd l q M hl hq hM
  obtain ⟨h, hh⟩ : ∃ h, q.factorial ^ (l - 1) = h + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (pow_pos (Nat.factorial_pos q) _)).symm⟩
  have hG0 : G ≠ 0 := by
    rintro rfl; exact Nat.factorial_ne_zero M (by simpa using hG)
  refine ⟨((G * h : ℕ) : K) / (M.factorial : K), G * h, ?_, ?_⟩
  · have hf : (q.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero q)
    have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hG0' : (G : K) ≠ 0 := Nat.cast_ne_zero.2 hG0
    have hl' : (q.factorial : K) ^ l = ((h : K) + 1) * q.factorial := by
      have : (q.factorial : K) ^ (l - 1) = (h : K) + 1 := by exact_mod_cast hh
      rw [← this, ← pow_succ]; congr 1; omega
    have hh0 : (h : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero h
    rw [hG]; push_cast
    rw [inv_pow, hl']
    field_simp
    ring
  · have hMf : (M.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)
    field_simp

section Mem

variable {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem mono_mem (N : ℕ) (c : K) (k : ℕ) (h : ((N / e).factorial : K) * c = k) :
    (fun _ => monomial N c : ZMod a → K⟦X⟧) ∈ SdSet t K e := by
  refine ⟨fun m => if m = N then (k : Wq l a) else 0, fun r => ?_, fun τ m => ?_⟩
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton N).subset fun m hm => ?_
    by_contra hne
    have hne' : m ≠ N := by simpa using hne
    exact hm (by simp only [if_neg hne']; exact dvd_zero _)
  · rw [coeff_monomial]
    split_ifs with hm
    · subst hm; simp [h]
    · simp [hm]

end Mem

end GlobalTheory.CrysPrism.DpGood

namespace GlobalTheory.CrysPrism

open DpGood in

theorem dpS_frob_good : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ n : ℕ,
    (dpS a e n : ZMod a → K⟦X⟧) ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e,
      frobTot K a l (dpS a e n) = (dpS a e n : ZMod a → K⟦X⟧) ^ l + (l : ZMod a → K⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t n
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  refine ⟨mono_mem t e n _ 1 ?_, ?_⟩
  · rw [Nat.cast_one]; exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have hM : l * (n / e) ≤ l * n / e := by
    rw [Nat.le_div_iff_mul_le (NeZero.pos e), mul_assoc]
    exact Nat.mul_le_mul_left l (Nat.div_mul_le_self n e)
  obtain ⟨c', k, hc, hk⟩ := key K l hl (n / e) (l * n / e) hM
  refine ⟨fun _ => monomial (l * n) c', mono_mem t e (l * n) c' k hk, ?_⟩
  funext τ
  rw [frobTot_apply, Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.natCast_apply]
  simp only [dpS]
  rw [frob, expand_monomial, monomial_pow, ← map_natCast (C : K →+* K⟦X⟧), ← smul_eq_C_mul,
    ← LinearMap.map_smul, ← map_add, mul_comm l n, smul_eq_mul, ← hc]

end GlobalTheory.CrysPrism
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerMonomial_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ n : ℕ, (dpS a e n : ZMod a → K⟦X⟧) ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e, frobTot K a l (dpS a e n) = (dpS a e n : ZMod a → K⟦X⟧) ^ l + (l : ZMod a → K⟦X⟧) * B := by
  atlas_forward_decl GlobalTheory.CrysPrism.dpS_frob_good
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem sdSet_eq_sum_add_mul (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) :
    ∀ F ∈ SdSet t K e, ∃ (N : ℕ) (v : ℕ → Wq l a), ∃ y ∈ SdSet t K e,
      F = ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n + (l : ZMod a → K⟦X⟧) * y := by
  rintro F ⟨w, hw, hF⟩
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : Wq l a) ≠ 0 := by
    have h := WittVector.p_nonzero l (Fq l a)
    exact h
  have h1 := hw 1
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at h1
  obtain ⟨N, hN⟩ := h1
  have h2 : ∀ n, ∃ z : Wq l a, (n < N → z = 0) ∧ (¬ n < N → w n = l * z) := by
    intro n
    by_cases h : n < N
    · exact ⟨0, fun _ => rfl, fun h' => absurd h h'⟩
    · obtain ⟨z, hz⟩ := hN n (not_lt.1 h)
      exact ⟨z, fun h' => absurd h' h, fun _ => by rw [hz, pow_one]⟩
  choose z hz0 hz using h2
  have hfac : ∀ n : ℕ, ((n / e).factorial : K) ≠ 0 := fun n => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  refine ⟨N, w, fun τ => PowerSeries.mk fun n => ((n / e).factorial : K)⁻¹ * algebraMap O K (emb t τ (z n)),
    ⟨z, fun r => ?_, fun τ n => ?_⟩, ?_⟩
  · filter_upwards [hw (r + 1)] with n hn
    by_cases h : n < N
    · rw [hz0 n h]; exact dvd_zero _
    · rw [hz n h, pow_succ'] at hn
      exact (mul_dvd_mul_iff_left hl0).1 hn
  · rw [coeff_mk, mul_inv_cancel_left₀ (hfac n)]
  · funext τ
    ext m
    apply mul_left_cancel₀ (hfac m)
    rw [hF]
    have hc : (l : K⟦X⟧) = C (l : K) := (map_natCast (C : K →+* K⟦X⟧) l).symm
    simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, map_add, map_sum, cstS_apply, dpS,
      hc, coeff_C_mul, coeff_monomial, coeff_mk, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    by_cases h : m < N
    · rw [if_pos h, hz0 m h, map_zero, map_zero]
      field_simp [hfac m]
      ring
    · rw [if_neg h, hz m h, map_mul, map_mul, map_natCast, map_natCast]
      field_simp [hfac m]
      ring

end GlobalTheory.CrysPrism
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerSeriesGeneratorSet_eq_sum_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, ∃ (N : ℕ) (v : ℕ → Wq l a), ∃ y ∈ SdSet t K e, F = ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n + (l : ZMod a → K⟦X⟧) * y := by
  atlas_forward_decl GlobalTheory.CrysPrism.sdSet_eq_sum_add_mul
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem cstS_mem_frob : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ w : Wq l a, cstS t K w ∈ SdSet t K e ∧ frobTot K a l (cstS t K w) = cstS t K (sigma l a w) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t w
  constructor
  · refine ⟨fun n => if n = 0 then w else 0, fun r => ?_, fun τ n => ?_⟩
    · refine (Set.finite_singleton 0).subset fun n hn => ?_
      by_contra h0
      exact hn (by simp [show n ≠ 0 from h0])
    · rw [cstS_apply, coeff_C]
      by_cases hn : n = 0
      · subst hn; simp
      · simp [hn]
  · funext τ
    change frob K l (cstS t K w (τ - 1)) = cstS t K (sigma l a w) τ
    rw [cstS_apply, cstS_apply, emb_sigma, ← PowerSeries.algebraMap_eq (R := K)]
    exact (frob K l).commutes _

theorem frob_sd_congr : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, (frobTot K a l) F ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e, (frobTot K a l) F = F ^ l + (l : ZMod a → K⟦X⟧) * B := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  have hclosed : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := sdSet_closed l a e O K t
  have memS : ∀ {F}, F ∈ SdSet t K e → F ∈ Sd t K e := fun h => Subring.subset_closure h
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  let G : (ZMod a → K⟦X⟧) → Prop := fun z => z ∈ Sd t K e ∧
    ∃ B ∈ Sd t K e, frobTot K a l z = z ^ l + (l : ZMod a → K⟦X⟧) * B
  have gadd : ∀ x y, G x → G y → G (x + y) := by
    rintro x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (⟨x, hx⟩ : Sd t K e) ⟨y, hy⟩
    have hr' := congrArg Subtype.val hr
    push_cast at hr'
    refine ⟨(Sd t K e).add_mem hx hy, Bx + By - x * y * r, ?_, ?_⟩
    · exact (Sd t K e).sub_mem ((Sd t K e).add_mem hBx hBy) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hx hy) r.2)
    · rw [map_add, ex, ey, hr']; ring
  have gmul : ∀ x y, G x → G y → G (x * y) := by
    rintro x y ⟨hx, Bx, hBx, ex⟩ ⟨hy, By, hBy, ey⟩
    refine ⟨(Sd t K e).mul_mem hx hy, Bx * y ^ l + x ^ l * By + (l : ZMod a → K⟦X⟧) * Bx * By, ?_, ?_⟩
    · have hlS : (l : ZMod a → K⟦X⟧) ∈ Sd t K e := natCast_mem (Sd t K e) l
      exact (Sd t K e).add_mem ((Sd t K e).add_mem ((Sd t K e).mul_mem hBx ((Sd t K e).pow_mem hy l))
        ((Sd t K e).mul_mem ((Sd t K e).pow_mem hx l) hBy)) ((Sd t K e).mul_mem ((Sd t K e).mul_mem hlS hBx) hBy)
    · rw [map_mul, ex, ey]; ring
  have gcst : ∀ w, G (cstS t K w) := by
    intro w
    obtain ⟨hm, hf⟩ := cstS_mem_frob l a e O K t w
    obtain ⟨x, hx⟩ := GlobalTheory.T.wittTiltFrobenius_eq_pow_add_mul l a w
    refine ⟨memS hm, cstS t K x, memS (cstS_mem_frob l a e O K t x).1, ?_⟩
    rw [hf, hx, map_add, map_pow, map_mul, map_natCast]
  have gdp : ∀ n, G (dpS a e n) := by
    intro n
    obtain ⟨hm, B, hB, eB⟩ := GlobalTheory.T.dividedPowerMonomial_frobenius_congr_pow l a e O K t n
    exact ⟨memS hm, B, memS hB, eB⟩
  have gsum : ∀ (N : ℕ) (v : ℕ → Wq l a), G (∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n) := by
    intro N v
    refine Finset.sum_induction _ G gadd ⟨(Sd t K e).zero_mem, 0, (Sd t K e).zero_mem, ?_⟩ fun n _ => gmul _ _ (gcst _) (gdp n)
    rw [map_zero, zero_pow hl0, mul_zero, add_zero]
  intro F hF
  refine ⟨GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t F hF, ?_⟩
  obtain ⟨N, v, y, hy, hFe⟩ := GlobalTheory.T.dividedPowerSeriesGeneratorSet_eq_sum_add_mul l a e O K t F hF
  obtain ⟨hg, Bg, hBg, eg⟩ := gsum N v
  set g := ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n
  set L : ZMod a → K⟦X⟧ := (l : ZMod a → K⟦X⟧)
  set Q := ∑ i ∈ Finset.range l, (g + L * y) ^ i * g ^ (l - 1 - i)
  have hQ : Q ∈ Sd t K e := (Sd t K e).sum_mem fun i _ => (Sd t K e).mul_mem
    ((Sd t K e).pow_mem ((Sd t K e).add_mem hg ((Sd t K e).mul_mem (natCast_mem (Sd t K e) l) (memS hy))) i)
    ((Sd t K e).pow_mem hg _)
  have geo : (g + L * y) ^ l = g ^ l + L * (y * Q) := by
    have h := geom_sum₂_mul (g + L * y) g l
    linear_combination -h
  refine ⟨Bg + frobTot K a l y - y * Q, hclosed _ ((Sd t K e).sub_mem ((Sd t K e).add_mem hBg
    (memS (GlobalTheory.T.frobenius_maps_dividedPowerSeriesGeneratorSet l a e O K t y hy))) ((Sd t K e).mul_mem (memS hy) hQ)), ?_⟩
  rw [hFe, map_add, map_mul, map_natCast]
  linear_combination eg - geo

end GlobalTheory.CrysPrism
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ SdSet t K e, (frobTot K a l) F ∈ SdSet t K e ∧ ∃ B ∈ SdSet t K e, (frobTot K a l) F = F ^ l + (l : ZMod a → K⟦X⟧) * B := by
  atlas_forward_decl GlobalTheory.CrysPrism.frob_sd_congr
end

section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
  GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.Compl

theorem smodEq_span_pow {R : Type} [CommRing R] (r x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {r} ^ n • ⊤ : Submodule R R)] ↔ ∃ z, x - y = r ^ n * z := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz, mul_comm]⟩, fun ⟨z, hz⟩ => ⟨z, by rw [hz, mul_comm]⟩⟩

theorem natCast_ne_zero_K (l : ℕ) [Fact l.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] {n : ℕ}
    (hn : n ≠ 0) : (n : K) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[l] K) n]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type)
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (e : ℕ)

def iota (τ : ZMod a) : Wq l a →+* K := (algebraMap O K).comp (emb t τ).toRingHom

variable {K}

theorem iota_injective (τ : ZMod a) : Function.Injective (iota t K τ) := by
  have := Fintype.ofFinite (Fq l a)
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra h0
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  have hu : IsUnit b := WittVector.isUnit_of_coeff_zero_ne_zero b hb
  rw [map_mul, map_pow, map_natCast] at hw
  exact mul_ne_zero (pow_ne_zero _ (natCast_ne_zero_K l (K := K) hl.out.ne_zero)) (hu.map (iota t K τ)).ne_zero hw

include t K in
theorem prime_natCast_ne_zero_wittOfTiltFiniteField : (l : Wq l a) ≠ 0 := fun h => by
  have h1 := congrArg (iota t K 0) h
  rw [map_natCast, map_zero] at h1
  exact natCast_ne_zero_K l (K := K) hl.out.ne_zero h1

variable (K) in

def Rep (F : ZMod a → K⟦X⟧) (w : ℕ → Wq l a) : Prop :=
  ∀ τ n, ((n / e).factorial : K) * coeff n (F τ) = iota t K τ (w n)

variable {t e}

theorem rep_unique {F : ZMod a → K⟦X⟧} {w v : ℕ → Wq l a} (hw : Rep t K e F w) (hv : Rep t K e F v) : w = v :=
  funext fun n => iota_injective t 0 (by rw [← hw 0 n, ← hv 0 n])

theorem eq_of_rep {F G : ZMod a → K⟦X⟧} {w : ℕ → Wq l a} (hF : Rep t K e F w) (hG : Rep t K e G w) : F = G := by
  funext τ
  ext n
  exact mul_left_cancel₀ (natCast_ne_zero_K l (K := K) (Nat.factorial_ne_zero _)) ((hF τ n).trans (hG τ n).symm)

theorem rep_sub {F G : ZMod a → K⟦X⟧} {w v : ℕ → Wq l a} (hF : Rep t K e F w) (hG : Rep t K e G v) :
    Rep t K e (F - G) (w - v) := fun τ n => by
  simp only [Pi.sub_apply, map_sub, mul_sub, hF τ n, hG τ n]

theorem rep_pow_mul (m : ℕ) {F : ZMod a → K⟦X⟧} {w : ℕ → Wq l a} (hF : Rep t K e F w) :
    Rep t K e ((l : ZMod a → K⟦X⟧) ^ m * F) (fun n => (l : Wq l a) ^ m * w n) := fun τ n => by
  have h1 : ((l : ZMod a → K⟦X⟧) ^ m * F) τ = C ((l : K) ^ m) * F τ := by
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, map_pow, map_natCast]
  rw [h1, coeff_C_mul, map_mul, map_pow, map_natCast, ← hF τ n]
  ring

variable (t e) in

def ofRep (w : ℕ → Wq l a) : ZMod a → K⟦X⟧ :=
  fun τ => PowerSeries.mk fun n => iota t K τ (w n) / ((n / e).factorial : K)

theorem rep_ofRep (w : ℕ → Wq l a) : Rep t K e (ofRep (K := K) t e w) w := fun τ n => by
  rw [ofRep, coeff_mk]
  exact mul_div_cancel₀ _ (natCast_ne_zero_K l (K := K) (Nat.factorial_ne_zero _))

variable (t e) in
theorem isHausdorff_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsHausdorff (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  have := Fintype.ofFinite (Fq l a)
  refine ⟨fun x hx => ?_⟩
  obtain ⟨w, -, hw⟩ := hsd x.1 x.2
  have hdiv : ∀ m k, ∃ q, w k = (l : Wq l a) ^ m * q := by
    intro m k
    obtain ⟨z, hz⟩ := (smodEq_span_pow _ _ _ m).1 (hx m)
    rw [sub_zero] at hz
    obtain ⟨v, -, hv⟩ := hsd z.1 z.2
    have h1 : x.1 = (l : ZMod a → K⟦X⟧) ^ m * z.1 := by rw [hz]; push_cast; rfl
    have h2 := rep_pow_mul m hv
    rw [← h1] at h2
    exact ⟨v k, congrFun (rep_unique hw h2) k⟩
  have hw0 : w = 0 := funext fun k => IsHausdorff.haus' (I := Ideal.span {(l : Wq l a)}) (w k) fun m => by
    obtain ⟨q, hq⟩ := hdiv m k
    exact (smodEq_span_pow _ _ _ m).2 ⟨q, by rw [sub_zero, hq]⟩
  apply Subtype.ext
  refine eq_of_rep (F := x.1) (G := 0) hw ?_
  rw [hw0]
  intro τ n
  simp

variable (t e) in
theorem isPrecomplete_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsPrecomplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  have := Fintype.ofFinite (Fq l a)
  refine ⟨fun f hf => ?_⟩
  choose w hw0 hw using fun j => hsd (f j).1 (f j).2
  have hc : ∀ {m j : ℕ}, m ≤ j → ∀ k,
      w m k ≡ w j k [SMOD (Ideal.span {(l : Wq l a)} ^ m • ⊤ : Submodule (Wq l a) (Wq l a))] := by
    intro m j hmj k
    obtain ⟨z, hz⟩ := (smodEq_span_pow _ _ _ m).1 (hf hmj)
    obtain ⟨v, -, hv⟩ := hsd z.1 z.2
    have h1 : (f m).1 - (f j).1 = (l : ZMod a → K⟦X⟧) ^ m * z.1 := by
      have h0 := congrArg Subtype.val hz
      push_cast at h0
      exact h0
    have h2 := rep_pow_mul m hv
    rw [← h1] at h2
    have h3 := congrFun (rep_unique (rep_sub (hw m) (hw j)) h2) k
    exact (smodEq_span_pow _ _ _ m).2 ⟨v k, by simpa using h3⟩
  choose W hW using fun k => IsPrecomplete.prec' (I := Ideal.span {(l : Wq l a)}) (fun j => w j k)
    (fun {m j} h => hc h k)
  have hW0 : LTo0 l W := fun r => (hw0 r r).mono fun k hk => by
    obtain ⟨q, hq⟩ := (smodEq_span_pow _ _ _ r).1 (hW k r)
    have h1 : W k = w r k - (l : Wq l a) ^ r * q := by rw [← hq]; ring
    rw [h1]
    exact dvd_sub hk (dvd_mul_right _ _)
  have hLmem : ofRep (K := K) t e W ∈ Sd t K e := Subring.subset_closure ⟨W, hW0, rep_ofRep W⟩
  refine ⟨⟨_, hLmem⟩, fun n => ?_⟩
  choose v hv using fun k => (smodEq_span_pow _ _ _ n).1 (hW k n)
  have hl0 : (l : Wq l a) ^ n ≠ 0 := pow_ne_zero _ (prime_natCast_ne_zero_wittOfTiltFiniteField t (K := K))
  have hv0 : LTo0 l v := fun r => ((hw0 n (r + n)).and (hW0 (r + n))).mono fun k hk => by
    have h1 : (l : Wq l a) ^ n * (l : Wq l a) ^ r ∣ (l : Wq l a) ^ n * v k := by
      rw [← hv k, ← pow_add, add_comm]
      exact dvd_sub hk.1 hk.2
    exact (mul_dvd_mul_iff_left hl0).1 h1
  have hymem : ofRep (K := K) t e v ∈ Sd t K e := Subring.subset_closure ⟨v, hv0, rep_ofRep v⟩
  refine (smodEq_span_pow _ _ _ n).2 ⟨⟨_, hymem⟩, Subtype.ext ?_⟩
  have h1 := rep_sub (hw n) (rep_ofRep (K := K) (t := t) (e := e) W)
  have h2 := rep_pow_mul n (rep_ofRep (K := K) (t := t) (e := e) v)
  have h3 : (fun k => (l : Wq l a) ^ n * v k) = w n - W := funext fun k => by rw [Pi.sub_apply, hv k]
  rw [h3] at h2
  have h4 := eq_of_rep h1 h2
  push_cast
  exact h4

variable (t e) in

theorem isAdicComplete_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) :=
  { toIsHausdorff := isHausdorff_of t e hsd, toIsPrecomplete := isPrecomplete_of t e hsd }

end GlobalTheory.CrysPrism.Compl
end
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem GlobalTheory.CrysPrism.isAdicComplete_Sd : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  exact GlobalTheory.CrysPrism.Compl.isAdicComplete_of t e (GlobalTheory.T.mem_sdSet_of_mem_sd l a e O K t)
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_dividedPowerSeriesSubring_prime : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  atlas_forward_decl GlobalTheory.CrysPrism.isAdicComplete_Sd
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.CompPP

theorem mem_span_pow_smul_top {R : Type} [CommRing R] (c x : R) (k : ℕ) :
    x ∈ (Ideal.span {c} ^ k • ⊤ : Submodule R R) ↔ c ^ k ∣ x := by
  change x ∈ Ideal.span {c} ^ k • (⊤ : Ideal R) ↔ _
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem natCast_l_ne_zero : (l : Wq l a) ≠ 0 := WittVector.p_nonzero l (Fq l a)

variable (K) in

theorem emb_injective (t : Wq l a →ₐ[ℤ_[l]] O) (τ : ZMod a) :
    Function.Injective fun x : Wq l a => algebraMap O K (emb t τ x) := by
  haveI : Nontrivial O :=
    ⟨⟨0, 1, fun h => one_ne_zero (by simpa using congrArg (algebraMap O K) h.symm : (1 : K) = 0)⟩⟩
  have ht : Function.Injective t := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
    have hu : IsUnit (t (b : Wq l a)) := b.isUnit.map t
    rw [map_mul, map_pow, map_natCast] at hx
    have hlm : (l : O) ^ m = 0 := (hu.mul_left_eq_zero).1 hx
    have h2 : ((l : ℤ_[l]) ^ m) • (1 : O) = 0 := by
      rw [Algebra.smul_def, mul_one, map_pow, map_natCast]; exact hlm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact pow_ne_zero m (Nat.cast_ne_zero.2 hl.out.ne_zero) h3
    · exact one_ne_zero h3
  exact IsUnitBall.inj.comp (ht.comp (sigmaNeg l a τ).injective)

variable (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

def Wit (F : ZMod a → K⟦X⟧⟦X⟧) (w : ℕ × ℕ → Wq l a) : Prop :=
  ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (F τ)) =
      algebraMap O K (emb t τ (w (i, n)))

omit [Module.Free ℤ_[l] O] in
theorem Wit.sub {F G : ZMod a → K⟦X⟧⟦X⟧} {w v : ℕ × ℕ → Wq l a} (hF : Wit t e F w) (hG : Wit t e G v) :
    Wit t e (F - G) (w - v) := by
  intro τ i n
  simp only [Pi.sub_apply, map_sub, mul_sub, hF τ i n, hG τ i n]

omit [Module.Free ℤ_[l] O] in
theorem Wit.zero : Wit t e (0 : ZMod a → K⟦X⟧⟦X⟧) 0 := by
  intro τ i n
  simp

omit [Module.Free ℤ_[l] O] in
theorem Wit.lpow {G : ZMod a → K⟦X⟧⟦X⟧} {v : ℕ × ℕ → Wq l a} (hG : Wit t e G v) (k : ℕ) :
    Wit t e ((l : ZMod a → K⟦X⟧⟦X⟧) ^ k * G) (fun p => (l : Wq l a) ^ k * v p) := by
  intro τ i n
  have h1 : ((l : ZMod a → K⟦X⟧⟦X⟧) ^ k * G) τ = C (C ((l : K) ^ k)) * G τ := by
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, map_pow, map_natCast]
  rw [h1, coeff_C_mul, coeff_C_mul, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
    ← hG τ i n]
  ring

theorem Wit.unique {F : ZMod a → K⟦X⟧⟦X⟧} {w v : ℕ × ℕ → Wq l a} (hw : Wit t e F w) (hv : Wit t e F v) :
    w = v :=
  funext fun p => emb_injective K t 0 ((hw 0 p.1 p.2).symm.trans (hv 0 p.1 p.2))

omit [Module.Free ℤ_[l] O] in
theorem Wit.eq [CharZero K] {F G : ZMod a → K⟦X⟧⟦X⟧} {w : ℕ × ℕ → Wq l a} (hF : Wit t e F w)
    (hG : Wit t e G w) : F = G :=
  funext fun τ => PowerSeries.ext fun i => PowerSeries.ext fun n =>
    mul_left_cancel₀ (Nat.cast_ne_zero.2 (by positivity)) ((hF τ i n).trans (hG τ i n).symm)

variable (K) in

def mkF (v : ℕ × ℕ → Wq l a) : ZMod a → K⟦X⟧⟦X⟧ := fun τ =>
  PowerSeries.mk fun i => PowerSeries.mk fun n =>
    algebraMap O K (emb t τ (v (i, n))) / ((i.factorial * (n / e).factorial : ℕ) : K)

omit [Module.Free ℤ_[l] O] in
theorem wit_mk [CharZero K] (v : ℕ × ℕ → Wq l a) : Wit t e (mkF K t e v) v := by
  intro τ i n
  simp only [mkF, coeff_mk]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (by positivity))

end GlobalTheory.CrysPrism.CompPP

namespace GlobalTheory.CrysPrism.CompPP

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

omit [Module.Free ℤ_[l] O] in

theorem tendsToZeroLAdically_of_eq_prime_pow_mul {u v : ℕ × ℕ → Wq l a} (k : ℕ) (h : ∀ p, u p = (l : Wq l a) ^ k * v p)
    (hu : LTo0 l u) : LTo0 l v := by
  intro r
  filter_upwards [hu (k + r)] with p hp
  rw [h p, pow_add] at hp
  exact (mul_dvd_mul_iff_left (pow_ne_zero k natCast_l_ne_zero)).1 hp

theorem dvd_iff [CharZero K] (hcl : ∀ F ∈ PPd t K e, F ∈ PPSet t K e) (F : ↥(PPd t K e)) (k : ℕ)
    {w : ℕ × ℕ → Wq l a} (hw : Wit t e F.1 w) :
    (l : ↥(PPd t K e)) ^ k ∣ F ↔ ∀ p, (l : Wq l a) ^ k ∣ w p := by
  constructor
  · rintro ⟨G, rfl⟩
    obtain ⟨v, -, hv⟩ := hcl G.1 G.2
    have h1 : Wit t e ((l : ↥(PPd t K e)) ^ k * G).1 (fun p => (l : Wq l a) ^ k * v p) := by
      have := Wit.lpow t e hv k
      simpa using this
    rw [Wit.unique t e hw h1]
    exact fun p => dvd_mul_right _ _
  · intro h
    choose v hv using h
    obtain ⟨w', hw0', hw'⟩ := hcl F.1 F.2
    rw [← Wit.unique t e hw hw'] at hw0'
    have hv0 : LTo0 l v := tendsToZeroLAdically_of_eq_prime_pow_mul k hv hw0'
    refine ⟨⟨mkF K t e v, Subring.subset_closure ⟨v, hv0, wit_mk t e v⟩⟩, Subtype.ext ?_⟩
    have h1 := Wit.lpow t e (wit_mk (K := K) t e v) k
    have h2 : (fun p => (l : Wq l a) ^ k * v p) = w := funext fun p => (hv p).symm
    rw [h2] at h1
    simpa using Wit.eq t e hw h1

theorem complete_of [CharZero K] (hcl : ∀ F ∈ PPd t K e, F ∈ PPSet t K e) :
    IsAdicComplete (Ideal.span {(l : ↥(PPd t K e))}) ↥(PPd t K e) := by
  have hWq : ∀ (x y : Wq l a) (n : ℕ), (x ≡ y [SMOD (Ideal.span {(l : Wq l a)} ^ n • ⊤ : Submodule (Wq l a) (Wq l a))] ↔
      (l : Wq l a) ^ n ∣ x - y) := fun x y n => by
    rw [SModEq.sub_mem, mem_span_pow_smul_top]
  have hPP : ∀ (x y : ↥(PPd t K e)) (n : ℕ), (x ≡ y [SMOD (Ideal.span {(l : ↥(PPd t K e))} ^ n • ⊤ :
      Submodule ↥(PPd t K e) ↥(PPd t K e))] ↔ (l : ↥(PPd t K e)) ^ n ∣ x - y) := fun x y n => by
    rw [SModEq.sub_mem, mem_span_pow_smul_top]
  refine { haus' := fun F hF => ?_, prec' := fun f hf => ?_ }
  · obtain ⟨w, -, hw⟩ := hcl F.1 F.2
    have h0 : w = 0 := funext fun p => IsHausdorff.haus' (I := Ideal.span {(l : Wq l a)}) (w p) fun n =>
      (hWq _ _ n).2 (by
        rw [sub_zero]
        exact (dvd_iff t e hcl F n hw).1 (by simpa using (hPP F 0 n).1 (hF n)) p)
    rw [h0] at hw
    exact Subtype.ext (Wit.eq t e hw (Wit.zero t e))
  · choose W hW0 hW using fun m => hcl (f m).1 (f m).2
    have hd : ∀ {m n : ℕ}, m ≤ n → ∀ p, (l : Wq l a) ^ m ∣ W m p - W n p := fun {m n} hmn p =>
      (dvd_iff t e hcl (f m - f n) m (Wit.sub t e (hW m) (hW n))).1 ((hPP _ _ m).1 (hf hmn)) p
    choose w hw using fun p => IsPrecomplete.prec' (I := Ideal.span {(l : Wq l a)}) (fun m => W m p)
      fun {m n} hmn => (hWq _ _ m).2 (hd hmn p)
    have hw' : ∀ p n, (l : Wq l a) ^ n ∣ W n p - w p := fun p n => (hWq _ _ n).1 (hw p n)
    have hw0 : LTo0 l w := by
      intro r
      filter_upwards [hW0 r r] with p hp
      simpa using dvd_sub hp (hw' p r)
    refine ⟨⟨mkF K t e w, Subring.subset_closure ⟨w, hw0, wit_mk t e w⟩⟩, fun n => (hPP _ _ n).2 ?_⟩
    exact (dvd_iff t e hcl _ n (Wit.sub t e (hW n) (wit_mk t e w))).2 fun p => hw' p n

end GlobalTheory.CrysPrism.CompPP

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism

theorem GlobalTheory.CrysPrism.PPd_isAdicComplete : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(PPd t K e))}) ↥(PPd t K e) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  exact GlobalTheory.CrysPrism.CompPP.complete_of t e (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t)
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_dividedTwoVariableSubring : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(PPd t K e))}) ↥(PPd t K e) := by
  atlas_forward_decl GlobalTheory.CrysPrism.PPd_isAdicComplete
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem frobS_eis_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O),
    ∃ B ∈ SdSet t K e, inclS t K (frobS l a (eis l a e)) = (l : ZMod a → K⟦X⟧) * B := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ _ _ t
  have hlp : l.Prime := hl.out
  have hl0 : (l : K) ≠ 0 := by
    have h : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
    rw [h]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hlp.ne_zero)
  have hle : l * e ≠ 0 := Nat.mul_ne_zero hlp.ne_zero (NeZero.ne e)
  have hf : frobS l a (eis l a e) = X ^ (l * e) + (l : (Wq l a)⟦X⟧) := by
    simp [eis, pow_mul]
  refine ⟨fun _ => 1 + C (l : K)⁻¹ * X ^ (l * e),
    ⟨fun n => if n = 0 then 1 else if n = l * e then (((l - 1).factorial : ℕ) : Wq l a) else 0, ?_, ?_⟩, ?_⟩
  · intro r
    rw [Filter.eventually_cofinite]
    refine (Set.finite_le_nat (l * e)).subset fun n hn => ?_
    by_contra h
    simp only [Set.mem_setOf_eq, not_le] at h
    apply hn
    simp only [show n ≠ 0 by omega, show n ≠ l * e by omega, if_false]
    exact dvd_zero _
  · intro τ n
    rw [map_add, coeff_one, coeff_C_mul, coeff_X_pow]
    by_cases h0 : n = 0
    · subst h0
      simp [hle.symm]
    · by_cases h1 : n = l * e
      · subst h1
        have hfac : (l : K)⁻¹ * (l.factorial : K) = ((l - 1).factorial : K) := by
          rw [← Nat.mul_factorial_pred hlp.ne_zero, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
        simp only [h0, hle, if_false, if_true, zero_add, mul_one, map_natCast]
        rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne e)), mul_comm, hfac]
      · simp [h0, h1]
  · funext τ
    ext n
    rw [inclS_apply, coeff_toAc, hf, Pi.mul_apply, Pi.natCast_apply, ← map_natCast (C : K →+* K⟦X⟧),
      coeff_C_mul, map_add (coeff n) (X ^ (l * e)) (l : (Wq l a)⟦X⟧), map_add (coeff n) (1 : K⟦X⟧), coeff_one, coeff_C_mul, coeff_X_pow, coeff_X_pow,
      ← map_natCast (C : Wq l a →+* (Wq l a)⟦X⟧), coeff_C]
    by_cases h0 : n = 0
    · subst h0
      simp [hle.symm]
    · by_cases h1 : n = l * e
      · subst h1
        simp [h0, hl0]
      · simp [h0, h1]

end GlobalTheory.CrysPrism
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_eisenstein_mem_prime_mul_dividedPowerSeries : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∃ B ∈ SdSet t K e, inclS t K (frobS l a (eis l a e)) = (l : ZMod a → K⟦X⟧) * B := by
  atlas_forward_decl GlobalTheory.CrysPrism.frobS_eis_mem
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

set_option maxHeartbeats 4000000 in

theorem exists_crys_prisms : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∃ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), PP.I = Ideal.span {(l : PP.A)} ∧ δ.comp p₀ = δ.comp p₁ ∧ (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) ∧ (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) ∧ (∀ τ y, j τ (PP.D.φ y) = φ₂ (j (τ - 1) y)) ∧ ∃ hS : ∀ τ y (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e, (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e) ∧ ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), Cr.I = Ideal.span {(l : Cr.A)} → (∀ x, eC (Cr.D.φ x) = frobC l (eC x)) → (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ g : ↥(GK (ϖ.field a)), ∃ ev : GlobalTheory.Prism.Hom PP Cr, ev.comp p₀ = h.comp (ϖ.toAinf a) ∧ ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) ∧ ∀ (y : PP.A) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (ev.f y) - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K fun τ => ⟨_, hS τ y i⟩ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ sh φ₂ hsh hφC hφsh
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hlp : l.Prime := Fact.out
  have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := natCast_ne_zero_ps hlK
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := natCast_ne_zero_ps hl1
  have tf1 : ∀ x : ZMod a → K⟦X⟧, (l : ZMod a → K⟦X⟧) * x = 0 → x = 0 := tf_pi hl1
  have tf2 : ∀ x : ZMod a → K⟦X⟧⟦X⟧, (l : ZMod a → K⟦X⟧⟦X⟧) * x = 0 → x = 0 := tf_pi hl2
  have tfS : ∀ x : ↥(Sd t K e), (l : ↥(Sd t K e)) * x = 0 → x = 0 := tf_sub _ tf1
  have tfP : ∀ x : ↥(PPd t K e), (l : ↥(PPd t K e)) * x = 0 → x = 0 := tf_sub _ tf2
  haveI hcS := GlobalTheory.T.isAdicComplete_dividedPowerSeriesSubring_prime l a e O K t
  haveI hcP := GlobalTheory.T.isAdicComplete_dividedTwoVariableSubring l a e O K t
  have hSd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := GlobalTheory.T.mem_sdSet_of_mem_sd l a e O K t
  have hPd : ∀ F ∈ PPd t K e, F ∈ PPSet t K e := GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t

  let φS : ↥(Sd t K e) →+* ↥(Sd t K e) := (frobTot K a l).toRingHom.restrict (Sd t K e) (Sd t K e)
    fun F hF => Subring.subset_closure (GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F hF)).1
  have hφS : ∀ F : ↥(Sd t K e), ∃ B, φS F = F ^ l + (l : ↥(Sd t K e)) * B := fun F => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.frobTot_mem_SdSet_and_eq_pow_add_mul l a e O K t F (hSd F F.2)).2
    exact ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩
  let DS : Delta l ↥(Sd t K e) := Delta.ofLift l φS tfS hφS
  let φP : ↥(PPd t K e) →+* ↥(PPd t K e) := (frob2 φ₂).restrict (PPd t K e) (PPd t K e)
    fun F hF => Subring.subset_closure (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F hF)).1
  have hφP : ∀ F : ↥(PPd t K e), ∃ B, φP F = F ^ l + (l : ↥(PPd t K e)) * B := fun F => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (hPd F F.2)).2
    exact ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext h⟩
  let DP : Delta l ↥(PPd t K e) := Delta.ofLift l φP tfP hφP

  let i0 : (Wq l a)⟦X⟧ →+* ↥(Sd t K e) := ((inclS t K).comp (frobS l a)).codRestrict (Sd t K e)
    fun x => Subring.subset_closure (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _)
  let iP0 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e) := ((constP a K).comp ((inclS t K).comp (frobS l a))).codRestrict
    (PPd t K e) fun x => Subring.subset_closure (constP_mem t e (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t _))
  let iP1 : (Wq l a)⟦X⟧ →+* ↥(PPd t K e) := ((shP a sh).comp ((inclS t K).comp (frobS l a))).codRestrict
    (PPd t K e) fun x => Subring.subset_closure (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).1
  let dg : ↥(PPd t K e) →+* ↥(Sd t K e) := (diag a K).restrict (PPd t K e) (Sd t K e)
    fun F hF => Subring.subset_closure (diag_mem t e (hPd F hF))
  have hdg0 : ∀ x, dg (iP0 x) = i0 x := fun x => Subtype.ext (funext fun τ => constantCoeff_C _)
  obtain ⟨BE, hBE, hE⟩ := GlobalTheory.T.frobenius_eisenstein_mem_prime_mul_dividedPowerSeries l a e O K t
  have hE0 : i0 (eis l a e) = (l : ↥(Sd t K e)) * ⟨BE, Subring.subset_closure hBE⟩ := Subtype.ext hE
  have hEP0 : iP0 (eis l a e) = (l : ↥(PPd t K e)) * ⟨constP a K BE, Subring.subset_closure (constP_mem t e hBE)⟩ :=
    Subtype.ext (by
      change constP a K (inclS t K (frobS l a (eis l a e))) = _
      rw [hE, map_mul, map_natCast]; rfl)
  have hdiff : ∀ x, iP1 x - iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x => by
    obtain ⟨B, hB, h⟩ := (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).2
    refine Ideal.mem_span_singleton'.2 ⟨⟨B, Subring.subset_closure hB⟩, Subtype.ext ?_⟩
    change B * (l : ZMod a → K⟦X⟧⟦X⟧) = _ - _
    rw [mul_comm]; exact h.symm
  have hmemS : ∀ x ∈ Ideal.span {eis l a e}, i0 x ∈ Ideal.span {(l : ↥(Sd t K e))} := fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hE0]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hmemP0 : ∀ x ∈ Ideal.span {eis l a e}, iP0 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, hEP0]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hmemP1 : ∀ x ∈ Ideal.span {eis l a e}, iP1 x ∈ Ideal.span {(l : ↥(PPd t K e))} := fun x hx => by
    have h := Ideal.add_mem _ (hdiff x) (hmemP0 x hx)
    rwa [sub_add_cancel] at h

  let str0 : ↥(OL (ϖ.field a)) →+* ↥(Sd t K e) ⧸ Ideal.span {(l : ↥(Sd t K e))} :=
    (Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp i0)
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemS x hx)).comp (ϖ.strMap a)
  let strP : ↥(OL (ϖ.field a)) →+* ↥(PPd t K e) ⧸ Ideal.span {(l : ↥(PPd t K e))} :=
    (Ideal.Quotient.lift (Ideal.span {eis l a e}) ((Ideal.Quotient.mk _).comp iP0)
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmemP0 x hx)).comp (ϖ.strMap a)
  let S₀ : Obj l ↥(OL (ϖ.field a)) := Obj.ofDistinguished hlp.pos DS (l : ↥(Sd t K e)) (nzd_of_tf tfS)
    (isUnit_delta_l DS tfS) (by rw [sup_idem]; exact hcS) (bdd_self l) str0
  let PP : Obj l ↥(OL (ϖ.field a)) := Obj.ofDistinguished hlp.pos DP (l : ↥(PPd t K e)) (nzd_of_tf tfP)
    (isUnit_delta_l DP tfP) (by rw [sup_idem]; exact hcP) (bdd_self l) strP

  have hlift : ∀ r : ↥(OL (ϖ.field a)), ∃ x : (Wq l a)⟦X⟧, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r :=
    fun r => Ideal.Quotient.mk_surjective _
  have hstrP : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → strP r = Ideal.Quotient.mk _ (iP0 x) :=
    fun r x h => by simp only [strP, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]
  have hstr0 : ∀ r x, Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r → str0 r = Ideal.Quotient.mk _ (i0 x) :=
    fun r x h => by simp only [str0, RingHom.comp_apply, ← h, Ideal.Quotient.lift_mk]

  let p₀ : GlobalTheory.Prism.Hom (ϖ.prism a) PP :=
    { f := iP0
      f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP0 fun x => Subtype.ext (funext fun τ => by
        change C (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (C (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))
        rw [hφC, frob_toAc])
      f_I := hmemP0
      f_str := fun r x h => (hstrP r x h).symm }
  let p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP :=
    { f := iP1
      f_δ := (deltaS l a).map_δ_of_map_φ DP tfP iP1 fun x => Subtype.ext (funext fun τ => by
        change sh (toAc t K (frobS l a (frobS l a x)) τ : K⟦X⟧) = φ₂ (sh (toAc t K (frobS l a x) (τ - 1) : K⟦X⟧))
        rw [hφsh, frob_toAc])
      f_I := hmemP1
      f_str := fun r x h => by
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) (iP1 x) = strP r
        rw [hstrP r x h, Ideal.Quotient.eq]
        exact hdiff x }
  let δ : GlobalTheory.Prism.Hom PP S₀ :=
    { f := dg
      f_δ := DP.map_δ_of_map_φ DS tfS dg fun y => Subtype.ext (funext fun τ => by
        change constantCoeff (φ₂ (y.1 (τ - 1))) = frob K l (constantCoeff (y.1 (τ - 1)))
        exact constantCoeff_φ₂ sh hsh l φ₂ hφC hφsh _)
      f_I := fun y hy => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
        exact (show ∀ c' : ↥(PPd t K e), dg (c' * (l : ↥(PPd t K e))) ∈ Ideal.span {(l : ↥(Sd t K e))} from
          fun c' => by rw [map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c
      f_str := fun r y h => by
        obtain ⟨x, hx⟩ := hlift r
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at h
        rw [hstrP r x hx] at h
        change Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y) = str0 r
        rw [hstr0 r x hx, ← hdg0]
        exact (show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' =
            Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk (Ideal.span {(l : ↥(Sd t K e))}) (dg y') =
            Ideal.Quotient.mk _ (dg (iP0 x)) from fun y' h' => by
          rw [Ideal.Quotient.eq] at h' ⊢
          rw [← map_sub]
          obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h'
          rw [← hc, map_mul, map_natCast]
          exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y h }
  let j : ZMod a → ↥(PPd t K e) →+* K⟦X⟧⟦X⟧ := fun τ =>
    (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) τ).comp (PPd t K e).subtype
  let j₀ : ZMod a → ↥(Sd t K e) →+* K⟦X⟧ := fun τ =>
    (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ).comp (Sd t K e).subtype
  have hS1 : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e :=
    fun τ y i => GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring l a e O K t y.1 (hPd _ y.2) τ i
  have hS : ∀ τ (y : ↥(PPd t K e)) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e :=
    fun τ y i => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ HasU.X_mem i) (hS1 τ y i)
  refine ⟨PP, S₀, p₀, p₁, δ, j, j₀, rfl, ?_, fun τ y => rfl, fun τ x => ⟨rfl, rfl⟩, fun τ y => rfl, hS, hS1, ?_⟩
  · exact Hom.ext' (RingHom.ext fun x => Subtype.ext (funext fun τ => by
      change constantCoeff (C (toAc t K (frobS l a x) τ : K⟦X⟧)) = constantCoeff (sh (toAc t K (frobS l a x) τ : K⟦X⟧))
      rw [constantCoeff_C, constantCoeff_sh sh hsh]))
  · intro Cr eC h hCI hCφ hh g
    obtain ⟨E, hEa, hEb, hEc, hEd⟩ := GlobalTheory.T.crystallineEval_ringHom_frobenius_taylor l a e O K t ϖ sh hsh φ₂ hφC hφsh g
    have tfC : ∀ x : Cr.A, (l : Cr.A) * x = 0 → x = 0 := fun x hx => eC.injective (by
      have h1 := congrArg eC hx
      rw [map_mul, map_natCast, map_zero] at h1
      rw [map_zero]; exact acris_nat_cancel hlp.ne_zero h1)
    have hev0 : ∀ x, eC.symm (E (iP0 x)) = h.f ((ϖ.toAinf a).f x) := fun x => eC.injective (by
      rw [RingEquiv.apply_symm_apply]; exact (hEa x _).trans (hh _).symm)
    let ev : GlobalTheory.Prism.Hom PP Cr :=
      { f := eC.symm.toRingHom.comp E
        f_δ := DP.map_δ_of_map_φ Cr.D tfC _ fun y => eC.injective (by
          change eC (eC.symm (E (φP y))) = eC (Cr.D.φ (eC.symm (E y)))
          rw [hCφ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
          exact hEc y.1 y.2 _)
        f_I := fun y hy => by
          rw [hCI]
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
          exact (show ∀ c' : ↥(PPd t K e), eC.symm (E (c' * (l : ↥(PPd t K e)))) ∈ Ideal.span {(l : Cr.A)} from
            fun c' => by
              rw [map_mul, map_mul, map_natCast, map_natCast]
              exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) c
        f_str := fun r y hy => by
          obtain ⟨x, hx⟩ := hlift r
          change Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y = strP r at hy
          rw [hstrP r x hx] at hy
          have h2 := (h.comp (ϖ.toAinf a)).f_str r x hx
          change Ideal.Quotient.mk Cr.I (h.f ((ϖ.toAinf a).f x)) = Cr.str r at h2
          rw [← h2, ← hev0]
          exact (show ∀ y' : ↥(PPd t K e), Ideal.Quotient.mk (Ideal.span {(l : ↥(PPd t K e))}) y' =
              Ideal.Quotient.mk _ (iP0 x) → Ideal.Quotient.mk Cr.I (eC.symm (E y')) =
              Ideal.Quotient.mk Cr.I (eC.symm (E (iP0 x))) from fun y' h' => by
            rw [Ideal.Quotient.eq] at h' ⊢
            rw [← map_sub, ← map_sub, hCI]
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h'
            rw [← hc, map_mul, map_mul, map_natCast, map_natCast]
            exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) y hy }
    refine ⟨ev, Hom.ext' (RingHom.ext fun x => hev0 x), Hom.ext' (RingHom.ext fun x => eC.injective ?_), fun y r => ?_⟩
    · change eC (eC.symm (E (iP1 x))) = eC (h.f ((ainfHom (ϖ.field a) g).f ((ϖ.toAinf a).f x)))
      rw [RingEquiv.apply_symm_apply]
      exact (hEb x _).trans (hh _).symm
    · change ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (eC.symm (E y)) - _
      rw [RingEquiv.apply_symm_apply]
      exact hEd y.1 y.2 (hS · y) r

end GlobalTheory.CrysPrism
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystalline_prisms : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∃ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), PP.I = Ideal.span {(l : PP.A)} ∧ δ.comp p₀ = δ.comp p₁ ∧ (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) ∧ (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) ∧ (∀ τ y, j τ (PP.D.φ y) = φ₂ (j (τ - 1) y)) ∧ ∃ hS : ∀ τ y (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (j τ y)) ∈ S O K e, (∀ τ y (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (j τ y) ∈ S O K e) ∧ ∀ (Cr : Obj l ↥(OL (ϖ.field a))) (eC : Cr.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj (ϖ.field a)) Cr), Cr.I = Ideal.span {(l : Cr.A)} → (∀ x, eC (Cr.D.φ x) = frobC l (eC x)) → (∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x)) → ∀ g : ↥(GK (ϖ.field a)), ∃ ev : GlobalTheory.Prism.Hom PP Cr, ev.comp p₀ = h.comp (ϖ.toAinf a) ∧ ev.comp p₁ = (h.comp (ainfHom (ϖ.field a) g)).comp (ϖ.toAinf a) ∧ ∀ (y : PP.A) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] eC (ev.f y) - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K fun τ => ⟨_, hS τ y i⟩ := by
  atlas_forward_decl GlobalTheory.CrysPrism.exists_crys_prisms
end
