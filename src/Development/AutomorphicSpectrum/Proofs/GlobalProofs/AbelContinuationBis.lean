import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PeriodicWeightBounded
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceSummable
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurther
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.WeightSumAsFiniteDifferences

section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity

variable {r : ℕ}

theorem update_add_single (i : Fin r) (m : Fin r → ℕ) (n k : ℕ) :
    Function.update (m + (Pi.single i n : Fin r → ℕ)) i k = Function.update m i k := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_apply, hj, Pi.single_apply]

theorem update_self_add (i : Fin r) (m : Fin r → ℕ) (e : ℕ) :
    Function.update m i (m i + e) = m + (Pi.single i e : Fin r → ℕ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_apply, hj, Pi.single_apply]

theorem partialSum_succ (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    partialSum i v (m + Pi.single i 1) = partialSum i v m + v m := by
  simp only [partialSum, update_add_single, Pi.add_apply, Pi.single_eq_same]
  rw [Finset.sum_range_succ, Function.update_eq_self]

theorem partialSum_of_zero (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (h : m i = 0) :
    partialSum i v m = 0 := by
  simp [partialSum, h]

theorem partialSumMean_add_single_one (l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    meanP l i v (m + Pi.single i 1) = meanP l i v m := by
  simp only [meanP, update_add_single]

theorem partialSum_period {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (h : GoodAt l i v)
    (m : Fin r → ℕ) : partialSum i v (m + Pi.single i l) = partialSum i v m := by
  simp only [partialSum, update_add_single, Pi.add_apply, Pi.single_eq_same]
  rw [Finset.sum_range_add]
  have h2 : ∑ e ∈ Finset.range l, v (Function.update m i (m i + e)) = 0 := by
    simp only [update_self_add]
    exact h.2 m
  rw [h2, add_zero]

theorem partialSum_bound {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (h : GoodAt l i v) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ m, |(v m : ℝ)| ≤ C) :
    ∀ m, |(partialSum i v m : ℝ)| ≤ l * C := by
  have key : ∀ n, ∀ m : Fin r → ℕ, m i = n → |(partialSum i v m : ℝ)| ≤ l * C := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hm
      by_cases hn : n < l
      · simp only [partialSum, hm]
        push_cast
        calc |∑ k ∈ Finset.range n, (v (Function.update m i k) : ℝ)|
            ≤ ∑ k ∈ Finset.range n, |(v (Function.update m i k) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ => hC _
          _ = n * C := by simp
          _ ≤ l * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hn.le) hC0
      · rw [not_lt] at hn
        have hmm : m = Function.update m i (n - l) + Pi.single i l := by
          funext j
          by_cases hj : j = i
          · subst hj
            simp only [Pi.add_apply, Function.update_self, Pi.single_eq_same]
            omega
          · simp [Function.update_apply, hj, Pi.single_apply]
        rw [hmm, partialSum_period h]
        exact ih (n - l) (by omega) _ (by simp)
  exact fun m => key (m i) m rfl

theorem abs_partialSumMean_le {l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    {K : ℝ} (hK : ∀ m, |(partialSum i v m : ℝ)| ≤ K) (m : Fin r → ℕ) :
    |(meanP l i v m : ℝ)| ≤ K := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  simp only [meanP]
  push_cast
  rw [abs_div, abs_of_pos hl', div_le_iff₀ hl']
  calc |∑ k ∈ Finset.range l, (partialSum i v (Function.update m i k) : ℝ)|
      ≤ ∑ k ∈ Finset.range l, |(partialSum i v (Function.update m i k) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range l, K := Finset.sum_le_sum fun k _ => hK _
    _ = K * l := by simp [mul_comm]

theorem summable_cast_mul {α : Type*} (w : α → ℚ) (K : ℝ) (hw : ∀ m, |(w m : ℝ)| ≤ K)
    {g : α → ℂ} (hg : Summable g) : Summable (fun m => (w m : ℂ) * g m) := by
  have hn : Summable (fun m => ‖g m‖) := by
    first
      | exact hg.norm
      | exact summable_norm_iff.mpr hg
  refine Summable.of_norm_bounded (hn.mul_left K) (fun m => ?_)
  rw [norm_mul, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hw m) (norm_nonneg _)

theorem stepIdentity (r l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (g : (Fin r → ℕ) → ℂ)
    (hl : 0 < l) (hgood : GoodAt l i v) (hv : BddW v) (hg : Summable g) :
    ∑' m, (v m : ℂ) * g m = ∑' m, (Bop l i v m : ℂ) * g m - ∑' m, (Aop l i v m : ℂ) * fd i g m := by
  obtain ⟨C, hC⟩ := hv
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hlC : 0 ≤ (l : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC0
  have hPS := partialSum_bound hl hgood hC0 hC
  have hMP : ∀ m, |(meanP l i v m : ℝ)| ≤ l * C := abs_partialSumMean_le hl hPS
  set δ : Fin r → ℕ := Pi.single i 1 with hδ
  have hsub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    simpa only [Real.norm_eq_abs] using norm_sub_le a b
  have hBb : ∀ m, |(Bop l i v m : ℝ)| ≤ l * C := by
    intro m
    unfold Bop
    split_ifs
    · exact hMP m
    · rw [Rat.cast_zero, abs_zero]
      exact hlC
  have hAb : ∀ m, |(Aop l i v m : ℝ)| ≤ 2 * (l * C) := by
    intro m
    simp only [Aop, Rat.cast_sub]
    calc _ ≤ |(partialSum i v (m + Pi.single i 1) : ℝ)| + |(meanP l i v m : ℝ)| := hsub _ _
      _ ≤ l * C + l * C := add_le_add (hPS _) (hMP m)
      _ = _ := by ring
  let T : (Fin r → ℕ) → ℂ := fun m =>
    ((partialSum i v m - meanP l i v m + Bop l i v m : ℚ) : ℂ) * g m
  have hTb : ∀ m, |((partialSum i v m - meanP l i v m + Bop l i v m : ℚ) : ℝ)| ≤ 3 * (l * C) := by
    intro m
    push_cast
    calc _ ≤ |(partialSum i v m : ℝ) - meanP l i v m| + |(Bop l i v m : ℝ)| := abs_add_le _ _
      _ ≤ (|(partialSum i v m : ℝ)| + |(meanP l i v m : ℝ)|) + |(Bop l i v m : ℝ)| :=
          add_le_add (hsub _ _) le_rfl
      _ ≤ (l * C + l * C) + l * C := add_le_add (add_le_add (hPS m) (hMP m)) (hBb m)
      _ = _ := by ring
  have hinj : Function.Injective (fun m : Fin r → ℕ => m + δ) := add_left_injective δ
  have hgs : Summable (fun m => g (m + δ)) := hg.comp_injective hinj
  have hfd : Summable (fd i g) := by
    have : fd i g = fun m => g (m + δ) - g m := rfl
    rw [this]
    exact hgs.sub hg
  have hsB : Summable (fun m => (Bop l i v m : ℂ) * g m) := summable_cast_mul _ _ hBb hg
  have hsA : Summable (fun m => (Aop l i v m : ℂ) * fd i g m) := summable_cast_mul _ _ hAb hfd
  have hsT : Summable T := summable_cast_mul _ _ hTb hg
  have hsT' : Summable (fun m => T (m + δ)) := hsT.comp_injective hinj
  have hT0 : ∀ m, m i = 0 → T m = 0 := by
    intro m hm
    simp [T, Bop, hm, partialSum_of_zero i v m hm]
  have hBs : ∀ m, Bop l i v (m + δ) = 0 := by
    intro m
    simp [Bop, δ]
  have hpt : ∀ m, (v m : ℂ) * g m =
      ((Bop l i v m : ℂ) * g m - (Aop l i v m : ℂ) * fd i g m) + (T (m + δ) - T m) := by
    intro m
    have h1 := partialSum_succ i v m
    have h2 := partialSumMean_add_single_one l i v m
    have h3 : Bop l i v (m + Pi.single i 1) = 0 := hBs m
    simp only [T, Aop, fd, hδ, h1, h2, h3]
    push_cast
    ring
  have hshift : ∑' m, T (m + δ) = ∑' m, T m := by
    refine hinj.tsum_eq (f := T) ?_
    intro m hm
    have hmi : m i ≠ 0 := fun h0 => hm (hT0 m h0)
    refine ⟨m - δ, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.sub_apply, δ, Pi.single_eq_same]
      omega
    · simp [δ, Pi.single_apply, hj]
  calc ∑' m, (v m : ℂ) * g m
      = ∑' m, (((Bop l i v m : ℂ) * g m - (Aop l i v m : ℂ) * fd i g m) + (T (m + δ) - T m)) :=
        tsum_congr hpt
    _ = (∑' m, (Bop l i v m : ℂ) * g m - ∑' m, (Aop l i v m : ℂ) * fd i g m) +
          (∑' m, T (m + δ) - ∑' m, T m) := by
        rw [(hsB.sub hsA).tsum_add (hsT'.sub hsT), hsB.tsum_sub hsA, hsT'.tsum_sub hsT]
    _ = _ := by rw [hshift, sub_self, add_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity
end
end

section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.AopProps

variable {r : ℕ}

lemma update_add_single (i : Fin r) (m : Fin r → ℕ) (t k : ℕ) :
    Function.update (m + (Pi.single i t : Fin r → ℕ)) i k = Function.update m i k := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

lemma add_single_eq_update (i : Fin r) (m : Fin r → ℕ) (t : ℕ) :
    m + (Pi.single i t : Fin r → ℕ) = Function.update m i (m i + t) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

lemma partialSum_update (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (k : ℕ) :
    partialSum i v (Function.update m i k) =
      ∑ j ∈ Finset.range k, v (Function.update m i j) := by
  simp [partialSum]

lemma partialSum_periodic {l : ℕ} (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hv : GoodAt l i v)
    (m : Fin r → ℕ) (k : ℕ) :
    partialSum i v (Function.update m i (k + l)) = partialSum i v (Function.update m i k) := by
  rw [partialSum_update, partialSum_update, Finset.sum_range_add]
  have h := hv.2 (Function.update m i k)
  have h2 : ∑ x ∈ Finset.range l, v (Function.update m i (k + x)) = 0 := by
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_single_eq_update, Function.update_self, Function.update_idem]
  rw [h2, add_zero]

lemma sum_window {l : ℕ} (f : ℕ → ℚ) (hf : ∀ k, f (k + l) = f k) (a : ℕ) :
    ∑ k ∈ Finset.range l, f (a + k) = ∑ k ∈ Finset.range l, f k :=
  _root_.UpperTheory.Reformulated.B.DYdd7.main f hf a

lemma partialSumMean_add_single (l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (t : ℕ) :
    meanP l i v (m + (Pi.single i t : Fin r → ℕ)) = meanP l i v m := by
  simp only [meanP, update_add_single]

lemma partialSum_abs_le (i : Fin r) (v : (Fin r → ℕ) → ℚ) {C : ℝ}
    (hC : ∀ m, |(v m : ℝ)| ≤ C) (m : Fin r → ℕ) (k : ℕ) :
    |((partialSum i v (Function.update m i k) : ℚ) : ℝ)| ≤ k * C := by
  rw [partialSum_update]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ C fun j _ => hC _).trans ?_
  simp

lemma partialSum_bound {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ)
    (hv : GoodAt l i v) {C : ℝ} (hC : ∀ m, |(v m : ℝ)| ≤ C) (m : Fin r → ℕ) :
    |((partialSum i v m : ℚ) : ℝ)| ≤ l * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC m)
  have hper : Function.Periodic (fun k => partialSum i v (Function.update m i k)) l :=
    fun k => partialSum_periodic i v hv m k
  have hmod : partialSum i v m = partialSum i v (Function.update m i (m i % l)) := by
    have h := hper.map_mod_nat (m i)
    simp only [Function.update_eq_self] at h
    exact h.symm
  rw [hmod]
  refine (partialSum_abs_le i v hC m _).trans ?_
  have : ((m i % l : ℕ) : ℝ) ≤ l := by exact_mod_cast (Nat.mod_lt _ hl).le
  exact mul_le_mul_of_nonneg_right this hC0

lemma abs_partialSumMean_le {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ)
    (hv : GoodAt l i v) {C : ℝ} (hC : ∀ m, |(v m : ℝ)| ≤ C) (m : Fin r → ℕ) :
    |((meanP l i v m : ℚ) : ℝ)| ≤ l * C := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  unfold meanP
  push_cast
  rw [abs_div, abs_of_pos hl', div_le_iff₀ hl']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((l : ℝ) * C) fun j _ => ?_).trans ?_
  · exact_mod_cast partialSum_bound hl i v hv hC _
  · simp [mul_comm]

lemma mul_partialSumMean {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) :
    (l : ℚ) * meanP l i v m = ∑ k ∈ Finset.range l, partialSum i v (Function.update m i k) := by
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold meanP
  field_simp

lemma Aop_goodAt {l : ℕ} (hl : 0 < l) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hv : GoodAt l i v) :
    GoodAt l i (Aop l i v) := by
  have hps : ∀ (m : Fin r → ℕ) (t : ℕ), partialSum i v (m + (Pi.single i t : Fin r → ℕ)) =
      partialSum i v (Function.update m i (m i + t)) := fun m t => by
    rw [add_single_eq_update]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · simp only [Aop, partialSumMean_add_single]
    have h1 : m + (Pi.single i l : Fin r → ℕ) + (Pi.single i 1 : Fin r → ℕ) =
        m + (Pi.single i (1 + l) : Fin r → ℕ) := by
      rw [add_assoc, ← Pi.single_add, add_comm l 1]
    rw [h1, hps, hps, ← add_assoc, partialSum_periodic i v hv]
  · have hterm : ∀ e, Aop l i v (m + (Pi.single i e : Fin r → ℕ)) =
        partialSum i v (Function.update m i (m i + 1 + e)) - meanP l i v m := fun e => by
      have h1 : m + (Pi.single i e : Fin r → ℕ) + (Pi.single i 1 : Fin r → ℕ) =
          m + (Pi.single i (1 + e) : Fin r → ℕ) := by
        rw [add_assoc, ← Pi.single_add, add_comm e 1]
      simp only [Aop, partialSumMean_add_single]
      rw [h1, hps, ← add_assoc]
    simp only [hterm]
    rw [Finset.sum_sub_distrib,
      sum_window (fun k => partialSum i v (Function.update m i k))
        (fun k => partialSum_periodic i v hv m k) (m i + 1), ← mul_partialSumMean hl]
    simp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.AopProps

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

open AopProps in

theorem aop_props : ∀ (r l : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ), 0 < l → GoodAt l i v → BddW v →
    BddW (Aop l i v) ∧ BddW (Bop l i v) ∧ GoodAt l i (Aop l i v) := by
  intro r l i v hl hv ⟨C, hC⟩
  refine ⟨⟨l * C + l * C, fun m => ?_⟩, ⟨l * C, fun m => ?_⟩, Aop_goodAt hl i v hv⟩
  · unfold Aop
    push_cast
    exact (abs_sub _ _).trans
      (add_le_add (partialSum_bound hl i v hv hC _) (abs_partialSumMean_le hl i v hv hC _))
  · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC m)
    unfold Bop
    split_ifs
    · exact abs_partialSumMean_le hl i v hv hC m
    · simpa using mul_nonneg (Nat.cast_nonneg l) hC0

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar

variable {r : ℕ}

lemma add_single_apply_ne {i k : Fin r} (h : k ≠ i) (m : Fin r → ℕ) (e : ℕ) :
    (m + (Pi.single k e : Fin r → ℕ)) i = m i := by
  simp [Pi.single_eq_of_ne h.symm]

lemma update_add_single {i k : Fin r} (h : k ≠ i) (m : Fin r → ℕ) (e t : ℕ) :
    Function.update (m + (Pi.single k e : Fin r → ℕ)) i t = Function.update m i t + (Pi.single k e : Fin r → ℕ) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Pi.single_eq_of_ne h.symm]
  · simp [Function.update_of_ne hj]

lemma partialSum_shift {i k : Fin r} (h : k ≠ i) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (e : ℕ) :
    partialSum i v (m + (Pi.single k e : Fin r → ℕ)) =
      ∑ t ∈ Finset.range (m i), v (Function.update m i t + (Pi.single k e : Fin r → ℕ)) := by
  unfold partialSum
  rw [add_single_apply_ne h]
  exact Finset.sum_congr rfl fun t _ => by rw [update_add_single h]

lemma meanP_shift (l : ℕ) {i k : Fin r} (h : k ≠ i) (v : (Fin r → ℕ) → ℚ) (m : Fin r → ℕ) (e : ℕ) :
    meanP l i v (m + (Pi.single k e : Fin r → ℕ)) =
      (∑ t ∈ Finset.range l, partialSum i v (Function.update m i t + (Pi.single k e : Fin r → ℕ))) / l := by
  unfold meanP
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [update_add_single h]

lemma partialSum_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    partialSum i v (m + (Pi.single k l : Fin r → ℕ)) = partialSum i v m := by
  rw [partialSum_shift h]
  unfold partialSum
  exact Finset.sum_congr rfl fun t _ => hp _

lemma meanP_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    meanP l i v (m + (Pi.single k l : Fin r → ℕ)) = meanP l i v m := by
  rw [meanP_shift l h]
  unfold meanP
  congr 1
  exact Finset.sum_congr rfl fun t _ => partialSum_period h hp _

lemma partialSum_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, partialSum i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  simp_rw [partialSum_shift h]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun t _ => hz _

lemma meanP_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, meanP l i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  simp_rw [meanP_shift l h]
  rw [← Finset.sum_div, Finset.sum_comm]
  rw [Finset.sum_eq_zero fun t _ => partialSum_zero h hz _, zero_div]

lemma Aop_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    Aop l i v (m + (Pi.single k l : Fin r → ℕ)) = Aop l i v m := by
  unfold Aop
  rw [add_right_comm, partialSum_period h hp, meanP_period h hp]

lemma Bop_period {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hp : ∀ m, v (m + (Pi.single k l : Fin r → ℕ)) = v m) (m : Fin r → ℕ) :
    Bop l i v (m + (Pi.single k l : Fin r → ℕ)) = Bop l i v m := by
  unfold Bop
  rw [add_single_apply_ne h, meanP_period h hp]

lemma Aop_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, Aop l i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  unfold Aop
  rw [Finset.sum_sub_distrib, meanP_zero h hz, sub_zero]
  simp_rw [add_right_comm m]
  exact partialSum_zero h hz _

lemma Bop_zero {l : ℕ} {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hz : ∀ m, ∑ e ∈ Finset.range l, v (m + (Pi.single k e : Fin r → ℕ)) = 0) (m : Fin r → ℕ) :
    ∑ e ∈ Finset.range l, Bop l i v (m + (Pi.single k e : Fin r → ℕ)) = 0 := by
  unfold Bop
  simp_rw [add_single_apply_ne h]
  by_cases h0 : m i = 0
  · simp only [h0, if_true]
    exact meanP_zero h hz m
  · simp [h0]

lemma partialSum_support {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hs : ∀ m, m k ≠ 0 → v m = 0) (m : Fin r → ℕ) (hm : m k ≠ 0) : partialSum i v m = 0 := by
  unfold partialSum
  refine Finset.sum_eq_zero fun t _ => hs _ ?_
  rwa [Function.update_of_ne h]

lemma meanP_support (l : ℕ) {i k : Fin r} (h : k ≠ i) {v : (Fin r → ℕ) → ℚ}
    (hs : ∀ m, m k ≠ 0 → v m = 0) (m : Fin r → ℕ) (hm : m k ≠ 0) : meanP l i v m = 0 := by
  unfold meanP
  rw [Finset.sum_eq_zero fun t _ => partialSum_support h hs _ (by rwa [Function.update_of_ne h]), zero_div]

theorem good_support_other (r l : ℕ) (i k : Fin r) (v : (Fin r → ℕ) → ℚ) (h : k ≠ i) :
    (GoodAt l k v → GoodAt l k (Aop l i v) ∧ GoodAt l k (Bop l i v)) ∧
    ((∀ m, m k ≠ 0 → v m = 0) → (∀ m, m k ≠ 0 → Aop l i v m = 0) ∧ (∀ m, m k ≠ 0 → Bop l i v m = 0)) := by
  refine ⟨fun hg => ⟨⟨Aop_period h hg.1, Aop_zero h hg.2⟩, ⟨Bop_period h hg.1, Bop_zero h hg.2⟩⟩, fun hs => ⟨fun m hm => ?_, fun m hm => ?_⟩⟩
  · unfold Aop
    rw [partialSum_support h hs _ (by simpa [Pi.single_eq_of_ne h] using hm), meanP_support l h hs m hm, sub_zero]
  · unfold Bop
    rw [meanP_support l h hs m hm, ite_self]

theorem otherVar_main : ∀ (r l : ℕ) (i k : Fin r) (v : (Fin r → ℕ) → ℚ), k ≠ i →
    (GoodAt l k v → GoodAt l k (Aop l i v) ∧ GoodAt l k (Bop l i v)) ∧
    ((∀ m, m k ≠ 0 → v m = 0) → (∀ m, m k ≠ 0 → Aop l i v m = 0) ∧ (∀ m, m k ≠ 0 → Bop l i v m = 0)) :=
  fun r l i k v h => good_support_other r l i k v h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OneVar

theorem goodAt_smul {r l : ℕ} {k : Fin r} {v : (Fin r → ℕ) → ℚ} (s : ℚ) (h : GoodAt l k v) :
    GoodAt l k (fun m => s * v m) := by
  refine ⟨fun m => by simp only [h.1 m], fun m => ?_⟩
  rw [← Finset.mul_sum, h.2 m, mul_zero]

theorem bddW_sign {r : ℕ} {v : (Fin r → ℕ) → ℚ} (c : ℕ) (h : BddW v) :
    BddW (fun m => (-1 : ℚ) ^ c * v m) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun m => ?_⟩
  have : |(((-1 : ℚ) ^ c * v m : ℚ) : ℝ)| = |(v m : ℝ)| := by
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [this]
  exact hC m

theorem iterate_good_bdd {r l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (hg : GoodAt l i v) (hb : BddW v) (c : ℕ) :
    GoodAt l i ((Aop l i)^[c] v) ∧ BddW ((Aop l i)^[c] v) := by
  induction c with
  | zero => exact ⟨hg, hb⟩
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    have := @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl ih.1 ih.2
    exact ⟨this.2.2, this.1⟩

theorem iterate_good_other {r l : ℕ} {i k : Fin r} {v : (Fin r → ℕ) → ℚ} (hk : k ≠ i)
    (hg : GoodAt l k v) (c : ℕ) : GoodAt l k ((Aop l i)^[c] v) := by
  induction c with
  | zero => exact hg
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact (((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 ih).1)

theorem iterate_supp_other {r l : ℕ} {i k : Fin r} {v : (Fin r → ℕ) → ℚ} (hk : k ≠ i)
    (hs : ∀ m, m k ≠ 0 → v m = 0) (c : ℕ) : ∀ m, m k ≠ 0 → (Aop l i)^[c] v m = 0 := by
  induction c with
  | zero => exact hs
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact (((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 ih).1)

theorem DL_replicate_succ {r : ℕ} (i : Fin r) (c : ℕ) (g : (Fin r → ℕ) → ℂ) :
    DL (List.replicate (c + 1) i) g = fd i (DL (List.replicate c i) g) := by
  simp [DL, List.replicate_succ]

theorem tsum_iterate {r l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (hg : GoodAt l i v) (hb : BddW v) {g : (Fin r → ℕ) → ℂ} (hs : Summable g) (N : ℕ) :
    ∑' m, (v m : ℂ) * g m =
      ∑ c ∈ Finset.range N, (-1 : ℂ) ^ c *
          ∑' m, (Bop l i ((Aop l i)^[c] v) m : ℂ) * DL (List.replicate c i) g m +
        (-1 : ℂ) ^ N * ∑' m, ((Aop l i)^[N] v m : ℂ) * DL (List.replicate N i) g m := by
  induction N with
  | zero => simp [DL]
  | succ N ih =>
    have hN := iterate_good_bdd hl hg hb N
    have key := @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity.stepIdentity r l i ((Aop l i)^[N] v) (DL (List.replicate N i) g) hl hN.1 hN.2
      (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r _ g hs)
    rw [ih, key, Finset.sum_range_succ, Function.iterate_succ_apply', DL_replicate_succ, pow_succ]
    ring

def uW {r : ℕ} (l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (c : ℕ) : (Fin r → ℕ) → ℚ :=
  if c < N then fun m => (-1 : ℚ) ^ c * Bop l i ((Aop l i)^[c] v) m
  else fun m => (-1 : ℚ) ^ N * (Aop l i)^[N] v m

theorem abel_oneVar : ∀ (r l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ), 0 < l → GoodAt l i v → BddW v →
  ∃ u : Fin (N + 1) → (Fin r → ℕ) → ℚ, (∀ c, BddW (u c)) ∧
    (∀ c : Fin (N + 1), (c : ℕ) = N ∨ ∀ m, m i ≠ 0 → u c m = 0) ∧
    (∀ c k, k ≠ i → GoodAt l k v → GoodAt l k (u c)) ∧
    (∀ c k, k ≠ i → (∀ m, m k ≠ 0 → v m = 0) → ∀ m, m k ≠ 0 → u c m = 0) ∧
    ∀ g : (Fin r → ℕ) → ℂ, Summable g →
      ∑' m, (v m : ℂ) * g m = ∑ c, ∑' m, (u c m : ℂ) * DL (List.replicate (c : ℕ) i) g m := by
  intro r l N i v hl hg hb
  refine ⟨fun c => uW l N i v c, fun c => ?_, fun c => ?_, fun c k hk hgk => ?_,
    fun c k hk hsk => ?_, fun g hs => ?_⟩
  · unfold uW
    beta_reduce
    split_ifs with h
    · have hc := iterate_good_bdd hl hg hb c
      exact bddW_sign _ (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl hc.1 hc.2).2.1
    · exact bddW_sign _ (iterate_good_bdd hl hg hb N).2
  · by_cases h : (c : ℕ) < N
    · refine Or.inr fun m hm => ?_
      simp [uW, h, Bop, hm]
    · exact Or.inl (by have := c.isLt; omega)
  · unfold uW
    beta_reduce
    split_ifs with h
    · exact goodAt_smul _ ((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 (iterate_good_other hk hgk c)).2
    · exact goodAt_smul _ (iterate_good_other hk hgk N)
  · intro m hm
    unfold uW
    beta_reduce
    split_ifs with h
    · simp [((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 (iterate_supp_other hk hsk c)).2 m hm]
    · simp [iterate_supp_other hk hsk N m hm]
  · rw [tsum_iterate hl hg hb hs N, Fin.sum_univ_castSucc, Finset.sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hc : (c : ℕ) < N := c.isLt
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [uW, hc, mul_assoc]
    · rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [uW, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OneVar
end
end

section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem expansion_on_finset (r l N : ℕ) (w : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hw : GoodWeight l w)
    (I : Finset (Fin r)) :
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ),
      (∀ q, BddW (u q)) ∧ (∀ q i, i ∉ I → GoodAt l i (u q) ∧ (cs q).count i = 0) ∧
      (∀ q i, i ∈ I → (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => w,
      fun _ => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic r l w hl (fun i m => hw.1 m i),
      fun _ i _ => ⟨⟨fun m => hw.1 m i, fun m => hw.2 m i⟩, by simp⟩,
      fun _ i hi => absurd hi (by simp), fun g _ => by simp [DL]⟩
  | insert a I ha ih =>
    obtain ⟨Q, _, cs, u, hb, hg, hs, hid⟩ := ih
    choose u' h1 h2 h3 h4 h5 using
      fun q => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OneVar.abel_oneVar r l N a (u q) hl (hg q a ha).1 (hb q)
    refine ⟨Q × Fin (N + 1), inferInstance, fun p => List.replicate (p.2 : ℕ) a ++ cs p.1,
      fun p => u' p.1 p.2, fun p => h1 p.1 p.2, ?_, ?_, ?_⟩
    · rintro ⟨q, c⟩ k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkI : k ∉ I := fun h => hk (Finset.mem_insert_of_mem h)
      refine ⟨h3 q c k hka (hg q k hkI).1, ?_⟩
      simp [List.count_append, List.count_replicate, (hg q k hkI).2, hka.symm]
    · rintro ⟨q, c⟩ k hk
      by_cases hka : k = a
      · subst hka
        have h0 : (cs q).count k = 0 := (hg q k ha).2
        rcases h2 q c with h | h
        · left
          simp [List.count_append, h0, h]
        · exact Or.inr h
      · have hkI : k ∈ I := (Finset.mem_insert.1 hk).resolve_left hka
        have hak : a ≠ k := fun h => hka h.symm
        rcases hs q k hkI with h | h
        · left
          simp [List.count_append, List.count_replicate, hak, h]
        · exact Or.inr (h4 q c k hka h)
    · intro g hgs
      rw [hid g hgs, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [h5 q _ (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r (cs q) g hgs)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [DL, List.foldr_append]

theorem expansion_all_variables : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w →
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ),
      (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  intro r l N w hl hw
  obtain ⟨Q, iQ, cs, u, hb, -, hs, hid⟩ := expansion_on_finset r l N w hl hw Finset.univ
  exact ⟨Q, iQ, cs, u, hb, fun q i => hs q i (Finset.mem_univ i), hid⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_weight_bounded : ∀ (r l : ℕ) (v : (Fin r → ℕ) → ℚ), 0 < l → (∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) → BddW v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic <;> assumption)
end

section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_sum_as_finite_differences : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w →
  ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ),
    (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
    ∀ g : (Fin r → ℕ) → ℂ, Summable g → ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.expansion_all_variables
end

section
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem summable_prod_fin {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) (r : ℕ) :
    Summable (fun m : Fin r → ℕ => ∏ i, f (m i)) := by
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have h2 := Summable.mul_of_nonneg hf ih (fun n => h0 n)
      (fun m => Finset.prod_nonneg fun i _ => h0 (m i))
    rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).summable_iff]
    convert h2 using 1
    funext x
    simp [Fin.consEquiv, Fin.prod_univ_succ]

private theorem exists_pos_lower_bound_of_forall_pos {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) :
    ∃ c : ℝ, 0 < c ∧ (∀ j, c ≤ b j) ∧ ∀ j i, c ≤ a j i := by
  classical
  let T : Finset ℝ := Finset.univ.image b ∪ Finset.univ.image (fun p : ι × Fin r => a p.1 p.2)
  by_cases hT : T.Nonempty
  · refine ⟨T.min' hT, ?_, fun j => T.min'_le _ ?_, fun j i => T.min'_le _ ?_⟩
    · have h := T.min'_mem hT
      simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
      rcases h with ⟨j, hj⟩ | ⟨⟨j, i⟩, hj⟩
      · rw [← hj]; exact hb j
      · rw [← hj]; exact ha j i
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨j, rfl⟩
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨(j, i), rfl⟩
  · refine ⟨1, one_pos, fun j => ?_, fun j i => ?_⟩
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT

theorem coneTerm_summable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ),
    r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re →
    Summable (coneTerm a b s) := by
  intro ι _ r a b hr ha hb s hs
  obtain ⟨c, hc0, hcb, hca⟩ := exists_pos_lower_bound_of_forall_pos a b ha hb
  have hσ0 : 0 < s.re := by linarith
  have hf : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-s.re)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hC : 0 ≤ (c ^ (-s.re)) ^ Fintype.card ι := pow_nonneg (Real.rpow_nonneg hc0.le _) _
  have hg := (summable_prod_fin hf (fun k => Real.rpow_nonneg (by positivity) _) r).mul_left
    ((c ^ (-s.re)) ^ Fintype.card ι)
  have key : ∀ {x y : ℝ}, 0 < x → x ≤ y → y ^ (-s.re) ≤ x ^ (-s.re) := fun hx hxy => by
    rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy hσ0.le)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hg)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ i, (m i : ℝ) := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, (m i : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (m i))
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith
  have hS0 : 0 < S := by linarith
  have hL : ∀ j, c * S ≤ b j + ∑ i, a j i * (m i : ℝ) := by
    intro j
    rw [hSdef, mul_add, mul_one, Finset.mul_sum]
    apply add_le_add (hcb j)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hca j i) (Nat.cast_nonneg _)
  have hLpos : ∀ j, 0 < b j + ∑ i, a j i * (m i : ℝ) := fun j => lt_of_lt_of_le (mul_pos hc0 hS0) (hL j)
  have hv1 : S ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hS1 (by linarith)
  have hv0 : 0 ≤ S ^ (-s.re) := Real.rpow_nonneg hS0.le _
  calc ‖coneTerm a b s m‖ = ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ (-s.re) := by
        rw [coneTerm, norm_prod]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hLpos j), Complex.neg_re]
    _ ≤ ∏ _j : ι, (c * S) ^ (-s.re) :=
        Finset.prod_le_prod (fun j _ => Real.rpow_nonneg (hLpos j).le _)
          (fun j _ => key (mul_pos hc0 hS0) (hL j))
    _ = (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ, Real.mul_rpow hc0.le hS0.le, mul_pow]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hv0 hv1 hr) hC
    _ = (c ^ (-s.re)) ^ Fintype.card ι * ∏ _i : Fin r, S ^ (-s.re) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * ∏ i, ((m i : ℝ) + 1) ^ (-s.re) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.prod_le_prod (fun i _ => hv0)
        intro i _
        apply key (by positivity)
        have hi : (m i : ℝ) ≤ ∑ k, (m k : ℝ) :=
          Finset.single_le_sum (fun k _ => Nat.cast_nonneg (m k)) (Finset.mem_univ i)
        rw [hSdef]
        linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_summable_right_half_plane : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re → Summable (coneTerm a b s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

def LineDeg {r : ℕ} (i : Fin r) (d : ℕ) (g : (Fin r → ℕ) → ℂ) : Prop :=
  ∀ m : Fin r → ℕ, ∃ q : Polynomial ℂ, q.degree < (d : WithBot ℕ) ∧
    ∀ t : ℕ, g (m + t • (Pi.single i 1 : Fin r → ℕ)) = q.eval (t : ℂ)

theorem degree_shift_sub_lt (q : Polynomial ℂ) (d : ℕ) (hq : q.degree < ((d + 1 : ℕ) : WithBot ℕ)) :
    (q.comp (Polynomial.X + 1) - q).degree < (d : WithBot ℕ) := by
  by_cases h0 : q.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    simp
  · have hq0 : q ≠ 0 := fun h => h0 (by simp [h])
    have hX : (Polynomial.X + 1 : Polynomial ℂ).natDegree = 1 := Polynomial.natDegree_X_add_C 1
    have hnat : (q.comp (Polynomial.X + 1)).natDegree = q.natDegree := by
      rw [Polynomial.natDegree_comp, hX, mul_one]
    have hlc : (q.comp (Polynomial.X + 1)).leadingCoeff = q.leadingCoeff := by
      have hm : (Polynomial.X + 1 : Polynomial ℂ).Monic := Polynomial.monic_X_add_C 1
      rw [Polynomial.leadingCoeff_comp (by rw [hX]; exact one_ne_zero), hm.leadingCoeff, one_pow, mul_one]
    have hp0 : q.comp (Polynomial.X + 1) ≠ 0 := by
      intro h
      apply hq0
      rw [← Polynomial.leadingCoeff_eq_zero, ← hlc, h, Polynomial.leadingCoeff_zero]
    have hdeg : (q.comp (Polynomial.X + 1)).degree = q.degree := by
      rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0, hnat]
    have hlt := Polynomial.degree_sub_lt hdeg hp0 hlc
    rw [hdeg, Polynomial.degree_eq_natDegree hq0] at hlt
    rw [Polynomial.degree_eq_natDegree hq0] at hq
    have h1 : q.natDegree < d + 1 := by exact_mod_cast hq
    have h2 : q.natDegree ≤ d := Nat.lt_succ_iff.mp h1
    exact lt_of_lt_of_le hlt (by exact_mod_cast h2)

theorem LineDeg.fd_self {r : ℕ} {i : Fin r} {d : ℕ} {g : (Fin r → ℕ) → ℂ}
    (h : LineDeg i (d + 1) g) : LineDeg i d (fd i g) := by
  intro m
  obtain ⟨q, hq, hg⟩ := h m
  refine ⟨q.comp (Polynomial.X + 1) - q, degree_shift_sub_lt q d hq, fun t => ?_⟩
  have e1 : m + t • (Pi.single i 1 : Fin r → ℕ) + Pi.single i 1 =
      m + (t + 1) • (Pi.single i 1 : Fin r → ℕ) := by
    rw [add_smul, one_smul, add_assoc]
  simp only [fd]
  rw [e1, hg, hg, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Nat.cast_add, Nat.cast_one]

theorem LineDeg.fd_any {r : ℕ} {i : Fin r} {d : ℕ} {g : (Fin r → ℕ) → ℂ} (k : Fin r)
    (h : LineDeg i d g) : LineDeg i d (fd k g) := by
  intro m
  obtain ⟨q₁, hq₁, hg₁⟩ := h (m + Pi.single k 1)
  obtain ⟨q₂, hq₂, hg₂⟩ := h m
  refine ⟨q₁ - q₂, lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hq₁ hq₂), fun t => ?_⟩
  simp only [fd]
  rw [add_right_comm, hg₁, hg₂, Polynomial.eval_sub]

theorem LineDeg.eq_zero {r : ℕ} {i : Fin r} {g : (Fin r → ℕ) → ℂ}
    (h : LineDeg i 0 g) (m : Fin r → ℕ) : g m = 0 := by
  obtain ⟨q, hq, hg⟩ := h m
  have hq0 : q = 0 := by
    by_contra hne
    rw [Polynomial.degree_eq_natDegree hne] at hq
    have : q.natDegree < 0 := by exact_mod_cast hq
    omega
  have := hg 0
  simp only [zero_smul, add_zero, hq0, Polynomial.eval_zero] at this
  exact this

theorem LineDeg.DL {r : ℕ} {i : Fin r} {d : ℕ} {g : (Fin r → ℕ) → ℂ} (h : LineDeg i d g)
    (cs : List (Fin r)) : LineDeg i (d - cs.count i) (DL cs g) := by
  induction cs with
  | nil => simpa [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL] using h
  | cons c cs ih =>
    have e : GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL (c :: cs) g = fd c (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL cs g) := rfl
    rw [e]
    by_cases hc : c = i
    · rw [hc, List.count_cons_self]
      rcases Nat.eq_zero_or_pos (d - cs.count i) with h0 | hpos
      · have h3 : d - (cs.count i + 1) = 0 := by omega
        rw [h3]
        rw [h0] at ih
        exact ih.fd_any i
      · obtain ⟨e', he⟩ : ∃ e', d - cs.count i = e' + 1 := ⟨d - cs.count i - 1, by omega⟩
        have h3 : d - (cs.count i + 1) = e' := by omega
        rw [h3]
        rw [he] at ih
        exact ih.fd_self
    · have h3 : (c :: cs).count i = cs.count i := by simp [List.count_cons, hc]
      rw [h3]
      exact ih.fd_any c

theorem lineDeg_coneTerm (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (i : Fin r)
    (p : ℕ) : LineDeg i (Fintype.card ι * p + 1) (coneTerm a b (-(p : ℂ))) := by
  classical
  intro m
  let c : ι → ℂ := fun j => ((b j + ∑ k, a j k * (m k : ℝ) : ℝ) : ℂ)
  refine ⟨∏ j, (Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)) ^ p, ?_, fun t => ?_⟩
  · have hnd : (∏ j, (Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)) ^ p).natDegree ≤
        Fintype.card ι * p := by
      have hj : ∀ j, ((Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)) ^ p).natDegree ≤ p := by
        intro j
        calc _ ≤ p * (Polynomial.C ((a j i : ℝ) : ℂ) * Polynomial.X + Polynomial.C (c j)).natDegree :=
              Polynomial.natDegree_pow_le
          _ ≤ p * 1 := Nat.mul_le_mul_left _ Polynomial.natDegree_linear_le
          _ = p := mul_one p
      refine (Polynomial.natDegree_prod_le _ _).trans ((Finset.sum_le_sum fun j _ => hj j).trans ?_)
      simp
    calc _ ≤ _ := Polynomial.degree_le_natDegree
      _ < _ := by exact_mod_cast Nat.lt_succ_of_le hnd
  · rw [Polynomial.eval_prod]
    simp only [coneTerm, neg_neg, Complex.cpow_natCast, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    simp only [c, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero, mul_add, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    push_cast
    ring

theorem DL_coneTerm_neg_natCast_eq_zero : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (cs : List (Fin r)) (i : Fin r) (N p : ℕ), cs.count i = N → Fintype.card ι * p < N →
  ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = 0 := by
  intro ι _ r a b cs i N p hN hlt m
  have h := (lineDeg_coneTerm ι r a b i p).DL cs
  rw [hN, show Fintype.card ι * p + 1 - N = 0 by omega] at h
  exact h.eq_zero m

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.high_difference_vanishes_negative_integer : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (cs : List (Fin r)) (i : Fin r) (N p : ℕ), cs.count i = N → Fintype.card ι * p < N →
  ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero
end

section
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem DL_coneTerm_neg_nat_rational :
    ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ), (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∀ cs : List (Fin r), ∃ ρ : (Fin r → ℕ) → ℚ, ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = (ρ m : ℂ) := by
  intro ι _ r a b p h cs
  induction cs with
  | nil =>
    choose q hq using h
    refine ⟨q, fun m => ?_⟩
    show GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm a b (-(p : ℂ)) m = _
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm, neg_neg, Complex.cpow_natCast]
    rw [← Complex.ofReal_ratCast, ← hq m]
    simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  | cons c cs ih =>
    obtain ⟨ρ, hρ⟩ := ih
    refine ⟨fun m => ρ (m + Pi.single c 1) - ρ m, fun m => ?_⟩
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL, List.foldr_cons, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.fd] at hρ ⊢
    rw [hρ, hρ, Rat.cast_sub]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_values_negative_integer_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ), (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∀ cs : List (Fin r), ∃ ρ : (Fin r → ℕ) → ℚ, ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = (ρ m : ℂ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational
end

section
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem series_value_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (N p : ℕ), Fintype.card ι * p < N →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∃ q : ℚ, ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) := by
  intro ι _ r a b u cs N p hN hcase hval
  by_cases hex : ∃ i, cs.count i = N
  · obtain ⟨i, hi⟩ := hex
    refine ⟨0, ?_⟩
    have h0 := GlobalTheory.T.high_difference_vanishes_negative_integer ι r a b cs i N p hi hN
    simp [h0]
  · have hsupp : ∀ m : Fin r → ℕ, m ≠ 0 → u m = 0 := by
      intro m hm
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hm (funext hcon)
      rcases hcase i with h | h
      · exact absurd ⟨i, h⟩ hex
      · exact h m hi
    obtain ⟨ρ, hρ⟩ := GlobalTheory.T.cone_values_negative_integer_rational ι r a b p hval cs
    refine ⟨u 0 * ρ 0, ?_⟩
    rw [tsum_eq_single 0 (fun m hm => by simp [hsupp m hm]), hρ 0]
    push_cast
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_values_negative_integers_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (N p : ℕ), Fintype.card ι * p < N →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∃ q : ℚ, ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.series_value_rational
end

section
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue

theorem entire_of_halfPlane_continuations :
    ∀ (S : ℂ → ℂ) (G : ℕ → ℂ → ℂ), (∀ k, DifferentiableOn ℂ (G k) {s | -(k : ℝ) < s.re}) →
  (∀ k s, 1 < s.re → G k s = S s) → ∃ T : ℂ → ℂ, Differentiable ℂ T ∧ ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → T s = G k s := by
  intro S G hG hS
  have hopen : ∀ r : ℝ, IsOpen {s : ℂ | r < s.re} := fun r =>
    isOpen_lt continuous_const Complex.continuous_re

  have hagree : ∀ j k : ℕ, j ≤ k → Set.EqOn (G j) (G k) {s : ℂ | -(j : ℝ) < s.re} := by
    intro j k hjk
    have hsub : {s : ℂ | -(j : ℝ) < s.re} ⊆ {s : ℂ | -(k : ℝ) < s.re} := by
      intro s hs
      have h1 : (j : ℝ) ≤ k := by exact_mod_cast hjk
      simp only [Set.mem_setOf_eq] at hs ⊢
      linarith
    have hfj : AnalyticOnNhd ℂ (G j) {s : ℂ | -(j : ℝ) < s.re} :=
      (hG j).analyticOnNhd (hopen _)
    have hfk : AnalyticOnNhd ℂ (G k) {s : ℂ | -(j : ℝ) < s.re} :=
      ((hG k).mono hsub).analyticOnNhd (hopen _)
    have hpre : IsPreconnected {s : ℂ | -(j : ℝ) < s.re} :=
      (convex_halfSpace_re_gt (-(j : ℝ))).isPreconnected
    have h2 : (2 : ℂ) ∈ {s : ℂ | -(j : ℝ) < s.re} := by
      have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      simp only [Set.mem_setOf_eq, Complex.re_ofNat]
      linarith
    have hev : G j =ᶠ[nhds (2 : ℂ)] G k := by
      have hmem : {s : ℂ | (1 : ℝ) < s.re} ∈ nhds (2 : ℂ) :=
        (hopen 1).mem_nhds (by simp)
      filter_upwards [hmem] with s hs
      rw [hS j s hs, hS k s hs]
    exact hfj.eqOn_of_preconnected_of_eventuallyEq hfk hpre h2 hev

  have hidx : ∀ s : ℂ, -((⌈-s.re⌉₊ + 1 : ℕ) : ℝ) < s.re := by
    intro s
    have h1 : -s.re ≤ (⌈-s.re⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith

  have hT : ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → G (⌈-s.re⌉₊ + 1) s = G k s := by
    intro k s hs
    rcases le_total (⌈-s.re⌉₊ + 1) k with h | h
    · exact hagree _ _ h (hidx s)
    · exact (hagree _ _ h hs).symm
  refine ⟨fun s => G (⌈-s.re⌉₊ + 1) s, ?_, hT⟩
  intro s
  set k := ⌈-s.re⌉₊ + 1 with hk
  have hs : s ∈ {w : ℂ | -(k : ℝ) < w.re} := hidx s
  have hnh : {w : ℂ | -(k : ℝ) < w.re} ∈ nhds s := (hopen _).mem_nhds hs
  have hd : DifferentiableAt ℂ (G k) s := (hG k).differentiableAt hnh
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hnh] with w hw
  exact hT k w hw

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_continuation_from_strips : ∀ (S : ℂ → ℂ) (G : ℕ → ℂ → ℂ), (∀ k, DifferentiableOn ℂ (G k) {s | -(k : ℝ) < s.re}) →
  (∀ k s, 1 < s.re → G k s = S s) → ∃ T : ℂ → ℂ, Differentiable ℂ T ∧ ∀ (k : ℕ) (s : ℂ), -(k : ℝ) < s.re → T s = G k s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Glue.entire_of_halfPlane_continuations
end

section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem stage (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ)
    (hr : r ≤ Fintype.card ι) (hl : 0 < l) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (hw : GoodWeight l w) (k : ℕ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | -(k : ℝ) < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = ∑' m, (w m : ℂ) * coneTerm a b s m) ∧
      ∀ p : ℕ, p < k → (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
        ∃ q : ℚ, G (-(p : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨Q, x, cs, u, hu, hcs, hsum⟩ := GlobalTheory.T.weight_sum_as_finite_differences r l (Fintype.card ι * k + 2) w hl hw
  refine ⟨fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m, ?_, ?_, ?_⟩
  · have h : ∀ q ∈ (Finset.univ : Finset Q), DifferentiableOn ℂ
        (fun s => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) {s : ℂ | -(k : ℝ) < s.re} :=
      fun q _ => GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb k (Fintype.card ι * k + 2) (cs q) (u q) le_rfl (hu q) (hcs q)
    have h2 := DifferentiableOn.sum h
    have h3 : (fun s : ℂ => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) =
        ∑ q, fun s : ℂ => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m := by
      funext s
      simp [Finset.sum_apply]
    rw [h3]
    exact h2
  · intro s hs
    exact (hsum (coneTerm a b s) (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)).symm
  · intro p hp hrat
    have hN : Fintype.card ι * p < Fintype.card ι * k + 2 := by
      have := Nat.mul_le_mul_left (Fintype.card ι) hp.le
      omega
    choose q hq using fun t => GlobalTheory.T.shintani_values_negative_integers_rational ι r a b (u t) (cs t) (Fintype.card ι * k + 2) p hN (hcs t) hrat
    refine ⟨∑ t, q t, ?_⟩
    simp only [Rat.cast_sum]
    exact Finset.sum_congr rfl fun t _ => hq t

theorem abelContinuation : AbelContinuation := by
  intro ι _ r l a b w hr hl ha hb hw
  choose G hG hGeq hGrat using fun k : ℕ => stage ι r l a b w hr hl ha hb hw k
  obtain ⟨T, hT, hTG⟩ := GlobalTheory.T.analytic_continuation_from_strips (fun s => ∑' m, (w m : ℂ) * coneTerm a b s m) G hG hGeq
  refine ⟨T, hT, ?_, ?_⟩
  · intro s hs
    have hs0 : -((0 : ℕ) : ℝ) < s.re := by
      rw [Nat.cast_zero, neg_zero]
      linarith
    rw [hTG 0 s hs0, hGeq 0 s hs]
    have hper : ∀ (i : Fin r) (m : Fin r → ℕ), w (m + Pi.single i l) = w m := by
      obtain ⟨h1, -⟩ := hw
      exact fun i m => h1 m i
    obtain ⟨C, hC⟩ := GlobalTheory.T.periodic_weight_bounded r l w hl hper
    have hcone := GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs
    refine Summable.hasSum (Summable.of_norm ?_)
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hcone.norm.mul_left C)
    have hwm : ‖(w m : ℂ)‖ ≤ C := by simpa using hC m
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hwm (norm_nonneg _)
  · intro p hrat
    have hp : -((p + 1 : ℕ) : ℝ) < (-(p : ℂ)).re := by norm_num
    rw [hTG (p + 1) _ hp]
    exact hGrat (p + 1) p (Nat.lt_succ_self p) hrat

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abel_continuation : AbelContinuation := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelContinuation <;> assumption)
end
