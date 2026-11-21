import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DropLevelsBasic
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulFlowValLe
import Formalism.DropLevelBounds.Statement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSumsStatement

section
section
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.FlowParameters

lemma sum_inflow (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : Finset ℕ) :
    ∑ a : ZMod d, ∑ i ∈ s, x (a - (i : ZMod d)) i = ∑ a, ∑ i ∈ s, x a i := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp (Equiv.subRight (i : ZMod d)) (fun a => x a i)

lemma flowVal_le_sum (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d D x) : flowVal d x ≤ ∑ a, D a := by
  unfold flowVal
  rw [← sum_inflow]
  refine Finset.sum_le_sum fun a _ => ?_
  have h1 := hx.2 a
  have h2 : 0 ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hx.1 a i)
  linarith

lemma flowVal_le_maxFlow (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (hx : IsFlow l d D x) : flowVal d x ≤ maxFlow l d D := by
  refine le_csSup ⟨∑ a, D a, ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨z, hz, rfl⟩
  exact flowVal_le_sum l d D z hz

lemma maxFlow_smul_le (l d : ℕ) [NeZero d] (c : ℝ) (hc : 0 ≤ c) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    maxFlow l d (fun a => c * D a) ≤ c * maxFlow l d D := by
  refine csSup_le ⟨_, fun _ _ => 0, ⟨fun _ _ => le_rfl, fun s => ?_⟩, rfl⟩ ?_
  · simpa using mul_nonneg hc (hD s)
  rintro t ⟨x, hx, rfl⟩
  rcases hc.eq_or_lt with rfl | hc'
  · simpa using flowVal_le_sum l d _ x hx
  · have hz : IsFlow l d D (fun a i => c⁻¹ * x a i) := by
      refine ⟨fun s i => mul_nonneg (by positivity) (hx.1 s i), fun s => ?_⟩
      have h := hx.2 s
      have e : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * (c⁻¹ * x s i)) +
          (∑ i ∈ oddLevels d, c⁻¹ * x (s - (i : ZMod d)) i) =
          c⁻¹ * ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
            (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i)) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, inv_mul_le_iff₀ hc']
      exact h
    have h := flowVal_le_maxFlow l d D _ hz
    have e : flowVal d (fun a i => c⁻¹ * x a i) = c⁻¹ * flowVal d x := by
      simp only [flowVal, Finset.mul_sum]
    rw [e, inv_mul_le_iff₀ hc'] at h
    exact h

theorem sizeDataSmall : ParametersSmall := by
  intro l d _ hl hd n m θ S W ys y u mon cCH cMON cB eB hW _ hval _ hS hzero _ hmon hsplit
    hB hCH hMON
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hg : 0 ≤ gam l := div_nonneg (by positivity) (by nlinarith)
  have hn : (0 : ℝ) ≤ n := by positivity
  have hscale := maxFlow_smul_le l d n hn W hW

  have hWsum : ∑ a, W a = (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) + (∑ a, u a) + ∑ a, mon a := by
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_inflow d (fun a i => (y a i : ℝ))]

  have hBsum : ∑ a, ∑ i ∈ oddLevels d, cB a i ≤
      n * gam l * (∑ a, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        (n * gam l - n) * (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) +
        ∑ a, ∑ i ∈ oddLevels d, eB a i := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i hi => ?_
    have := hB a i hi
    linarith
  have hCHsum : ∑ a, cCH a ≤ n * gam l * (∑ a, u a) + m * (∑ a, u a) / ((l : ℝ) - 1) := by
    refine (Finset.sum_le_sum fun a _ => hCH a).trans (le_of_eq ?_)
    rw [← Finset.sum_mul]
    ring
  have hMONsum : ∑ a, cMON a ≤ (∑ a, mon a) / ((l : ℝ) - 1) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun a _ => hMON a

  have hround : flowVal d ys ≤ (∑ a, ∑ i ∈ oddLevels d, (y a i : ℝ)) +
      S * (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
        (fun p => ys p.1 p.2 ≠ 0)).card := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Finset.sum_product,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases h : ys a i = 0
    · simp [h]
    · have := hS a i
      simp only [ne_eq, h, not_false_eq_true, if_true, Nat.cast_one, mul_one]
      linarith
  have hmonsum : 0 ≤ n * gam l * ∑ a, mon a :=
    mul_nonneg (mul_nonneg hn hg) (Finset.sum_nonneg fun a _ => hmon a)
  have h1 := mul_le_mul_of_nonneg_left (hval.trans hround) hn
  have h2 : gam l * ∑ a, (n : ℝ) * W a = n * gam l * ∑ a, W a := by
    rw [← Finset.mul_sum]; ring
  have h3 := congrArg (fun t => n * gam l * t) hWsum
  unfold Fnum
  rw [h2]
  linarith

end GlobalTheory.FlowParameters
end

open Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizeData_small_bound : ParametersSmall := by
  atlas_forward_decl GlobalTheory.FlowParameters.sizeDataSmall
end

section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.OrbitPlan

theorem exists_good {S : ℕ} {G : Set ℕ} (h : Windows S G) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y ∈ G, (y : ℝ) ≤ r ∧ r - y ≤ S := by
  have h1 := Nat.floor_le hr
  have h2 := Nat.lt_floor_add_one r
  by_cases hS : S ≤ ⌊r⌋₊ + 1
  · obtain ⟨y, hy, hy1, hy2⟩ := h.2 (⌊r⌋₊ + 1 - S)
    have a1 : y ≤ ⌊r⌋₊ := by omega
    have a2 : ⌊r⌋₊ + 1 ≤ y + S := by omega
    have b1 : (y : ℝ) ≤ ⌊r⌋₊ := by exact_mod_cast a1
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ y + S := by exact_mod_cast a2
    exact ⟨y, hy, by linarith, by linarith⟩
  · have a2 : ⌊r⌋₊ + 1 ≤ S := by omega
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ S := by exact_mod_cast a2
    exact ⟨0, h.1, by simpa using hr, by simp only [Nat.cast_zero]; linarith⟩

theorem logTerm_nonneg {l n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) :
    0 ≤ (n : ℝ) * (Real.logb l n + 1) := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.logb_nonneg h1 h2
  positivity

theorem orbit_sum_fifty_one : WindowedChoiceExistsWithBound := by
  intro l d _ hp hl hd he n m k S hn hk hS W Good hG
  classical
  have hW0 : (0 : ZMod d → ℝ) ≤ fun a => (W a : ℝ) := fun a => Nat.cast_nonneg _
  obtain ⟨ys, hflow, hsupp, hcard, hval⟩ :=
    GlobalTheory.BasicFlow.main.1 l d (by omega) (fun a => (W a : ℝ)) hW0 (i0 k l)
  obtain ⟨hodd, h3, -, hthl⟩ := GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l hk (by omega)
  have hex : ∀ a i, ∃ y : ℕ, (y ≠ 0 → y ∈ Good a i) ∧ (y : ℝ) ≤ ys a i ∧
      ys a i - y ≤ (S : ℝ) + 1 := by
    intro a i
    by_cases hc : i ∈ oddLevels d ∧ i < i0 k l
    · obtain ⟨y, hy, h1, h2⟩ := exists_good (hG a i hc.1 hc.2) (hflow.1 a i)
      exact ⟨y, fun _ => hy, h1, by linarith⟩
    · have : ys a i = 0 := hsupp a i (by
        by_cases h : i ∈ oddLevels d
        · left; by_contra h'; exact hc ⟨h, by omega⟩
        · right; exact h)
      refine ⟨0, fun h => absurd rfl h, by simp [this], ?_⟩
      simp only [this, Nat.cast_zero, sub_zero]; positivity
  choose y hyG hyle hyge using hex
  have hy0 : ∀ a i, ys a i = 0 → y a i = 0 := by
    intro a i h
    have := hyle a i
    rw [h] at this
    exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hle : ∀ a, (∑ i ∈ oddLevels d, l ^ i * y a i) +
      (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) ≤ W a := by
    intro a
    have h1 : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * ys a i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyle a i) (by positivity)
    have h2 : (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤
        ∑ i ∈ oddLevels d, ys (a - (i : ZMod d)) i :=
      Finset.sum_le_sum fun i _ => hyle _ i
    have h3 := hflow.2 a
    have : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ (W a : ℝ) := by
      simp only at h3
      linarith
    exact_mod_cast this
  let p : Plan l d W :=
    { y := y
      u := fun a => W a - ((∑ i ∈ oddLevels d, l ^ i * y a i) +
        (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i))
      supp := fun a i hi => hy0 a i (hsupp a i (Or.inr hi))
      bal := fun a => by have := hle a; omega }
  have hcard' : (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
      fun x => y x.1 x.2 ≠ 0).card ≤ d := by
    refine le_trans (Finset.card_le_card ?_) hcard
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, fun h => hx.2 (hy0 _ _ h)⟩
  refine ⟨p, ⟨fun a i hi => hy0 a i (hsupp a i (Or.inl hi)), hyG, hcard'⟩, ?_⟩
  have hbal : ∀ a, (W a : ℝ) = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + (p.u a : ℝ) := by
    intro a
    have := p.bal a
    exact_mod_cast this
  set L : ℝ := (n : ℝ) * (Real.logb l n + 1) with hL
  have hL0 : 0 ≤ L := logTerm_nonneg hl hn
  have key := GlobalTheory.T.sizeData_small_bound l d (by omega) hd n m (thl k l) ((S : ℝ) + 1) (fun a => (W a : ℝ)) ys y
    (fun a => (p.u a : ℝ)) (fun _ => 0) (fun a => chBd l n m (p.u a)) (fun _ => 0)
    (fun a i => blockBd l n m i (y a i))
    (fun a i => (if y a i ≠ 0 then L else 0) +
      ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y a i / ((l : ℝ) - 1))
    hW0 hflow (by rw [hthl, inv_mul_eq_div]; exact hval) hyle hyge hy0
    (fun a => Nat.cast_nonneg _) (fun _ => le_rfl) (fun a => by rw [add_zero]; exact hbal a)
    (fun a i _ => by
      by_cases h : y a i = 0
      · simp [blockBd, h]
      · simp only [blockBd, bdP, h, if_false, ne_eq, not_false_eq_true, if_true, hL]
        linarith)
    (fun a => le_rfl) (fun _ => by simp)
  simp only [Finset.sum_const_zero, add_zero, zero_div, Finset.sum_add_distrib] at key

  have e1 : (∑ a, ∑ i ∈ oddLevels d, (if y a i ≠ 0 then L else 0)) ≤ d * L := by
    rw [← Finset.sum_product' (f := fun a i => if y a i ≠ 0 then L else 0), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard') hL0
  have e2 : (n : ℝ) * ((S : ℝ) + 1) * (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
      (fun p => ys p.1 p.2 ≠ 0)).card ≤ n * ((S : ℝ) + 1) * d :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)
  have hi3 : (3 : ℝ) ≤ i0 k l := by exact_mod_cast h3
  have hrow : ∀ a, (∑ i ∈ oddLevels d,
      ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y a i / ((l : ℝ) - 1)) ≤
      (2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)) * W a := by
    intro a
    have c0 : 0 ≤ 2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) :=
      div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hl1.le
    have h1 : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤ W a := by
      have : (∑ i ∈ oddLevels d, l ^ i * y a i) ≤ W a := le_trans (Nat.le_add_right _ _) (hle a)
      exact_mod_cast this
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 c0)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases h : y a i = 0
    · simp [h]
    have hi1 : i < i0 k l := by
      by_contra h'
      exact h (hy0 a i (hsupp a i (Or.inl (by omega))))
    have hio : Odd i := (Finset.mem_filter.1 hi).2
    have hi2 : i + 2 ≤ i0 k l := by
      obtain ⟨s, hs⟩ := hio
      obtain ⟨t, ht⟩ := hodd
      omega
    have hi2' : (i : ℝ) + 1 ≤ (i0 k l : ℝ) - 1 := by
      have : (i : ℝ) + 2 ≤ i0 k l := by exact_mod_cast hi2
      linarith
    have hpow : (1 : ℝ) ≤ (l : ℝ) ^ i := one_le_pow₀ (by linarith)
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hl1.le
    have q : ((i : ℝ) + 1) * ((l : ℝ) ^ i + 1) ≤ ((i0 k l : ℝ) - 1) * (2 * (l : ℝ) ^ i) :=
      mul_le_mul hi2' (by linarith) (by positivity) (by linarith)
    have := mul_le_mul_of_nonneg_right q (show (0 : ℝ) ≤ (m : ℝ) * y a i by positivity)
    linarith
  have e3 := Finset.sum_le_sum fun a (_ : a ∈ (Finset.univ : Finset (ZMod d))) => hrow a
  rw [← Finset.mul_sum] at e3
  have e4 : (m : ℝ) * (∑ a, (p.u a : ℝ)) / ((l : ℝ) - 1) ≤ m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) := by
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)) hl1.le
    exact_mod_cast Nat.sub_le _ _
  have e5 : (2 * (i0 k l : ℝ) - 1) * m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) =
      (2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)) * (∑ a, (W a : ℝ)) +
        m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) := by ring
  rw [e5]
  change (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) + ∑ a, chBd l n m (p.u a) ≤ _
  linarith

theorem contentOrbit : ContentOrbit := by
  intro l d _ hp hl hd he n m k S hn hk hS W Good T θ w th hG hT hw hTW hth hθ
  obtain ⟨p, hok, hb⟩ := orbit_sum_fifty_one l d hp hl hd he n m k S hn hk hS W Good hG
  refine ⟨p, hok, ?_⟩
  have hs := GlobalTheory.FlowScaling.main.2.1 l d (by omega) hd he n T θ w (fun a => (W a : ℝ)) th hT hw hTW
    hth hθ
  obtain ⟨-, h3, -, hthl⟩ := GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l hk (by omega)
  have hi3 : (3 : ℝ) ≤ i0 k l := by exact_mod_cast h3
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have ht0 : 0 ≤ thl k l := by rw [hthl]; positivity
  have hsum : T * (∑ a, (W a : ℝ)) ≤ ∑ a, w a := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [hTW a]
    have := mul_nonneg (hw a).le (hth a).1
    linarith
  have c0 : 0 ≤ (2 * (i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hl1.le
  have e1 := mul_le_mul_of_nonneg_left hsum c0
  have e2 := mul_le_mul_of_nonneg_left hsum (mul_nonneg ht0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  have e3 := mul_le_mul_of_nonneg_left hb hT.le
  have e4 : ∀ x : ℝ, (2 * (i0 k l : ℝ) - 1) * m * x / ((l : ℝ) - 1) =
      (2 * (i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) * x := fun x => by ring
  rw [e4] at e3 ⊢
  nlinarith

theorem main : WindowedChoiceExistsWithBound ∧ ContentOrbit := ⟨orbit_sum_fifty_one, contentOrbit⟩

end GlobalTheory.OrbitPlan
end
