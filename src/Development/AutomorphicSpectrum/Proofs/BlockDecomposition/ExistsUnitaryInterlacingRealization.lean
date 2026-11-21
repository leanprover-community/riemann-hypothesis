import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionDiagonalIdentity

section
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem pfOrth : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ),
    Function.Injective (Sum.elim d d') → ∀ i k, i ≠ k →
      1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) = 0 := by
  intro m d d' hinj i k hik
  have hi := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj i
  have hk := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj k
  have hne : d i - d k ≠ 0 := sub_ne_zero.mpr fun h => hik (Sum.inl.inj (@hinj (Sum.inl i) (Sum.inl k) h))
  have hij : ∀ j, d i - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h =>
    Sum.inl_ne_inr (@hinj (Sum.inl i) (Sum.inr j) h)
  have hkj : ∀ j, d k - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h =>
    Sum.inl_ne_inr (@hinj (Sum.inl k) (Sum.inr j) h)
  have hdiff : ∑ j, pfR d d' j / (d i - d' j) - ∑ j, pfR d d' j / (d k - d' j) =
      -(d i - d k) * ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hij j, hkj j]
    ring
  have key : (d i - d k) * (1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j))) = 0 := by
    linear_combination hi - hk - hdiff
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · exact h

end GlobalTheory.CompanionTheory.RgHeFrame
end

open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_off_diagonal_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i k, i ≠ k → 1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RgHeFrame.pfOrth
end

section
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

open Polynomial

variable {m : ℕ}

noncomputable def pfPoly (x : ℝ) (r d' : Fin m → ℝ) : ℝ[X] :=
  (X - C x) * ∏ j, (X - C (d' j)) + ∑ j, C (r j) * ∏ k ∈ univ.erase j, (X - C (d' k))

lemma eval_pfPoly (x : ℝ) (r d' : Fin m → ℝ) (s : ℝ) (hs : ∀ j, s - d' j ≠ 0) :
    (pfPoly x r d').eval s =
      (∏ j, (s - d' j)) * (s - x + ∑ j, r j / (s - d' j)) := by
  have hj : ∀ j, (∏ k ∈ univ.erase j, (s - d' k)) = (∏ k, (s - d' k)) / (s - d' j) := by
    intro j
    rw [eq_div_iff (hs j), mul_comm, Finset.mul_prod_erase univ (fun k => s - d' k) (mem_univ j)]
  simp only [pfPoly, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_prod, eval_finset_sum]
  rw [mul_add, Finset.mul_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hj j]
  ring

lemma prod_eq_pfPoly (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (h : Function.Injective (Sum.elim d d')) :
    (∏ i, (X - C (d i)) : ℝ[X]) = pfPoly (pfX d d') (pfR d d') d' := by
  have hdd' : ∀ i j, d i - d' j ≠ 0 := by
    intro i j hij
    have : Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j) := by
      simpa using sub_eq_zero.mp hij
    exact absurd (h this) (by simp)
  have hinj : Function.Injective d := fun a b hab => by
    have : Sum.elim d d' (Sum.inl a) = Sum.elim d d' (Sum.inl b) := by simpa using hab
    simpa using h this
  have hP : (∏ i, (X - C (d i)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hQ : (∏ j, (X - C (d' j)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPd : (∏ i, (X - C (d i)) : ℝ[X]).degree = (m + 1 : ℕ) := by
    rw [degree_eq_natDegree hP.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  have hQd : (∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  have hL : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).Monic := (monic_X_sub_C _).mul hQ
  have hLd : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).degree = (m + 1 : ℕ) := by
    rw [degree_eq_natDegree hL.ne_zero, (monic_X_sub_C _).natDegree_mul hQ, hQd]
    simp [add_comm]
  have hsub : ((∏ i, (X - C (d i)) : ℝ[X]) -
      (X - C (pfX d d')) * ∏ j, (X - C (d' j))).degree < ((m + 1 : ℕ) : WithBot ℕ) := by
    have := degree_sub_lt (hPd.trans hLd.symm) hP.ne_zero (hP.leadingCoeff.trans hL.leadingCoeff.symm)
    rwa [hPd] at this
  have hterm : ∀ j : Fin m, (C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < ((m + 1 : ℕ) : WithBot ℕ) := by
    intro j
    rw [← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ?_
    have hM : (∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).Monic :=
      monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
    rw [degree_eq_natDegree hM.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
    exact_mod_cast (by omega : m - 1 < m + 1)
  have hsum : (∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < ((m + 1 : ℕ) : WithBot ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => hterm j
  have hdeg : ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d').degree
      < (univ : Finset (Fin (m + 1))).card := by
    have : ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d') =
        ((∏ i, (X - C (d i)) : ℝ[X]) - (X - C (pfX d d')) * ∏ j, (X - C (d' j))) -
          ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) := by
      simp only [pfPoly]; ring
    rw [this]
    simpa using (degree_sub_le _ _).trans_lt (max_lt hsub hsum)
  refine sub_eq_zero.mp (eq_zero_of_degree_lt_of_eval_index_eq_zero univ hinj.injOn hdeg ?_)
  intro i _
  have hz := GlobalTheory.T.partial_fraction_diagonal_identity d d' h i
  rw [eval_sub, eval_pfPoly _ _ _ _ (hdd' i), hz, mul_zero, eval_prod]
  simp only [eval_sub, eval_X, eval_C, sub_zero]
  exact Finset.prod_eq_zero (mem_univ i) (sub_self _)

theorem pfDer : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ),
    Function.Injective (Sum.elim d d') →
      ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  intro m d d' h i
  have hdd' : ∀ j, d i - d' j ≠ 0 := by
    intro j hij
    have : Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j) := by
      simpa using sub_eq_zero.mp hij
    exact absurd (h this) (by simp)
  set Q : ℝ[X] := ∏ j, (X - C (d' j)) with hQdef
  have hQe : ∀ s, Q.eval s = ∏ j, (s - d' j) := fun s => by simp [hQdef, eval_prod]
  have hQ0 : Q.eval (d i) ≠ 0 := by
    rw [hQe]; exact Finset.prod_ne_zero_iff.2 fun j _ => hdd' j

  let f : ℝ → ℝ := fun s => s - pfX d d' + ∑ j, pfR d d' j / (s - d' j)
  have hterm : ∀ j ∈ (univ : Finset (Fin m)), HasDerivAt (fun s => pfR d d' j / (s - d' j))
      (-(pfR d d' j / (d i - d' j) ^ 2)) (d i) := by
    intro j _
    have h1 : HasDerivAt (fun s : ℝ => s - d' j) 1 (d i) := (hasDerivAt_id _).sub_const _
    have h2 := (hasDerivAt_const (d i) (pfR d d' j)).fun_div h1 (hdd' j)
    exact h2.congr_deriv (by simp [neg_div])
  have hf : HasDerivAt f (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2) (d i) := by
    have h3 := HasDerivAt.fun_sum hterm
    have h4 := ((hasDerivAt_id (d i)).sub_const (pfX d d')).fun_add h3
    exact h4.congr_deriv (by simp [sub_eq_add_neg])
  have hf0 : f (d i) = 0 := GlobalTheory.T.partial_fraction_diagonal_identity d d' h i
  have hprod : HasDerivAt (fun s => Q.eval s * f s)
      (Q.eval (d i) * (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2)) (d i) := by
    have := (Q.hasDerivAt (d i)).fun_mul hf
    exact this.congr_deriv (by simp [hf0])

  set P : ℝ[X] := ∏ k, (X - C (d k)) with hPdef
  have hPfac : P = (X - C (d i)) * ∏ k ∈ univ.erase i, (X - C (d k)) :=
    (Finset.mul_prod_erase univ (fun k => (X - C (d k) : ℝ[X])) (mem_univ i)).symm
  have hPder : P.derivative.eval (d i) = ∏ k ∈ univ.erase i, (d i - d k) := by
    rw [hPfac, derivative_mul]
    simp [eval_prod]
  have hev : (fun s => P.eval s) =ᶠ[nhds (d i)] fun s => Q.eval s * f s := by
    have hopen : ∀ᶠ s in nhds (d i), ∀ j, s - d' j ≠ 0 := by
      refine Filter.eventually_all.2 fun j => ?_
      have hc : ContinuousAt (fun s : ℝ => s - d' j) (d i) := by fun_prop
      exact hc.eventually_ne (hdd' j)
    filter_upwards [hopen] with s hs
    rw [hPdef, prod_eq_pfPoly d d' h, eval_pfPoly _ _ _ _ hs, hQe]
  have huniq := (P.hasDerivAt (d i)).unique (hprod.congr_of_eventuallyEq hev)
  rw [hPder] at huniq
  unfold pfD
  rw [← hQe (d i), huniq]
  field_simp

end GlobalTheory.CompanionTheory.RgHeFrame
end

open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_square_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RgHeFrame.pfDer
end

section
section
open Finset Matrix PositivityTheory.RgHe.Frame

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeFrame

def sg (b : Bool) : ℝ := if b then 1 else -1

lemma sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

lemma sg_ne_zero (b : Bool) : sg b ≠ 0 := by cases b <;> simp [sg]

lemma sg_cast (b : Bool) : ((sg b : ℝ) : ℂ) = if b then 1 else -1 := by cases b <;> simp [sg]

variable {n : ℕ}

def cc (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (i : Fin (n + 1)) : ℝ := 1 / √|pfD d d' i|

def yy (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (j : Fin n) : ℝ :=
  √(-(sg (ε' j) * pfR d d' j))

def G0 (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (r : Fin n ⊕ Unit)
    (i : Fin (n + 1)) : ℝ :=
  Sum.elim (fun j => cc d d' i * yy ε' d d' j / (d i - d' j)) (fun _ => cc d d' i) r

def X0 (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (r t : Fin n ⊕ Unit) : ℝ :=
  Sum.elim
    (fun a => Sum.elim (fun b => if a = b then d' a else 0) (fun _ => yy ε' d d' a) t)
    (fun _ => Sum.elim (fun b => sg (ε' b) * yy ε' d d' b) (fun _ => pfX d d') t) r

lemma yy_sq {ε' : Fin n → Bool} {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {j : Fin n}
    (h : 0 < -(sg (ε' j) * pfR d d' j)) :
    sg (ε' j) * (yy ε' d d' j * yy ε' d d' j) = -pfR d d' j := by
  unfold yy
  rw [Real.mul_self_sqrt h.le]
  have := sg_mul_self (ε' j)
  linear_combination (-pfR d d' j) * this

lemma cc_sq {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {i : Fin (n + 1)} {b : Bool}
    (h : 0 < sg b * pfD d d' i) : cc d d' i * cc d d' i * pfD d d' i = sg b := by
  have hcc : cc d d' i * cc d d' i = 1 / |pfD d d' i| := by
    unfold cc
    rw [div_mul_div_comm, Real.mul_self_sqrt (abs_nonneg _), one_mul]
  rw [hcc]
  cases b with
  | true =>
    have hp : 0 < pfD d d' i := by simpa [sg] using h
    rw [abs_of_pos hp]
    simp only [sg]
    field_simp
    simp
  | false =>
    have hp : pfD d d' i < 0 := by simpa [sg] using h
    rw [abs_of_neg hp]
    simp only [sg]
    have := hp.ne
    field_simp
    simp

lemma cc_ne_zero {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {i : Fin (n + 1)} {b : Bool}
    (h : 0 < sg b * pfD d d' i) : cc d d' i ≠ 0 := by
  intro h0
  have := cc_sq h
  rw [h0] at this
  exact sg_ne_zero b (by simpa using this.symm)

lemma sum_terms {ε' : Fin n → Bool} {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ}
    (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j)) (i k : Fin (n + 1)) :
    ∑ j, (cc d d' i * yy ε' d d' j / (d i - d' j)) * sg (ε' j) *
        (cc d d' k * yy ε' d d' j / (d k - d' j)) =
      -(cc d d' i * cc d d' k * ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j))) := by
  rw [mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h := yy_sq (hR j)
  calc (cc d d' i * yy ε' d d' j / (d i - d' j)) * sg (ε' j) *
        (cc d d' k * yy ε' d d' j / (d k - d' j))
      = cc d d' i * cc d d' k * (sg (ε' j) * (yy ε' d d' j * yy ε' d d' j)) /
          ((d i - d' j) * (d k - d' j)) := by
          simp only [div_eq_mul_inv, mul_inv]; ring
    _ = _ := by rw [h]; ring

lemma gram {ε : Fin (n + 1) → Bool} {d : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {d' : Fin n → ℝ}
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (hz : ε (e (Sum.inr ())) = true)
    (hs : ∀ a, ε (e (Sum.inl a)) = ε' a) (hinj : Function.Injective (Sum.elim d d'))
    (hD : ∀ i, 0 < sg (ε i) * pfD d d' i) (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j))
    (i k : Fin (n + 1)) :
    ∑ r, G0 ε' d d' (e.symm r) i * sg (ε r) * G0 ε' d d' (e.symm r) k =
      if i = k then sg (ε i) else 0 := by
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply, G0, Sum.elim_inl, Sum.elim_inr, hs, hz, univ_unique,
    sum_singleton]
  rw [sum_terms hR]
  have hz1 : sg true = 1 := by simp [sg]
  rw [hz1]
  by_cases hik : i = k
  · subst hik
    have h1 := GlobalTheory.T.partial_fraction_square_identity d d' hinj i
    have h2 := cc_sq (hD i)
    simp only [if_true]
    have h3 : ∑ j, pfR d d' j / ((d i - d' j) * (d i - d' j)) =
        ∑ j, pfR d d' j / (d i - d' j) ^ 2 := by
      refine sum_congr rfl fun j _ => ?_
      rw [sq]
    rw [h3]
    linear_combination (cc d d' i * cc d d' i) * h1 + h2
  · have h1 := GlobalTheory.T.partial_fraction_off_diagonal_identity d d' hinj i k hik
    simp only [hik, if_false]
    linear_combination (cc d d' i * cc d d' k) * h1

lemma inter {d : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {d' : Fin n → ℝ}
    (hinj : Function.Injective (Sum.elim d d'))
    (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j)) (r : Fin n ⊕ Unit) (i : Fin (n + 1)) :
    ∑ t, X0 ε' d d' r t * G0 ε' d d' t i = G0 ε' d d' r i * d i := by
  have hne : ∀ j, d i - d' j ≠ 0 := by
    intro j h
    have : (Sum.inl i : Fin (n + 1) ⊕ Fin n) = Sum.inr j :=
      hinj (by simpa using sub_eq_zero.mp h)
    simp at this
  rw [Fintype.sum_sum_type]
  rcases r with a | u
  · simp only [X0, G0, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton, ite_mul, zero_mul,
      sum_ite_eq, mem_univ, if_true]
    have := hne a
    field_simp
    ring
  · simp only [X0, G0, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton]
    have h0 := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj i
    have h1 : ∑ j, sg (ε' j) * yy ε' d d' j * (cc d d' i * yy ε' d d' j / (d i - d' j)) =
        -(cc d d' i * ∑ j, pfR d d' j / (d i - d' j)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun j _ => ?_
      have h := yy_sq (hR j)
      calc sg (ε' j) * yy ε' d d' j * (cc d d' i * yy ε' d d' j / (d i - d' j))
          = cc d d' i * (sg (ε' j) * (yy ε' d d' j * yy ε' d d' j)) / (d i - d' j) := by ring
        _ = _ := by rw [h]; ring
    rw [h1]
    linear_combination (-cc d d' i) * h0

theorem build : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), ε (e (Sum.inr ())) = true → (∀ a, ε (e (Sum.inl a)) = ε' a) → Function.Injective (Sum.elim d d') → (∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i) → (∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j)) → ∃ g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Formalism.REAL.inUJ ε g ∧ X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) ∧ (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) ∧ ∀ i, ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ)) i ≠ 0 := by
  intro n ε d ε' d' e hz hs hinj hD hR
  have hD' : ∀ i, 0 < sg (ε i) * pfD d d' i := hD
  have hR' : ∀ j, 0 < -(sg (ε' j) * pfR d d' j) := hR
  obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ r i, g r i = ((G0 ε' d d' (e.symm r) i : ℝ) : ℂ) := ⟨Matrix.of _, fun _ _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ r t, X r t = ((X0 ε' d d' (e.symm r) (e.symm t) : ℝ) : ℂ) := ⟨Matrix.of _, fun _ _ => rfl⟩
  refine ⟨g, X, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.REAL.inUJ Formalism.REAL.Jm
    ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hg,
      RCLike.star_def, Complex.conj_ofReal]
    have h := gram e hz hs hinj hD' hR' i k
    have h2 := congrArg (fun x : ℝ => (x : ℂ)) h
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, sg_cast] at h2
    rw [h2]
    by_cases hik : i = k
    · simp [hik, sg_cast]
    · simp [hik]
  · ext r i
    rw [Matrix.mul_diagonal, Matrix.mul_apply, ← Equiv.sum_comp e]
    simp only [hg, hX, Equiv.symm_apply_apply]
    have h := inter (ε' := ε') hinj hR' (e.symm r) i
    exact_mod_cast h
  · intro a b
    simp only [hX, Equiv.symm_apply_apply, X0, Sum.elim_inl]
    split_ifs <;> simp
  · intro i
    rw [Matrix.mulVec_single_one]
    change (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) i (e (Sum.inr ())) ≠ 0
    unfold Formalism.REAL.Jm
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hg,
      Equiv.symm_apply_apply, G0, Sum.elim_inr, hz, RCLike.star_def, Complex.conj_ofReal]
    have hc := cc_ne_zero (hD' i)
    have : ((cc d d' i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
    cases h : ε i <;> simpa using this

end GlobalTheory.CompanionTheory.RgHeFrame
end
end

open Finset Matrix PositivityTheory.RgHe.Frame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_interlacing_realization : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), ε (e (Sum.inr ())) = true → (∀ a, ε (e (Sum.inl a)) = ε' a) → Function.Injective (Sum.elim d d') → (∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i) → (∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j)) → ∃ g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Formalism.REAL.inUJ ε g ∧ X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) ∧ (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) ∧ ∀ i, ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ)) i ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RgHeFrame.build
end
