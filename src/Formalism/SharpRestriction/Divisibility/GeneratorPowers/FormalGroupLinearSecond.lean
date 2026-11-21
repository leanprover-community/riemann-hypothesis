import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation

open MvPolynomial

variable {S : Type} [CommRing S] {d : ℕ}

abbrev Io (S σ : Type) [CommRing S] : Ideal (MvPolynomial σ S) := idealOfVars σ S

def xs (S : Type) [CommRing S] {n : ℕ} (d : ℕ) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => X (k, i)

def lin {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) : Fin d → MvPolynomial (Fin n × Fin d) S :=
  fun i => ∑ l, C (A i l) * X (k, l)

def ev2 {τ : Type} (h : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S) : MvPolynomial τ S :=
  aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h

lemma eval_pair_coordinates (h : MvPolynomial (Fin 2 × Fin d) S) : ev2 h (xs S d 0) (xs S d 1) = h := by
  have hf : (fun p : Fin 2 × Fin d => ![xs S d 0, xs S d 1] p.1 p.2) = X := by
    funext p
    rcases p with ⟨k, i⟩
    fin_cases k <;> simp [xs]
  unfold ev2
  rw [hf, aeval_X_left_apply]

lemma aeval_eval_pair {τ τ' : Type} (g : τ → MvPolynomial τ' S) (h : MvPolynomial (Fin 2 × Fin d) S)
    (u v : Fin d → MvPolynomial τ S) :
    aeval g (ev2 h u v) = ev2 h (fun i => aeval g (u i)) (fun i => aeval g (v i)) := by
  have hf : (fun p : Fin 2 × Fin d => aeval g (![u, v] p.1 p.2)) =
      (fun p : Fin 2 × Fin d => ![fun i => aeval g (u i), fun i => aeval g (v i)] p.1 p.2) := by
    funext p
    rcases p with ⟨k, i⟩
    fin_cases k <;> simp
  unfold ev2
  rw [← AlgHom.comp_apply, comp_aeval, hf]

lemma eval_pair_one {τ : Type} (u v : Fin d → MvPolynomial τ S) : ev2 (1 : MvPolynomial (Fin 2 × Fin d) S) u v = 1 := by
  simp [ev2]

lemma eval_pair_sub {τ : Type} (h h' : MvPolynomial (Fin 2 × Fin d) S) (u v : Fin d → MvPolynomial τ S) :
    ev2 (h - h') u v = ev2 h u v - ev2 h' u v := by
  simp [ev2]

section Sub

variable {σ τ : Type}

lemma aeval_mem_pow (g : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (k : ℕ) {p : MvPolynomial σ S}
    (hp : p ∈ Io S σ ^ k) : aeval g p ∈ Io S τ ^ k := by
  have h1 : Io S σ ≤ (Io S τ).comap (aeval g) := by
    show Ideal.span (Set.range X) ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simpa using hg i
  exact (Ideal.le_comap_pow (f := aeval g) k) (Ideal.pow_right_mono h1 k hp)

lemma sub_C_mem (p : MvPolynomial σ S) : p - C (coeff 0 p) ∈ Io S σ := by
  have h := (mem_pow_idealOfVars_iff' (σ := σ) (R := S) 1 (p - C (coeff 0 p))).2 (fun x hx => by
    have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).1 (by omega)
    subst hx0
    simp)
  simpa using h

lemma aeval_sub_aeval_mem (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (p : MvPolynomial σ S) : aeval g p - aeval g' p ∈ Io S τ := by
  have h0 : p - C (coeff 0 p) ∈ Io S σ ^ 1 := by simpa using sub_C_mem p
  have h1 := aeval_mem_pow g hg 1 h0
  have h2 := aeval_mem_pow g' hg' 1 h0
  have h3 := sub_mem (by simpa using h1) (by simpa using h2)
  simpa [map_sub, aeval_C] using h3

lemma aeval_sub_mem_sq (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) {p : MvPolynomial σ S} (hp : p ∈ Io S σ) :
    aeval g p - aeval g' p ∈ Io S τ ^ 2 := by
  have hp' : p ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ S)) := hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    simpa using hgg i
  | zero => simp
  | add x y _ _ hx hy =>
    have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
      simp only [map_add]; ring
    rw [e]; exact add_mem hx hy
  | smul r x hxm hx =>
    have e : aeval g (r • x) - aeval g' (r • x) =
        (aeval g r - aeval g' r) * aeval g x + aeval g' r * (aeval g x - aeval g' x) := by
      simp only [smul_eq_mul, map_mul]; ring
    rw [e]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hx)
    rw [pow_two]
    have hx1 : x ∈ Io S σ ^ 1 := by simpa using hxm
    exact Ideal.mul_mem_mul (aeval_sub_aeval_mem g g' hg hg' r) (by simpa using aeval_mem_pow g hg 1 hx1)

lemma aeval_sub_mem_pow (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ) (hg' : ∀ i, g' i ∈ Io S τ)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) : ∀ (k : ℕ) (p : MvPolynomial σ S), p ∈ Io S σ ^ k →
    aeval g p - aeval g' p ∈ Io S τ ^ (k + 1)
  | 0, p, _ => by simpa using aeval_sub_aeval_mem g g' hg hg' p
  | k + 1, p, hp => by
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on (C := fun p => aeval g p - aeval g' p ∈ Io S τ ^ (k + 1 + 1)) hp ?_ ?_
    · intro a ha b hb
      have e : aeval g (a * b) - aeval g' (a * b) =
          (aeval g a - aeval g' a) * aeval g b + aeval g' a * (aeval g b - aeval g' b) := by
        simp only [map_mul]; ring
      rw [e]
      refine add_mem ?_ ?_
      · rw [pow_succ]
        have hb1 : b ∈ Io S σ ^ 1 := by simpa using hb
        exact Ideal.mul_mem_mul (aeval_sub_mem_pow g g' hg hg' hgg k a ha)
          (by simpa using aeval_mem_pow g hg 1 hb1)
      · have e2 : Io S τ ^ (k + 1 + 1) = Io S τ ^ k * Io S τ ^ 2 := by rw [← pow_add]
        rw [e2]
        exact Ideal.mul_mem_mul (aeval_mem_pow g' hg' k ha) (aeval_sub_mem_sq g g' hg hg' hgg hb)
    · intro x y hx hy
      have e : aeval g (x + y) - aeval g' (x + y) = (aeval g x - aeval g' x) + (aeval g y - aeval g' y) := by
        simp only [map_add]; ring
      rw [e]; exact add_mem hx hy

lemma eq_zero_of_isHomogeneous {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j)
    (hm : h ∈ Io S σ ^ (j + 1)) : h = 0 := by
  ext e
  rw [coeff_zero]
  by_contra hne
  have h1 := (mem_pow_idealOfVars_iff (j + 1) h).1 hm e (mem_support_iff.2 hne)
  have h2 : e.degree = j := by
    have := hh hne
    rw [Finsupp.degree_eq_weight_one]
    exact this
  omega

lemma sub_homogeneousComponent_mem {W : MvPolynomial σ S} {j : ℕ} (hW : W ∈ Io S σ ^ j) :
    W - homogeneousComponent j W ∈ Io S σ ^ (j + 1) := by
  rw [mem_pow_idealOfVars_iff'] at hW ⊢
  intro x hx
  rw [coeff_sub, coeff_homogeneousComponent]
  split_ifs with h
  · simp
  · have : x.degree < j := by omega
    simp [hW x this]

lemma aeval_double {h : MvPolynomial σ S} {j : ℕ} (hh : h.IsHomogeneous j) :
    aeval (fun i => X i + X i) h = C ((2 : S) ^ j) * h := by
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : e.degree = j := by
    have := hh (mem_support_iff.1 he)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  have h2 : ∀ i (k : ℕ), (X i + X i : MvPolynomial σ S) ^ k = C 2 ^ k * X i ^ k := by
    intro i k; rw [← two_mul, mul_pow, ← map_ofNat C 2]
  have key : e.prod (fun i k => (X i + X i : MvPolynomial σ S) ^ k) =
      C ((2 : S) ^ e.degree) * e.prod (fun i k => (X i : MvPolynomial σ S) ^ k) := by
    unfold Finsupp.prod
    simp_rw [h2]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow]
    rfl
  rw [aeval_monomial, monomial_eq, key, ← hdeg, algebraMap_eq]
  ring

end Sub

lemma eval_pair_homogeneous {τ : Type} {h : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ} (hh : h.IsHomogeneous j)
    (u v : Fin d → MvPolynomial τ S) (hu : ∀ i, (u i).IsHomogeneous 1) (hv : ∀ i, (v i).IsHomogeneous 1) :
    (ev2 h u v).IsHomogeneous j := by
  have := hh.aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) (n := 1)
    (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
  rw [one_mul] at this
  exact this

lemma xs_hom {n : ℕ} (k : Fin n) (i : Fin d) : (xs S d k i).IsHomogeneous 1 := isHomogeneous_X S _

lemma lin_hom {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) (i : Fin d) : (lin A k i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X S _).C_mul _

lemma xs_mem {n : ℕ} (k : Fin n) (i : Fin d) : xs S d k i ∈ Io S (Fin n × Fin d) :=
  Ideal.subset_span ⟨_, rfl⟩

lemma lin_mem {n : ℕ} (A : Fin d → Fin d → S) (k : Fin n) (i : Fin d) : lin A k i ∈ Io S (Fin n × Fin d) :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)

section Main

variable [Algebra ℚ S]

lemma eval_pair_additive_first {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    {τ : Type} (u u' v : Fin d → MvPolynomial τ S) :
    ev2 h (fun i => u i + u' i) v = ev2 h u v + ev2 h u' v := by
  have := congrArg (aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2)) hA
  rw [map_add, aeval_eval_pair, aeval_eval_pair, aeval_eval_pair] at this
  have e0 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (0 : Fin 3) i + xs S d 1 i)) =
      fun i => u i + u' i := by funext i; simp [xs]
  have e1 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (0 : Fin 3) i)) = u := by
    funext i; simp [xs]
  have e2 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (1 : Fin 3) i)) = u' := by
    funext i; simp [xs]
  have e3 : (fun i => aeval (fun p : Fin 3 × Fin d => ![u, u', v] p.1 p.2) (xs S d (2 : Fin 3) i)) = v := by
    funext i; simp [xs]
  rw [e0, e1, e2, e3] at this
  exact this

lemma symm_of {h : MvPolynomial (Fin 2 × Fin d) S} (hs : ev2 h (xs S d 1) (xs S d 0) = h) {τ : Type}
    (u v : Fin d → MvPolynomial τ S) : ev2 h u v = ev2 h v u := by
  have := aeval_eval_pair (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h (xs S d 1) (xs S d 0)
  rw [hs] at this
  change aeval (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) h = _
  rw [this]
  congr 1 <;> funext i <;> simp [xs]

lemma lin_add_lin (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0) {n : ℕ}
    (k : Fin n) : (fun i => lin A k i + lin Ab k i) = xs S d k := by
  funext i
  simp only [lin, xs, ← Finset.sum_add_distrib, ← add_mul, ← map_add, hAA]
  simp

theorem step {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A 0 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab 1 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (aW : Fin d → MvPolynomial (Fin 1 × Fin d) S) (hW : ∀ i, aW i - lin A 0 i ∈ Io S (Fin 1 × Fin d) ^ 2)
    (hdiag : ev2 P (xs S d 0) aW - 1 ∈ Io S (Fin 1 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := by
  set W := P - 1 with hWdef
  set h := homogeneousComponent j W with hhdef
  have hR : W - h ∈ Io S _ ^ (j + 1) := sub_homogeneousComponent_mem hP
  have hh : h.IsHomogeneous j := homogeneousComponent_isHomogeneous j W
  have hhI : h ∈ Io S _ ^ j := by
    have := sub_mem hP (Ideal.pow_le_pow_right (Nat.le_succ j) hR)
    simpa using this
  have hmj : ∀ {σ : Type} {p : MvPolynomial σ S}, p ∈ Io S σ ^ (m + 1) → p ∈ Io S σ ^ (j + 1) :=
    fun hp => Ideal.pow_le_pow_right (by omega) hp
  have hsq : ∀ {τ : Type} {p : MvPolynomial τ S}, p ∈ Io S τ ^ 2 → p ∈ Io S τ :=
    fun hp => Ideal.pow_le_self two_ne_zero hp
  have hPW : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), ev2 P u v = 1 + ev2 W u v := by
    intro τ u v; rw [hWdef, eval_pair_sub, eval_pair_one]; ring
  have hTr : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), (∀ i, u i ∈ Io S τ) → (∀ i, v i ∈ Io S τ) →
      ev2 W u v - ev2 h u v ∈ Io S τ ^ (j + 1) := by
    intro τ u v hu hv
    rw [← eval_pair_sub]
    exact aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ hR
  have hEvW : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), (∀ i, u i ∈ Io S τ) → (∀ i, v i ∈ Io S τ) →
      ev2 W u v ∈ Io S τ ^ j := fun u v hu hv =>
    aeval_mem_pow _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv]) _ hP
  have hRep : ∀ {τ : Type} (u v u' v' : Fin d → MvPolynomial τ S), (∀ i, u i ∈ Io S τ) → (∀ i, v i ∈ Io S τ) →
      (∀ i, u' i ∈ Io S τ) → (∀ i, v' i ∈ Io S τ) → (∀ i, u i - u' i ∈ Io S τ ^ 2) →
      (∀ i, v i - v' i ∈ Io S τ ^ 2) → ev2 h u v - ev2 h u' v' ∈ Io S τ ^ (j + 1) := by
    intro τ u v u' v' hu hv hu' hv' huu hvv
    exact aeval_sub_mem_pow _ _ (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu, hv])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [hu', hv'])
      (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [huu, hvv]) j h hhI
  have hx : ∀ {n : ℕ} (k : Fin n) (i : Fin d), xs S d k i ∈ Io S (Fin n × Fin d) := fun k i => xs_mem k i
  have hl : ∀ {n : ℕ} (B : Fin d → Fin d → S) (k : Fin n) (i : Fin d), lin B k i ∈ Io S (Fin n × Fin d) :=
    fun B k i => lin_mem B k i

  have hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2) := by
    have hfF : ∀ i, fF i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hF i)) (add_mem (hx 0 i) (hx 1 i)); simpa using this
    have k1 : ev2 W fF (xs S d 2) - ev2 W (xs S d 0) (xs S d 2) - ev2 W (xs S d 1) (xs S d 2) ∈
        Io S _ ^ (j + 1) := by
      have e : ev2 W fF (xs S d 2) - ev2 W (xs S d 0) (xs S d 2) - ev2 W (xs S d 1) (xs S d 2) =
          (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) +
            ev2 W (xs S d 0) (xs S d 2) * ev2 W (xs S d 1) (xs S d 2) := by
        rw [hPW, hPW, hPW]; ring
      rw [e]
      refine add_mem (hmj hph1) (Ideal.pow_le_pow_right (by omega : j + 1 ≤ j + j) ?_)
      rw [pow_add]
      exact Ideal.mul_mem_mul (hEvW _ _ (hx 0) (hx 2)) (hEvW _ _ (hx 1) (hx 2))
    have k3 := hRep fF (xs S d 2) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) hfF (hx 2)
      (fun i => add_mem (hx 0 i) (hx 1 i)) (hx 2) hF (fun i => by simp)
    have hE : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2) -
        ev2 h (xs S d 1) (xs S d 2) ∈ Io S _ ^ (j + 1) := by
      have e : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2) -
          ev2 h (xs S d 1) (xs S d 2) =
          (ev2 W fF (xs S d 2) - ev2 W (xs S d 0) (xs S d 2) - ev2 W (xs S d 1) (xs S d 2)) -
            (ev2 W fF (xs S d 2) - ev2 h fF (xs S d 2)) + (ev2 W (xs S d 0) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2)) +
            (ev2 W (xs S d 1) (xs S d 2) - ev2 h (xs S d 1) (xs S d 2)) -
            (ev2 h fF (xs S d 2) - ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) := by ring
      rw [e]
      exact sub_mem (add_mem (add_mem (sub_mem k1 (hTr _ _ hfF (hx 2))) (hTr _ _ (hx 0) (hx 2)))
        (hTr _ _ (hx 1) (hx 2))) k3
    have hom : (ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) - ev2 h (xs S d 0) (xs S d 2) -
        ev2 h (xs S d 1) (xs S d 2)).IsHomogeneous j :=
      ((eval_pair_homogeneous hh _ _ (fun i => (xs_hom 0 i).add (xs_hom 1 i)) (xs_hom 2)).sub
        (eval_pair_homogeneous hh _ _ (xs_hom 0) (xs_hom 2))).sub (eval_pair_homogeneous hh _ _ (xs_hom 1) (xs_hom 2))
    have := eq_zero_of_isHomogeneous hom hE
    rw [sub_sub, sub_eq_zero] at this
    exact this

  have hs : ev2 h (xs S d 1) (xs S d 0) = h := by
    have k : ev2 h (xs S d 1) (xs S d 0) - h ∈ Io S _ ^ (j + 1) := by
      have e : ev2 h (xs S d 1) (xs S d 0) - h = (ev2 P (xs S d 1) (xs S d 0) - P) -
          (ev2 W (xs S d 1) (xs S d 0) - ev2 h (xs S d 1) (xs S d 0)) + (W - h) := by
        rw [hPW, hWdef]; ring
      rw [e]
      exact add_mem (sub_mem (hmj hsym) (hTr _ _ (hx 1) (hx 0))) hR
    have := eq_zero_of_isHomogeneous ((eval_pair_homogeneous hh _ _ (xs_hom 1) (xs_hom 0)).sub hh) k
    exact sub_eq_zero.1 this
  have add1 : ∀ {τ : Type} (u u' v : Fin d → MvPolynomial τ S),
      ev2 h (fun i => u i + u' i) v = ev2 h u v + ev2 h u' v := fun u u' v => eval_pair_additive_first hA1 u u' v
  have symm : ∀ {τ : Type} (u v : Fin d → MvPolynomial τ S), ev2 h u v = ev2 h v u :=
    fun u v => symm_of hs u v
  have add2 : ∀ {τ : Type} (u v v' : Fin d → MvPolynomial τ S),
      ev2 h u (fun i => v i + v' i) = ev2 h u v + ev2 h u v' := by
    intro τ u v v'
    rw [symm, add1, symm v u, symm v' u]
  suffices h0 : h = 0 by
    have := add_mem hR (show h ∈ Io S _ ^ (j + 1) by rw [h0]; exact zero_mem _)
    simpa using this
  by_cases hj2 : j = 2
  · have haW : ∀ i, aW i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hW i)) (hl A 0 i); simpa using this
    have haW0 : ∀ i, aW0 i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hW0 i)) (hl A 0 i); simpa using this
    have haB1 : ∀ i, aB1 i ∈ Io S _ := fun i => by
      have := add_mem (hsq (hB1 i)) (hl Ab 1 i); simpa using this
    have hd1 : ev2 h (xs S d (0 : Fin 1)) (lin A 0) = 0 := by
      have k : ev2 h (xs S d (0 : Fin 1)) (lin A 0) ∈ Io S _ ^ (j + 1) := by
        have e : ev2 h (xs S d (0 : Fin 1)) (lin A 0) = (ev2 P (xs S d 0) aW - 1) -
            (ev2 W (xs S d 0) aW - ev2 h (xs S d 0) aW) - (ev2 h (xs S d 0) aW - ev2 h (xs S d 0) (lin A 0)) := by
          rw [hPW]; ring
        rw [e]
        exact sub_mem (sub_mem (hmj hdiag) (hTr _ _ (hx 0) haW))
          (hRep _ _ _ _ (hx 0) haW (hx 0) (hl A 0) (fun i => by simp) hW)
      exact eq_zero_of_isHomogeneous (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom A 0)) k
    have hb1 : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) = ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) := by
      have k : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) ∈ Io S _ ^ (j + 1) := by
        have e : ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2)) - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2)) =
            (ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1) -
            (ev2 W aW0 (xs S d 1) - ev2 h aW0 (xs S d 1)) + (ev2 W (xs S d 0) aB1 - ev2 h (xs S d 0) aB1) -
            (ev2 h aW0 (xs S d 1) - ev2 h (lin A (0 : Fin 2)) (xs S d (1 : Fin 2))) +
            (ev2 h (xs S d 0) aB1 - ev2 h (xs S d (0 : Fin 2)) (lin Ab (1 : Fin 2))) := by
          rw [hPW, hPW]; ring
        rw [e]
        exact add_mem (sub_mem (add_mem (sub_mem (hmj hbal) (hTr _ _ haW0 (hx 1))) (hTr _ _ (hx 0) haB1))
          (hRep _ _ _ _ haW0 (hx 1) (hl A 0) (hx 1) hW0 (fun i => by simp)))
          (hRep _ _ _ _ (hx 0) haB1 (hx 0) (hl Ab 1) (fun i => by simp) hB1)
      exact sub_eq_zero.1 (eq_zero_of_isHomogeneous
        ((eval_pair_homogeneous hh _ _ (lin_hom A 0) (xs_hom 1)).sub (eval_pair_homogeneous hh _ _ (xs_hom 0) (lin_hom Ab 1))) k)
    have hsub : ∀ (g : Fin 1 × Fin d → MvPolynomial (Fin 2 × Fin d) S),
        ev2 h (fun i => aeval g (xs S d (0 : Fin 1) i)) (fun i => aeval g (lin A (0 : Fin 1) i)) = 0 := by
      intro g; rw [← aeval_eval_pair, hd1, map_zero]
    have hd0 : ev2 h (xs S d (0 : Fin 2)) (lin A 0) = 0 := by
      have := hsub (fun p => xs S d (0 : Fin 2) p.2); simp [xs, lin] at this; exact this
    have hd1' : ev2 h (xs S d (1 : Fin 2)) (lin A 1) = 0 := by
      have := hsub (fun p => xs S d (1 : Fin 2) p.2); simp [xs, lin] at this; exact this
    have hd01 : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 1 i) (fun i => lin A 0 i + lin A 1 i) = 0 := by
      have := hsub (fun p => xs S d (0 : Fin 2) p.2 + xs S d 1 p.2)
      simpa [xs, lin, mul_add, Finset.sum_add_distrib] using this
    have e1 : ev2 h (xs S d (0 : Fin 2)) (lin A (1 : Fin 2)) + ev2 h (xs S d (1 : Fin 2)) (lin A (0 : Fin 2)) = 0 := by
      have := hd01
      rw [add1, add2, add2] at this
      linear_combination this - hd0 - hd1'
    rw [symm (xs S d (1 : Fin 2)) (lin A (0 : Fin 2)), hb1] at e1
    have e2 : ev2 h (xs S d (0 : Fin 2)) (fun i => lin A (1 : Fin 2) i + lin Ab (1 : Fin 2) i) = 0 := by
      rw [add2]; linear_combination e1
    rw [lin_add_lin A Ab hAA 1, eval_pair_coordinates] at e2
    exact e2
  · have h2x : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 0 i) (xs S d 1) = h + h := by
      rw [add1, eval_pair_coordinates]
    have h4 : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 0 i) (fun i => xs S d 1 i + xs S d 1 i) =
        h + h + (h + h) := by
      rw [add2, h2x]
    have hf : (fun p : Fin 2 × Fin d =>
        ![fun i => xs S d (0 : Fin 2) i + xs S d 0 i, fun i => xs S d 1 i + xs S d 1 i] p.1 p.2) =
        fun p => X p + X p := by
      funext p; rcases p with ⟨k, i⟩; fin_cases k <;> simp [xs]
    have hsc : ev2 h (fun i => xs S d (0 : Fin 2) i + xs S d 0 i) (fun i => xs S d 1 i + xs S d 1 i) =
        C ((2 : S) ^ j) * h := by
      rw [← aeval_double hh]
      show aeval _ h = _
      rw [hf]
    have h4' : C ((2 : S) ^ j - 4) * h = 0 := by
      have e4 : (C (4 : S) : MvPolynomial (Fin 2 × Fin d) S) = 4 := map_ofNat C 4
      rw [map_sub, sub_mul, ← hsc, h4, e4]; ring
    have hne : (2 : ℚ) ^ j - 4 ≠ 0 := by
      intro h0
      have h1 : ((2 ^ j : ℕ) : ℚ) = ((2 ^ 2 : ℕ) : ℚ) := by push_cast; linarith
      exact hj2 (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h1))
    have hu : IsUnit (C ((2 : S) ^ j - 4) : MvPolynomial (Fin 2 × Fin d) S) := by
      have e : ((2 : S) ^ j - 4) = algebraMap ℚ S ((2 : ℚ) ^ j - 4) := by
        rw [map_sub, map_pow, map_ofNat, map_ofNat]
      rw [e]; exact ((IsUnit.mk0 _ hne).map (algebraMap ℚ S)).map C
    exact hu.mul_right_eq_zero.1 h4'

theorem unit_eq_one {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A 0 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab 1 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (aW : Fin d → MvPolynomial (Fin 1 × Fin d) S) (hW : ∀ i, aW i - lin A 0 i ∈ Io S (Fin 1 × Fin d) ^ 2)
    (hdiag : ev2 P (xs S d 0) aW - 1 ∈ Io S (Fin 1 × Fin d) ^ (m + 1)) :
    P - 1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1) := by
  have hbase : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 1 := by
    have haW : ∀ i, aW i ∈ Io S _ := fun i => by
      have := add_mem (Ideal.pow_le_self two_ne_zero (hW i)) (lin_mem A 0 i); simpa using this
    set c := coeff 0 P with hcdef
    have h1 : ev2 (P - C c) (xs S d (0 : Fin 1)) aW ∈ Io S _ := by
      have h0 : P - C c ∈ Io S (Fin 2 × Fin d) ^ 1 := by simpa using sub_C_mem P
      have := aeval_mem_pow (fun p : Fin 2 × Fin d => ![xs S d (0 : Fin 1), aW] p.1 p.2)
        (fun p => by rcases p with ⟨k, i⟩; fin_cases k <;> simp [xs_mem, haW]) 1 h0
      rw [pow_one] at this
      exact this
    have e : ev2 P (xs S d (0 : Fin 1)) aW = ev2 (P - C c) (xs S d (0 : Fin 1)) aW + C c := by
      rw [eval_pair_sub]; simp [ev2]
    have h3 : C (c - 1) ∈ Io S (Fin 1 × Fin d) := by
      have := sub_mem (Ideal.pow_le_self (by omega : m + 1 ≠ 0) hdiag) h1
      have e2 : ev2 P (xs S d (0 : Fin 1)) aW - 1 - ev2 (P - C c) (xs S d (0 : Fin 1)) aW = C (c - 1) := by
        rw [e, map_sub, map_one]; ring
      rw [e2] at this; exact this
    have hc : c - 1 = 0 := by
      have := (C_mem_pow_idealOfVars_iff 1 (c - 1)).1 (by rw [pow_one]; exact h3)
      simpa using this
    have hc1 : c = 1 := by linear_combination hc
    have : P - 1 = P - C c := by rw [hc1, map_one]
    rw [this, pow_one]; exact sub_C_mem P
  have key : ∀ j, 1 ≤ j → j ≤ m + 1 → P - 1 ∈ Io S (Fin 2 × Fin d) ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact hbase
    | succ n hn ih =>
      intro hn'
      exact step hn (by omega) fF hF hph1 hsym A Ab hAA aW0 aB1 hW0 hB1 hbal aW hW hdiag (ih (by omega))
  exact key (m + 1) (by omega) le_rfl

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1

open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

private theorem memIo_lemma {σ : Type} (n : ℕ) (p : MvPolynomial σ S) :
    p ∈ Io S σ ^ n ↔ ∀ x ∈ p.support, n ≤ Finsupp.degree x :=
  mem_pow_idealOfVars_iff n p

private theorem ccmem_lemma_2 {σ : Type} {n : ℕ} {p : MvPolynomial σ S} (hp : p ∈ Io S σ ^ (n + 1)) :
    coeff 0 p = 0 := by
  by_contra hne
  have h := (memIo_lemma (n + 1) p).1 hp 0 (MvPolynomial.mem_support_iff.2 hne)
  simp [Finsupp.degree] at h

private theorem ccaeval_lemma_3 {σ τ : Type} (g : σ → MvPolynomial τ S) (hg : ∀ i, constantCoeff (g i) = 0)
    (p : MvPolynomial σ S) : constantCoeff (aeval g p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq, constantCoeff_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, constantCoeff_X, hg, mul_zero]

private theorem memcc_lemma_19 {σ : Type} {p : MvPolynomial σ S} (hp : constantCoeff p = 0) :
    p ∈ Io S σ ^ 1 := by
  rw [memIo_lemma]
  intro x hx
  by_contra hlt
  have h0 : Finsupp.degree x = 0 := by omega
  have hs : ∑ j ∈ x.support, x j = 0 := h0
  have hx0 : x = 0 := by
    ext i
    by_contra hi
    exact hi ((Finset.sum_eq_zero_iff.1 hs) i (Finsupp.mem_support_iff.2 hi))
  subst hx0
  exact (MvPolynomial.mem_support_iff.1 hx) hp

private theorem weak_lemma_24 {σ : Type} {m n : ℕ} (h : m ≤ n) {p : MvPolynomial σ S}
    (hp : p ∈ Io S σ ^ n) : p ∈ Io S σ ^ m := by
  rw [memIo_lemma] at hp ⊢
  intro x hx
  have := hp x hx
  omega

private theorem base_lemma_17 {σ τ : Type} (g g' : σ → MvPolynomial τ S)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) (p : MvPolynomial σ S) :
    aeval g p - aeval g' p ∈ Io S τ ^ 2 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, sub_self, Submodule.zero_mem]
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, aeval_X, aeval_X]
    have e : aeval g p * g i - aeval g' p * g' i =
        aeval g p * (g i - g' i) + (aeval g p - aeval g' p) * g' i := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hgg i)) (Ideal.mul_mem_right _ _ hp)

private theorem subst_lemma_18 {σ τ : Type} (g g' : σ → MvPolynomial τ S) (hg : ∀ i, g i ∈ Io S τ ^ 1)
    (hgg : ∀ i, g i - g' i ∈ Io S τ ^ 2) (n : ℕ) :
    ∀ p ∈ Io S σ ^ n, aeval g p ∈ Io S τ ^ n ∧ aeval g p - aeval g' p ∈ Io S τ ^ (n + 1) := by
  have hcg : ∀ i, constantCoeff (g i) = 0 := fun i => ccmem_lemma_2 (n := 0) (hg i)
  induction n with
  | zero =>
    intro p _
    refine ⟨by simp, weak_lemma_24 (by norm_num) (base_lemma_17 g g' hgg p)⟩
  | succ n ih =>
    intro p hp
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro a ha b hb
      obtain ⟨h1, h2⟩ := ih a ha
      have hb0 : coeff 0 b = 0 := ccmem_lemma_2 (n := 0) (p := b) (by rwa [zero_add, pow_one])
      have hb1 : aeval g b ∈ Io S τ ^ 1 := by
        apply memcc_lemma_19
        rw [ccaeval_lemma_3 g hcg]
        exact hb0
      have hb2 : aeval g b - aeval g' b ∈ Io S τ ^ 2 := base_lemma_17 g g' hgg b
      have hb3 : aeval g' b ∈ Io S τ ^ 1 := by
        have h := Ideal.sub_mem _ hb1 (weak_lemma_24 (by norm_num) hb2)
        simpa using h
      constructor
      · rw [map_mul, pow_succ]
        exact Ideal.mul_mem_mul h1 (by rwa [pow_one] at hb1)
      · rw [map_mul, map_mul]
        have e : aeval g a * aeval g b - aeval g' a * aeval g' b =
            aeval g a * (aeval g b - aeval g' b) + (aeval g a - aeval g' a) * aeval g' b := by ring
        rw [e]
        have k1 := Ideal.mul_mem_mul h1 hb2
        have k2 := Ideal.mul_mem_mul h2 hb3
        rw [← pow_add] at k1 k2
        have e1 : n + 2 = n + 1 + 1 := by omega
        rw [e1] at k1
        exact Ideal.add_mem _ k1 k2
    · intro x y hx hy
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      constructor
      · rw [map_add]
        exact Ideal.add_mem _ hx1 hy1
      · rw [map_add, map_add, add_sub_add_comm]
        exact Ideal.add_mem _ hx2 hy2

private theorem ev2sub_lemma_25 {τ : Type} (u v u' v' : Fin d → MvPolynomial τ S)
    (hu : ∀ i, u i ∈ Io S τ ^ 1) (hv : ∀ i, v i ∈ Io S τ ^ 1)
    (huu : ∀ i, u i - u' i ∈ Io S τ ^ 2) (hvv : ∀ i, v i - v' i ∈ Io S τ ^ 2)
    (n : ℕ) (p : MvPolynomial (Fin 2 × Fin d) S) (hp : p ∈ Io S (Fin 2 × Fin d) ^ n) :
    ev2 p u v ∈ Io S τ ^ n ∧ ev2 p u v - ev2 p u' v' ∈ Io S τ ^ (n + 1) := by
  refine subst_lemma_18 _ _ ?_ ?_ n p hp
  · rintro ⟨k, i⟩
    fin_cases k
    · simpa using hu i
    · simpa using hv i
  · rintro ⟨k, i⟩
    fin_cases k
    · simpa using huu i
    · simpa using hvv i

private theorem wtdeg_lemma_20 {σ : Type} (e : σ →₀ ℕ) : Finsupp.weight 1 e = Finsupp.degree e := by
  rw [Finsupp.weight_apply]
  show (e.sum fun i c => c • (1 : σ → ℕ) i) = ∑ i ∈ e.support, e i
  simp [Finsupp.sum]

private theorem hX_lemma_22 {σ : Type} (i : σ) : (X i : MvPolynomial σ S).IsHomogeneous 1 := by
  classical
  intro e he
  rw [coeff_X'] at he
  split_ifs at he with h
  · rw [← h]
    simp [Finsupp.weight_apply, Finsupp.sum_single_index]
  · exact absurd rfl he

private theorem homog_lemma_21 {σ τ : Type} {p : MvPolynomial σ S} {j : ℕ} (hp : p.IsHomogeneous j)
    (g : σ → MvPolynomial τ S) (hg : ∀ i, (g i).IsHomogeneous 1) : (aeval g p).IsHomogeneous j := by
  have h := hp.eval₂ C g (fun r => isHomogeneous_C _ r) hg
  rw [one_mul] at h
  rw [aeval_def, algebraMap_eq]
  exact h

private theorem ev2homog_lemma_23 {τ : Type} {p : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ}
    (hp : p.IsHomogeneous j) (u v : Fin d → MvPolynomial τ S) (hu : ∀ i, (u i).IsHomogeneous 1)
    (hv : ∀ i, (v i).IsHomogeneous 1) : (ev2 p u v).IsHomogeneous j := by
  apply homog_lemma_21 hp
  rintro ⟨k, i⟩
  fin_cases k
  · simpa using hu i
  · simpa using hv i

private theorem zeroOf_lemma_26 {τ : Type} {p : MvPolynomial τ S} {j : ℕ} (hh : p.IsHomogeneous j)
    (hp : p ∈ Io S τ ^ (j + 1)) : p = 0 := by
  ext e
  rw [coeff_zero]
  by_contra he
  have h1 : Finsupp.weight 1 e = j := hh he
  have h2 := (memIo_lemma (j + 1) p).1 hp e (MvPolynomial.mem_support_iff.2 he)
  rw [wtdeg_lemma_20] at h1
  omega

theorem lead_biadd {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) :
    ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
        ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) +
          ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) ∧
      ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) = homogeneousComponent j (P - 1) := by
  have hxJ : ∀ (k : Fin 3) (i : Fin d), xs S d k i ∈ Io S (Fin 3 × Fin d) ^ 1 :=
    fun k i => memcc_lemma_19 (by simp [xs])
  have hyJ : ∀ (k : Fin 2) (i : Fin d), xs S d k i ∈ Io S (Fin 2 × Fin d) ^ 1 :=
    fun k i => memcc_lemma_19 (by simp [xs])
  have haJ : ∀ i, xs S d (0 : Fin 3) i + xs S d 1 i ∈ Io S (Fin 3 × Fin d) ^ 1 :=
    fun i => Ideal.add_mem _ (hxJ 0 i) (hxJ 1 i)
  have hfJ : ∀ i, fF i ∈ Io S (Fin 3 × Fin d) ^ 1 := by
    intro i
    have h := Ideal.add_mem _ (weak_lemma_24 (by norm_num) (hF i)) (haJ i)
    simpa using h
  have hR : P - 1 - homogeneousComponent j (P - 1) ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := by
    have hP' := hP
    rw [memIo_lemma] at hP' ⊢
    intro x hx
    rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hx
    split_ifs at hx with hxj
    · simp at hx
    · have hxQ : x ∈ (P - 1).support := by
        rw [MvPolynomial.mem_support_iff]
        simpa using hx
      have := hP' x hxQ
      omega
  have hQj := homogeneousComponent_isHomogeneous j (P - 1)
  have hXh : ∀ (k : Fin 3) (i : Fin d), (xs S d k i).IsHomogeneous 1 := fun k i => hX_lemma_22 _
  have hYh : ∀ (k : Fin 2) (i : Fin d), (xs S d k i).IsHomogeneous 1 := fun k i => hX_lemma_22 _
  have z2 : ∀ (w : Fin d → MvPolynomial (Fin 3 × Fin d) S) (i : Fin d), w i - w i ∈ Io S (Fin 3 × Fin d) ^ 2 := by
    intro w i
    simp
  have y2 : ∀ (w : Fin d → MvPolynomial (Fin 2 × Fin d) S) (i : Fin d), w i - w i ∈ Io S (Fin 2 × Fin d) ^ 2 := by
    intro w i
    simp
  constructor
  · have m1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
        Io S (Fin 3 × Fin d) ^ (j + 1) := weak_lemma_24 (by omega) hph1
    have m2 := (ev2sub_lemma_25 fF (xs S d (2 : Fin 3)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i)
      (xs S d (2 : Fin 3)) hfJ (hxJ 2) hF (z2 _) j (P - 1) hP).2
    have m3 := (ev2sub_lemma_25 (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d (2 : Fin 3))
      (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d (2 : Fin 3)) haJ (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1
    have m4 := (ev2sub_lemma_25 (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 0) (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1
    have m5 := (ev2sub_lemma_25 (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 1) (hxJ 2) (z2 _) (z2 _) (j + 1) _ hR).1
    have t4 := (ev2sub_lemma_25 (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (0 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 0) (hxJ 2) (z2 _) (z2 _) j _ hP).1
    have t5 := (ev2sub_lemma_25 (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3)) (xs S d (1 : Fin 3)) (xs S d (2 : Fin 3))
      (hxJ 1) (hxJ 2) (z2 _) (z2 _) j _ hP).1
    have m6 : ev2 (P - 1) (xs S d 0) (xs S d 2) * ev2 (P - 1) (xs S d 1) (xs S d 2) ∈
        Io S (Fin 3 × Fin d) ^ (j + 1) := by
      have h := Ideal.mul_mem_mul t4 t5
      rw [← pow_add] at h
      exact weak_lemma_24 (by omega) h
    have hE : ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) -
        ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) -
        ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) = 0 := by
      apply zeroOf_lemma_26
      · exact ((ev2homog_lemma_23 hQj _ _ (fun i => (hXh 0 i).add (hXh 1 i)) (hXh 2)).sub
          (ev2homog_lemma_23 hQj _ _ (hXh 0) (hXh 2))).sub (ev2homog_lemma_23 hQj _ _ (hXh 1) (hXh 2))
      · have hid : ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) -
            ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) -
            ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) =
            (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) -
            (ev2 (P - 1) fF (xs S d 2) - ev2 (P - 1) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) -
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) +
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) +
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) +
            ev2 (P - 1) (xs S d 0) (xs S d 2) * ev2 (P - 1) (xs S d 1) (xs S d 2) := by
          simp only [ev2, map_sub, map_one]
          ring
        rw [hid]
        exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
          (Ideal.sub_mem _ (Ideal.sub_mem _ m1 m2) m3) m4) m5) m6
    linear_combination hE
  · have s1 : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := weak_lemma_24 (by omega) hsym
    have s2 := (ev2sub_lemma_25 (xs S d (1 : Fin 2)) (xs S d (0 : Fin 2)) (xs S d (1 : Fin 2)) (xs S d (0 : Fin 2))
      (hyJ 1) (hyJ 0) (y2 _) (y2 _) (j + 1) _ hR).1
    have hE : ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) - homogeneousComponent j (P - 1) = 0 := by
      apply zeroOf_lemma_26
      · exact (ev2homog_lemma_23 hQj _ _ (hYh 1) (hYh 0)).sub hQj
      · have hid : ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) - homogeneousComponent j (P - 1) =
            (ev2 P (xs S d 1) (xs S d 0) - P) -
            ev2 (P - 1 - homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) +
            (P - 1 - homogeneousComponent j (P - 1)) := by
          simp only [ev2, map_sub, map_one]
          ring
        rw [hid]
        exact Ideal.add_mem _ (Ideal.sub_mem _ s1 s2) hR
    linear_combination hE

private theorem monoDiag_lemma_4 {σ : Type} (s : σ → S) (e : σ →₀ ℕ) (a : S) :
    aeval (fun p => C (s p) * X p) (monomial e a) = monomial e ((e.prod fun p k => s p ^ k) * a) := by
  rw [aeval_monomial, algebraMap_eq, monomial_eq, C_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring

private theorem coeffDiag_lemma_5 {σ : Type} (s : σ → S) (h : MvPolynomial σ S) (e : σ →₀ ℕ) :
    coeff e (aeval (fun p => C (s p) * X p) h) = (e.prod fun p k => s p ^ k) * coeff e h := by
  classical
  conv_lhs => rw [h.as_sum]
  rw [map_sum, coeff_sum]
  simp only [monoDiag_lemma_4, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro he
    simp only [MvPolynomial.mem_support_iff, not_not] at he
    rw [if_pos rfl, he, mul_zero]

private theorem cancel_lemma_6 {a : ℕ} (ha : a ≠ 1) {c : S} (h : (2 : S) ^ a * c = 2 * c) : c = 0 := by
  have hq : ((2 : ℚ) ^ a - 2) ≠ 0 := by
    intro h0
    have h1 : ((2 ^ a : ℕ) : ℚ) = ((2 : ℕ) : ℚ) := by
      push_cast
      linarith
    have h2 : 2 ^ a = 2 ^ 1 := by
      rw [pow_one]
      exact_mod_cast h1
    exact ha (Nat.pow_right_injective (le_refl 2) h2)
  have h3 : algebraMap ℚ S ((2 : ℚ) ^ a - 2) * c = 0 := by
    rw [map_sub, map_pow, map_ofNat]
    linear_combination h
  calc c = algebraMap ℚ S (((2 : ℚ) ^ a - 2)⁻¹ * ((2 : ℚ) ^ a - 2)) * c := by
        rw [inv_mul_cancel₀ hq, map_one, one_mul]
    _ = algebraMap ℚ S (((2 : ℚ) ^ a - 2)⁻¹) * (algebraMap ℚ S ((2 : ℚ) ^ a - 2) * c) := by
        rw [map_mul, mul_assoc]
    _ = 0 := by rw [h3, mul_zero]

private theorem prod_ite_pow_eq_two_pow_sum (k : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) :
    (e.prod fun p n => (if p.1 = k then (2 : S) else 1) ^ n) = 2 ^ (∑ i, e (k, i)) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_two]
  fin_cases k <;> simp [Finset.prod_pow_eq_pow_sum]

private theorem comp_lemma_9 {σ τ υ : Type} (g : σ → MvPolynomial τ S) (r : τ → MvPolynomial υ S)
    (p : MvPolynomial σ S) : aeval r (aeval g p) = aeval (fun i => aeval r (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]

private theorem aevalX_lemma_10 {σ : Type} (p : MvPolynomial σ S) : aeval X p = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]

private theorem wt_lemma_11 (e : Fin 2 × Fin d →₀ ℕ) :
    Finsupp.weight 1 e = (∑ i, e (0, i)) + ∑ i, e (1, i) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem aeval_double_fst_of_additive {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2)) :
    aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h = h + h := by
  obtain ⟨r, hr⟩ : ∃ r : Fin 3 × Fin d → MvPolynomial (Fin 2 × Fin d) S,
      ∀ q, r q = if q.1 = 2 then X (1, q.2) else X (0, q.2) := ⟨_, fun _ => rfl⟩
  have H := congrArg (aeval r) hA1
  have e1 : aeval r (ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) =
      aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h := by
    rw [ev2, comp_lemma_9]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨k, i⟩
    fin_cases k <;> simp [xs, hr]
    rw [← two_mul]
    congr 1
  have e2 : ∀ k : Fin 3, k ≠ 2 → aeval r (ev2 h (xs S d k) (xs S d 2)) = h := by
    intro k hk
    rw [ev2, comp_lemma_9]
    conv_rhs => rw [← aevalX_lemma_10 h]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨l, i⟩
    fin_cases l <;> simp [xs, hr, hk]
  rw [e1, map_add, e2 0 (by decide), e2 1 (by decide)] at H
  exact H

private theorem aeval_double_snd_of_symm {h : MvPolynomial (Fin 2 × Fin d) S}
    (h0 : aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h = h + h)
    (hs : ev2 h (xs S d (1 : Fin 2)) (xs S d 0) = h) :
    aeval (fun p : Fin 2 × Fin d => C (if p.1 = 1 then (2 : S) else 1) * X p) h = h + h := by
  obtain ⟨G, hG⟩ : ∃ G : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S,
      ∀ q, G q = if q.1 = 0 then C (2 : S) * X (1, q.2) else X (0, q.2) := ⟨_, fun _ => rfl⟩
  have e1 : aeval (fun p : Fin 2 × Fin d => C (if p.1 = 1 then (2 : S) else 1) * X p)
      (ev2 h (xs S d (1 : Fin 2)) (xs S d 0)) = aeval G h := by
    rw [ev2, comp_lemma_9]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨k, i⟩
    fin_cases k <;> simp [xs, hG]
  have e2 : ev2 (aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h)
      (xs S d (1 : Fin 2)) (xs S d 0) = aeval G h := by
    rw [ev2, comp_lemma_9]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨k, i⟩
    fin_cases k <;> simp [xs, hG]
  have e3 : ev2 (h + h) (xs S d (1 : Fin 2)) (xs S d 0) = h + h := by
    unfold ev2 at hs ⊢
    rw [map_add, hs]
  rw [hs] at e1
  rw [e1, ← e2, h0, e3]

private theorem row_degree_eq_one_of_aeval_double {h : MvPolynomial (Fin 2 × Fin d) S} (k : Fin 2)
    (hk : aeval (fun p : Fin 2 × Fin d => C (if p.1 = k then (2 : S) else 1) * X p) h = h + h)
    (e : Fin 2 × Fin d →₀ ℕ) (he : coeff e h ≠ 0) : ∑ i, e (k, i) = 1 := by
  by_contra hne
  apply he
  apply cancel_lemma_6 hne
  have H := congrArg (coeff e) hk
  rw [coeffDiag_lemma_5, prod_ite_pow_eq_two_pow_sum, coeff_add] at H
  rw [H, two_mul]

theorem zero_of_biadd {h : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ} (hh : h.IsHomogeneous j) (hj2 : j ≠ 2)
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    (hs : ev2 h (xs S d 1) (xs S d 0) = h) : h = 0 := by
  ext e
  rw [coeff_zero]
  by_contra he
  have h0 := row_degree_eq_one_of_aeval_double 0 (aeval_double_fst_of_additive hA1) e he
  have h1 := row_degree_eq_one_of_aeval_double 1 (aeval_double_snd_of_symm (aeval_double_fst_of_additive hA1) hs) e he
  have hw : Finsupp.weight 1 e = j := hh he
  rw [wt_lemma_11, h0, h1] at hw
  omega

theorem stepNo2 {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) (hj2 : j ≠ 2)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := by
  obtain ⟨hA, hs⟩ := lead_biadd hj1 hjm fF hF hph1 hsym hP
  have h0 := zero_of_biadd (homogeneousComponent_isHomogeneous j (P - 1)) hj2 hA hs
  rw [memIo_lemma] at hP ⊢
  intro x hx
  have hle := hP x hx
  rcases Nat.lt_or_ge j (Finsupp.degree x) with hlt | hge
  · omega
  · exfalso
    have hxj : Finsupp.degree x = j := le_antisymm hge hle
    have hcx := congrArg (coeff x) h0
    rw [coeff_homogeneousComponent, if_pos hxj, coeff_zero] at hcx
    exact (MvPolynomial.mem_support_iff.1 hx) hcx

theorem eq_one_of_cube {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (h3 : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 3) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1) := by
  have key : ∀ k, 3 + k ≤ m + 1 → P - 1 ∈ Io S (Fin 2 × Fin d) ^ (3 + k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using h3
    | succ k ih =>
      intro hk
      have h := stepNo2 (j := 3 + k) (by omega) (by omega) (by omega) fF hF hph1 hsym (ih (by omega))
      have e : 3 + (k + 1) = 3 + k + 1 := by omega
      rw [e]
      exact h
  by_cases hm : m + 1 ≤ 3
  · rw [memIo_lemma] at h3 ⊢
    intro x hx
    have := h3 x hx
    omega
  · have h := key (m + 1 - 3) (by omega)
    have e : 3 + (m + 1 - 3) = m + 1 := by omega
    rw [e] at h
    exact h

theorem const_one {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hu : IsUnit (coeff 0 P)) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 1 := by
  have hx : ∀ (k : Fin 3) (i : Fin d), constantCoeff (xs S d k i) = 0 := by
    intro k i
    simp [xs]
  have hfF : ∀ i, constantCoeff (fF i) = 0 := by
    intro i
    have h2 : coeff 0 (fF i - (xs S d 0 i + xs S d 1 i)) = 0 := ccmem_lemma_2 (n := 1) (hF i)
    rw [coeff_sub, coeff_add] at h2
    have h0 : coeff 0 (xs S d 0 i) = 0 := hx 0 i
    have h1 : coeff 0 (xs S d 1 i) = 0 := hx 1 i
    rw [h0, h1, add_zero, sub_zero] at h2
    exact h2
  have key : ∀ u v : Fin d → MvPolynomial (Fin 3 × Fin d) S, (∀ i, constantCoeff (u i) = 0) →
      (∀ i, constantCoeff (v i) = 0) → constantCoeff (ev2 P u v) = coeff 0 P := by
    intro u v hu hv
    rw [ev2, ccaeval_lemma_3]
    · rfl
    · rintro ⟨k, i⟩
      fin_cases k
      · simpa using hu i
      · simpa using hv i
  have h1 : constantCoeff (ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2)) = 0 :=
    ccmem_lemma_2 hph1
  rw [map_sub, map_mul, key _ _ hfF (hx 2), key _ _ (hx 0) (hx 2), key _ _ (hx 1) (hx 2)] at h1
  have h2 : coeff 0 P * (1 - coeff 0 P) = 0 := by linear_combination h1
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have h3 : 1 - coeff 0 P = 0 := by
    calc 1 - coeff 0 P = (v * coeff 0 P) * (1 - coeff 0 P) := by rw [hv, one_mul]
      _ = v * (coeff 0 P * (1 - coeff 0 P)) := by ring
      _ = 0 := by rw [h2, mul_zero]
  rw [memIo_lemma]
  intro x hx
  by_contra hlt
  have h0 : Finsupp.degree x = 0 := by omega
  have hs : ∑ j ∈ x.support, x j = 0 := h0
  have hx0 : x = 0 := by
    ext i
    by_contra hi
    exact hi ((Finset.sum_eq_zero_iff.1 hs) i (Finsupp.mem_support_iff.2 hi))
  subst hx0
  apply MvPolynomial.mem_support_iff.1 hx
  rw [coeff_sub, coeff_zero_one]
  linear_combination -h3

theorem aeval_diag_monomial {σ : Type} (s : σ → S) (e : σ →₀ ℕ) (a : S) :
    aeval (fun p => C (s p) * X p) (monomial e a) = monomial e ((e.prod fun p k => s p ^ k) * a) := by
  apply monoDiag_lemma_4 (s := s) (e := e) (a := a) <;> assumption

theorem coeff_aeval_diag {σ : Type} (s : σ → S) (h : MvPolynomial σ S) (e : σ →₀ ℕ) :
    coeff e (aeval (fun p => C (s p) * X p) h) = (e.prod fun p k => s p ^ k) * coeff e h := by
  classical
  conv_lhs => rw [h.as_sum]
  rw [map_sum, coeff_sum]
  simp only [aeval_diag_monomial, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro he
    simp only [MvPolynomial.mem_support_iff, not_not] at he
    rw [if_pos rfl, he, mul_zero]

theorem prod_position (k : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) :
    (e.prod fun p n => (if p.1 = k then (2 : S) else 1) ^ n) = 2 ^ (∑ i, e (k, i)) := by
  apply prod_ite_pow_eq_two_pow_sum (k := k) (e := e) <;> assumption

private theorem coeffXX_lemma_15 (c : S) (a b : Fin 2 × Fin d) (e : Fin 2 × Fin d →₀ ℕ) :
    coeff e (C c * (X a * X b)) = if Finsupp.single a 1 + Finsupp.single b 1 = e then c else 0 := by
  rw [X, X, monomial_mul, C_mul_monomial, coeff_monomial, mul_one, mul_one]

private theorem one_lemma_16 (f : Fin d → ℕ) (hs : ∑ i, f i = 1) (i0 : Fin d) (h0 : f i0 ≠ 0) (i : Fin d) :
    f i = if i = i0 then 1 else 0 := by
  have hsplit := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i0)
  rw [hs] at hsplit
  have hi0 : f i0 = 1 := by omega
  have hrest : ∑ x ∈ Finset.univ.erase i0, f x = 0 := by omega
  split_ifs with hi
  · rw [hi, hi0]
  · exact (Finset.sum_eq_zero_iff.1 hrest) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)

theorem bilin_of_biadd {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    (hs : ev2 h (xs S d 1) (xs S d 0) = h) :
    h = ∑ i, ∑ l, C (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1) h) *
      (X ((0 : Fin 2), i) * X ((1 : Fin 2), l)) := by
  have h0 := aeval_double_fst_of_additive hA1
  have h1 := aeval_double_snd_of_symm h0 hs
  ext e
  simp only [coeff_sum, coeffXX_lemma_15]
  by_cases hz : coeff e h = 0
  · rw [hz]
    symm
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun l _ => ?_))
    split_ifs with heq <;> simp only [heq, hz]
  · have hs0 := row_degree_eq_one_of_aeval_double 0 h0 e hz
    have hs1 := row_degree_eq_one_of_aeval_double 1 h1 e hz
    have hne0 : ∑ i, e (0, i) ≠ 0 := by
      rw [hs0]
      exact one_ne_zero
    have hne1 : ∑ i, e (1, i) ≠ 0 := by
      rw [hs1]
      exact one_ne_zero
    obtain ⟨i0, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
    obtain ⟨l0, -, hl0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne1
    have hE : e = Finsupp.single ((0 : Fin 2), i0) 1 + Finsupp.single ((1 : Fin 2), l0) 1 := by
      ext ⟨k, i⟩
      revert k
      rw [Fin.forall_fin_two]
      constructor
      · have hu := one_lemma_16 (fun i => e (0, i)) hs0 i0 hi0 i
        rw [hu]
        by_cases hii : i = i0
        · subst hii
          simp [Finsupp.single_apply]
        · simp [Finsupp.single_apply, hii, Ne.symm hii]
      · have hu := one_lemma_16 (fun i => e (1, i)) hs1 l0 hl0 i
        rw [hu]
        by_cases hii : i = l0
        · subst hii
          simp [Finsupp.single_apply]
        · simp [Finsupp.single_apply, hii, Ne.symm hii]
    subst hE
    rw [Finset.sum_eq_single i0, Finset.sum_eq_single l0, if_pos rfl]
    · intro l _ hl
      rw [if_neg]
      intro heq
      have := congrArg (fun f => f ((1 : Fin 2), l)) heq
      simp [Finsupp.single_apply, Ne.symm hl] at this
    · intro h'
      exact absurd (Finset.mem_univ _) h'
    · intro i _ hi
      refine Finset.sum_eq_zero (fun l _ => ?_)
      rw [if_neg]
      intro heq
      have := congrArg (fun f => f ((0 : Fin 2), i)) heq
      simp [Finsupp.single_apply, Ne.symm hi] at this
    · intro h'
      exact absurd (Finset.mem_univ _) h'

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2

open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)

variable {S : Type} [CommRing S] {d : ℕ}

theorem jetSubstP_mk {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval (fun i => φ i - C (constantCoeff (φ i))) P) := rfl

theorem mk_eq_iff {κ : Type} (m : ℕ) (a b : MvPolynomial κ S) :
    Ideal.Quotient.mk (orig S κ ^ (m + 1)) a = Ideal.Quotient.mk (orig S κ ^ (m + 1)) b ↔
      a - b ∈ Io S κ ^ (m + 1) := by
  rw [Ideal.Quotient.eq]
  exact Iff.rfl

private theorem coeff_mul_eq_zero_lemma_4 {τ : Type} (A B : MvPowerSeries τ S) (a b : ℕ)
    (hA : ∀ x : τ →₀ ℕ, x.degree < a → MvPowerSeries.coeff x A = 0)
    (hB : ∀ x : τ →₀ ℕ, x.degree < b → MvPowerSeries.coeff x B = 0) :
    ∀ x : τ →₀ ℕ, x.degree < a + b → MvPowerSeries.coeff x (A * B) = 0 := by
  classical
  intro x hx
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  replace hp : p.1 + p.2 = x := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      | exact Finset.mem_antidiagonal.1 hp
      | simpa using hp
  have hdeg : p.1.degree + p.2.degree = x.degree := by
    rw [← hp]
    have e : ∀ y : τ →₀ ℕ, y.degree = y.sum (fun _ k => k) := fun y => by
      first
        | rfl
        | simp [Finsupp.degree, Finsupp.sum]
    rw [e, e, e, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  by_cases h1 : p.1.degree < a
  · rw [hA _ h1, zero_mul]
  · rw [hB _ (by omega), mul_zero]

private theorem order_prod_lemma_5 {τ τ' : Type} (σ' : τ' → MvPowerSeries τ S)
    (hσ : ∀ s, MvPowerSeries.constantCoeff (σ' s) = 0) (e : τ' →₀ ℕ) (x : τ →₀ ℕ)
    (hx : x.degree < e.degree) : MvPowerSeries.coeff x (e.prod fun s n => σ' s ^ n) = 0 := by
  classical
  have hpow : ∀ s (n : ℕ) (y : τ →₀ ℕ), y.degree < n → MvPowerSeries.coeff y (σ' s ^ n) = 0 := by
    intro s n
    induction n with
    | zero => intro y hy; omega
    | succ n ih =>
      intro y hy
      rw [pow_succ]
      refine coeff_mul_eq_zero_lemma_4 _ _ n 1 ih ?_ y (by omega)
      intro z hz
      have hz0 : z = 0 := by
        first
          | exact (Finsupp.degree_eq_zero_iff z).1 (by omega)
          | exact Finsupp.degree_eq_zero_iff.1 (by omega)
      rw [hz0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hσ]
  have hprod : ∀ (t : Finset τ') (y : τ →₀ ℕ), y.degree < ∑ s ∈ t, e s →
      MvPowerSeries.coeff y (∏ s ∈ t, σ' s ^ e s) = 0 := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro y hy
      simp at hy
    · intro a t ha ih y hy
      rw [Finset.prod_insert ha]
      rw [Finset.sum_insert ha] at hy
      exact coeff_mul_eq_zero_lemma_4 _ _ (e a) (∑ s ∈ t, e s) (hpow a (e a)) ih y hy
  have he : e.degree = ∑ s ∈ e.support, e s := by
    first
      | rfl
      | simp [Finsupp.degree]
  exact hprod e.support x (he ▸ hx)

private theorem eq_single_lemma_6 {κ : Type} (e : κ →₀ ℕ) (he : e.degree = 1) : ∃ q, e = Finsupp.single q 1 := by
  classical
  have h1 : ∑ i ∈ e.support, e i = 1 := by
    first
      | exact he
      | simpa [Finsupp.degree] using he
  obtain ⟨q, hq⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have h2 := Finset.add_sum_erase e.support e hq
  rw [h1] at h2
  have hq0 : e q ≠ 0 := Finsupp.mem_support_iff.1 hq
  have h3s : ∑ i ∈ e.support.erase q, e i = 0 := by omega
  have h3 := Finset.sum_eq_zero_iff.1 h3s
  refine ⟨q, ?_⟩
  ext i
  by_cases hi : i = q
  · subst hi
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_contra hne
    exact hne (h3 i (Finset.mem_erase.2 ⟨hi, Finsupp.mem_support_iff.2 hne⟩))

theorem formal_group_linear_second (G : FGLaw S d) (i j : Fin d) :
    MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0 := by
  have key : ∀ f : PS S 2 d, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)
      (ev (n := 1) ![0, pt S d 0] f) = MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) f := by
    intro f
    unfold ev
    have hσ : ∀ s : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![0, pt S d 0] : Fin 2 → Pt S 1 d) s.1 s.2) = 0 := by
      rintro ⟨a, l⟩
      obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      · simp
      · simp [pt]
    have hS : MvPowerSeries.HasSubst
        (fun s : Fin 2 × Fin d => (![0, pt S d 0] : Fin 2 → Pt S 1 d) s.1 s.2) := by
      first
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hσ
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hσ
        | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact ⟨fun s => by rw [hσ s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    rw [MvPowerSeries.coeff_subst hS]
    have hd1 : (Finsupp.single ((0 : Fin 1), j) 1).degree = 1 := by
      first
        | simp
        | simp [Finsupp.degree]
    rw [finsum_eq_single _ (Finsupp.single ((1 : Fin 2), j) 1)]
    · rw [Finsupp.prod_single_index (by simp)]
      simp [pt, MvPowerSeries.coeff_X]
    · intro e he
      rcases lt_trichotomy e.degree 1 with hlt | heq | hgt
      · have he0 : e = 0 := by
          first
            | exact (Finsupp.degree_eq_zero_iff e).1 (by omega)
            | exact Finsupp.degree_eq_zero_iff.1 (by omega)
        subst he0
        simp [MvPowerSeries.coeff_one]
      · obtain ⟨⟨q1, q2⟩, rfl⟩ := eq_single_lemma_6 e heq
        rw [Finsupp.prod_single_index (by simp)]
        obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp
        · simp
        · have hq : q2 ≠ j := fun h => he (by rw [h])
          simp [pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]
      · have h0 := order_prod_lemma_5 _ hσ e (Finsupp.single ((0 : Fin 1), j) 1) (by omega)
        first
          | simp only [h0, smul_zero]
          | rw [h0, smul_zero]
          | erw [h0, smul_zero]
  have hu := congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)) (G.unit i)
  rw [key, MvPowerSeries.coeff_X] at hu
  rw [hu]
  by_cases h : j = i
  · subst h
    simp
  · simp [Finsupp.single_left_inj one_ne_zero, h]

theorem formal_group_linear_first (G : FGLaw S d) (i j : Fin d) :
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0 := by
  have key : ∀ f : PS S 2 d, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)
      (ev (n := 2) ![pt S d 1, pt S d 0] f) = MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) f := by
    intro f
    unfold ev
    have hσ : ∀ s : Fin 2 × Fin d, MvPowerSeries.constantCoeff
        ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) s.1 s.2) = 0 := by
      rintro ⟨a, l⟩
      obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      · simp [pt]
      · simp [pt]
    have hS : MvPowerSeries.HasSubst
        (fun s : Fin 2 × Fin d => (![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) s.1 s.2) := by
      first
        | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hσ
        | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hσ
        | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [hσ s]; exact IsNilpotent.zero
        | exact ⟨fun s => by rw [hσ s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
    rw [MvPowerSeries.coeff_subst hS]
    have hd1 : (Finsupp.single ((0 : Fin 2), j) 1).degree = 1 := by
      first
        | simp
        | simp [Finsupp.degree]
    rw [finsum_eq_single _ (Finsupp.single ((1 : Fin 2), j) 1)]
    · rw [Finsupp.prod_single_index (by simp)]
      simp [pt, MvPowerSeries.coeff_X]
    · intro e he
      rcases lt_trichotomy e.degree 1 with hlt | heq | hgt
      · have he0 : e = 0 := by
          first
            | exact (Finsupp.degree_eq_zero_iff e).1 (by omega)
            | exact Finsupp.degree_eq_zero_iff.1 (by omega)
        subst he0
        simp [MvPowerSeries.coeff_one]
      · obtain ⟨⟨q1, q2⟩, rfl⟩ := eq_single_lemma_6 e heq
        rw [Finsupp.prod_single_index (by simp)]
        obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp
        · simp [pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero]
        · have hq : q2 ≠ j := fun h => he (by rw [h])
          simp [pt, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]
      · have h0 := order_prod_lemma_5 _ hσ e (Finsupp.single ((0 : Fin 2), j) 1) (by omega)
        first
          | simp only [h0, smul_zero]
          | rw [h0, smul_zero]
          | erw [h0, smul_zero]
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)) (G.comm i)
  rw [key] at hc
  rw [← hc]
  exact formal_group_linear_second G i j

theorem eq_single_of_degree_one {κ : Type} (e : κ →₀ ℕ) (he : e.degree = 1) : ∃ q, e = Finsupp.single q 1 := by
  apply eq_single_lemma_6 (e := e) (he := he) <;> assumption

private theorem mem_degLE_lemma {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ} {x : κ →₀ ℕ}
    (hx : x.degree ≤ n) : x ∈ degLE n := by
  have hle : ∀ i, x i ≤ n := by
    intro i
    by_cases hi : x i = 0
    · rw [hi]
      exact Nat.zero_le n
    · exact le_trans (Finset.single_le_sum (f := fun j => x j) (fun j _ => Nat.zero_le (x j))
        (Finsupp.mem_support_iff.2 hi)) hx
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨fun i => ⟨x i, Nat.lt_succ_of_le (hle i)⟩, Finset.mem_univ _, ?_⟩, hx⟩
  ext i
  simp

private theorem coeff_psTrunc_lemma_2 {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S) (n : ℕ)
    (x : κ →₀ ℕ) : coeff x (psTrunc n f) = if x.degree ≤ n then MvPowerSeries.coeff x f else 0 := by
  unfold psTrunc
  rw [coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq]
  by_cases h : x.degree ≤ n
  · rw [if_pos (mem_degLE_lemma h), if_pos h]
  · have h' : x ∉ degLE n := by
      intro h'
      unfold degLE at h'
      exact h (Finset.mem_filter.1 h').2
    rw [if_neg h', if_neg h]

private theorem mem_pow_Io_lemma_3 {κ : Type} (k : ℕ) (p : MvPolynomial κ S)
    (hp : ∀ x ∈ p.support, k ≤ x.degree) : p ∈ Io S κ ^ k := by
  have hX : ∀ i, (X i : MvPolynomial κ S) ∈ Io S κ := fun i => Ideal.subset_span ⟨i, rfl⟩
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun x hx => ?_
  rw [monomial_eq]
  refine Ideal.mul_mem_left _ _ ?_
  have h2 : x.degree = ∑ a ∈ x.support, x a := by
    first
      | rfl
      | simp [Finsupp.degree]
  have h1 : (x.prod fun n e => (X n : MvPolynomial κ S) ^ e) ∈ Io S κ ^ x.degree := by
    unfold Finsupp.prod
    rw [h2, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun a _ => Ideal.pow_mem_pow (hX a) _
  exact Ideal.pow_le_pow_right (hp x hx) h1

theorem psTrunc_law_sub_mem (G : FGLaw S d) {m : ℕ} (hm : 1 ≤ m) (j : Fin d) :
    psTrunc m (G.F j) - (X ((0 : Fin 2), j) + X ((1 : Fin 2), j)) ∈ Io S (Fin 2 × Fin d) ^ 2 := by
  apply mem_pow_Io_lemma_3
  intro x hx
  rw [mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2] at hx
  by_contra hlt
  have h1 : x.degree ≤ 1 := by omega
  rw [if_pos (h1.trans hm)] at hx
  apply hx
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h0
  · have hx0 : x = 0 := by
      first
        | exact (Finsupp.degree_eq_zero_iff x).1 h0
        | exact Finsupp.degree_eq_zero_iff.1 h0
    subst hx0
    simp [coeff_X', MvPowerSeries.coeff_zero_eq_constantCoeff_apply, G.const]
  · obtain ⟨⟨q1, q2⟩, rfl⟩ := eq_single_of_degree_one x h0
    obtain rfl | rfl : q1 = 0 ∨ q1 = 1 := by fin_cases q1 <;> simp
    · by_cases hq : q2 = j
      · subst hq
        simp [coeff_X', formal_group_linear_first, Finsupp.single_left_inj one_ne_zero]
      · simp [coeff_X', formal_group_linear_first, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]
    · by_cases hq : q2 = j
      · subst hq
        simp [coeff_X', formal_group_linear_second, Finsupp.single_left_inj one_ne_zero]
      · simp [coeff_X', formal_group_linear_second, Finsupp.single_left_inj one_ne_zero, hq, Ne.symm hq]

def bil (M : Fin d → Fin d → S) : MvPolynomial (Fin 2 × Fin d) S :=
  ∑ i, ∑ l, C (M i l) * (X ((0 : Fin 2), i) * X ((1 : Fin 2), l))

abbrev sil (i l : Fin d) : Fin 2 × Fin d →₀ ℕ := Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1

theorem sil_inj {i l i0 l0 : Fin d} : sil i l = sil i0 l0 ↔ i = i0 ∧ l = l0 := by
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h ((0 : Fin 2), i)
    have h2 := DFunLike.congr_fun h ((1 : Fin 2), l)
    constructor
    · by_contra hne
      simp [sil, Finsupp.single_apply, hne, Ne.symm hne] at h1
    · by_contra hne
      simp [sil, Finsupp.single_apply, hne, Ne.symm hne] at h2
  · rintro ⟨rfl, rfl⟩
    rfl

theorem coeff_XX (e : Fin 2 × Fin d →₀ ℕ) (i l : Fin d) :
    coeff e (X ((0 : Fin 2), i) * X ((1 : Fin 2), l) : MvPolynomial (Fin 2 × Fin d) S) =
      if sil i l = e then 1 else 0 := by
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]

theorem coeff_bil (M : Fin d → Fin d → S) (i0 l0 : Fin d) : coeff (sil i0 l0) (bil M) = M i0 l0 := by
  simp only [bil, coeff_sum, coeff_C_mul, coeff_XX, sil_inj]
  rw [Finset.sum_eq_single i0]
  · rw [Finset.sum_eq_single l0]
    · rw [if_pos ⟨rfl, rfl⟩, mul_one]
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro l _
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem bil_ext {M M' : Fin d → Fin d → S} (h : bil M = bil M') : M = M' := by
  funext i l
  have h' := congrArg (coeff (sil i l)) h
  rw [coeff_bil, coeff_bil] at h'
  exact h'

theorem bil_mem (M : Fin d → Fin d → S) : bil M ∈ Io S (Fin 2 × Fin d) ^ 2 := by
  have hX : ∀ p, (X p : MvPolynomial (Fin 2 × Fin d) S) ∈ Io S (Fin 2 × Fin d) :=
    fun p => Ideal.subset_span ⟨p, rfl⟩
  refine Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_
  rw [pow_two]
  exact Ideal.mul_mem_mul (hX _) (hX _)

theorem bil_hom (M : Fin d → Fin d → S) : (bil M).IsHomogeneous 2 := by
  unfold bil
  refine IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun l _ => ?_
  have h0 : (C (M i l) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 0 := by
    first
      | exact isHomogeneous_C _ _
      | exact isHomogeneous_C _
  have h1 : (X ((0 : Fin 2), i) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 1 := by
    first
      | exact isHomogeneous_X _ _
      | exact isHomogeneous_X _
  have h2 : (X ((1 : Fin 2), l) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 1 := by
    first
      | exact isHomogeneous_X _ _
      | exact isHomogeneous_X _
  simpa using h0.mul (h1.mul h2)

theorem psTrunc_sub_mem {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ S) {k m : ℕ} (hkm : k ≤ m) :
    psTrunc m f - psTrunc k f ∈ Io S κ ^ (k + 1) := by
  apply mem_pow_Io_lemma_3
  intro x hx
  rw [mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2, coeff_psTrunc_lemma_2] at hx
  by_contra hlt
  have h1 : x.degree ≤ k := by omega
  rw [if_pos (h1.trans hkm), if_pos h1, sub_self] at hx
  exact hx rfl

section Poly

variable [Algebra ℚ S]

open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1

theorem eval_pair_bilinear {τ : Type} (M : Fin d → Fin d → S) (u v : Fin d → MvPolynomial τ S) :
    ev2 (bil M) u v = ∑ i, ∑ l, C (M i l) * (u i * v l) := by
  simp [ev2, bil, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]

theorem lead_bil {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (hm : 2 ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hu : IsUnit (coeff 0 P)) :
    P - 1 ∈ Io S (Fin 2 × Fin d) ^ 2 ∧
      P - 1 - bil (fun i l => coeff (sil i l) (homogeneousComponent 2 (P - 1))) ∈ Io S (Fin 2 × Fin d) ^ 3 ∧
      ∀ i l, coeff (sil i l) (homogeneousComponent 2 (P - 1)) = coeff (sil l i) (homogeneousComponent 2 (P - 1)) := by
  have h1 := const_one fF hF hph1 hu
  have h2 : P - 1 ∈ Io S _ ^ 2 := stepNo2 le_rfl (by omega) (by omega) fF hF hph1 hsym h1
  obtain ⟨hA1, hs⟩ := lead_biadd (j := 2) (by omega) hm fF hF hph1 hsym h2
  have hb := bilin_of_biadd hA1 hs
  set B := fun i l => coeff (sil i l) (homogeneousComponent 2 (P - 1)) with hB
  have hbB : homogeneousComponent 2 (P - 1) = bil B := hb
  refine ⟨h2, ?_, ?_⟩
  · rw [← hbB]; exact sub_homogeneousComponent_mem h2
  · have e1 : ev2 (bil B) (xs S d 1) (xs S d 0) = bil (fun i l => B l i) := by
      rw [eval_pair_bilinear, bil, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [xs]; ring
    rw [← hbB, hs, hbB] at e1
    intro i l
    have := congrFun (congrFun (bil_ext e1) i) l
    exact this

theorem coeff_linL (A B : Fin d → Fin d → S) (i0 l0 : Fin d) :
    coeff (sil i0 l0) (∑ i, ∑ l, C (B i l) * (PairEvaluation.lin A (0 : Fin 2) i * xs S d (1 : Fin 2) l)) =
      ∑ i, A i i0 * B i l0 := by
  have key : ∀ i l j, coeff (sil i0 l0) (C (B i l) * (C (A i j) * X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) :
      MvPolynomial (Fin 2 × Fin d) S) = if j = i0 ∧ l = l0 then B i l * A i j else 0 := by
    intro i l j
    rw [show (C (B i l) * (C (A i j) * X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) : MvPolynomial (Fin 2 × Fin d) S) =
      C (B i l * A i j) * (X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) by rw [map_mul]; ring]
    rw [coeff_C_mul, coeff_XX]
    by_cases h : j = i0 ∧ l = l0
    · rw [if_pos (sil_inj.2 h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (sil_inj.1 h')), if_neg h, mul_zero]
  simp only [PairEvaluation.lin, xs, Finset.sum_mul, Finset.mul_sum, coeff_sum, key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single l0 (fun l _ hl => Finset.sum_eq_zero fun j _ => by simp [hl]) (by simp)]
  rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp), if_pos ⟨rfl, rfl⟩, mul_comm]

theorem coeff_linR (Ab B : Fin d → Fin d → S) (i0 l0 : Fin d) :
    coeff (sil i0 l0) (∑ i, ∑ l, C (B i l) * (xs S d (0 : Fin 2) i * PairEvaluation.lin Ab (1 : Fin 2) l)) =
      ∑ l, B i0 l * Ab l l0 := by
  have key : ∀ i l j, coeff (sil i0 l0) (C (B i l) * (X ((0 : Fin 2), i) * (C (Ab l j) * X ((1 : Fin 2), j))) :
      MvPolynomial (Fin 2 × Fin d) S) = if i = i0 ∧ j = l0 then B i l * Ab l j else 0 := by
    intro i l j
    rw [show (C (B i l) * (X ((0 : Fin 2), i) * (C (Ab l j) * X ((1 : Fin 2), j))) : MvPolynomial (Fin 2 × Fin d) S) =
      C (B i l * Ab l j) * (X ((0 : Fin 2), i) * X ((1 : Fin 2), j)) by rw [map_mul]; ring]
    rw [coeff_C_mul, coeff_XX]
    by_cases h : i = i0 ∧ j = l0
    · rw [if_pos (sil_inj.2 h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (sil_inj.1 h')), if_neg h, mul_zero]
  simp only [PairEvaluation.lin, xs, Finset.sum_mul, Finset.mul_sum, coeff_sum, key]
  rw [Finset.sum_eq_single i0 (fun i _ hi => Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun j _ => by simp [hi]) (by simp)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l0 (fun j _ hj => by simp [hj]) (by simp), if_pos ⟨rfl, rfl⟩]

end Poly

section Act

open ReciprocityTheory.ChartRestriction.G.TB (dLin)

theorem psTrunc_act_sub_mem (φ : Fin d → PS S 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {m : ℕ}
    (hm : 1 ≤ m) (i : Fin d) :
    psTrunc m (φ i) - ∑ j, C (dLin φ i j) * X ((0 : Fin 1), j) ∈ Io S (Fin 1 × Fin d) ^ 2 := by
  apply mem_pow_Io_lemma_3
  intro x hx
  rw [mem_support_iff, coeff_sub, coeff_psTrunc_lemma_2] at hx
  by_contra hlt
  have h1 : x.degree ≤ 1 := by omega
  rw [if_pos (h1.trans hm)] at hx
  apply hx
  rw [coeff_sum]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h0
  · have hx0 : x = 0 := by
      first
        | exact (Finsupp.degree_eq_zero_iff x).1 h0
        | exact Finsupp.degree_eq_zero_iff.1 h0
    subst hx0
    simp [coeff_C_mul, coeff_X', MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
  · obtain ⟨⟨q1, q2⟩, rfl⟩ := eq_single_of_degree_one x h0
    have hq1 : q1 = 0 := Subsingleton.elim _ _
    subst hq1
    rw [Finset.sum_eq_single q2]
    · simp [coeff_C_mul, coeff_X', dLin]
    · intro j _ hj
      simp [coeff_C_mul, coeff_X', Finsupp.single_left_inj one_ne_zero, hj]
    · simp

theorem psIn_act_sub_mem (φ : Fin d → PS S 1 d) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {m : ℕ}
    (hm : 1 ≤ m) (k : Fin 2) (i : Fin d) :
    psIn d m ![k] (φ i) - C (constantCoeff (psIn d m ![k] (φ i))) - PairEvaluation.lin (dLin φ) k i ∈
      Io S (Fin 2 × Fin d) ^ 2 := by
  have hmap : ∀ q ∈ Io S (Fin 1 × Fin d) ^ 2,
      rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) q ∈ Io S (Fin 2 × Fin d) ^ 2 := by
    intro q hq
    have hle : Ideal.map (rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) :
        MvPolynomial (Fin 1 × Fin d) S →ₐ[S] MvPolynomial (Fin 2 × Fin d) S) (Io S (Fin 1 × Fin d)) ≤
          Io S (Fin 2 × Fin d) := by
      rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨s, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, rename_X]
      exact Ideal.subset_span ⟨_, rfl⟩
    have h2 := Ideal.mem_map_of_mem (rename (fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin 2) p.1, p.2)) :
        MvPolynomial (Fin 1 × Fin d) S →ₐ[S] MvPolynomial (Fin 2 × Fin d) S) hq
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hle 2 h2
  have h3 := hmap _ (psTrunc_act_sub_mem φ hφ hm i)
  have hc0 : constantCoeff (psIn d m ![k] (φ i)) = 0 := by
    rw [psIn, constantCoeff_rename]
    have h0 : constantCoeff (psTrunc m (φ i)) = coeff 0 (psTrunc m (φ i)) := by
      first
        | rfl
        | simp [constantCoeff_eq]
    rw [h0, coeff_psTrunc_lemma_2]
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
  convert h3 using 1
  rw [hc0, map_zero, sub_zero, map_sub]
  congr 1
  all_goals first
    | rfl
    | simp [PairEvaluation.lin, map_sum, rename_X, rename_C]

end Act

end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
end
end
