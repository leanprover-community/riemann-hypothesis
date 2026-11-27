module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Signed Fourier rows for the dyadic Bernoulli sum

Write `S = 2*T` for the dyadic part of the residue-field multiplicative order and
`N = h*S` for the dyadic conductor. In the linear range, `S ∣ h` and `T*f < h`.
The powers indexing a row visit the residues `a + h*(q*i % (2*T))`. With
`γ^T = -1`, their frequency is `γ^q`. Folding the summation indices at
the midpoint of the conductor gives a single progression of length `T*f`.
This works over a commutative ring even when the odd conductor `f` is zero in it.

The two representatives and their Fourier phases are from Christopher Daniel Pang
and Hearthline's [derivation of the two rows](https://github.com/leanprover-community/riemann-hypothesis/issues/5647).
-/

@[expose] public section

namespace UpperTheory.V.X

open Finset

variable {R : Type*} [CommRing R] {f T q : ℕ}

/-- Sum over the lifts of a residue modulo `N`, with a minus sign below half the conductor. -/
def bernoulliSignedCoeff (φ : ZMod f → R) (N r : ℕ) : R :=
  ∑ j : Fin f,
    let x := r + N * j
    if x < f * N / 2 then -φ x else φ x

/-- The half-length Fourier row in the linear range, indexed in its original order. -/
def bernoulliFourierRow (φ : ZMod f → R) (N a v T : ℕ) (β : R) : R :=
  ∑ i : Fin T, bernoulliSignedCoeff φ N (a * v ^ (i : ℕ) % N) * β ^ (i : ℕ)

/-- The quadratic term in a power of `1 + h*c` vanishes modulo `N = h*(2*T)` when
`2*T ∣ h`. This gives the least nonnegative representative of each row entry. -/
private theorem rowResidue {a h v c : ℕ} (ha : a < h) (hT : 0 < T) (hh : 2 * T ∣ h)
    (hv : v ≡ 1 + h * c [MOD h * (2 * T)]) (hq : a * c ≡ q [MOD 2 * T]) (i : ℕ) :
    a * v ^ i % (h * (2 * T)) = a + h * (q * i % (2 * T)) := by
  have hpow : v ^ i ≡ 1 + h * (c * i) [MOD h * (2 * T)] := by
    induction i with
    | zero => simp [Nat.ModEq]
    | succ i ih =>
      rw [pow_succ]
      apply (ih.mul hv).trans
      rw [show (1 + h * (c * i)) * (1 + h * c) =
        1 + h * (c * (i + 1)) + h * h * (c * i * c) by ring]
      exact Nat.add_modEq_left_iff.mpr (dvd_mul_of_dvd_left (Nat.mul_dvd_mul_left h hh) _)
  have hstep := (hq.mul_right i).trans (Nat.mod_modEq (q * i) (2 * T)).symm
  apply Nat.mod_eq_of_modEq ((hpow.mul_left a).trans ?_)
  · have hr := Nat.mod_lt (q * i) (show 0 < 2 * T by omega)
    have hle := Nat.mul_le_mul_left h (Nat.succ_le_of_lt hr)
    rw [Nat.mul_succ] at hle
    omega
  · rw [show a * (1 + h * (c * i)) = a + h * (a * c * i) by ring]
    exact (hstep.mul_left' h).add_left a

private def liftIndex (T q i j : ℕ) : ℕ := q * i % (2 * T) + T * (2 * j)

/-- Reducing a lift index modulo the half-length folds the upper and lower halves together.
Reduction modulo `T` recovers the row index, then reduction modulo `f` recovers the lift. -/
private noncomputable def foldIndexEquiv (hf : Odd f) (hT : 0 < T) (hq : T.Coprime q) :
    Fin T × Fin f ≃ Fin (T * f) :=
  Equiv.ofBijective (fun p ↦ ⟨liftIndex T q p.1 p.2 % (T * f),
    Nat.mod_lt _ (Nat.mul_pos hT hf.pos)⟩) <| by
    apply (Fintype.bijective_iff_injective_and_card _).2
    refine ⟨?_, by simp⟩
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have he : liftIndex T q i j ≡ liftIndex T q i' j' [MOD T * f] := congrArg Fin.val h
    have hres (k b : ℕ) : liftIndex T q k b ≡ q * k [MOD T] :=
      (Nat.add_modEq_left_iff.mpr (dvd_mul_right T _)).trans
        ((Nat.mod_modEq _ _).of_dvd (dvd_mul_left T 2))
    have hii := (hres i j).symm.trans ((he.of_mul_right f).trans (hres i' j'))
    have hi : i = i' := Fin.ext ((hii.cancel_left_of_coprime hq).eq_of_lt_of_lt i.isLt i'.isLt)
    subst i'
    have hjj := he.add_left_cancel' (q * i % (2 * T))
    have hj : 2 * (j : ℕ) ≡ 2 * (j' : ℕ) [MOD f] := Nat.ModEq.mul_left_cancel' hT.ne' hjj
    have hmod := hj.cancel_left_of_coprime (Nat.coprime_two_right.mpr hf)
    exact Prod.ext rfl (Fin.ext (hmod.eq_of_lt_of_lt j.isLt j'.isLt))

/-- Each lift contributes the negative of the term at its folded index. Above the
midpoint, translation by `T*f` preserves the coefficient and reverses the phase. -/
private theorem foldedTerm (φ : ZMod f → R) (a h : ℕ) (ha : a < h) (hf : Odd f)
    (hT : 0 < T) (γ : R) (hγ : γ ^ T = -1) (i : Fin T) (j : Fin f) :
    let t := liftIndex T q i j
    let x := a + h * (q * i % (2 * T)) + h * (2 * T) * j
    (if x < f * (h * (2 * T)) / 2 then -φ x else φ x) * (γ ^ q) ^ (i : ℕ) =
      -(φ (a + h * (t % (T * f) : ℕ)) * γ ^ (t % (T * f))) := by
  dsimp only
  let t := liftIndex T q i j
  have hx : a + h * (q * i % (2 * T)) + h * (2 * T) * j = a + h * t := by
    dsimp [t, liftIndex]; ring
  have hhalf : f * (h * (2 * T)) / 2 = h * (T * f) := by
    rw [show f * (h * (2 * T)) = h * (T * f) * 2 by ring, Nat.mul_div_cancel _ (by decide)]
  have hlt : a + h * t < h * (T * f) ↔ t < T * f := by
    constructor
    · intro hlt
      by_contra! hge
      exact hlt.not_ge ((Nat.mul_le_mul_left h hge).trans (Nat.le_add_left _ _))
    · intro ht
      have := Nat.mul_le_mul_left h (Nat.succ_le_of_lt ht)
      rw [Nat.mul_succ] at this
      omega
  have hfull : γ ^ (2 * T) = 1 := by rw [two_mul, pow_add, hγ]; simp
  have hphase : (γ ^ q) ^ (i : ℕ) = γ ^ t := by
    rw [← pow_mul, pow_eq_pow_mod _ hfull]
    dsimp [t, liftIndex]
    rw [pow_add, show T * (2 * (j : ℕ)) = (2 * T) * j by ring, pow_mul, hfull, one_pow, mul_one]
  have hperiod : γ ^ (T * f) = -1 := by rw [pow_mul, hγ, hf.neg_one_pow]
  rw [hx, hhalf, if_congr hlt rfl rfl, hphase]
  change (if t < T * f then _ else _) * γ ^ t =
    -(φ (a + h * (t % (T * f) : ℕ)) * γ ^ (t % (T * f)))
  by_cases ht : t < T * f
  · simp [ht, Nat.mod_eq_of_lt ht]
  · have hbound : t < T * f + T * f := by
      have hr := Nat.mod_lt (q * i) (show 0 < 2 * T by omega)
      have hj := Nat.mul_le_mul_left (2 * T) j.isLt
      rw [Nat.mul_succ] at hj
      dsimp [t, liftIndex]
      linarith only [hr, hj]
    have hr : t % (T * f) + T * f = t := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    have hx' : ((a + h * t : ℕ) : ZMod f) = (a + h * (t % (T * f) : ℕ) : ZMod f) := by
      conv_lhs => rw [← hr]
      simp
    have hpow : γ ^ t = -(γ ^ (t % (T * f))) := calc
      γ ^ t = γ ^ (t % (T * f) + T * f) := congrArg (γ ^ ·) hr.symm
      _ = _ := by rw [pow_add, hperiod, mul_neg_one]
    rw [ite_eq_right ht, hx', hpow, mul_neg]

/-- Folding the signed lifts at the midpoint yields the negative of one Fourier progression.
The phase and the sign both change at the fold since `f` is odd. -/
theorem bernoulliFourierRow_eq_sum (φ : ZMod f → R) {a h v c : ℕ} (ha : a < h) (hf : Odd f)
    (hT : 0 < T) (hh : 2 * T ∣ h) (hv : v ≡ 1 + h * c [MOD h * (2 * T)])
    (hstep : a * c ≡ q [MOD 2 * T]) (hq : T.Coprime q) (γ : R) (hγ : γ ^ T = -1) :
    bernoulliFourierRow φ (h * (2 * T)) a v T (γ ^ q) =
      -∑ t ∈ range (T * f), φ (a + h * t : ZMod f) * γ ^ t := by
  let F (r : Fin (T * f)) : R := -(φ (a + h * (r : ℕ) : ZMod f) * γ ^ (r : ℕ))
  let e := foldIndexEquiv hf hT hq
  calc
    _ = ∑ i : Fin T, ∑ j : Fin f, F (e (i, j)) := by
      unfold bernoulliFourierRow bernoulliSignedCoeff
      simp_rw [rowResidue ha hT hh hv hstep, sum_mul]
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ foldedTerm φ a h ha hf hT γ hγ i j
    _ = ∑ r : Fin (T * f), F r := by rw [← e.sum_comp F, Fintype.sum_prod_type]
    _ = _ := by
      simp only [F, sum_neg_distrib]
      rw [← Fin.sum_univ_eq_sum_range (fun t : ℕ ↦ φ (a + h * t : ZMod f) * γ ^ t)]

/-- Subtracting two signed rows whose starts differ by one step modulo the odd conductor
leaves twice the value at their common endpoint. -/
theorem bernoulliFourierRow_sub (φ : ZMod f → R) {a a' h v c : ℕ} (ha : a < h) (ha' : a' < h)
    (hshift : (a' : ZMod f) = a + h) (hf : Odd f) (hT : 0 < T) (hh : 2 * T ∣ h)
    (hv : v ≡ 1 + h * c [MOD h * (2 * T)]) (hstep : a * c ≡ q [MOD 2 * T])
    (hstep' : a' * c ≡ q [MOD 2 * T]) (hq : T.Coprime q) (γ : R) (hγ : γ ^ T = -1) :
    γ * bernoulliFourierRow φ (h * (2 * T)) a' v T (γ ^ q) -
      bernoulliFourierRow φ (h * (2 * T)) a v T (γ ^ q) = 2 * φ a := by
  let w (t : ℕ) := φ (a + h * t : ZMod f) * γ ^ t
  have hterm (t : ℕ) : γ * (φ (a' + h * t : ZMod f) * γ ^ t) = w (t + 1) := by
    simp [w, hshift, mul_add, pow_succ, add_assoc, add_comm, mul_comm, mul_assoc]
  have hend : w (T * f) = -(φ a) := by simp [w, pow_mul, hγ, hf.neg_one_pow]
  have htel := sum_range_succ' w (T * f)
  rw [sum_range_succ] at htel
  rw [bernoulliFourierRow_eq_sum φ ha' hf hT hh hv hstep' hq γ hγ,
    bernoulliFourierRow_eq_sum φ ha hf hT hh hv hstep hq γ hγ, mul_neg, mul_sum]
  simp_rw [hterm]
  change -(∑ t ∈ range (T * f), w (t + 1)) - -(∑ t ∈ range (T * f), w t) = _
  rw [hend, show w 0 = φ a by simp [w]] at htel
  linear_combination htel

/-- The row stride `5^(2^k)` differs from 1 by an odd multiple of `4*2^k`. -/
private theorem five_pow_stride (k : ℕ) : ∃ c, Odd c ∧ 5 ^ (2 ^ k) = 1 + 4 * 2 ^ k * c := by
  induction k with
  | zero => exact ⟨1, odd_one, rfl⟩
  | succ k ih =>
    obtain ⟨c, hc, h⟩ := ih
    refine ⟨c * (2 * (2 ^ k * c) + 1), hc.mul ⟨2 ^ k * c, rfl⟩, ?_⟩
    rw [pow_succ 2 k, pow_mul, h]
    ring

/-- Choose the same sign in `T*f ± 1` and `h - T*f ± 1` so both starts are 1 modulo 4. -/
private theorem rowStarts {h : ℕ} (hf : Odd f) (hT : 2 ≤ T) (hTe : Even T)
    (hh : 2 * T ∣ h) (hlt : T * f < h) :
    ∃ a a' : ℕ, a < h ∧ a % 4 = 1 ∧ a' < h ∧ a' % 4 = 1 ∧ a' ≡ a [MOD 2 * T] ∧
      (a' : ZMod f) = a + h ∧ ((a : ZMod f) = 1 ∨ (a : ZMod f) = -1) := by
  let m := T * f
  have hm : T ≤ m := Nat.le_mul_of_pos_right T hf.pos
  have hgap : T ≤ h - m := Nat.le_of_dvd (by dsimp [m]; omega)
    (Nat.dvd_sub ((dvd_mul_left T 2).trans hh) (dvd_mul_right T f))
  have hm2 : m % 2 = 0 := Nat.even_iff.mp (hTe.mul_right f)
  have hh4 : 4 ∣ h := dvd_trans (Nat.mul_dvd_mul_left 2 hTe.two_dvd) hh
  have hd : m % 4 = 0 ∨ m % 4 = 2 := by omega
  let a := m + 1 - m % 4
  let a' := h - m + 1 - m % 4
  have hrel : a' + 2 * m = a + h := by dsimp [a, a']; omega
  have hmod : a' ≡ a [MOD 2 * T] := calc
    a' ≡ a' + 2 * m [MOD 2 * T] := Nat.left_modEq_add_iff.mpr ⟨f, by dsimp [m]; ring⟩
    _ = a + h := hrel
    _ ≡ a [MOD 2 * T] := Nat.add_modEq_left_iff.mpr hh
  have hm0 : (m : ZMod f) = 0 := by simp [m]
  have hshift := congrArg (fun x : ℕ ↦ (x : ZMod f)) hrel
  push_cast at hshift
  simp only [hm0, mul_zero, add_zero] at hshift
  refine ⟨a, a', ?_, ?_, ?_, ?_, hmod, hshift, ?_⟩
  · dsimp [a]; omega
  · dsimp [a]; omega
  · dsimp [a']; omega
  · dsimp [a']; omega
  · rcases hd with hd | hd
    · left
      simp [a, hd, hm0]
    · right
      have ha : a + 1 = m := by dsimp [a]; omega
      have he := congrArg (fun x : ℕ ↦ (x : ZMod f)) ha
      push_cast at he
      linear_combination he + hm0

/-- Rephase a row of odd step `q` at a prescribed frequency `β` by inverting the step
modulo the full cycle. -/
private theorem exists_row_phase {β : R} (hT : 0 < T) (hq : q.Coprime (2 * T))
    (hβ : β ^ T = -1) : ∃ γ : R, γ ^ T = -1 ∧ γ ^ q = β := by
  obtain ⟨b, _, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime hq (by omega)
  have hmod : q * b ≡ 1 [MOD 2 * T] := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < 2 * T by omega)] using hb
  have hbodd : Odd b := (Nat.odd_mul.mp (Nat.odd_iff.mpr (hmod.of_mul_right T))).2
  refine ⟨β ^ b, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hβ, hbodd.neg_one_pow]
  · have hfull : β ^ (2 * T) = 1 := by rw [two_mul, pow_add, hβ]; simp
    rw [← pow_mul, mul_comm, pow_eq_pow_mod _ hfull, hb, pow_one]

/-- In the linear range of the improved cutoff, at least one actual Fourier row of the
signed coefficients is nonzero. Here `N = h*(2*T)`, and `5^(2^k)` is the row stride.
The endpoint hypotheses apply, in particular, to character values over a field of odd
characteristic. -/
theorem exists_bernoulliFourierRow_ne_zero {K : Type*} [Field K] (φ : ZMod f → K)
    (hf : Odd f) (hφ : φ 1 ≠ 0 ∧ φ (-1) ≠ 0) (h2 : (2 : K) ≠ 0) (t k : ℕ) (β : K) :
    let T := 2 ^ (t + 1)
    let h := 4 * 2 ^ k
    2 * T ∣ h → T * f < h → β ^ T = -1 →
      ∃ a < h, a % 4 = 1 ∧ bernoulliFourierRow φ (h * (2 * T)) a (5 ^ (2 ^ k)) T β ≠ 0 := by
  intro T h hh hlt hβ
  have hT : 2 ≤ T := by
    dsimp [T]
    rw [pow_succ]
    have := Nat.two_pow_pos t
    omega
  have hTe : Even T := Even.pow_of_ne_zero even_two (by omega : t + 1 ≠ 0)
  obtain ⟨a, a', ha, ha4, ha', ha4', hmod, hshift, hsign⟩ := rowStarts hf hT hTe hh hlt
  obtain ⟨c, hc, hv⟩ := five_pow_stride k
  let q := a * c
  have haodd : Odd a := Nat.odd_iff.mpr (by omega)
  have hq : (2 * T).Coprime q := by
    rw [show 2 * T = 2 ^ (t + 2) by dsimp [T]; ring]
    exact (haodd.mul hc).coprime_two_left.pow_left _
  obtain ⟨γ, hγ, hβ'⟩ := exists_row_phase (by omega : 0 < T) hq.symm hβ
  have hvmod : 5 ^ (2 ^ k) ≡ 1 + h * c [MOD h * (2 * T)] := by rw [hv]
  have hcert := bernoulliFourierRow_sub φ ha ha' hshift hf (by omega : 0 < T) hh
    hvmod (Nat.ModEq.refl q) (hmod.mul_right c)
    (hq.of_dvd_left (dvd_mul_left T 2)) γ hγ
  rw [hβ'] at hcert
  by_contra! hz
  rw [hz a ha ha4, hz a' ha' ha4', mul_zero, sub_zero] at hcert
  rcases hsign with hs | hs
  · exact (mul_ne_zero h2 hφ.1) (hs ▸ hcert.symm)
  · exact (mul_ne_zero h2 hφ.2) (hs ▸ hcert.symm)

/-- At odd conductor 5 in characteristic 5, the first row can vanish on its own.
Here `N = 64`, the stride is `5^4`, and `γ = 3` gives `β = 2`. -/
example :
    let row (a : ℕ) := bernoulliFourierRow (id : ZMod 5 → ZMod 5) 64 a (5 ^ 4) 2 2
    row 9 = 0 ∧ row 5 = 1 ∧ 3 * row 5 - row 9 = -2 := by decide

end UpperTheory.V.X
