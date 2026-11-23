module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.PreOfGens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries

variable {B : Type} [CommRing B]

theorem e_pow (Q : PDPoly B) (l n : ℕ) :
    ∃ M : ℕ, M * l.factorial ^ n = (n * l).factorial ∧ Q.e l ^ n = (M : Q.P) * Q.e (n * l) := by
  induction n with
  | zero => exact ⟨1, by simp, by simp [Q.e_zero]⟩
  | succ n ih =>
    obtain ⟨M, h1, h2⟩ := ih
    refine ⟨M * (n * l + l).choose (n * l), ?_, ?_⟩
    · have := Nat.add_choose_mul_factorial_mul_factorial (n * l) l
      rw [← Nat.choose_symm_add] at this
      rw [Nat.succ_mul, ← this, ← h1]; ring
    · rw [pow_succ, h2, mul_assoc, Q.e_mul, Nat.succ_mul]; push_cast; ring

theorem choose_fac (a b : ℕ) : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rwa [Nat.add_sub_cancel_left] at h

theorem num1 (m n : ℕ) {K : ℕ} (hK : K ≠ 0) :
    m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) =
      (m + n).choose m * (m + n).uniformBell K := by
  apply GlobalTheory.PDA.uniformBell_mul_uniformBell <;> assumption

theorem num2 (n l M : ℕ) {K : ℕ} (hK : K ≠ 0) (hM : M * l.factorial ^ n = (n * l).factorial) :
    M * n.uniformBell K * (n * l + n * K).choose (n * l) = (l + K).choose l ^ n * n.uniformBell (l + K) := by
  have h1 := Nat.uniformBell_mul_eq n hK
  have h3 := Nat.uniformBell_mul_eq n (show l + K ≠ 0 by omega)
  have h4 := choose_fac (n * l) (n * K)
  have h5 := choose_fac l K
  have hpos : 0 < l.factorial ^ n * K.factorial ^ n * n.factorial := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc _ = (n * l + n * K).choose (n * l) * (M * l.factorial ^ n) *
        (n.uniformBell K * K.factorial ^ n * n.factorial) := by ring
    _ = (n * (l + K)).factorial := by rw [h1, hM, h4, mul_add]
    _ = n.uniformBell (l + K) * ((l + K).choose l * l.factorial * K.factorial) ^ n * n.factorial := by
        rw [h5, h3]
    _ = _ := by ring

def gb (Q : PDPoly B) (K n : ℕ) : Q.P := (n.uniformBell K : Q.P) * Q.e (n * K)

theorem gb_zero (Q : PDPoly B) (K : ℕ) : gb Q K 0 = 1 := by simp [gb, Nat.uniformBell_zero_left, Q.e_zero]

theorem gb_mul (Q : PDPoly B) {K : ℕ} (hK : K ≠ 0) (m n : ℕ) :
    gb Q K m * gb Q K n = ((m + n).choose m : Q.P) * gb Q K (m + n) := by
  unfold gb
  have h := num1 m n hK
  calc ((m.uniformBell K : Q.P) * Q.e (m * K)) * ((n.uniformBell K : Q.P) * Q.e (n * K))
      = ((m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) : ℕ) : Q.P) *
          Q.e (m * K + n * K) := by
        rw [mul_mul_mul_comm, Q.e_mul]
        push_cast
        ring
    _ = _ := by
        rw [h, ← add_mul]
        push_cast
        ring

private theorem dividedPower_identities_D_and_e_eq_gb (Q : PDPoly B) : ∃ D : ℕ → Q.P → Q.P,
    (∀ x, D 0 x = 1) ∧
    (∀ n x y, D n (x + y) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, D p.1 x * D p.2 y) ∧
    (∀ m n x, D m x * D n x = ((m + n).choose m : Q.P) * D (m + n) x) ∧
    (∀ n (c : B) x, D n (c • x) = algebraMap B Q.P c ^ n * D n x) ∧
    (∀ n K, K ≠ 0 → D n (Q.e K) = gb Q K n) := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ℕ → B → PowerSeries Q.P, ∀ K b,
      F K b = PowerSeries.mk fun j => algebraMap B Q.P (b ^ j) * gb Q K j := ⟨_, fun _ _ => rfl⟩
  have F0 : ∀ K, F K 0 = 1 := by
    intro K
    ext j
    rw [hF, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    rcases j with _ | j
    · simp [gb_zero]
    · simp
  have Fadd : ∀ K, K ≠ 0 → ∀ a b, F K (a + b) = F K a * F K b := by
    intro K hK a b
    ext n
    rw [PowerSeries.coeff_mul]
    simp only [hF, PowerSeries.coeff_mk]
    have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        algebraMap B Q.P (a ^ p.1) * gb Q K p.1 * (algebraMap B Q.P (b ^ p.2) * gb Q K p.2) =
          algebraMap B Q.P (a ^ p.1 * b ^ p.2 * (n.choose p.1 : B)) * gb Q K n := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [mul_mul_mul_comm, gb_mul Q hK, hp]
      simp only [map_mul, map_natCast]
      ring

    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, add_pow,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have Fsc : ∀ K c b, F K (c * b) = PowerSeries.rescale (algebraMap B Q.P c) (F K b) := by
    intro K c b
    ext n
    rw [PowerSeries.coeff_rescale]
    simp only [hF, PowerSeries.coeff_mk, mul_pow, map_mul, map_pow]
    ring
  have Fexp : ∀ K, K ≠ 0 → ∀ b, IsExp (F K b) := by
    intro K hK b m n
    simp only [hF, PowerSeries.coeff_mk]
    rw [mul_mul_mul_comm, gb_mul Q hK, pow_add, map_mul]
    ring
  have exp1 : IsExp (1 : PowerSeries Q.P) := by
    intro m n
    simp only [PowerSeries.coeff_one]
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn]
  obtain ⟨E, hE⟩ : ∃ E : Finset ℕ → Q.P → PowerSeries Q.P, ∀ S x,
      E S x = ∏ k ∈ S, F (k + 1) (Q.e.repr x (k + 1)) := ⟨_, fun _ _ => rfl⟩
  have cover : ∀ x : Q.P, ∀ k, Q.e.repr x (k + 1) ≠ 0 →
      k ∈ Finset.range ((Q.e.repr x).support.sup id) := by
    intro x k hk
    have hmem : k + 1 ∈ (Q.e.repr x).support := Finsupp.mem_support_iff.mpr hk
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    exact Finset.mem_range.mpr (by omega)
  have Eind : ∀ x S T, (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ S) →
      (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ T) → E S x = E T x := by
    intro x S T hS hT
    have mono : ∀ U V, U ⊆ V → (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ U) → E U x = E V x := by
      intro U V hUV hU
      rw [hE, hE]
      apply Finset.prod_subset hUV
      intro k _ hk
      have : Q.e.repr x (k + 1) = 0 := by
        by_contra h
        exact hk (hU k h)
      rw [this, F0]
    rw [mono S (S ∪ T) Finset.subset_union_left hS, mono T (S ∪ T) Finset.subset_union_right hT]
  have c0 : ∀ S x, PowerSeries.coeff 0 (E S x) = 1 := by
    intro S x
    rw [hE]
    induction S using Finset.induction_on with
    | empty => simp
    | insert k S hk ih =>
      rw [Finset.prod_insert hk, PowerSeries.coeff_mul]
      simp [ih, hF, gb_zero]
  refine ⟨fun n x => PowerSeries.coeff n (E (Finset.range ((Q.e.repr x).support.sup id)) x),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact c0 _ x
  · intro n x y
    dsimp only
    obtain ⟨S, hxS, hyS, hxyS⟩ : ∃ S : Finset ℕ, (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ S) ∧
        (∀ k, Q.e.repr y (k + 1) ≠ 0 → k ∈ S) ∧ (∀ k, Q.e.repr (x + y) (k + 1) ≠ 0 → k ∈ S) :=
      ⟨Finset.range ((Q.e.repr x).support.sup id) ∪ Finset.range ((Q.e.repr y).support.sup id) ∪
        Finset.range ((Q.e.repr (x + y)).support.sup id),
        fun k hk => Finset.mem_union_left _ (Finset.mem_union_left _ (cover x k hk)),
        fun k hk => Finset.mem_union_left _ (Finset.mem_union_right _ (cover y k hk)),
        fun k hk => Finset.mem_union_right _ (cover _ k hk)⟩
    rw [Eind x _ S (cover x) hxS, Eind y _ S (cover y) hyS, Eind (x + y) _ S (cover _) hxyS]
    have : E S (x + y) = E S x * E S y := by
      rw [hE, hE, hE, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [show Q.e.repr (x + y) = Q.e.repr x + Q.e.repr y from map_add _ _ _, Finsupp.add_apply,
        Fadd _ (Nat.succ_ne_zero k)]
    rw [this, PowerSeries.coeff_mul]
  · intro m n x
    dsimp only
    have : IsExp (E (Finset.range ((Q.e.repr x).support.sup id)) x) := by
      rw [hE]
      exact Finset.prod_induction _ IsExp (fun f g hf hg => hf.mul hg) exp1
        (fun k _ => Fexp _ (Nat.succ_ne_zero k) _)
    exact this m n
  · intro n c x
    dsimp only
    obtain ⟨S, hxS, hcS⟩ : ∃ S : Finset ℕ, (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ S) ∧
        (∀ k, Q.e.repr (c • x) (k + 1) ≠ 0 → k ∈ S) :=
      ⟨Finset.range ((Q.e.repr x).support.sup id) ∪ Finset.range ((Q.e.repr (c • x)).support.sup id),
        fun k hk => Finset.mem_union_left _ (cover x k hk),
        fun k hk => Finset.mem_union_right _ (cover _ k hk)⟩
    rw [Eind x _ S (cover x) hxS, Eind (c • x) _ S (cover _) hcS]
    have : E S (c • x) = PowerSeries.rescale (algebraMap B Q.P c) (E S x) := by
      rw [hE, hE, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [show Q.e.repr (c • x) = c • Q.e.repr x from map_smul _ _ _, Finsupp.smul_apply, smul_eq_mul,
        Fsc]
    rw [this, PowerSeries.coeff_rescale]
  · intro n K hK
    dsimp only
    have hS : ∀ k, Q.e.repr (Q.e K) (k + 1) ≠ 0 →
        k ∈ Finset.range ((Q.e.repr (Q.e K)).support.sup id) ∪ {K - 1} :=
      fun k hk => Finset.mem_union_left _ (cover _ k hk)
    rw [Eind (Q.e K) _ _ (cover _) hS, hE, Finset.prod_eq_single (K - 1)]
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hK), Q.e.repr_self, Finsupp.single_eq_same, hF,
        PowerSeries.coeff_mk, one_pow, map_one, one_mul]
    · intro k _ hk
      rw [Q.e.repr_self, Finsupp.single_apply, if_neg (by omega), F0]
    · intro h
      exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self _)) h

theorem pre_aug (B : Type) [CommRing B] (Q : PDPoly B) : ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧
    ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  apply GlobalTheory.PDA.exists_isPreDividedPowers_augmentation <;> assumption

end FubiniStudyChowHeightFormula₂.Adr
