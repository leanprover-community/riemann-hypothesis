module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.BigExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.WADVR

lemma Sm.sum {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
    [Algebra W Q] [IsFractionRing W Q] {ϖ : W} {κ : Type*} (s : Finset κ) (f : κ → Q) (k : ℤ)
    (h : ∀ i ∈ s, Sm Q ϖ k (f i)) : Sm Q ϖ k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Sm.zero (Q := Q) (ϖ := ϖ) k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end PI.WADVR

namespace PI.WA

open PI.WADVR

theorem rho_projection_assembly : Assembly := by
  intro E _ ι _ W Q _ _ _ _ _ _ iw p hp0 hpu hden ϖ hϖ hz x N
  classical
  choose z hz0 hzi hzj using hz
  choose n hn using fun i => exists_sm_target (hϖ i) (hp0 i) N
  set K : ℕ := ∑ i, n i with hK
  have hnK : ∀ i, n i ≤ K := fun i =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  choose y c hy using fun i => hden i (x i) K
  have hyS : ∀ i, PI.WADVR.Sm (Q i) (ϖ i) K (iw i (y i) - x i) := fun i =>
    sm_of_density (hϖ i) (hpu i) (hy i)
  choose k hk using fun i j => sm_exists (hϖ j) (iw j (y i))
  set B : ℕ := ∑ i, ∑ j, (-(k i j)).toNat with hB
  have hkB : ∀ i j, -(k i j) ≤ (B : ℤ) := by
    intro i j
    have h1 : (-(k i j)).toNat ≤ ∑ j', (-(k i j')).toNat :=
      Finset.single_le_sum (f := fun j' => (-(k i j')).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have h2 : ∑ j', (-(k i j')).toNat ≤ B :=
      Finset.single_le_sum (f := fun i' => ∑ j', (-(k i' j')).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h3 := Int.self_le_toNat (-(k i j))
    have h4 : ((-(k i j)).toNat : ℤ) ≤ B := by exact_mod_cast h1.trans h2
    linarith
  set r : ℕ := 1 + K + B with hr
  have hr1 : 1 ≤ r := by omega
  have hrk : ∀ i j, (K : ℤ) ≤ (r : ℤ) + k i j := by
    intro i j
    have := hkB i j
    push_cast [hr]
    linarith
  let e : ι → E := fun i => z i ^ r * (1 + z i ^ r)⁻¹
  refine ⟨∑ i, e i * y i, fun j => ?_⟩
  have he : ∀ i, iw j (e i) = iw j (z i) ^ r * (1 + iw j (z i) ^ r)⁻¹ := by
    intro i; simp [e, map_mul, map_pow, map_inv₀, map_add (f := _), map_one]

  have hT : ∀ i, PI.WADVR.Sm (Q j) (ϖ j) K
      ((iw j (e i) - if i = j then 1 else 0) * iw j (y i)) := by
    intro i
    by_cases hij : i = j
    · subst hij
      obtain ⟨hne, hsm⟩ := big_one_add_pow (hϖ i) ((map_ne_zero (iw i)).mpr (hz0 i)) (hzi i) hr1
      have hid : iw i (e i) - (if i = i then 1 else 0) = -(1 + iw i (z i) ^ r)⁻¹ := by
        rw [if_pos rfl, he]
        calc iw i (z i) ^ r * (1 + iw i (z i) ^ r)⁻¹ - 1
            = (iw i (z i) ^ r - (1 + iw i (z i) ^ r)) * (1 + iw i (z i) ^ r)⁻¹ := by
              rw [sub_mul, mul_inv_cancel₀ hne]
          _ = -(1 + iw i (z i) ^ r)⁻¹ := by ring
      rw [hid]
      exact (hsm.neg.mul (hϖ i) (hk i i)).mono (hϖ i) (hrk i i)
    · rw [if_neg hij, sub_zero, he]
      obtain ⟨_, hsm⟩ := small_one_add_pow (hϖ j) (hzj i j (Ne.symm hij)) hr1
      exact (hsm.mul (hϖ j) (hk i j)).mono (hϖ j) (hrk i j)
  have hsum : iw j (∑ i, e i * y i) - x j =
      (∑ i, (iw j (e i) - if i = j then 1 else 0) * iw j (y i)) + (iw j (y j) - x j) := by

    rw [map_sum]
    simp only [map_mul, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have htot : PI.WADVR.Sm (Q j) (ϖ j) K (iw j (∑ i, e i * y i) - x j) := by
    rw [hsum]
    exact (PI.WADVR.Sm.sum _ _ _ fun i _ => hT i).add (hyS j)
  obtain ⟨c', hc'⟩ := hn j _ (htot.mono (hϖ j) (by exact_mod_cast hnK j))
  exact ⟨c', by rw [← hc']; ring⟩

end PI.WA
