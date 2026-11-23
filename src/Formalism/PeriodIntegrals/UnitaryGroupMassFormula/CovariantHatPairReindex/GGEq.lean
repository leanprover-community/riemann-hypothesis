module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SkipTwoOfGe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem one_side {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M)
    (hF : ∀ (x : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x)
    (β β' : Fin (m + 2) → ℂ) :
    ∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id • ((β (c 0) * β' (c 1)) • F (fun k => c k.succ.succ)) =
      (m.factorial : ℂ) • ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by
  rw [sum_two id F hF, ← reindex_pairs F β β', Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp only [id, smul_smul]
  congr 1
  ring

noncomputable def GG {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M) (β β' a a' : Fin (m + 2) → ℂ) : M :=
  ∑ c : Fin (m + 2) → Fin (m + 2), ∑ d : Fin (m + 2) → Fin (m + 2),
    (sgnL c id * sgnL d id * (β (c 0) * β' (c 1)) * (a (d 0) * a' (d 1))) •
      F (fun k => c k.succ.succ) (fun k => d k.succ.succ)

theorem GG_eq {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M)
    (hR : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) y = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (hC : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F x (y ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (β β' a a' : Fin (m + 2) → ℂ) :
    GG F β β' a a' = ((m.factorial : ℂ) * m.factorial) •
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2), ∑ j : Fin (m + 2), ∑ j' : Fin (m + 2),
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β i * β' i' - β i' * β' i) *
            (a j * a' j' - a j' * a' j)) • F (skip2 i i') (skip2 j j')
        else 0 := by
  let Φ : (Fin m → Fin (m + 2)) → M := fun x =>
    ∑ d : Fin (m + 2) → Fin (m + 2), sgnL d id • ((a (d 0) * a' (d 1)) • F x (fun k => d k.succ.succ))
  have hΦ : ∀ (x : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      Φ (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • Φ x := by
    intro x π
    simp only [Φ, hR, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm _ (sgnL d id), smul_comm ((Equiv.Perm.sign π : ℤ) : ℂ) (a (d 0) * a' (d 1))]
  have h1 : GG F β β' a a' =
      ∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id • ((β (c 0) * β' (c 1)) • Φ (fun k => c k.succ.succ)) := by
    unfold GG
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Φ, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    ring
  have h2 : ∀ i i' : Fin (m + 2), Φ (skip2 i i') = (m.factorial : ℂ) • ∑ j : Fin (m + 2), ∑ j' : Fin (m + 2),
      if j < j' then ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (a j' * a' j - a j * a' j')) •
        F (skip2 i i') (skip2 j j') else 0 := by
    intro i i'
    exact one_side (fun y => F (skip2 i i') y) (fun y π => hC _ y π) a a'
  rw [h1, one_side Φ hΦ β β', Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  by_cases hi : i < i'
  · simp only [hi, if_true, true_and, h2, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases hj : j < j'
    · simp only [hj, if_true, smul_smul]
      congr 1
      rw [pow_add, pow_add, pow_add, pow_add]
      ring
    · simp [hj]
  · simp [hi]

end PI.QnCovHat2W
