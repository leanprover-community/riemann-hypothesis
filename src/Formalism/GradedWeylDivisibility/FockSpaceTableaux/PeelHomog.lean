module

public import Formalism.GradedWeylDivisibility.StatementC
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcpeel_support {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (a0 : Fin r) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) B) (d : Fin r × Fin n →₀ ℕ)
    (hd : AddMonoidAlgebra.coeff (peel l j a0 k g) d ≠ 0) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ d = (m.erase (a0, l)).erase (a0, j) := by
  unfold peel at hd
  rw [coeff_sum] at hd
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
  refine ⟨m, hm1, hm2, ?_⟩
  rw [coeff_monomial] at hne
  split_ifs at hne with h
  · exact h.symm
  · exact absurd rfl hne

private theorem weight_single_eq_nsmul {σ M : Type*} [AddCommMonoid M] (w : σ → M) (s : σ) (c : ℕ) :
    Finsupp.weight w (Finsupp.single s c) = c • w s := by
  first
    | (rw [Finsupp.weight_apply, Finsupp.sum_single_index]; exact zero_smul ℕ (w s))
    | simp [Finsupp.weight_apply]

private theorem eq_erase_erase_add_single_add_single {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m : Fin r × Fin n →₀ ℕ) :
    m = (m.erase (a0, l)).erase (a0, j) + Finsupp.single (a0, l) (m (a0, l)) +
      Finsupp.single (a0, j) (m (a0, j)) := by
  ext ⟨b, t⟩
  simp only [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply, Prod.mk.injEq]
  by_cases hb : b = a0
  · subst hb
    by_cases hl : t = l
    · subst hl
      simp [hlj, Ne.symm hlj]
    · by_cases hj : t = j
      · subst hj
        simp [hl, Ne.symm hl]
      · simp [hl, hj, Ne.symm hl, Ne.symm hj]
  · simp [hb, Ne.symm hb]

private theorem weight_pairW_apply_eq_zero_of_vanish {r n : ℕ} (l j : Fin n) (a0 : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (hl : d (a0, l) = 0) (hj : d (a0, j) = 0) :
    Finsupp.weight (pairW l j) d (a0, l) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  dsimp only
  have hi0 : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  obtain ⟨b, t⟩ := i
  by_cases ht : t = j
  · have hne : ¬ ((b, l) = (a0, l)) := by
      intro h
      simp only [Prod.mk.injEq] at h
      rw [h.1, ht] at hi0
      exact hi0 hj
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, l) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]
  · have hne : ¬ ((b, t) = (a0, l)) := by
      intro h
      rw [h] at hi0
      exact hi0 hl
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, t) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]

private theorem weight_pairW_eq_erase_of_split {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m d ω : Fin r × Fin n →₀ ℕ) (hdl : d (a0, l) = 0) (hdj : d (a0, j) = 0)
    (hsplit : m = d + Finsupp.single (a0, l) (m (a0, l)) + Finsupp.single (a0, j) (m (a0, j)))
    (hw : Finsupp.weight (pairW l j) m = ω) :
    Finsupp.weight (pairW l j) d = ω.erase (a0, l) := by
  have hpl : pairW (r := r) l j (a0, l) = Finsupp.single (a0, l) 1 := by
    simp [pairW, hlj]
  have hpj : pairW (r := r) l j (a0, j) = Finsupp.single (a0, l) 1 := by
    simp [pairW]
  have key : ω = Finsupp.weight (pairW l j) d +
      Finsupp.single (a0, l) (m (a0, l) + m (a0, j)) := by
    rw [← hw]
    conv_lhs => rw [hsplit]
    rw [map_add (f := _), map_add (f := _), weight_single_eq_nsmul, weight_single_eq_nsmul, hpl, hpj]
    first
      | (rw [add_assoc, ← add_smul, Finsupp.smul_single, smul_eq_mul, mul_one])
      | (ext y
         simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
         split_ifs <;> ring)
  ext x
  by_cases hx : x = (a0, l)
  · rw [hx, Finsupp.erase_same]
    exact weight_pairW_apply_eq_zero_of_vanish l j a0 d hdl hdj
  · rw [Finsupp.erase_ne hx, key, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hx),
      add_zero]

theorem sliceHomogeneous : PeelHomog := by
  intro B _ r n l j hlj a0 ω k g hg
  refine ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨m, hm, -, rfl⟩ := lcpeel_support l j a0 k g d hd
    exact weight_pairW_eq_erase_of_split l j hlj a0 m _ ω
      (by simp [Finsupp.erase_apply, hlj]) (by simp [Finsupp.erase_apply])
      (eq_erase_erase_add_single_add_single l j hlj a0 m) (hg (mem_support_iff.mp hm))
  · intro d hd
    obtain ⟨m, -, -, rfl⟩ :=
      lcpeel_support l j a0 k g d (mem_support_iff.mp hd)
    exact ⟨by simp [Finsupp.erase_apply, hlj], by simp [Finsupp.erase_apply]⟩

end Formalism.GradedWeylDivisibility
