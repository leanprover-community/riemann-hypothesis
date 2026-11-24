module

public import Formalism.GaussValuationBounds.Statement
public import Formalism.WindowSums.PowerSeriesRelationList
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.NOK

theorem kapBound_proof : KapBound := by
  intro ℓ _ hℓ χ hχ ell g h a JJ hJJ hbd
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ
  refine ⟨hne, ?_⟩

  have hcard : (JJ.erase 0).card ≤ 20 * g := by
    calc (JJ.erase 0).card ≤ JJ.card := Finset.card_le_card (Finset.erase_subset _ _)
      _ ≤ (Finset.univ.biUnion (fun t : Fin 5 => Finset.Ico (a t) (a t + 4 * (g : ℤ)))).card :=
          Finset.card_le_card hJJ
      _ ≤ ∑ t : Fin 5, (Finset.Ico (a t) (a t + 4 * (g : ℤ))).card := Finset.card_biUnion_le
      _ = ∑ t : Fin 5, 4 * g := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Int.card_Ico, add_sub_cancel_left]
          omega
      _ = 20 * g := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring

  have hsumv : ((∑ i ∈ JJ.erase 0, padicValInt ℓ i : ℕ) : ℝ) ≤
      5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := by
    have hle : (∑ i ∈ JJ.erase 0, padicValInt ℓ i) ≤
        ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
          padicValInt ℓ i := by
      calc (∑ i ∈ JJ.erase 0, padicValInt ℓ i)
          ≤ ∑ i ∈ JJ.erase 0, ∑ t : Fin 5,
              (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) := by
            apply Finset.sum_le_sum
            intro i hi
            obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (hJJ (Finset.mem_of_mem_erase hi))
            calc padicValInt ℓ i
                = (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
                  (if_pos ht).symm
              _ ≤ ∑ t' : Fin 5,
                    (if i ∈ Finset.Ico (a t') (a t' + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
                  Finset.single_le_sum
                    (f := fun t' => if i ∈ Finset.Ico (a t') (a t' + 4 * (g : ℤ)) then padicValInt ℓ i else 0)
                    (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
        _ = ∑ t : Fin 5, ∑ i ∈ JJ.erase 0,
              (if i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)) then padicValInt ℓ i else 0) :=
            Finset.sum_comm
        _ = ∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
              padicValInt ℓ i := by
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.sum_filter]
    have hwin : ∀ t : Fin 5,
        ((∑ i ∈ (JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))),
            padicValInt ℓ i : ℕ) : ℝ) ≤ 4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ)) := by
      intro t
      have hw := Formalism.WindowSums.arc_WindowSum ℓ (a t) (4 * g) (2 * h)
        ((JJ.erase 0).filter (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ)))) ?_ ?_ ?_
      · push_cast at hw ⊢
        exact hw
      · intro i hi
        rw [Finset.mem_filter] at hi
        push_cast
        exact hi.2
      · intro h0
        rw [Finset.mem_filter] at h0
        exact (Finset.mem_erase.mp h0.1).1 rfl
      · intro i hi
        rw [Finset.mem_filter] at hi
        push_cast
        exact hbd i (Finset.mem_of_mem_erase hi.1)
    calc ((∑ i ∈ JJ.erase 0, padicValInt ℓ i : ℕ) : ℝ)
        ≤ ((∑ t : Fin 5, ∑ i ∈ (JJ.erase 0).filter
              (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = ∑ t : Fin 5, ((∑ i ∈ (JJ.erase 0).filter
              (fun i => i ∈ Finset.Ico (a t) (a t + 4 * (g : ℤ))), padicValInt ℓ i : ℕ) : ℝ) := by
          rw [Nat.cast_sum]
      _ ≤ ∑ _t : Fin 5, (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) :=
          Finset.sum_le_sum (fun t _ => hwin t)
      _ = 5 * (4 * (g : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ (2 * (h : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  have hsplit : (∑ i ∈ JJ.erase 0, (1 + ell + padicValInt ℓ i)) =
      (JJ.erase 0).card * (1 + ell) + ∑ i ∈ JJ.erase 0, padicValInt ℓ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  have hc : (((JJ.erase 0).card * (1 + ell) : ℕ) : ℝ) ≤ 20 * (g : ℝ) * (1 + (ell : ℝ)) := by
    have h1 : (JJ.erase 0).card * (1 + ell) ≤ 20 * g * (1 + ell) := Nat.mul_le_mul_right _ hcard
    exact_mod_cast h1
  rw [hval, hsplit]
  push_cast at hc hsumv ⊢
  linarith

end Formalism.NOK
