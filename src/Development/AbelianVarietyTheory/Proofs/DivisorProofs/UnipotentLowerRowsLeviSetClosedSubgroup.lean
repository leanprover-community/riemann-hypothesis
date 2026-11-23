module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

open MeasureTheory in
open scoped FourierTransform ContDiff in
private theorem mem_levSet_iff_unitriangular_below_r {n r : ℕ} {g : GL (Fin n) ℂ} :
    g ∈ _root_.GlobalTheory.JSW.levSet n r ↔
      ∀ i : Fin n, r ≤ (i : ℕ) →
        (∀ j < i, (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧ (g : Matrix (Fin n) (Fin n) ℂ) i i = 1 :=
  Iff.rfl

open MeasureTheory in
open scoped FourierTransform ContDiff in
private theorem mul_apply_eq_apply_of_unitriangular_index_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    {i : Fin n} (hA : (∀ j < i, A i j = 0) ∧ A i i = 1)
    (hB : ∀ k, i < k → ∀ j < k, B k j = 0) (j : Fin n) (hj : j ≤ i) :
    (A * B) i j = B i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA.2, one_mul]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hA.1 k hk, zero_mul]
    · rw [hB k hk j (lt_of_le_of_lt hj hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h


open MeasureTheory in
open scoped FourierTransform ContDiff in
theorem _root_.GlobalTheory.JSW.levSet_closed_subgroup : ∀ (n r : ℕ),
    (∀ g ∈ _root_.GlobalTheory.JSW.levSet n r, ∀ h ∈ _root_.GlobalTheory.JSW.levSet n r,
      g * h ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    (∀ g ∈ _root_.GlobalTheory.JSW.levSet n r, g⁻¹ ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    (∀ u ∈ _root_.GlobalTheory.SmGL.unipB ℂ (Fin n), u ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    IsClosed (_root_.GlobalTheory.JSW.levSet n r) := by
  intro n r
  refine ⟨fun g hg h hh => ?_, fun g hg => ?_, fun u hu => ?_, ?_⟩
  · rw [mem_levSet_iff_unitriangular_below_r] at hg hh ⊢
    intro i hi
    have hrow := mul_apply_eq_apply_of_unitriangular_index_le (hg i hi) (B := (h : Matrix (Fin n) (Fin n) ℂ))
      fun k hk => (hh k (hi.trans (Fin.lt_iff_val_lt_val.mp hk).le)).1
    rw [Units.val_mul]
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hrow j hj.le]
      exact (hh i hi).1 j hj
    · rw [hrow i le_rfl]
      exact (hh i hi).2
  · rw [mem_levSet_iff_unitriangular_below_r] at hg ⊢
    have hgh : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
      Units.mul_inv g
    have key : ∀ m : ℕ, ∀ i : Fin n, r ≤ (i : ℕ) → n - (i : ℕ) ≤ m →
        (∀ j < i, ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
          ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1 := by
      intro m
      induction m with
      | zero =>
        intro i _ hm
        have := i.isLt
        omega
      | succ m ih =>
        intro i hi hm
        have hrow := mul_apply_eq_apply_of_unitriangular_index_le (hg i hi)
          (B := ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
          fun k hk => by
            have hik := Fin.lt_iff_val_lt_val.mp hk
            exact (ih k (hi.trans hik.le) (by omega)).1
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [← hrow j hj.le, hgh, Matrix.one_apply_ne hj.ne']
        · rw [← hrow i le_rfl, hgh, Matrix.one_apply_eq]
    exact fun i hi => key n i hi (Nat.sub_le _ _)
  · rw [_root_.GlobalTheory.SmGL.mem_unipB] at hu
    exact fun i _ => ⟨fun j hj => hu.1 i j hj, hu.2 i⟩
  · have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) i j :=
      fun i j => Units.continuous_val.matrix_elem i j
    have hset : _root_.GlobalTheory.JSW.levSet n r = ⋂ i : Fin n, ⋂ (_ : r ≤ (i : ℕ)),
        ((⋂ j : Fin n, ⋂ (_ : j < i), {g : GL (Fin n) ℂ | (g : Matrix (Fin n) (Fin n) ℂ) i j = 0}) ∩
          {g : GL (Fin n) ℂ | (g : Matrix (Fin n) (Fin n) ℂ) i i = 1}) := by
      ext g
      simp only [mem_levSet_iff_unitriangular_below_r, Set.mem_iInter, Set.mem_inter_iff,
        Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      (isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const).inter
        (isClosed_eq (hc i i) continuous_const)

end GlobalTheory.JSW
