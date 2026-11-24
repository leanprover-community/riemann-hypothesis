module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace PI.GGMirBoundW

open Finset Matrix

noncomputable section

open Classical

theorem rowExists : RowExists := by
  intro F _ _ n r hr
  obtain ⟨k, hk⟩ : ∃ k, r k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap k (Fin.last n) with hσ
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.updateRow 1 (Fin.last n) (fun j => r (σ j)) with hA
  have hAtri : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hi : i ≠ Fin.last n := fun h => by
      subst h
      exact absurd hij' (not_lt.mpr (Fin.le_last j))
    rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]
  have hdetA : A.det = r k := by
    rw [Matrix.det_of_lowerTriangular A hAtri, Finset.prod_eq_single (Fin.last n)]
    · rw [hA, Matrix.updateRow_self]
      simp [hσ]
    · intro i _ hi
      rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_eq]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set B := A.submatrix id σ with hB
  have hdetB : B.det ≠ 0 := by
    rw [hB, Matrix.det_permute', hdetA]
    refine mul_ne_zero ?_ hk
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdetB)
  refine ⟨hunit.unit, fun j => ?_⟩
  rw [IsUnit.unit_spec]
  simp [hB, hA, hσ, Matrix.updateRow_self, Equiv.swap_apply_self]

end

end PI.GGMirBoundW
