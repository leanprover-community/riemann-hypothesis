module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

theorem UpperTheory.Reformulated.B.DetMulExpand.det_mul_expand :
    ∀ {F : Type} [inst : CommRing F] {k r : ℕ} (A : Matrix (Fin k) (Fin r) F) (B : Matrix (Fin r) (Fin k) F),
      (A * B).det = ∑ f : Fin k → Fin r, (∏ a : Fin k, A a (f a)) * (B.submatrix f id).det := by
  intro F _ k r A B
  have h1 : (A * B) = (fun a => ∑ j, (A a j • B j : Fin k → F)) := by
    ext a c
    simp [Matrix.mul_apply, Finset.sum_apply]
  have h2 : (A * B).det
      = (Matrix.detRowAlternating (R := F) (n := Fin k)).toMultilinearMap
          (fun a => ∑ j, (A a j • B j : Fin k → F)) := by
    rw [← h1]
    rfl

  rw [h2, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl
