module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnipotentIntegralPreservesLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_gram : RankG := by
  intro D T T' Z hG
  classical
  by_cases hdet : Z.det = 0
  · have hm : leadMinorE Z D.R.rS ≠ 0 := by
      intro hm
      apply hG
      have h1 : leadMinorE Z (D.R.rS + 1) = 0 := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos le_rfl, Fin.castLE_rfl, Matrix.submatrix_id_id]
        exact hdet
      simp [Formalism.L2.SG.CntLocal.GZ, h1, hm]
    have h : D.R.rS ≤ D.R.rS + 1 := Nat.le_succ _
    set B := Z.submatrix (Fin.castLE h) (Fin.castLE h) with hB
    have hBdet : B.det ≠ 0 := by
      have e : leadMinorE Z D.R.rS = B.det := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos h]
      rwa [← e]
    refine ⟨Matrix.of fun j i => if hj : (j : ℕ) < D.R.rS then B⁻¹ ⟨j, hj⟩ i else 0, ?_⟩
    have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hBdet)
    ext a i
    rw [← hBB]
    simp only [Matrix.mul_apply, betaZ, Matrix.submatrix_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
      Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, not_false_eq_true, dif_neg, mul_zero,
      add_zero, id]
    rfl
  · refine ⟨(Z⁻¹).submatrix id Fin.castSucc, ?_⟩
    have hZ : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z (isUnit_iff_ne_zero.2 hdet)
    unfold betaZ
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hZ]
    exact Matrix.submatrix_one_embedding Fin.castSuccEmb

end PI.UnitaryGroupMassFormula.CntFormula
