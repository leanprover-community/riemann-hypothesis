module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QuasiDeterminantConjInv
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.RgConjQdet

open Finset

theorem conj_single_apply {n : ℕ} (U Ui : Matrix (Fin n) (Fin n) ℂ) (p q a b : Fin n) :
    (U * Matrix.single p q 1 * Ui : Matrix (Fin n) (Fin n) ℂ) a b = U a p * Ui q b := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem conjQdet : CompanionTheory.RgExh.Dec.J.ConjQdet := by
  intro n X U Ui hUUi hUiU u
  have hE : ∀ (x : ℂ) (p q : Fin n),
      Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) x p q =
        ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d := by
    intro x p q
    have hd : ∑ c, ∑ d, (U c p * Ui q d) • (if c = d then algebraMap ℂ (Module.End ℂ X.V) x else 0)
        = if p = q then algebraMap ℂ (Module.End ℂ X.V) x else 0 := by
      simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.sum_smul]
      have hc : ∑ c, U c p * Ui q c = (Ui * U) q p := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
      rw [hc, hUiU, Matrix.one_apply]
      by_cases hpq : p = q
      · subst hpq
        simp
      · rw [if_neg (Ne.symm hpq), if_neg hpq, zero_smul]
    simp only [Formalism.REAL.Tm, ReciprocityTheory.ChartRestriction.DS.actM, conj_single_apply, Matrix.transpose_apply,
      Finset.smul_sum, smul_smul, smul_add, Finset.sum_add_distrib]
    rw [hd]
  have hT : Formalism.REAL.Tm (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)) =
      fun x p q => ∑ c, U.transpose p c • ∑ d, Ui.transpose d q • Formalism.REAL.Tm X.E x c d :=
    funext fun x => funext fun p => funext fun q => hE x p q
  rw [PI.UnitaryGroupMassFormula.DSIC.qdet_eq_qF (fun p q => ReciprocityTheory.ChartRestriction.DS.actM X.E (U * Matrix.single p q 1 * Ui)), hT,
    PI.UnitaryGroupMassFormula.DSIC.qF_row, PI.UnitaryGroupMassFormula.DSIC.qF_col X.E X.gl, smul_smul, Matrix.det_transpose,
    Matrix.det_transpose, ← Matrix.det_mul, hUUi, Matrix.det_one, one_smul]

end GlobalTheory.CompanionTheory.RgConjQdet
