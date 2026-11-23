module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidueStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStepStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPowStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem genLinVolume : GenLinVolume := by
  intro E _ _ hE j hj
  induction j, hj using Nat.le_induction with
  | base => simpa using GlobalTheory.T.glNormOneAdelicQuotientVolume_one_eq_residue E hE
  | succ j hj ih =>
    have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv E := by
      unfold Formalism.HermitianLatticesTheory.vInv
      positivity
    have hz : 0 ≤ zetaE E (j + 1) := zero_le_one.trans (GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow E (j + 1) (by omega)).1
    have h := GlobalTheory.T.glNormOneAdelicQuotientVolume_siegel_step E hE (j + 1) (by omega)
      (by rw [Nat.add_sub_cancel, ih]; exact ENNReal.ofReal_lt_top)
    rw [h, Nat.add_sub_cancel, ih, ← ENNReal.ofReal_mul' (mul_nonneg (pow_nonneg hv _) hz),
      Finset.prod_Icc_succ_top (by omega)]
    congr 1
    have e : Formalism.HermitianLatticesTheory.fDeg E * (j + 1) ^ 2 =
        Formalism.HermitianLatticesTheory.fDeg E * j ^ 2 + Formalism.HermitianLatticesTheory.fDeg E * (2 * (j + 1) - 1) := by
      have : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [this]; ring
    rw [e, pow_add]
    ring

end GlobalTheory.FlagMeas
