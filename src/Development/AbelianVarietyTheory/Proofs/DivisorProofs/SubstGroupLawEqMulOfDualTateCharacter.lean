module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensorStatement
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
open TensorProduct

namespace GlobalTheory.QLog.Chart

theorem subst_μ_eq_inL_mul_inR : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) →
    subst c.μ u = inL u * inR u := by
  intro p _ O _ _ _ G d c χ u hu
  set D := subst c.μ u - inL u * inR u with hD
  have hev : ∀ n, c.ev₂ n D = 0 := by
    intro n
    obtain ⟨h1, h2, h3, -⟩ := ev₂_eval p O G d c n u
    rw [hD, map_sub, map_mul, h1, h2, h3, hu n, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      (isGroupLikeElem_charElem χ n).comul_eq_tmul_self, sub_self]
  rw [← sub_eq_zero, ← hD]
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : O)})) _ fun m => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O (G.A n) (G.A n) (Fin d) (Fin d) (c.x n) (c.x n) (c.ev n) (c.ev n) (c.ev₂ n) m
    (α.degree + 1) (c.isEval n) (c.isEval n) (c.isEval₂ n) (c.surj n) (c.surj n) hn hn D (hev n) α
    (Nat.lt_succ_self _)

end GlobalTheory.QLog.Chart
