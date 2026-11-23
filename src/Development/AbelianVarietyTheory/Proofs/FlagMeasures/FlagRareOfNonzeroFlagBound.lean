module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.RareFlags
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FlagRareProof

theorem flagRare_of_nonzeroFlagBound : GlobalTheory.FlagMeas.NonzeroFlagBound → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare := by
  intro h
  refine ⟨⌈Real.exp 15⌉₊, ?_⟩
  intro B p q hsig hn hq hrd hf

  have hn' : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 hn
  have hn1 : 1 ≤ B.I.n := by
    have : 0 < ⌈Real.exp 15⌉₊ := Nat.ceil_pos.2 (Real.exp_pos 15)
    omega
  have hlog : 15 ≤ Real.log B.I.n := by
    have := Real.log_le_log (Real.exp_pos 15) hn'
    rwa [Real.log_exp] at this
  have key := h B.I B.μf B.fund B.fund_spec p q hsig hlog hq hrd hf

  have hset : {x | least B.I x < 1 / 2} = {x | stepLt B.I x (1 / 2) ≠ ⊥} := by
    ext x
    have hx := ((GlobalTheory.CountSteps.steps B.I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.2 hn1).2.2
    simp only [Set.mem_ofPred_eq, ne_eq, hx, not_le]
  have hnf : 0 ≤ (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  rw [prob, hset, Formalism.MainNotions.S.AutInst.vol, ← ENNReal.toReal_div]
  calc _ ≤ Real.exp (-(1 / 3 * (B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
        ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le key
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.FlagRareProof
