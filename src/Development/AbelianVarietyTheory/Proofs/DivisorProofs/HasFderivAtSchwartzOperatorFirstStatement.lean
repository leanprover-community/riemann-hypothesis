module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFderivAtSchwartzOperatorFirst
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

@[expose] public section

open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

theorem _root_.GlobalTheory.T.has_fderiv_at_schwartz_operator_first : ∀ {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V'), HasFDerivAt (opFst T f) ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V') + (dSndCLM T f (y, x')).comp (ContinuousLinearMap.snd ℝ W V')) (y, x') := by
  first | exact @GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst | exact GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst | (intros; apply GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst <;> assumption)
