module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowGrassmannBlockCurvatureSupertraceZero
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


theorem _root_.GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero : ∀ {n p q : ℕ} (e : Fin p × Fin q → Fin n) (k : ℕ), 1 ≤ k → ((GlobalTheory.GrassModel.blockPoly e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace + ((-GlobalTheory.GrassModel.blockPolyBar e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace = 0 := by
  first | exact @GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | exact GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | (intros; apply GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar <;> assumption)
