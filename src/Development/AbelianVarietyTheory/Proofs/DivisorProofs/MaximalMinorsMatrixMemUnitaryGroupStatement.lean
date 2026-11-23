module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalMinorsMatrixMemUnitaryGroup
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

open Matrix
open scoped Classical


theorem _root_.GlobalTheory.T.maximalMinorsMatrix_mem_unitaryGroup : ∀ {N a : ℕ} (M : Matrix (Fin N) (Fin N) ℂ), M ∈ Matrix.unitaryGroup (Fin N) ℂ → (Matrix.of fun s s' : {s : Fin a → Fin N // StrictMono s} => (Matrix.of fun i i' : Fin a => M (s'.1 i') (s.1 i)).det) ∈ Matrix.unitaryGroup {s : Fin a → Fin N // StrictMono s} ℂ := by
  first | exact @GlobalTheory.minorsMatrix_mem_unitaryGroup | exact GlobalTheory.minorsMatrix_mem_unitaryGroup | (intros; apply GlobalTheory.minorsMatrix_mem_unitaryGroup <;> assumption)
