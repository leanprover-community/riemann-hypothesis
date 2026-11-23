module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.IndDim
public import CompanionTheory.AutomorphicTheory.MirabolicRestriction.MirabolicInduction.IndIrr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling

namespace CompanionTheory.Mirab

variable {k : Type} [Field k] [Fintype k] (n : ℕ)

theorem mirabInduced_isIrreducible (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) : (mirabInduced n ψ₀).IsIrreducible := by
  exact CompanionTheory.Mirab.Irr.mirabInduced_isIrreducible n ψ₀ hψ

theorem finrank_mirabInducedSpace_eq_index (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = (uniSub k n).index := by
  exact CompanionTheory.Mirab.Dim.finrank_mirabInducedSpace_eq_index n ψ₀

theorem index_uniSub : (uniSub k n).index = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by
  exact CompanionTheory.Mirab.Dim.index_uniSub n

theorem finrank_mirabInducedSpace (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by
  rw [finrank_mirabInducedSpace_eq_index, index_uniSub]

end CompanionTheory.Mirab
