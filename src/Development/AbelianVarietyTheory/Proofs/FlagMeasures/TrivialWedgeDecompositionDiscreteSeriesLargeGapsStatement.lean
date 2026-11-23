module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialWedgeDecompositionDiscreteSeriesLargeGaps
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.trivialWedgeDecomposition_discreteSeries_largeGaps : BranchingSupport.HypsG → ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (F F' : (Fin (2 * r + k + 1) → ℤ) → BranchingSupport.Rep k r) (ν : Fin (2 * r + k + 1) → ℤ), BranchingSupport.Num k r lam u b bv ga h q0 → BranchingSupport.IsFamG lam q0 F → BranchingSupport.IsFamG lam q0 F' → BranchingSupport.n1 ν + 2 ≤ q0 → ∃ io pr ep, BranchingSupport.TensH (BranchingSupport.cmp 0) (BranchingSupport.cmp 0 (Formalism.QuantumDeterminants.Hpk k r)) (F ν) (fun I : BranchingSupport.Sub (2 * r + k + 1) 0 => F' (ν + BranchingSupport.eZ I.1)) io pr ep := by
  first | exact @GlobalTheory.TrivWedge.tensH_trivial | exact GlobalTheory.TrivWedge.tensH_trivial | (intros; apply GlobalTheory.TrivWedge.tensH_trivial <;> assumption)
