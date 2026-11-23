module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentiableAtOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGapStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypotheses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOfMemLowKSub
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem stepBoundAt_of_countHyp : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ)
    (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  intro B Cg n₀ d p q b hn₀ hC
  obtain ⟨-, -, -, -, -, -, hrk, -, -, -, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    countHyp_numerics B Cg n₀ d p q b hn₀ hC
  have hK := countHyp_isKTypeOf_lowKSub B Cg n₀ d p q b hn₀ hC
  obtain ⟨hD, -, -, -, -, -, -, -, hlam, -⟩ := hC
  refine GlobalTheory.StepGlob.stepBoundAt_of_local B b (fun v => ?_)
  obtain ⟨hpar, hds, -, -⟩ := hD v
  have hU : IsURepOn (UJset (B.I.ε v)) (B.σ v) := hds.2.2.1
  have h120v : 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hrk v]; exact h120
  have heig := GlobalTheory.T.lowestKType_infinitesimalChar_large_gap B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hpar hds h (hgap v) h120v
  exact ⟨hU, GlobalTheory.StepBoundOneRep.stepBound_of_eigen B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) b hU
    (hK v) heig (hlam v)⟩

end GlobalTheory.Dec
