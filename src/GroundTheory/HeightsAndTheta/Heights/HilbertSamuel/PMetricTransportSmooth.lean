module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricTransportSmooth
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLattice
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ChangeOfLattice

noncomputable section

namespace MetricTransportSmooth

theorem matActC_one {J : Type} [Fintype J] [DecidableEq J] (z : J → ℂ) : matActC (1 : Matrix J J ℚ) z = z := by
  have h := matActC_smul_one (J := J) (1 : ℚ) z
  simpa using h

theorem matActC_zero {J : Type} [Fintype J] (A : Matrix J J ℚ) : matActC A 0 = 0 := by
  funext i
  simp [matActC]

theorem proof : MetricTransportSmooth.Statement := by
  intro κ _ B m m' hB hm hm'
  classical
  obtain ⟨B', hBB', hB'B⟩ := isInvMat_mul hB
  have hinv : ∀ w, matActC B (matActC B' w) = w := fun w => by
    rw [matActC_mul, hBB', matActC_one]
  have heq : ∀ w, m'.ρ w = m.ρ (matActC B' w) := fun w => by
    rw [← hm' (matActC B' w), hinv]
  have hmaps : Set.MapsTo (matActC B') {z : Ix κ → ℂ | z ≠ 0} {z | z ≠ 0} := fun w hw h0 => by
    apply hw
    rw [← hinv w, h0, matActC_zero]
  exact (hm.comp (contDiff_matActC B').contDiffOn hmaps).congr fun w _ => heq w

end MetricTransportSmooth

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
