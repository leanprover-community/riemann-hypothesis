module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegral
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.center_operator_commutes_integral : ∀ (n : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (U : ℝ → Mat n → V) (g : ℝ → ℝ) (T : ℝ) (w : List (Bool × ℕ)), ContDiffOn ℝ ∞ (Function.uncurry U) (Set.univ ×ˢ GLs n) → IsBump g T → ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • U t x') x = ∫ t, (g t : ℂ) • zOp w (U t) x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg | exact GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.ZOpAvg.zOp_avg <;> assumption)
