module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpTwoOfCoshDecayUnitaryPQCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.memLp_two_of_cosh_decay_unitaryPQCover : GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.CoshIntegral → ∀ (p q n : ℕ), p + q < n → ∀ (T : GrpData p q) (f : T.G → ℂ) (C : ℝ), Continuous f → (∀ k ∈ T.Kset, ∀ X ∈ pR p q, ‖f (k * T.expt X)‖ ≤ C * decay n X) → MemLp f 2 T.haar := by
  first | exact @GlobalTheory.CoshSqInt.memLp_two_of_decay | exact GlobalTheory.CoshSqInt.memLp_two_of_decay | (intros; apply GlobalTheory.CoshSqInt.memLp_two_of_decay <;> assumption)
