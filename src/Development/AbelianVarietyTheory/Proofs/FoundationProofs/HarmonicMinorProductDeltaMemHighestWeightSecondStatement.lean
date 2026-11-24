module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaMemHighestWeightSecond
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

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harmonicMinorProductDelta_mem_highestWeight_second : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) := by
  first | exact @GlobalTheory.DeltaHighest.delta_mem_hwSub | exact GlobalTheory.DeltaHighest.delta_mem_hwSub | (intros; apply GlobalTheory.DeltaHighest.delta_mem_hwSub <;> assumption)
