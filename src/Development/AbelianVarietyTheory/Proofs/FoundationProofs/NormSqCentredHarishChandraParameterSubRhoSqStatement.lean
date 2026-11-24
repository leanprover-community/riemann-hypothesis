module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqCentredHarishChandraParameterSubRhoSq
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

theorem _root_.GlobalTheory.T.normSq_centredHarishChandraParameter_sub_rhoSq : ∀ (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ), normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  first | exact @GlobalTheory.normSq_hcParam_sub_rhoSq | exact GlobalTheory.normSq_hcParam_sub_rhoSq | (intros; apply GlobalTheory.normSq_hcParam_sub_rhoSq <;> assumption)
