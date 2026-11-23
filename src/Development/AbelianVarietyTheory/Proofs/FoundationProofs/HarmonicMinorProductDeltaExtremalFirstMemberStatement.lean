module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicMinorProductDeltaExtremalFirstMember
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

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harmonicMinorProductDelta_extremal_first_member : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → delta hn ap am ≠ 0 ∧ delta hn ap am ∈ wtSub (fockAct1 p q n 0) (wtExt n ap am) ∧ (∀ i j : Fin p, i < j → fockAct1 p q n 0 (Eab (Sum.inl i) (Sum.inl j)) (delta hn ap am) = 0) ∧ (∀ i j : Fin q, i < j → fockAct1 p q n 0 (Eab (Sum.inr j) (Sum.inr i)) (delta hn ap am) = 0) ∧ KilledByLower (fockAct1 p q n 0) (delta hn ap am) := by
  first | exact @GlobalTheory.FockMinorExtremal.delta_extremal | exact GlobalTheory.FockMinorExtremal.delta_extremal | (intros; apply GlobalTheory.FockMinorExtremal.delta_extremal <;> assumption)
