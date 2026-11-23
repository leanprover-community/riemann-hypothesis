module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqFlatMapFourierJacobiRow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.partialReduction_eq_flatMapFourierJacobiRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ + 1 → ∀ (lρ : Fin c), lρ.val = ρ → ∀ (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.PartRed.red ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) (GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ) Φ x = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ (Matrix.of fun r s => Sum.elim (fun r => x (Sum.inl r) (Sum.inl s)) (fun _ => x (Sum.inr lρ) (Sum.inl s)) r) := by
  first | exact @GlobalTheory.RedFlatRow.red_eq_flRow | exact GlobalTheory.RedFlatRow.red_eq_flRow | (intros; apply GlobalTheory.RedFlatRow.red_eq_flRow <;> assumption)
