module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SlabMeasureSqueeze
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.slab_measure_squeeze' : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε (maxK ε ∩ flagM ε W) E → (∀ i, (E i)ᴴ = -E i) → ∀ ν : Measure (Formalism.REAL.UJ ε), ν (maxK ε ∩ flagM ε W)ᶜ = 0 → (∀ l ∈ maxK ε ∩ flagM ε W, ν.map (fun g => g * l) = ν) → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, u * m * k ∈ hsBall ε r → ν (hsBall ε (r / (1 + η))) ≤ ν {l | l * k ∈ slab ε E ρ r} ∧ ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  first | exact @GlobalTheory.IwConst.slab_measure_squeeze | exact GlobalTheory.IwConst.slab_measure_squeeze | (intros; apply GlobalTheory.IwConst.slab_measure_squeeze <;> assumption)
