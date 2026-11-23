module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureInterTranslateEqZeroOfCovolume
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.T.measure_inter_translate_eq_zero_of_covolume : ∀ (X : Type) [Mul X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X] (S : Set X) (μ : Measure X) [SigmaFinite μ] (U D : Set X), S.Countable → (∀ γ ∈ S, Measurable fun x => γ * x) → (∀ γ ∈ S, μ.map (fun x => γ * x) = μ) → (∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x)) → (∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x) → MeasurableSet U → (∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) → MeasurableSet D → D ⊆ U → (∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) → covol S μ A = μ (A ∩ D)) → ∀ γ ∈ S, (∀ x ∈ U, γ * x ≠ x) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
  first | exact @GlobalTheory.StrictDomain.measure_inter_translate_eq_zero | exact GlobalTheory.StrictDomain.measure_inter_translate_eq_zero | (intros; apply GlobalTheory.StrictDomain.measure_inter_translate_eq_zero <;> assumption)
