module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTsumCosetsFundamentalDomainEqCovol
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lintegral_tsum_cosets_fundamentalDomain_eq_covol : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ S : Subgroup G) (μ : Measure G) (fund : Set G) (Φ : G → ENNReal) (ι : Type) [Countable ι] (r : ι → G), (Γ : Set G).Countable → S ≤ Γ → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → Measurable Φ → (∀ γ ∈ S, ∀ g, Φ (γ * g) = Φ g) → (∀ i, r i ∈ Γ) → (∀ γ ∈ Γ, ∃! i, γ * (r i)⁻¹ ∈ S) → ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ = covol (S : Set G) (μ.withDensity Φ) Set.univ := by
  first | exact @GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol | exact GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol | (intros; apply GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol <;> assumption)
