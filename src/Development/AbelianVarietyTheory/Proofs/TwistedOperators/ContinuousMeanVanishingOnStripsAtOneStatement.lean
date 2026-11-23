module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMeanVanishingOnStripsAtOne
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.continuousMean_vanishing_on_strips_at_one : ∀ (D : D7) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (R K : Subgroup (GA D W)), IsClosed (R : Set (GA D W)) → (∀ a ∈ GinfC W, ∀ b ∈ GfC W, a * b ∈ R → a ∈ R ∧ b ∈ R) → K ≤ GfC W → IsCompact (K : Set (GA D W)) → IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)) → ∀ (μR : Measure R), μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (𝓡 : Set R) (𝓑 : Set (GA D W)), IsFundamentalDomain ((GQ W ⊓ R).subgroupOf R) 𝓡 μR → IsFundamentalDomain (GQ W ⊓ R : Subgroup (GA D W)) 𝓑 vW.μ → ∀ f : GA D W → ℂ, Measurable f → (∀ γ ∈ GQ W ⊓ R, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓑 vW.μ → (∀ h, IntegrableOn (fun r : R => f (r * h)) 𝓡 μR) → (Continuous fun h => ∫ r in 𝓡, f ((r : GA D W) * h) ∂μR) → (∀ k ∈ K, ∀ g, f (g * k) = f g) → (∀ h, f h ≠ 0 → ∃ r ∈ R, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) → (∀ C : Set (GA D W), IsCompact C → C ⊆ GinfC W → MeasurableSet (strip W R C) ∧ ∫ h in 𝓑 ∩ strip W R C, f h ∂vW.μ = 0) → ∫ r in 𝓡, f r ∂μR = 0 := by
  first | exact @GlobalTheory.StripVanish.mean_eq_zero_of_strips | exact GlobalTheory.StripVanish.mean_eq_zero_of_strips | (intros; apply GlobalTheory.StripVanish.mean_eq_zero_of_strips <;> assumption)
