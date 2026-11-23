module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBaseTermUnfoldingCoordinates
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.integral_baseTerm_unfolding_coordinates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsTh ψ d W x₀ Th → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), NullMeasurableSet 𝓐 vN.ν → NullMeasurableSet 𝓑 vW.μ → (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) ≠ ⊤ → IntegrableOn (fun h => G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ)) 𝓑 vW.μ ∧ ∫ p in 𝓐 ×ˢ 𝓑, Th p.1.1 * G p.2 * term ψ d W vS (om (p.1.1, p.2) Φ) x₀ ∂(vN.ν.prod vW.μ) = ∫ h in 𝓑, G h * fl ψ d W vS vb vU Th (rat x₀) (om (1, h) Φ) ∂vW.μ := by
  first | exact @GlobalTheory.Unf.integral_base_term_coords | exact GlobalTheory.Unf.integral_base_term_coords | (intros; apply GlobalTheory.Unf.integral_base_term_coords <;> assumption)
