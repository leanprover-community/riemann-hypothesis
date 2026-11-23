module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittUnfoldedIntegralLeCoreQuotientHeight
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

theorem _root_.GlobalTheory.T.wittUnfoldedIntegral_le_coreQuotientHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : GlobalTheory.Unf.Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤ ENNReal.ofReal (C * quotHeight V₀ g ^ A) := by
  first | exact @GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight | exact GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight | (intros; apply GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight <;> assumption)
