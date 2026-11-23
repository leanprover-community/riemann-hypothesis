module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPullbackMemBoundedCuspidalHolomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCoverStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralPullbackUniformisedLevelCoverPlacesStatement
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

set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUp

theorem baseForms_sub_cover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → C.IsPinned a n → baseForms T j σ a n ⊆ C.ratForms a n ∧ ∀ (S : Set (HeightOneSpectrum (𝓞 T.Q.c.F))) (S₂ : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), (∀ la₂ ∈ S₂, ∃ la ∈ S, ∀ x : 𝓞 T.Q.c.F, x ∈ la.asIdeal ↔ la₂.valuation C.d.c₂.F (C.inc x) < 1) → baseInt T j σ a n S ⊆ C.intForms a n S₂ := by
  intro D T hL j hj σ hσ C hU a n hD hP
  constructor
  · intro x hx
    obtain ⟨f, ⟨hf, hh⟩, rfl⟩ := hx
    obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n f hf
    exact ⟨f₂, ⟨hf₂, GlobalTheory.T.coverPullback_mem_boundedCuspidalHolomorphic D T hL j hj σ hσ C hU a n hD f hf hh f₂ hf₂ hpull⟩, hP.2 f hf f₂ hf₂ hpull⟩
  · intro S S₂ hS
    intro x hx
    obtain ⟨f, ⟨hf, hh, hi⟩, rfl⟩ := hx
    obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.T.exists_pullback_section_to_levelCover D T hL j hj σ hσ C hU.1 a n f hf
    exact ⟨f₂, ⟨⟨hf₂, GlobalTheory.T.coverPullback_mem_boundedCuspidalHolomorphic D T hL j hj σ hσ C hU a n hD f hf hh f₂ hf₂ hpull⟩,
      GlobalTheory.T.integral_pullback_uniformisedLevelCover_places D T hL j hj σ hσ C hU a n hD S S₂ hS f hf hi f₂ hf₂ hpull⟩, hP.2 f hf f₂ hf₂ hpull⟩

end GlobalTheory.CoverUp
