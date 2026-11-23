module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace GlobalTheory.CompanionTheory.SecThrough

theorem secEx : SecEx := by
  intro E _ _ _ S₀ hS₀
  let f : Pl E → HeightOneSpectrum (𝓞 (maximalRealSubfield E)) := fun w => w.under (𝓞 (maximalRealSubfield E))
  have hex : ∀ y : Set.range f, ∃ u : Pl E, f u = y.1 ∧ ∀ w ∈ S₀, f w = y.1 → u = w := by
    rintro ⟨_, w₀, rfl⟩
    by_cases h : ∃ w ∈ S₀, f w = f w₀
    · obtain ⟨w, hw, hfw⟩ := h
      exact ⟨w, hfw, fun w' hw' _ => Finset.card_le_one.1 hS₀ w hw w' hw'⟩
    · exact ⟨w₀, rfl, fun w hw hfw => absurd ⟨w, hw, hfw⟩ h⟩
  let g : Set.range f → Pl E := fun y => (hex y).choose
  have hg : ∀ y, f (g y) = y.1 := fun y => (hex y).choose_spec.1
  have hg₀ : ∀ y, ∀ w ∈ S₀, f w = y.1 → g y = w := fun y => (hex y).choose_spec.2
  refine ⟨Set.range g, fun w => ⟨g ⟨f w, w, rfl⟩, ⟨⟨_, rfl⟩, hg _⟩, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨⟨y, rfl⟩, hy⟩
    exact congrArg g (Subtype.ext ((hg y).symm.trans hy))
  · intro w hw
    exact ⟨⟨f w, w, rfl⟩, hg₀ _ w hw rfl⟩
  · intro w hw
    refine ⟨⟨f w, w, rfl⟩, ?_⟩
    by_contra hne
    exact hw ⟨_, hne, hg _⟩

end GlobalTheory.CompanionTheory.SecThrough

end
