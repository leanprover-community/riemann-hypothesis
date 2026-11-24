module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

def BlockTypes : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (W : Submodule ℂ (Kinf E N → ℂ)), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ω ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θ ∧
  ∀ (r s : ℕ) (h : r + s = N) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
    (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
    HasType (h ▸ K) (h ▸ W) V → Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) →
    (∃ K' ∈ Θ r, ∃ W' ∈ Ω r, HasType K' W' V₁) ∧ (∃ K' ∈ Θ s, ∃ W' ∈ Ω s, HasType K' W' V₂)

def TwBound : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), ∃ C : ℝ,
  ∀ (V : Submodule ℂ (Sm E N)) (m : (E →+* ℂ) → Multiset ℂ), IsDiscrete V → (∀ τ, HasInfCharGL V τ (m τ)) →
    ‖∑ τ, (m τ).sum‖ ≤ C

def NodeEmb : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (V : Submodule ℂ (Sm E (r + s)))
  (V₁ : Submodule ℂ (Sm E r)) (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V →
  Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) →
  Emb V (· ∈ (Tr.node (.leaf V₁ (z₁ - (s : ℂ) / 2)) (.leaf V₂ (z₂ + (r : ℂ) / 2)) : Tr E (r + s)).space)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
