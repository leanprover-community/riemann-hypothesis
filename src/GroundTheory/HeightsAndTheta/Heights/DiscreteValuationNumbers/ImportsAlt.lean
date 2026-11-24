module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem EffectiveCase.proof (h₀ : NoCommonComponentCase.Statement.{u}) (h₁ : CommonFactorInduction.Statement.{u}) :
    EffectiveCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ

  suffices H : ∀ n : ℕ, ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
      ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
      (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
      commonExcess ϖ P f g s = n → ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L by
    intro K _ _ ι _ P d hP b f g hD c s hs hsP hH L
    exact H _ K ι P d hP b f g hD c s hs hsP hH rfl L
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ ι _ P d hP b f g hD c s hs hsP hH hn L
    by_cases hcom : ∃ G, (C ϖ : MRing ι O) ∈ G ∧ divCycle P s G ≠ 0 ∧ ratDiv P f g G ≠ 0
    · refine h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hcom ?_ L
      intro K' _ _ ι' _ P' d' hP' b' f' g' hD' c' s' hs' hsP' hH' hlt L'
      exact ih _ (hn ▸ hlt) K' ι' P' d' hP' b' f' g' hD' c' s' hs' hsP' hH' rfl L'
    · refine h₀ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH (fun G hG hsG => ?_) L
      by_contra hDG
      exact hcom ⟨G, hG, hsG, hDG⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
