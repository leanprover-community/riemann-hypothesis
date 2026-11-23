module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermFiniteProjection
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermProjectionFunctionForm
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermProjectionStep
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimeGermFiniteProjection.exists_of_step (hStep : PrimeGermProjectionStep.Statement) :
    ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)), P.IsPrime →
      ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
  have key : ∀ (n : ℕ) (σ : Type) [Fintype σ], Fintype.card σ = n → ∀ (w : σ → ℂ) (P : Ideal (holGerms w)),
      P.IsPrime → ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro σ _ hn w P hP
      by_cases h0 : P = ⊥
      · subst h0
        exact isFiniteGermProjection_bot w
      · exact hStep σ w P hP h0 fun τ _ hτ v Q hQ => ih _ (hn ▸ hτ) τ rfl v Q hQ
  intro σ _ w P hP
  exact key _ σ rfl w P hP

theorem PrimeGermFiniteProjection.proof (hStep : PrimeGermProjectionStep.Statement)
    (hFF : GermProjectionFunctionForm.Statement) : PrimeGermFiniteProjection.Statement := by
  intro σ _ w k p hp hP
  obtain ⟨d, A, hA⟩ := PrimeGermFiniteProjection.exists_of_step hStep σ w _ hP
  exact ⟨d, A, hFF σ w k p d A hp hA⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
