module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ss_sub_ssgt0 {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SS la) : P ∈ X.SSgt la 0 := by
  refine ⟨hP, ?_⟩
  intro ξ hξ ν hν x hx
  by_contra hne
  have hpos : ∀ τ, 0 ≤ ν τ := BoundedSectionAlgebra.sign_of_bdd (X := X) moderateCoefficientPositivity_holds hP.1 hξ ν hx hne
  have hsum : ∑ τ, ν τ = 0 := le_antisymm hν (Finset.sum_nonneg fun τ _ => hpos τ)
  have hz : ν = 0 := by
    funext τ
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => hpos τ)).1 hsum τ (Finset.mem_univ τ)
  subst hz
  exact hne (hP.2 ξ hξ x hx)

theorem interp_of_kron {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {δ : ℕ} (xs : Fin δ → Frame X.Ψ r)
    (h : ∀ j, ∃ F ∈ X.SSgt la 0, ∀ j', F (xs j') = if j' = j then 1 else 0) :
    ∀ v : Fin δ → ℂ, ∃ F ∈ X.SSgt la 0, ∀ j, F (xs j) = v j := by
  intro v
  choose F hF hval using h
  obtain ⟨h0, hadd, hsmul⟩ := (siegelSpaceAlgebra_holds (E := E) r X la la 0).2.2.1
  refine ⟨∑ j, v j • F j, ?_, ?_⟩
  · exact Finset.sum_induction (fun j => v j • F j) (· ∈ X.SSgt la 0)
      (fun a b ha hb => hadd a ha b hb) h0 (fun j _ => hsmul (v j) (F j) (hF j))
  · intro j
    simp [Finset.sum_apply, hval]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
