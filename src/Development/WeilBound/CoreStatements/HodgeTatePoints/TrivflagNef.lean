module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsMinorNeZero
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsVanishingIdeal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem trivflag_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : Top.RootModel Ψ N) [CharZero M.Ω] (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o M.Ω] (ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω)), (∀ τ, Num.TrivFlagMod o (p : o) M.y N (fun i => M.xdeg (τ, i))) → ∀ mu : Top.Wt Ψ N, Top.Dominant mu → M.NefAt p mu 0 := by
  intro Ψ _ N M _ p _ o _ _ ho hτ mu hmu
  intro W hW
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have key : ∀ τ : Ψ, 0 ≤ ∑ i : Fin N, mu τ i * (-(geoNum 1 W (fun _ : Fin 1 => M.xdeg (τ, i)) : ℝ)) := by
    intro τ
    obtain ⟨hp, ht⟩ := trivflag_deg M.Ω M.K M.ι M.y p o ho W N (fun i => M.xdeg (τ, i)) h1 h2 h3 h4 (hτ τ)
    apply abel_sum N (mu τ) (fun i => -(geoNum 1 W (fun _ : Fin 1 => M.xdeg (τ, i)) : ℝ))
    · intro a b hab
      exact hmu τ a b hab
    · intro i hi
      have := hp i hi
      simp only [Finset.sum_neg_distrib, neg_nonneg]
      exact_mod_cast this
    · simp only [Finset.sum_neg_distrib, neg_eq_zero]
      exact_mod_cast ht
  unfold Top.RootModel.curveDeg
  rw [Fintype.sum_option]
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, M.x_deg]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_nonneg fun τ _ => ?_
  refine le_of_le_of_eq (key τ) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end PositivityTheory.HtPt.Gf
