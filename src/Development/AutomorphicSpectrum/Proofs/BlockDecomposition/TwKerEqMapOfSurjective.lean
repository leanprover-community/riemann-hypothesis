module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
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

open GlobalTheory.PRep

namespace GlobalTheory.CompanionTheory.PRep

theorem twKer_eq_map_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (N : Subgroup G) (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W) (hf : Function.Surjective f)
    (hint : ∀ g v, f (ρ g v) = σ g (f v)) : twKer σ N θ = (twKer ρ N θ).map f := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨n, w', rfl⟩
    obtain ⟨v, rfl⟩ := hf w'
    exact ⟨ρ n v - (θ n : ℂ) • v, ⟨n, v, rfl⟩, by rw [map_sub, map_smul, hint]⟩
  · rintro ⟨_, ⟨n, v, rfl⟩, rfl⟩
    exact ⟨n, f v, by rw [map_sub, map_smul, hint]⟩

theorem twKer_map_closed : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G)
    (θ : N →* ℂˣ) (f : V →ₗ[ℂ] W), Function.Surjective f → (∀ g v, f (ρ g v) = σ g (f v)) →
    twKer σ N θ = (twKer ρ N θ).map f :=
  fun ρ σ N θ f hf hint => GlobalTheory.CompanionTheory.PRep.twKer_eq_map_of_surjective ρ σ N θ f hf hint

end GlobalTheory.CompanionTheory.PRep
