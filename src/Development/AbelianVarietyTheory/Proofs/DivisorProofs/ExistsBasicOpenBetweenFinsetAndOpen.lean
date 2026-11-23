module

public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_basicOpen_between_finset_and_open : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (V : X.Opens), V ≤ W → ∀ s : Finset X, (∀ x ∈ s, x ∈ V) → ∃ f : Γ(X, W), X.basicOpen f ≤ V ∧ ∀ x ∈ s, x ∈ X.basicOpen f := by
  classical
  intro X W hW V hVW s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · refine ⟨0, ?_, fun x hx => absurd hx (Finset.notMem_empty x)⟩
    rw [Scheme.basicOpen_zero]
    exact bot_le
  set Z : Set (PrimeSpectrum Γ(X, W)) := {p | hW.fromSpec p ∉ V} with hZ
  have hZc : IsClosed Z := by
    have h := (hW.fromSpec ⁻¹ᵁ V).isOpen.isClosed_compl
    exact h
  let P : X → Ideal Γ(X, W) := fun x => if h : x ∈ W then (hW.primeIdealOf ⟨x, h⟩).asIdeal else ⊤
  have hPx : ∀ x (h : x ∈ W), P x = (hW.primeIdealOf ⟨x, h⟩).asIdeal := fun x h => by
    simp only [P, dif_pos h]
  have hP : ∀ i ∈ s, i ≠ x₀ → i ≠ x₀ → (P i).IsPrime := by
    intro x hx _ _
    rw [hPx x (hVW (hs x hx))]
    exact (hW.primeIdealOf _).isPrime
  have key : ¬ ((PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) ⊆
      ⋃ i ∈ (↑s : Set X), (P i : Set Γ(X, W))) := by
    rw [Ideal.subset_union_prime x₀ x₀ hP]
    rintro ⟨x, hx, hle⟩
    have hxW : x ∈ W := hVW (hs x hx)
    rw [hPx x hxW] at hle
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈
        PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) :=
      (PrimeSpectrum.mem_zeroLocus _ _).2 hle
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq] at hmem
    apply hmem
    show hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ V
    rw [hW.fromSpec_primeIdealOf]
    exact hs x hx
  obtain ⟨f, hfI, hfP⟩ := Set.not_subset.mp key
  refine ⟨f, ?_, ?_⟩
  · intro y hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    obtain ⟨p, rfl⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    have hp : p ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := hy
    rw [hW.fromSpec_preimage_basicOpen] at hp
    by_contra hnot
    have hpZ : p ∈ Z := hnot
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hp
      ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hfI p hpZ)
  · intro x hx
    have hxW : x ∈ W := hVW (hs x hx)
    have hf : f ∉ (hW.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      intro h
      apply hfP
      rw [Set.mem_iUnion₂]
      exact ⟨x, hx, by rw [hPx x hxW]; exact h⟩
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hW.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).2 hf
    have h2 : hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ X.basicOpen f := hmem
    rwa [hW.fromSpec_primeIdealOf] at h2

end GlobalTheory.Mum
