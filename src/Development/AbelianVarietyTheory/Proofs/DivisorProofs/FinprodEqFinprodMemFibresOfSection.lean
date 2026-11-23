module

public import Mathlib.Algebra.BigOperators.Finprod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Order.CompletePartialOrder
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finprod_eq_finprod_mem_fibres_of_section :
    ∀ {α γ M : Type} [CommMonoid M] (p : α → γ) (S : Set α) (f : α → M),
      (∀ x, ∃! s, s ∈ S ∧ p s = p x) → (Function.mulSupport f).Finite →
        ∏ᶠ x, f x = ∏ᶠ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x := by
  intro α γ M _ p S f hS hf
  choose g hg using fun x => (hS x).exists
  have key : ∀ s ∈ S, ∀ x, p x = p s ↔ g x = s := by
    intro s hs x
    constructor
    · intro h
      exact (hS x).unique (hg x) ⟨hs, h.symm⟩
    · rintro rfl
      exact (hg x).2.symm
  set T := hf.toFinset with hT
  have hin : ∀ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x = ∏ x ∈ T with g x = s, f x := by
    intro s hs
    apply finprod_mem_eq_prod_of_subset
    · rintro x ⟨hx1, hx2⟩
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hT, Set.Finite.mem_toFinset]
      exact ⟨hx2, (key s hs x).1 hx1⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact (key s hs x).2 hx.2
  rw [finprod_mem_congr rfl hin, finprod_eq_prod_of_mulSupport_subset f (s := T) (by simp [hT])]
  rw [finprod_mem_eq_prod_of_subset (t := T.image g)]
  · exact (Finset.prod_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem g hi) f).symm
  · rintro s ⟨_, hs⟩
    rw [Function.mem_mulSupport] at hs
    obtain ⟨u, hu, _⟩ := Finset.exists_ne_one_of_prod_ne_one hs
    rw [Finset.mem_filter] at hu
    rw [Finset.coe_image]
    exact ⟨u, hu.1, hu.2⟩
  · intro s hs
    rw [Finset.coe_image] at hs
    obtain ⟨u, _, rfl⟩ := hs
    exact (hg u).1

end GlobalTheory
