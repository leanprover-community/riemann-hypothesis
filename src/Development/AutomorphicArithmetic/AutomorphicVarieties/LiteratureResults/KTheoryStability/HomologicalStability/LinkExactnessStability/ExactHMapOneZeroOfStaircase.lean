module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSyzygyFactorization
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SurjectiveHMapZeroOfStaircase
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
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence
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

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.StairMid

variable {k G : Type} [CommRing k] [Group G]

def shC (C : ℕ → Rep k G) (Z : Rep k G) : ℕ → Rep k G
  | 0 => Z
  | n + 1 => C (n + 2)

def shD (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p) (Z : Rep k G) (b : C 2 ⟶ Z) :
    ∀ p, shC C Z (p + 1) ⟶ shC C Z p
  | 0 => b
  | p + 1 => d (p + 2)

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hs hex hH
  obtain ⟨Z, ι, hι, b, hse, hbι, hbs, hdb, hexb⟩ := GlobalTheory.T.exists_syzygy_factorization k G C d hd hs (hex 0 (by omega))
  have hfun : ∀ {A B : Rep k G} (f : A ⟶ B), hMap f i = (groupHomology.functor k G i).map f := fun f => rfl
  have hsurj : Function.Surjective (hMap b i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i (shC C Z) (shD C d Z b) ?_ hbs ?_ ?_
    · intro p
      cases p with
      | zero => exact hdb
      | succ p => exact hd (p + 2)
    · intro p hp
      cases p with
      | zero => exact hexb (hex 1 (by omega))
      | succ p => exact hex (p + 2) (by omega)
    · intro p q hp hpq
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      exact hH (r + 2) q (by omega) (by omega)
  have hles := (ShortComplex.moduleCat_exact_iff _).1 (groupHomology.mapShortComplex₂_exact hse i)
  have hcomp : hMap (d 1) i = hMap b i ≫ hMap ι i := by
    rw [hfun, hfun, hfun, ← hbι]
    exact (groupHomology.functor k G i).map_comp b ι
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hles x hx
    obtain ⟨z, rfl⟩ := hsurj y
    refine ⟨z, ?_⟩
    rw [hcomp]
    exact hy
  · rintro ⟨z, rfl⟩
    have h0 : hMap (d 1) i ≫ hMap (d 0) i = 0 := by
      have e := (groupHomology.functor k G i).map_comp (d 1) (d 0)
      rw [hd 0, Functor.map_zero] at e
      rw [hfun, hfun]
      exact e.symm
    rw [← ModuleCat.comp_apply, h0]
    rfl

end GlobalTheory.HomStab.StairMid

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exact_hMap_one_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.StairMid.main
end
