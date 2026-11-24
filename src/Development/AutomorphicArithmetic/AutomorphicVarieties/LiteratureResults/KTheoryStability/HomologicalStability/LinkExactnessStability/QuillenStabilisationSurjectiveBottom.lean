module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HomologyRowExactOfStabilisationPattern
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem stab_surj_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  intro k G _ _ i C d hd hs hex M e s hiso hsq hinj hsur
  have hsurjH : Function.Surjective (hMap (d 0) i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i C d hd hs hex ?_
    intro p q hp hpq
    refine GlobalTheory.T.homology_row_exact_of_stabilisation_pattern k G C d hd M e s (i + 2) hiso hsq p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev (by obtain ⟨r, hr⟩ := hev; omega) hpq
    · intro hodd
      exact hsur (p + 1) q hodd.add_one (by omega) (by omega)
  have h0 : e 1 i ≫ hMap (d 0) i = s 0 i ≫ e 0 i := by
    have hev : Even 0 := ⟨0, rfl⟩
    rw [hsq 0 i (by omega)]
    exact if_pos hev
  haveI := hiso 0 i (by omega)
  haveI := hiso 1 i (by omega)
  have b0 := ConcreteCategory.bijective_of_isIso (e 0 i)
  have b1 := ConcreteCategory.bijective_of_isIso (e 1 i)
  intro y
  obtain ⟨w, hw⟩ := hsurjH (e 0 i y)
  obtain ⟨x, rfl⟩ := b1.2 w
  refine ⟨x, b0.1 ?_⟩
  rw [← hw]
  have h1 := congrArg (fun f : M 1 i ⟶ groupHomology (C 0) i => f.hom x) h0
  simpa using h1.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.quillen_stabilisation_surjective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  first
  | exact @GlobalTheory.HomStab.stab_surj_bottom
end
