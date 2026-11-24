module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqComplexExactAtOfAllLinksExactAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem low_union_aff_subset_low_succ (R : Type) [CommRing R] (n : ℕ) :
    low R n ∪ aff R n n ⊆ low R (n + 1) := by
  intro x hx
  rcases hx with hx | hx
  · intro i hi
    exact hx i (by omega)
  · intro i hi
    have := hx i (by omega)
    simpa [Finsupp.single_apply, show n ≠ i by omega] using this

theorem linkExactLow_succ_of_linkExactAff : ∀ (R : Type) [CommRing R] (s n : ℕ),
    LinkExactAff R s n → LinkExactLow R s (n + 1) := by
  intro R _ s n h τ hτ p hp
  have hsub : SubClosed (uniM R (ℕ →₀ R)) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1
  apply exactAt_of_links (ℕ →₀ R) _ (low R n ∪ aff R n n)
  · intro l hl l' hl'
    refine ⟨fun x hx => hl.1 x (hl'.subset hx), hsub _ hl.2 _ ?_⟩
    simpa using hl'
  · intro τ1 hτ1 hlen
    have heq : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1)) τ) (low R n ∪ aff R n n) τ1 =
        linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n n) (τ ++ τ1) := by
      ext w
      constructor
      · rintro ⟨hw, -, h2⟩
        refine ⟨hw, ?_⟩
        rw [List.append_assoc]
        exact h2
      · rintro ⟨hw, h2⟩
        refine ⟨hw, fun x hx => ?_, ?_⟩
        · rcases List.mem_append.mp hx with hx | hx
          · exact hτ1.1 x hx
          · exact low_union_aff_subset_low_succ R n (hw x hx)
        · rw [← List.append_assoc]
          exact h2
    rw [heq]
    exact h n le_rfl (τ ++ τ1) hτ1.2 (p - τ1.length) (by rw [List.length_append]; omega)

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.linkExactLow_add_one_of_linkExactAff : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactAff R s n → LinkExactLow R s (n + 1) := by
  first
  | exact @GlobalTheory.linkExactLow_succ_of_linkExactAff
  | exact @GlobalTheory.low_union_aff_subset_low_succ
end
