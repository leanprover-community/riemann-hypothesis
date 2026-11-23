module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInUniMOfExactAtMapLinearEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkSuccUnionTranslateOfCoordOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsAutomorphismPreservingTranslatesCoordOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

namespace GlobalTheory

theorem uniM_map_equiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (ψ : M ≃ₗ[R] M)
    {τ : List M} (hτ : τ ∈ uniM R M) : τ.map ψ ∈ uniM R M := by
  exact ((T.subClosed_and_perm_and_linearEquiv_invariant_uniM R M).2.2 ψ τ).mpr hτ

theorem linkExact_low_union_aff_of_ne_nil : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, s ≤ n →
    LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), τ ≠ [] → ∀ p : ℕ,
    p + s + τ.length ≤ n + 2 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  intro R _ s hs n hn hL j hj τ hτ hne p hp
  obtain ⟨v, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hv : [v] ∈ uniM R (ℕ →₀ R) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1 _ hτ [v] (by simp)
  obtain ⟨ψ, hlow, haff, hψv⟩ := T.exists_automorphism_preserving_translates_coord_one R s hs n hn v hv
  refine T.exactAt_linkIn_uniM_of_exactAt_map_linearEquiv R (ℕ →₀ R) ψ (low R (n + 1) ∪ aff R (n + 1) j) ?_ _ p ?_
  · intro x
    simp only [Set.mem_union, hlow, haff]
  · refine T.exactAt_link_succ_union_translate_of_coord_one R s n hL j hj _ (uniM_map_equiv ψ hτ) (ψ v) (by simp) hψv p ?_
    simpa using hp

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exactAt_linkIn_succ_union_translate_of_ne_nil : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ n : ℕ, s ≤ n → LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), τ ≠ [] → ∀ p : ℕ, p + s + τ.length ≤ n + 2 → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  first
  | exact @GlobalTheory.linkExact_low_union_aff_of_ne_nil
  | exact @GlobalTheory.uniM_map_equiv
end
