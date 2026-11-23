module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsHomologousCycleWithEntriesInOfExactAtLinks
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleBoundedByCone
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

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem exactAt_of_links_cone : ∀ (V : Type) (F : Set (List V)) (S : Set V) (y : V), SubClosed F →
    (∀ l ∈ linkIn F S [], y :: l ∈ F) → ∀ (p : ℕ),
    (∀ τ ∈ F, ∀ x, τ.getLast? = some x → x ∉ S → τ.length ≤ p →
      ExactAt (linkIn F S τ) (p - τ.length)) → ExactAt F p := by
  intro V F S y hF hy p hlink c hc hbd
  obtain ⟨b, hb, hc', hbd'⟩ := GlobalTheory.T.exists_homologous_cycle_with_entries_in_of_exactAt_links V F S hF p hlink c hc hbd
  obtain ⟨b', hb', hbb'⟩ := GlobalTheory.T.seqChain_cycle_bounded_by_cone V F (linkIn F S []) y hy p (c - bd V b) hc' hbd'
  refine ⟨b + b', Submodule.add_mem _ hb hb', ?_⟩
  rw [map_add (f := _), hbb']
  abel

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
end
