module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.orbClosed :
    OrbClosed := by
  intro Γ V S _ _ _ _ d G hG K hKY hK s s'
  unfold UpperTheory.V.Lit.Dr.Geo.Proper at hG
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hpY, hpA⟩
  obtain ⟨L, hLn, hLY, hL⟩ := local_compact_nhds (G.isOpen.mem_nhds hpY)
  have hFfin : {γ | (G.σ γ) s = s' ∧ ∃ q ∈ L ∪ K, (G.ρ γ) q ∈ L ∪ K}.Finite :=
    hG (L ∪ K) (Set.union_subset hLY hKY) (hL.union hK) s s'
  set F := {γ | (G.σ γ) s = s' ∧ ∃ q ∈ L ∪ K, (G.ρ γ) q ∈ L ∪ K} with hF
  have hBc : IsClosed (⋃ γ ∈ F, (G.ρ γ) ⁻¹' K) :=
    hFfin.isClosed_biUnion fun γ _ => hK.isClosed.preimage (G.ρ γ).continuous
  have hpB : p ∉ ⋃ γ ∈ F, (G.ρ γ) ⁻¹' K := by
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists]
    intro γ hγF hγ
    exact hpA ⟨γ, hγF.1, hγ⟩
  have hnb : (⋃ γ ∈ F, (G.ρ γ) ⁻¹' K)ᶜ ∈ nhds p := hBc.isOpen_compl.mem_nhds hpB
  filter_upwards [hLn, hnb] with q hqL hqB
  refine ⟨hLY hqL, ?_⟩
  rintro ⟨γ, hσ, hγ⟩
  apply hqB
  simp only [Set.mem_iUnion, Set.mem_preimage]
  exact ⟨γ, ⟨hσ, q, Or.inl hqL, Or.inr hγ⟩, hγ⟩
