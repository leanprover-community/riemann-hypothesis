module

public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem preimage_box_shrinking : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [Finite ι] (e : G ≃ₜ+ (ι → A)) (U : ℕ → Set A), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : A) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : A)).smallSets → (∀ k, IsCompact (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ IsOpen (e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ (0 : G) ∈ e ⁻¹' Set.pi Set.univ (fun _ => U k)) ∧ Filter.Tendsto (fun k => e ⁻¹' Set.pi Set.univ (fun _ => U k)) Filter.atTop (nhds (0 : G)).smallSets := by
  intro G A ι _ _ _ _ _ e U hU hlim
  refine ⟨fun k => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact e.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun _ => (hU k).1)
  · exact (isOpen_set_pi Set.finite_univ fun _ _ => (hU k).2.1).preimage e.continuous
  · show e 0 ∈ Set.pi Set.univ (fun _ => U k)
    rw [map_zero]
    exact Set.mem_univ_pi.2 fun _ => (hU k).2.2
  · rw [Filter.tendsto_smallSets_iff] at hlim ⊢
    intro t ht
    have hc : Filter.Tendsto e.symm (nhds 0) (nhds 0) := by
      have h0 : Filter.Tendsto e.symm (nhds 0) (nhds (e.symm 0)) := e.symm.continuous.tendsto 0
      rw [map_zero] at h0
      exact h0
    have h1 : e.symm ⁻¹' t ∈ nhds (0 : ι → A) := hc ht
    rw [nhds_pi, Filter.mem_pi'] at h1
    obtain ⟨I, s, hs, hsub⟩ := h1
    have hW : (⋂ i, s i) ∈ nhds (0 : A) := Filter.iInter_mem.2 hs
    filter_upwards [hlim _ hW] with k hk
    intro x hx
    have h2 : e x ∈ Set.pi (I : Set ι) s := fun i _ =>
      Set.mem_iInter.1 (hk (hx i (Set.mem_univ i))) i
    simpa using hsub h2

end GlobalTheory.CompanionTheory.BigCell
