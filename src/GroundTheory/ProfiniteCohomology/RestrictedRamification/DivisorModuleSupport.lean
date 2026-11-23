module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModule
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {I : Type} {H : I → Type} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
  (φ : ∀ i, H i →* G) (hφ : ∀ i, Continuous (φ i)) (A : Type) [AddCommGroup A]

theorem finite_divFunEval_ne_zero (n : ℕ) (x : cohomology (divFunRep φ A) n) :
    {i | (cohomologyMapAlong (φ i) (hφ i) (divFunEval φ A i) n).hom x ≠ 0}.Finite := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective (divFunRep φ A) n x
  set c := cochainOf (A := divFunRep φ A) (cocycleι (A := divFunRep φ A) (p := n) z) with hc
  have hfin : (Set.range c).Finite := (isLocallyConstant_cochainOf _).range_finite
  have hT : (⋃ f ∈ Set.range c, {i | ((f : divFun φ A) : I → G → A) i ≠ 0}).Finite :=
    hfin.biUnion fun f _ => (f : divFun φ A).2.1
  refine hT.subset fun i hi => ?_
  by_contra hiT
  apply hi
  have hz : cocyclesMapAlong (φ i) (hφ i) (divFunEval φ A i) n z = 0 := by
    apply cocycleι_injective
    apply cochainOf_injective
    rw [cochainOf_cocycleι_cocyclesMapAlong, map_zero]
    funext h
    rw [divFunEval_hom_apply]
    have hmem : ((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i = 0 := by
      by_contra hne
      exact hiT (Set.mem_biUnion ⟨_, rfl⟩ hne)
    change ((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i 1 = 0
    rw [hmem]
    rfl
  change (cohomologyMapAlong (φ i) (hφ i) (divFunEval φ A i) n) (cohomologyπ (divFunRep φ A) n z) = 0
  rw [cohomologyMapAlong_cohomologyπ, hz, map_zero]

end

end GroundTheory.ProfCoh
