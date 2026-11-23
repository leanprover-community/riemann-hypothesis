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
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Sheaf.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open scoped ContDiff Manifold Topology

namespace UpperTheory.V.Cj.A

theorem partBase : PartBase := by
  intro V _ _ _ Y hY D hD hDp
  let Y' : TopologicalSpace.Opens V := ⟨Y, hY⟩
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : LocallyCompactSpace Y' := Y'.isOpen.locallyCompactSpace
  haveI : SecondCountableTopology V := inferInstance
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, V) (M := Y') isClosed_univ
    (fun j => ((↑) : Y' → V) ⁻¹' D j) (fun j => (hD j).preimage continuous_subtype_val)
    (fun x _ => Set.mem_iUnion.2 ⟨(x : V), hDp x x.2⟩)
  classical
  refine ⟨fun j p => if h : p ∈ Y then f j ⟨p, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    let g : V → ℝ := fun p => if h : p ∈ Y then f j ⟨p, h⟩ else 0
    have h1 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ (fun y : Y' => g (y : V)) ⟨x, hx⟩ := by
      have e : (fun y : Y' => g (y : V)) = f j := by
        funext y
        exact dif_pos y.2
      rw [e]
      exact (f j).contMDiff.contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ) ∞ g x :=
      (contMDiffAt_subtype_iff (U := Y') (f := g) (x := ⟨x, hx⟩)).1 h1
    exact (contMDiffAt_iff_contDiffAt.1 h2).contDiffWithinAt
  · intro p hp
    obtain ⟨t, ht, htf⟩ := f.locallyFinite ⟨p, hp⟩
    obtain ⟨N, hN, hNt⟩ := (mem_nhds_subtype _ _ _).1 ht
    refine ⟨N, hN, htf.subset ?_⟩
    rintro j ⟨x, hxN, hne⟩
    by_cases hxY : x ∈ Y
    · have h : f j ⟨x, hxY⟩ ≠ 0 := by simpa [hxY] using hne
      exact ⟨⟨x, hxY⟩, h, hNt hxN⟩
    · exact (hne (dif_neg hxY)).elim
  · intro p hp
    refine Eq.trans ?_ (f.sum_eq_one (x := ⟨p, hp⟩) (Set.mem_univ _))
    exact finsum_congr fun j => dif_pos hp
  · intro j p hne
    by_cases hpY : p ∈ Y
    · have h : f j ⟨p, hpY⟩ ≠ 0 := by simpa [hpY] using hne
      exact hf j (subset_tsupport _ h)
    · exact (hne (dif_neg hpY)).elim

end UpperTheory.V.Cj.A
