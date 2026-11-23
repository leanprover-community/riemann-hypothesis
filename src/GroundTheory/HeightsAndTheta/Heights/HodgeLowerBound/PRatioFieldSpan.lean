module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRatioFieldSpan
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace RatioFieldSpan

variable {F M : Type} [Field F] [Field M] [Algebra F M]

theorem div_mem_adjoin {I : Type} (u : I → M) (v : M) {x : M}
    (hx : x ∈ Submodule.span F (Set.range u)) :
    x / v ∈ IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    exact IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_div]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, mul_div_assoc]
    exact mul_mem (IntermediateField.algebraMap_mem _ a) hx

theorem adjoin_le {I J : Type} (u : I → M) (w : J → M) (v v' : M)
    (hw : ∀ j, w j ∈ Submodule.span F (Set.range u)) (hv' : v' ∈ Submodule.span F (Set.range u))
    (hv : v ≠ 0) (hv'0 : v' ≠ 0) :
    IntermediateField.adjoin F (Set.range fun j => w j / v') ≤
      IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  have h1 := div_mem_adjoin (F := F) u v (hw j)
  have h2 := div_mem_adjoin (F := F) u v hv'
  have key : w j / v' = (w j / v) / (v' / v) := by
    field_simp
  show w j / v' ∈ IntermediateField.adjoin F (Set.range fun i => u i / v)
  rw [key]
  exact div_mem h1 h2

theorem full : RatioFieldSpan.Statement := by
  intro F M _ _ _ I J u w v v' hspan hv hv' hv0 hv'0
  apply le_antisymm
  · apply adjoin_le w u v' v
    · intro i
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [← hspan]; exact hv
    · exact hv'0
    · exact hv0
  · apply adjoin_le u w v v'
    · intro j
      rw [hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    · exact hv'
    · exact hv0
    · exact hv'0

end RatioFieldSpan

end GroundTheory.Heights₂.Heights.LowerBoundFree
