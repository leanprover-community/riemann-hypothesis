module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem stepClass1_of (h : CorankOneIsEquivalenceOnRow) : StepClass1 := by
  intro D X Y u hc νL νB ng
  obtain ⟨hR, hS, hT⟩ := h D X Y u u hc
  have hsub : ∀ t ∈ (Y.tO u u).genSet, t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  intro t ht t' ht'
  rw [genT_ngSet] at ht ht'
  change t ∈ (Y.tO u u).genSet at ht
  change t' ∈ (Y.tO u u).genSet at ht'
  have es : (genT (scT (Y.tO u u))).s0 t t' = 1 ↔ (Y.tO u u).s0 t t' = 1 := by
    simp only [genT, scT, and_true]
    by_cases hc : (Y.tO u u).s0 t t' = 1
    · simp [hc]
    · simp [hc]
  show ((scT (Y.tO u u)).rowOf t = (scT (Y.tO u u)).rowOf t' ∧ (genT (scT (Y.tO u u))).s0 t t' = 1) ↔
    cls1 Y u t = cls1 Y u t'
  rw [es]
  change ((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (Y.tO u u).s0 t t' = 1) ↔ cls1 Y u t = cls1 Y u t'
  constructor
  · rintro ⟨hr, h1⟩
    have b1 := hS t (hsub t ht) t' (hsub t' ht') hr h1
    ext x
    simp only [cls1, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr, hT t' (hsub t' ht') t (hsub t ht) x (hsub x hx) hr.symm hrx.symm b1 hx1⟩
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr.symm, hT t (hsub t ht) t' (hsub t' ht') x (hsub x hx) hr hrx.symm h1 hx1⟩
  · intro hc
    have hm : t' ∈ cls1 Y u t' := ⟨ht', rfl, hR t' (hsub t' ht')⟩
    rw [← hc] at hm
    exact ⟨hm.2.1.symm, hm.2.2⟩

end GlobalTheory.Core.One
