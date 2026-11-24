module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BddCpt

theorem bdd_entries_of_isCompact_closure_zpowers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t : UL n w),
    IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) →
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (t ^ k).1.1 i j ∈ Ov E w := by
  intro E _ _ _ n w t hK
  have hO : IsOpen ((Ov E w : Set (w.adicCompletion E))) := Valued.isOpen_valuationSubring _
  have hNe : (nhdsWithin (0 : w.adicCompletion E) {0}ᶜ).NeBot := by
    letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
    exact NormedField.nhdsNE_neBot 0
  have hev : ∀ᶠ a in nhds (0 : w.adicCompletion E),
      ∀ s ∈ closure (Subgroup.zpowers t : Set (UL n w)), ∀ i j, a * s.1.1 i j ∈ Ov E w := by
    refine hK.eventually_forall_of_forall_eventually fun s _ => ?_
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hc : Continuous (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) := by fun_prop
    have h0 : (fun z : w.adicCompletion E × UL n w => z.1 * z.2.1.1 i j) (0, s) ∈ (Ov E w : Set _) := by
      simp only [zero_mul]; exact (Ov E w).zero_mem
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
  obtain ⟨a, ha, ha0⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set (w.adicCompletion E))))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (w.adicCompletion E))))).exists
  exact ⟨a, ha0, fun k i j => ha _ (subset_closure ⟨k, rfl⟩) i j⟩

end GlobalTheory.BddCpt
