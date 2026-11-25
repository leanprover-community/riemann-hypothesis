module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Real

@[expose] public section

open scoped Topology

namespace GlobalTheory.CompanionTheory.SW.TailCut

theorem tprod_tail_cut : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι),
    Summable (fun v => |a v - 1|) → S ⊆ S' →
      ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  intro ι _ a S S' hsum hSS'
  have hmul : ∀ T : Set ι, Multipliable (T.mulIndicator a) := by
    intro T
    have hs : Summable fun v => ‖T.mulIndicator a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hsum
      by_cases hv : v ∈ T
      · simp [Set.mulIndicator_of_mem hv, Real.norm_eq_abs]
      · simp [Set.mulIndicator_of_notMem hv]
    have h := multipliable_one_add_of_summable hs
    simpa using h
  have e1 : (∏' v : {v // v ∉ S}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : (∏' v : {v // v ∉ S'}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have hdis : Disjoint (↑(S' \ S) : Set ι) {v | v ∉ S'} :=
    Set.disjoint_left.mpr fun v hv hv' => hv' (Finset.mem_sdiff.mp hv).1
  have hunion : (↑(S' \ S) : Set ι) ∪ {v | v ∉ S'} = {v | v ∉ S} := by
    ext v
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_sdiff, Set.mem_ofPred_eq]
    grind
  rw [e1, e2, ← hunion, Set.mulIndicator_union_of_disjoint hdis,
    Multipliable.tprod_mul (hmul _) (hmul _), ← prod_eq_tprod_mulIndicator]

end GlobalTheory.CompanionTheory.SW.TailCut
