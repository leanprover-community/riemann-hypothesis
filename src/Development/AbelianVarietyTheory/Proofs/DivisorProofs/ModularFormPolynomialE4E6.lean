module

public import ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open ReciprocityTheory.PGsh in
theorem isMF_eq_sum_monomials :
    ∀ (w : ℕ) (F : ℍ → ℂ), IsMF w F → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ),
      (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
        ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro w F hF
  obtain ⟨g, hg⟩ := hF
  have hm := coe_mem_monoSpanF w g
  rw [monoSpanF, Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨(monoIdx w).image fun a => (a, monoB w a),
    fun p => if h : p.1 ∈ monoIdx w then c ⟨p.1, h⟩ else 0, ?_, fun τ => ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact monoIdx_wt ha
  · rw [Finset.sum_image (fun a _ b _ h => congrArg Prod.fst h), ← hg τ, ← hc,
      Finset.sum_apply, ← Finset.sum_coe_sort (monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coe_monoW a.2]
    simp [a.2]

end GlobalTheory.QFam
