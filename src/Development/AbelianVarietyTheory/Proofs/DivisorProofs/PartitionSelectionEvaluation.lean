module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.RowsParts

variable {Bd : BdT} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {eps : ℝ} {Fm : FamP eps} {hc : 𝒜 Fm}

theorem ev_prem {p : Prop} {q : ℝ → BdP Bd} (h : p → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc (q C)) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc fun D O c b => p → q C D O c b := by
  by_cases hp : p
  · obtain ⟨C0, h0, h⟩ := h hp
    refine ⟨C0, h0, fun C hC => ?_⟩
    obtain ⟨x0, h⟩ := h C hC
    exact ⟨x0, fun x hx hle i _ => h x hx hle i⟩
  · exact ⟨0, le_rfl, fun _ _ => ⟨0, fun _ _ _ _ h => absurd h hp⟩⟩

end GlobalTheory.Fc.RowsParts

namespace GlobalTheory.Fc

open RowsParts

end GlobalTheory.Fc
