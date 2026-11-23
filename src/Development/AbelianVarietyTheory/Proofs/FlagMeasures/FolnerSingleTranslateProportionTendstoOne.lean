module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem folner_single_translate : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r))
    (Om : ℕ → Set (Mt k r)), IsFolner S μ Om → ∀ p ∈ S,
    Filter.Tendsto (fun j => μ {s | s ∈ Om j ∧ lmulM p s ∈ Om j} / μ (Om j)) Filter.atTop (nhds 1) := by
  intro k r S μ Om h p hp
  obtain ⟨_, hC⟩ := h
  obtain ⟨Oc, hOc, hlim⟩ := hC {p} isCompact_singleton (Set.singleton_subset_iff.2 hp)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun j => ?_) (fun j => ?_)
  · refine ENNReal.div_le_div_right (measure_mono fun x hx => ?_) _
    exact ⟨(hOc j).2.1 hx, (hOc j).2.2 p rfl x hx⟩
  · exact (ENNReal.div_le_div_right (measure_mono fun x (hx : x ∈ {s | s ∈ Om j ∧ lmulM p s ∈ Om j}) => hx.1) _).trans ENNReal.div_self_le_one

end GlobalTheory.SgInf
