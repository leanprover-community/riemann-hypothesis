module

public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory

theorem isCompact_pi_upperHalfPlane_im_bounds :
    ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  intro ι _ L hL hpos
  obtain ⟨C, hC⟩ := hL.isBounded.exists_norm_le
  have hup : ∀ z ∈ L, ∀ i, (z i).im ≤ C := fun z hz i =>
    (Complex.im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hC z hz))
  rcases L.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, 0, one_pos, by simp [hE]⟩
  have hm : ∀ i, ∃ m : ℝ, 0 < m ∧ ∀ z ∈ L, m ≤ (z i).im := by
    intro i
    have hc : Continuous fun z : ι → ℂ => (z i).im :=
      Complex.continuous_im.comp (continuous_apply i)
    obtain ⟨x, hx, hmin⟩ := hL.exists_isMinOn hne hc.continuousOn
    exact ⟨(x i).im, hpos x hx i, fun z hz => hmin hz⟩
  choose m hm0 hmle using hm
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, C, one_pos, fun z _ i => isEmptyElim i⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty m, C, ?_, fun z hz i => ⟨?_, hup z hz i⟩⟩
  · exact (Finset.lt_inf'_iff _).2 fun i _ => hm0 i
  · exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (hmle i z hz)

end GlobalTheory
