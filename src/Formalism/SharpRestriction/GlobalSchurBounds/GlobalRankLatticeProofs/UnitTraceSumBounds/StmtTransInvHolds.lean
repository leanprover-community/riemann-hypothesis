module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLatticeHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhEvenOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetLat
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TransInvOf
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

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem lamOf_lat_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ :=
  lamOf_lat idealLattice_holds D cc hc δ hδ

theorem delta_ne_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  delta_ne' idealLattice_holds D cc hc δ hδ

theorem sgStar_spec (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Differentiable ℂ (sgStar (lamOf D cc δ)) ∧ deriv (sgStar (lamOf D cc δ)) 0 = 1 ∧
      (∀ z, sgStar (lamOf D cc δ) (-z) = -sgStar (lamOf D cc δ) z) := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat_holds D cc hc δ (delta_ne_holds D cc hc δ hδ)
  have h := sigmaStarEx_holds w₁ w₂ hw
  rw [hL]
  unfold sgStar
  have hs := Classical.epsilon_spec h
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem area_lamOf (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt |(NumberField.discr D.host.K : ℝ)| / 2 := by
  have h := idealLattice_holds D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
    (Formalism.MainNotions.Ext.finrank_K D.host) (Formalism.MainNotions.Ext.no_real_K D.host) cc δ hc hδ
  exact h.2

end Formalism.MainNotions.Ext
