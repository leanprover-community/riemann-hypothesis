module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem lamOf_lat (HI : IdealLattice) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ := by
  have hd : D.host.d ≠ 0 := by
    intro h0
    have hs : D.host.sqd = 0 := by
      have h := D.host.sqd_sq
      rw [h0] at h
      simp at h
      exact h
    have hK : D.host.K = ⊥ := by
      show IntermediateField.adjoin ℚ {D.host.sqd} = ⊥
      rw [hs]
      exact IntermediateField.adjoin_simple_eq_bot_iff.mpr (zero_mem _)
    have h1 := (IntermediateField.finrank_eq_one_iff).mpr hK
    have h2 := Formalism.HC.HostRaw.finrank_K (H := D.host.toHostRaw)
    omega
  have hreal : IsEmpty (D.host.K →+* ℝ) := by
    refine ⟨fun f => ?_⟩
    have hs : (⟨D.host.sqd, Formalism.HC.HostRaw.sqd_mem_K (H := D.host.toHostRaw)⟩ : D.host.K) ^ 2 =
        -((D.host.d : ℕ) : D.host.K) := by
      apply Subtype.ext
      simpa using D.host.sqd_sq
    have h2 := congrArg f hs
    rw [map_pow, map_neg, map_natCast] at h2
    have h3 := sq_nonneg (f ⟨D.host.sqd, Formalism.HC.HostRaw.sqd_mem_K (H := D.host.toHostRaw)⟩)
    have h4 : (0 : ℝ) < (D.host.d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    linarith
  obtain ⟨⟨w₁, w₂, hw, heq⟩, -⟩ :=
    HI D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) (Formalism.HC.HostRaw.finrank_K (H := D.host.toHostRaw))
      hreal cc δ hc hδ
  exact ⟨w₁, w₂, hw, heq⟩

theorem delta_ne (HI : IdealLattice) (HD : DiscrNe) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat HI D cc hc 1 one_ne_zero
  intro h0
  have h12 : δ ^ 12 = discr (lamOf D cc 1) := hδ
  rw [h0, hL] at h12
  exact HD w₁ w₂ hw (by simpa using h12.symm)

end Formalism.MainNotions.Ext
