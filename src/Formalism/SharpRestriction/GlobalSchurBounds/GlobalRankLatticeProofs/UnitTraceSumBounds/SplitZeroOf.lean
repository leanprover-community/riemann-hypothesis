module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.BeConjOfNorm
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhIsotropicOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext

def OkpSplit (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → SplitK D p →
    ∃ α ∈ OKp D lam, ∃ a b : ℤ_[p], α = (zc a, zc b) ∧ IsUnit (a - b)

def OkpNorm (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ∀ α ∈ OKp D lam, ∃ n : ℤ_[p], α.1 * α.2 = zc n

def OkpTwoUnits (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 →
    ∀ α ∈ OKp D lam, ∃ β ∈ OKp D lam, ∃ γ ∈ OKp D lam, ‖β.1‖ = 1 ∧ ‖γ.1‖ = 1 ∧ α = β + γ

theorem beConj_of (H : BeConjOfNorm) (D : D7) (hN : OkpNorm D) (hU : OkpTwoUnits D) (he : endInt D) (ha : addInt D)
    (hn : phNorm D) (hB : beBiadd D) : beConj D := by
  intro p _ cc δ g hAt hp α hα
  have hadd : ∀ β ∈ OKp D g.lam, ∀ γ ∈ OKp D g.lam, β + γ ∈ OKp D g.lam :=
    fun β hβ γ hγ => okp_add D g.lam β γ hβ hγ
  exact H p g (OKp D g.lam) hAt.2.2.2.2 (fun β hβ => okpSwap_holds D p g.lam β hβ) hadd
    (fun β hβ => he p cc δ g hAt β hβ) (ha p cc δ g hAt).1 (fun β hβ => hN p g.lam β hβ)
    (fun β hβ => hU p g.lam hp β hβ) (fun β hβ => hn p cc δ g hAt hp β hβ) (hB p cc δ g hAt).1 α hα

end Formalism.MainNotions.Ext.CutA
