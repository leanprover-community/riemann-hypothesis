module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResRdApply
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn

@[expose] public section

namespace GlobalTheory.FlatPair

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem holAlg_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  intro E _ _ _ r X hne
  obtain ⟨y0, hy0⟩ := hne
  haveI : Nontrivial (holAlg X) := ⟨⟨0, 1, fun h => by
    have := congrFun (congrArg Subtype.val h) ⟨y0, hy0⟩
    simp at this⟩⟩
  haveI : NoZeroDivisors (holAlg X) := ⟨fun {a b} hab => by
    by_contra! hcon
    obtain ⟨ha, hb⟩ := hcon
    obtain ⟨F, hF, hFa⟩ := a.2
    obtain ⟨G, hG, hGb⟩ := b.2
    have ha' : ∃ y : X.dom, (a : X.dom → ℂ) y ≠ 0 := by
      by_contra! h
      exact ha (Subtype.ext (funext h))
    obtain ⟨y, hy⟩ := ha'
    have hfg : ∀ w ∈ X.dom, F w * G w = 0 := by
      intro w hw
      have := congrFun (congrArg Subtype.val hab) ⟨w, hw⟩
      rw [← hFa ⟨w, hw⟩, ← hGb ⟨w, hw⟩]
      simpa using this
    have hFy : F y.1 ≠ 0 := by rw [← hFa y]; exact hy
    have key := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hF hG hfg y.2 hFy
    apply hb
    apply Subtype.ext
    funext z
    rw [hGb z]
    simpa using key z.1 z.2⟩
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FlatPair
