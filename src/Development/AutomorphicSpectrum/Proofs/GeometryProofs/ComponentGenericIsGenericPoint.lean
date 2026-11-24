module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.GenPtModel

theorem mem_genericPoints_of_eq {X : Scheme.{0}} {x : X}
    (h : ∀ p : X, p ⤳ x → p = x) : x ∈ genericPoints X := by
  show closure {x} ∈ irreducibleComponents X
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, fun T hT hxT => ?_⟩
  obtain ⟨p, hp⟩ := QuasiSober.sober hT.2 hT.1
  have hpx : p = x := h p ((hp.specializes_iff_mem).2 (hxT (subset_closure (Set.mem_singleton x))))
  intro y hy
  rw [← hpx]
  exact specializes_iff_mem_closure.1 ((hp.specializes_iff_mem).2 hy)

theorem genPt_mem_genericPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∈ genericPoints Y.X := by
  intro E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ
  apply mem_genericPoints_of_eq
  intro p hp
  have hp' : p ∈ Set.range (Y.X.fromSpecStalk (GlobalTheory.CompanionTheory.Ar.genPt ξ₀)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hp
  obtain ⟨q, rfl⟩ := hp'
  have hfield : IsField (Y.X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ₀)) :=
    MulEquiv.isField (Field.toIsField Ω₀)
      (RingEquiv.ofBijective (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo ξ₀)) hξ.bij).toMulEquiv
  have hq : q = IsLocalRing.closedPoint _ := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal q.isPrime.ne_top
    · intro a ha
      by_cases h0 : a = 0
      · rw [h0]
        exact q.asIdeal.zero_mem
      · obtain ⟨b, hb⟩ := hfield.mul_inv_cancel h0
        exact absurd ⟨⟨a, b, hb, by rw [mul_comm]; exact hb⟩, rfl⟩ ((IsLocalRing.mem_maximalIdeal a).1 ha)
  rw [hq, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.CompanionTheory.Ar.GenPtModel
