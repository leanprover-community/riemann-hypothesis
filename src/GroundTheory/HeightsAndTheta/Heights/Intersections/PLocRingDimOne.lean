module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingDimOne
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingFrac
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingLocal
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingNoeth
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingPow
public import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingDimOne.proof (hF : LocRingFrac.Statement) (hN : LocRingNoeth.Statement)
    (hL : LocRingLocal.Statement) (hPow : LocRingPow.Statement) : LocRingDimOne.Statement := by
  classical
  intro K _ ι _ P s a W hP hs hsP hW
  obtain ⟨hPp, hPh, -⟩ := hP
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨hloc, hunit⟩ := hL K ι P W hPp hWp hPW
  have hNoeth := hN K ι P W hPp hWp hPW hW.2
  refine ⟨hNoeth, hloc, ?_⟩

  choose c hc using hW.2
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) c a
  have htW := AvoidRing.coordProd_not_mem hWp c hc a
  set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k
  have htP : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  set x : FractionRing (MRing ι ⧸ P) := IsLocalization.mk' _ (Ideal.Quotient.mk P s) ⟨_, htP⟩
  have hxA : x ∈ locRing P W := Subring.subset_closure ⟨s, t, a, htP, htW, hs, ht, rfl⟩
  have hx : x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) :=
    IsLocalization.mk'_spec _ _ _
  set x' : locRing P W := ⟨x, hxA⟩
  have hxu : ¬ IsUnit x' := fun h => (hunit x' s t a hs ht htW hx).mp h hsW
  have hx0 : x' ≠ 0 := by
    intro h
    have h0 : x = 0 := congrArg Subtype.val h
    rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hsP hx

  have hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x'}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun Q hQ _ y hy => ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
    obtain ⟨u, v, b, hu, hv, hvW, hyuv⟩ := hF K ι P W hPp hWp hPW y y.2
    have huW : u ∈ W := by
      by_contra h
      exact hy ((hunit y u v b hu hv hvW hyuv).mpr h)
    obtain ⟨n, z, hz, hyn⟩ :=
      hPow K ι P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hyuv
    have hyn' : y ^ n = x' * ⟨z, hz⟩ := Subtype.ext (by simpa using hyn)
    have hyQ : y ^ n ∈ Q := hyn' ▸ Ideal.mul_mem_right _ _ (hQ.2 (Ideal.mem_span_singleton_self x'))
    exact hQ.1.mem_of_pow_mem n hyQ
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : IsLocalRing.maximalIdeal (locRing P W) ≠ ⊥ := fun h =>
    hx0 (by simpa [h] using (IsLocalRing.mem_maximalIdeal x').mpr hxu)
  have h1 : (IsLocalRing.maximalIdeal (locRing P W)).height = 1 :=
    le_antisymm hle (Order.one_le_iff_ne_zero.mpr (fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)))
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h1]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
