module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreDivisor
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreComponent
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemMinimalPrimesOfMemDivSuppDivSupp

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem multAt_pos_of_mem_divSupp_field {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] {V W : Ideal (MRingOver F ι)} {f : MRingOver F ι}
    (hW : W ∈ divSupp V f) : 0 < multAt (V ⊔ Ideal.span {f}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W)))
  rw [multAt, dite_eq_left hWp, inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne

theorem SegreDivisor.proof (h₁ : SegreComponent.Statement.{u, v, w}) :
    SegreDivisor.Statement.{u, v, w} := by
  intro K _ ι _ F _ V n hV
  obtain ⟨i, hi⟩ : ∃ i : ∀ k, ι k, IsChart V i :=
    ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩
  refine ⟨_, isMultiHomog_coordProd (F := F) i (fun _ => 1), coordProd_not_mem hV.1.1 i hi _, ?_⟩
  obtain ⟨W, hW⟩ := h₁ K ι F V n _ hV (isMultiHomog_coordProd (F := F) i (fun _ => 1))
  intro h0
  have hpos := multAt_pos_of_mem_divSupp_field hW
  rw [← DivisorCycleSwap.divCycle_apply_of_mem hW, h0, Finsupp.zero_apply] at hpos
  exact lt_irrefl _ hpos

end GroundTheory.Heights₂.Heights.Targets
