module

public import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFactAlt
public import Lemmata.GeneralBFactTail.Imports
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lemmata.GeneralBFactLast.Imports
public import Mathlib.RingTheory.OrderOfVanishing.Basic

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

open Module Submodule

theorem addVal_prod {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by
  first | exact Bl.general_b_fact'''''''.goal1 ..

theorem gaugeSplitting_holds : NormLengthStatement := by
  intro O B _ _ _ _ _ _ _ _ g hg
  classical
  have : Module.Free O B := Module.free_iff_isTorsionFree.mpr inferInstance
  set b := Module.Free.chooseBasis O B
  set I : Ideal B := Ideal.span ({g} : Set B)
  have hI : I ≠ ⊥ := by simpa [I] using hg
  have h := Ideal.finrank_eq_finrank b I hI
  have hlen : Module.length O (B ⧸ I) =
      ∑ i, IsDiscreteValuationRing.addVal O (smithNormalFormCoeffs b h i) := by
    rw [(Ideal.quotientEquivPiSpan I b hI).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (Algebra.norm O g) (∏ i, smithNormalFormCoeffs b h i) := by
    rw [Algebra.norm_apply]
    have key := _root_.Bl.general_b_fact_tail.goal1 b (I.restrictScalars O) h
      (b.equiv (Ideal.basisSpanSingleton b hg) (Equiv.refl _))
    convert key using 2
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    have h1 := Basis.equiv_apply (b := b) (b' := Ideal.basisSpanSingleton b hg) (e := Equiv.refl _) i
    refine Eq.trans ?_ (congrArg Subtype.val h1).symm
    rw [Equiv.refl_apply, Ideal.basisSpanSingleton_apply]
    rfl
  rw [hlen, ← addVal_prod, ← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal]
  exact Ring.ord_eq_of_associated hdet

end ReciprocityTheory.MultiplicativeHeights
