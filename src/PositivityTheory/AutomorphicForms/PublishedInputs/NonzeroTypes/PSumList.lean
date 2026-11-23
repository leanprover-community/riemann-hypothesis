module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.TNZ

namespace P_sumList

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem monomial_sum_iff_alt (x y : WD h) : (WD.lpSum x y).mono0 ↔ x.mono0 ∧ y.mono0 := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N]
      constructor
      · intro hN
        refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
        · have := congrArg Prod.fst (LinearMap.congr_fun hN (v, 0))
          simpa using this
        · have := congrArg Prod.snd (LinearMap.congr_fun hN (0, v))
          simpa using this
      · rintro ⟨ha, hb⟩
        rw [ha, hb, LinearMap.prodMap_zero]

theorem charPol_lpSum (x y : WD h) (σ : Weil h) :
    (WD.lpSum x y).charPol σ = x.charPol σ * y.charPol σ := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.charPol_mk, WD.charPol_mk, WD.charPol_mk, WDRep.sum_ρ,
        LinearMap.charpoly_prodMap]

theorem monomial_zero_alt : (WD.lpZero (h := h)).mono0 := by
  rw [WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff, WDRep.diag_N]

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 := by
  refine Polynomial.eq_one_of_monic_natDegree_zero (WD.charPol_monic _ σ) ?_
  rw [WD.charPol_natDegree, WD.lpZero, WD.lpDim_mk]
  simp

end P_sumList

open P_sumList in
theorem step_sumList : SumOverListProp := by
  intro E Ω _ _ _ _ _ A w h l
  refine ⟨?_, fun σ => ?_⟩
  · induction l with
    | nil => simp [sumList, monomial_zero_alt]
    | cons y l ih =>
      rw [sumList, List.foldr_cons, ← sumList, monomial_sum_iff_alt, ih]
      simp
  · induction l with
    | nil => simp [sumList, charPol_lpZero]
    | cons y l ih =>
      rw [sumList, List.foldr_cons, ← sumList, charPol_lpSum, ih, List.map_cons, List.prod_cons]

end UpperTheory.TNZ
