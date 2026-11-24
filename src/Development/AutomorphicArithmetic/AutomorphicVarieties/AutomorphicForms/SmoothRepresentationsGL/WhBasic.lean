module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

open GroundTheory.Automorphic.FourierWhittaker in
private theorem exists_uGL {E : Type} [Field E] [NumberField E] {n : ℕ} (ν : GA E n) (hν : IsY 0 ν.val) :
    ∃ X : Pos n → Ad E, ν = uGL X ∧ supN ν.val = supSum 0 X := by
  classical
  refine ⟨fun p => ν.val p.1.1 p.1.2, Units.ext (Matrix.ext fun a b => ?_), ?_⟩
  · rw [coe_uGL, uMat_apply]
    split_ifs with h1 h2
    · subst h1; exact (hν a (Nat.zero_le _)).1
    · rfl
    · exact (hν a (Nat.zero_le _)).2 b (lt_of_le_of_ne (not_lt.1 h2) (Ne.symm h1))
  · unfold supN supSum
    rw [← Finset.sum_product', ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp ⊢
      omega
    · intro p _ q _ h
      exact Subtype.ext h
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hq
      refine ⟨⟨q, by rw [Fin.lt_def]; omega⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro p _
      rfl

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.Smo.whBasic :
    UpperTheory.V.Af.Smo.WhBasic := by
  intro E _ _ n f hf
  refine ⟨?_, ?_, ?_⟩
  · have : whittaker f = partialCoeff f 0 := funext fun g => whittaker_eq_partialCoeff_zero hf.cont g
    rw [this]
    exact continuous_partialCoeff hf.cont 0
  · obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨C, fun g => ?_⟩
    have h := norm_setIntegral_le_of_norm_le_const (μ := vecMeasure E (Pos n)) (s := vecDomain E (Pos n))
      (f := fun X => f (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) (C := C)
      (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) fun X _ => by
        rw [norm_mul, Circle.norm_coe, mul_one]
        exact hC _
    rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one] at h
  · intro ν hν g
    obtain ⟨X, h1, h2⟩ := exists_uGL ν hν
    rw [h2, h1]
    exact GroundTheory.Automorphic.MultiplicityOne.whittaker_uGL_mul hf.cont hf.left X g
