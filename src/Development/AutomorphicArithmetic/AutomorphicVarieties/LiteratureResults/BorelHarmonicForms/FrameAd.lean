module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.frameAd :
    UpperTheory.V.Lit.Bor.FrameAd := by
  intro E _ _ _ a n e he N _ _ β k
  have hk1 : k.1 * star k.1 = 1 := k.2.2
  have hc : ∀ i j, trF (e i).1 (adHerm k (e j)).1 = trF (e j).1 (star k.1 * (e i).1 * k.1) := fun i j => by
    have h : ((e i).1 * (k.1 * (e j).1 * star k.1)).trace = ((e j).1 * (star k.1 * (e i).1 * k.1)).trace := by
      rw [show (e i).1 * (k.1 * (e j).1 * star k.1) = ((e i).1 * k.1) * ((e j).1 * star k.1) by simp only [mul_assoc],
        Matrix.trace_mul_comm]
      simp only [mul_assoc]
    simp only [trF, adHerm, h]
  have hs : ∀ i, ∑ j, trF (e i).1 (adHerm k (e j)).1 • adHerm k (e j) = e i := fun i => by
    have h := congrArg Subtype.val (he ⟨star k.1 * (e i).1 * k.1, IsSelfAdjoint.conjugate' (e i).2 k.1⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    refine Subtype.ext ?_
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hc]
    calc ∑ j, trF (e j).1 (star k.1 * (e i).1 * k.1) • (adHerm k (e j)).1
        = k.1 * (∑ j, trF (e j).1 (star k.1 * (e i).1 * k.1) • (e j).1) * star k.1 := by
          simp only [adHerm, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      _ = k.1 * (star k.1 * (e i).1 * k.1) * star k.1 := by rw [← h]
      _ = (k.1 * star k.1) * (e i).1 * (k.1 * star k.1) := by simp only [mul_assoc]
      _ = (e i).1 := by rw [hk1, one_mul, mul_one]
  calc ∑ j, β (adHerm k (e j)) (adHerm k (e j))
      = ∑ j, β (∑ i, trF (e i).1 (adHerm k (e j)).1 • e i) (adHerm k (e j)) :=
        Finset.sum_congr rfl fun j _ => by rw [← he (adHerm k (e j))]
    _ = ∑ j, ∑ i, trF (e i).1 (adHerm k (e j)).1 • β (e i) (adHerm k (e j)) := by

        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ i, β (e i) (∑ j, trF (e i).1 (adHerm k (e j)).1 • adHerm k (e j)) := by
        rw [Finset.sum_comm]

        simp only [map_sum, map_smul]
    _ = ∑ j, β (e j) (e j) := by simp only [hs]
