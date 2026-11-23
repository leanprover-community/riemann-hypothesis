module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameAd
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

theorem UpperTheory.V.Lit.Bor.delCochain :
    UpperTheory.V.Lit.Bor.DelCochain := by
  intro E _ _ _ a n e he M _ _ _ _ κ L h q ω hω k X
  let β : Herm E a →ₗ[ℝ] Herm E a →ₗ[ℝ] M :=
    LinearMap.mk₂ ℝ (fun Y Z => L (toL Y.1) (ω.curryLeft Z fun i => adHerm k (X i)))
      (fun Y Y' Z => LinearMap.congr_fun (map_add L (toL Y.1) (toL Y'.1)) _)
      (fun c Y Z => LinearMap.congr_fun (map_smul L c (toL Y.1)) _)
      (fun Y Z Z' => by rw [map_add (f := _), AlternatingMap.add_apply, map_add (f := _)])
      (fun c Y Z => by
        rw [map_smul, AlternatingMap.smul_apply]
        exact ((L (toL Y.1)).restrictScalars ℝ).map_smul c _)
  have hβ : ∀ Y Z, β Y Z = L (toL Y.1) (ω (Matrix.vecCons Z fun i => adHerm k (X i))) := fun _ _ => rfl
  have key := UpperTheory.V.Lit.Bor.frameAd E a n e he M β k
  simp only [hβ] at key

  rw [del_apply, del_apply, map_sum, ← key]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (Matrix.vecCons (adHerm k (e j)) fun i => adHerm k (X i)) =
      fun i => adHerm k (Matrix.vecCons (e j) X i) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [hc, hω k]
  exact (LinearMap.congr_fun (h k (e j)) _).symm
