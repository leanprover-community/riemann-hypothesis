module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConjAt
public import GroundTheory.AutomorphicForms.MacdonaldFormula
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem rhoPair_dual {n : ℕ} (l : Fin n → ℤ) :
    rhoPair (fun i => -l (Fin.rev i)) = rhoPair l := by
  unfold rhoPair
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  rw [Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ n)]
  push_cast
  ring

private theorem conj_vPoly (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (vPoly n (t : ℂ)) = vPoly n (t : ℂ) := by
  unfold vPoly
  simp [map_prod, map_div₀]


theorem UpperTheory.Gal.Gen.gammaConj_pf :
    UpperTheory.Gal.Gen.RConj → UpperTheory.Gal.Gen.GammaConj := by
  intro hR F _ _ _ _ n _ _ μ _
  show ∀ z, _
  intro z hinj hz g
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have htp : Cartan.diagPow F n l = Iwasawa.torusPow F n l := by
    apply Units.ext
    rw [Cartan.coe_diagPow, Iwasawa.coe_torusPow]
  have hl' : Antitone (fun i : Fin n => -l (Fin.rev i)) := by
    intro i j hij
    show -l (Fin.rev j) ≤ -l (Fin.rev i)
    exact neg_le_neg (hl (Fin.rev_le_rev.mpr hij))
  have hinv : (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      k₂⁻¹ * Iwasawa.torusPow F n (-l) * k₁⁻¹ := by
    rw [Iwasawa.torusPow_neg, ← htp]
    group
  have hcomp : Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i)) =
      Iwasawa.torusPow F n ((-l) ∘ Fin.revPerm) := rfl
  have hZinv : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      zonalSpherical μ z (Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i))) := by
    rw [hinv, zonalSpherical_mul_right z _ (inv_mem hk₁), zonalSpherical_mul_left z (inv_mem hk₂),
      hcomp, zonalSpherical_torusPow_comp]
  have hZ : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) =
      zonalSpherical μ z (Iwasawa.torusPow F n l) := by
    rw [zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, htp]
  rw [hZinv, hZ]
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hcast : (((qF F : ℝ)⁻¹ : ℝ) : ℂ) = ((qF F : ℂ))⁻¹ := by simp
  have m1 := macdonald_formula_hlR (μ := μ) z hl'
  have m2 := macdonald_formula_hlR (μ := μ) z hl
  have hc := hR n ((qF F : ℝ))⁻¹ l z hinj hz
  rw [hcast] at hc
  have hhm : halfModulus F (fun i : Fin n => -l (Fin.rev i)) = halfModulus F l := by
    rw [halfModulus_eq, halfModulus_eq, rhoPair_dual]
  have hhmr : (starRingEnd ℂ) (halfModulus F l) = halfModulus F l := by
    rw [halfModulus_eq, map_zpow₀]
    simp [sqrtQ]
  have hvr : (starRingEnd ℂ) (vPoly n ((qF F : ℂ))⁻¹) = vPoly n ((qF F : ℂ))⁻¹ := by
    rw [← hcast]
    exact conj_vPoly n _
  apply mul_left_cancel₀ hv
  rw [m1, hhm, hc]
  have m2c := congrArg (starRingEnd ℂ) m2
  rw [map_mul, map_mul, hvr, hhmr] at m2c
  rw [m2c]
