module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open Polynomial

private theorem charpoly_unit_smul {R : Type} [CommRing R] {n : ℕ} (r : Rˣ)
    (M : Matrix (Fin n) (Fin n) R) :
    ((r : R) • M).charpoly =
      C ((r : R) ^ n) * M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) := by
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  have hmat : Matrix.charmatrix ((r : R) • M) =
      (C (r : R) : R[X]) • (Matrix.charmatrix M).map
        (compRingHom (C ((r⁻¹ : Rˣ) : R) * X)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.charmatrix_apply_eq, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        coe_compRingHom_apply, sub_comp, X_comp, C_comp, mul_sub, ← mul_assoc, hc, one_mul,
        ← C_mul]
    · simp only [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, coe_compRingHom_apply, neg_comp, C_comp, mul_neg, ← C_mul]
  have hdet : M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) =
      ((Matrix.charmatrix M).map (compRingHom (C ((r⁻¹ : Rˣ) : R) * X))).det := by
    rw [Matrix.charpoly, ← coe_compRingHom_apply, RingHom.map_det]
    rfl
  rw [Matrix.charpoly, hmat, Matrix.det_smul, Fintype.card_fin, hdet, C_pow]

private theorem separable_comp_unit {R : Type} [CommRing R] (r : Rˣ) {p : R[X]}
    (hp : p.Separable) : (p.comp (C ((r⁻¹ : Rˣ) : R) * X)).Separable := by
  obtain ⟨a, b, hab⟩ := hp
  set L : R[X] := C ((r⁻¹ : Rˣ) : R) * X with hL
  have hd : derivative (p.comp L) = C ((r⁻¹ : Rˣ) : R) * (derivative p).comp L := by
    rw [derivative_comp, hL, derivative_C_mul, derivative_X, mul_one]
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  refine ⟨a.comp L, b.comp L * C (r : R), ?_⟩
  have h := congrArg (fun q : R[X] => q.comp L) hab
  simp only [add_comp, mul_comp, one_comp] at h
  rw [hd, ← h]
  linear_combination ((b.comp L) * (derivative p).comp L) * hc

theorem UpperTheory.charpoly_separable_unit_smul :
    SepSc := by
  intro R _ n r M h
  rw [charpoly_unit_smul, Polynomial.separable_def, derivative_C_mul]
  exact (isCoprime_mul_unit_left (isUnit_C.2 (r.isUnit.pow n)) _ _).2
    (separable_comp_unit r h)
