module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.UniformExportStatement
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.D

private lemma reflect_cp_inv {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (g : GL (Fin n) R) :
    reflect n (cp g⁻¹) = C ((cp g⁻¹).coeff 0) * cp g := by
  have h1 : reflect n (cp g⁻¹) = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpolyRev := by
    rw [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, cp]
  have h2 := Matrix.charpoly_inv ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) (Units.isUnit _)
  have h3 := Matrix.det_eq_sign_charpoly_coeff ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  rw [← Matrix.coe_units_inv, inv_inv] at h2
  have h4 : IsUnit ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have h5 := Ring.mul_inverse_cancel _ h4
  rw [h1, cp, cp, h2]
  nth_rewrite 1 [h3] at h5
  have h6 := congrArg (C : R → R[X]) h5
  simp only [map_mul, map_pow, map_neg, map_one] at h6
  linear_combination (-((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpolyRev) * h6

private lemma ct_mul {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) : ct c (A * B) = ct c B * ct c A := by
  rw [ct, ct, ct, ← Matrix.transpose_mul, Matrix.map_mul]

private lemma ct_ct {k R : Type} [CommRing k] [CommRing R] [Algebra k R] (c : R ≃ₐ[k] R) (hc : c ^ 2 = 1) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : ct c (ct c A) = A := by
  ext i j
  have := congrArg (fun f : R ≃ₐ[k] R => f (A i j)) hc
  simpa [ct, pow_two] using this

private lemma csr_of_cong {k R : Type} [CommRing k] [CommRing R] [Algebra k R] [Nontrivial R] (c : R ≃ₐ[k] R) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (g : GL (Fin n) R) (hJ : IsUnit J.det) (h : cong c g J = J) :
    IsCsr c n (cp g) := by
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det J).2 hJ
  have h1 : ct c (g : Matrix (Fin n) (Fin n) R) =
      u.val * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (u⁻¹).val := by
    rw [cong] at h
    nth_rewrite 1 [← h]
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  have h2 : (cp g).map (c : R →+* R) = cp g⁻¹ := by
    have h3 := congrArg Matrix.charpoly h1
    rw [Matrix.coe_units_inv u, Matrix.charpoly_units_conj, ct, Matrix.charpoly_transpose] at h3
    rw [cp, cp, ← h3, ← Matrix.charpoly_map]
    rfl
  refine ⟨Matrix.charpoly_monic _, ?_, ?_, ?_⟩
  · rw [cp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · have h4 : IsUnit (g : Matrix (Fin n) (Fin n) R).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    rw [Matrix.det_eq_sign_charpoly_coeff] at h4
    exact isUnit_of_mul_isUnit_right h4
  · have h5 : c ((cp g).coeff 0) = (cp g⁻¹).coeff 0 := by
      rw [← h2, Polynomial.coeff_map]
      rfl
    rw [h2, h5, reflect_cp_inv]

theorem csrOf : CsrOf := by
  intro k R _ _ _ _ c hc n
  refine ⟨fun J g hJ h => csr_of_cong c J g hJ h, fun d => ?_⟩
  refine csr_of_cong c ((d⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) _
    ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)) ?_
  have h1 : (th c d).val = ct c (d⁻¹ : GL (Fin n) R).val := rfl
  have h2 : ct c d.val * (th c d).val = 1 := (th c d).inv_val
  rw [cong, Units.val_mul, ct_mul]
  nth_rewrite 1 [h1]
  rw [ct_ct c hc]
  simp only [mul_assoc, Units.inv_mul_cancel_left, h2, mul_one]

end UpperTheory.ConvolutionTheory.D
