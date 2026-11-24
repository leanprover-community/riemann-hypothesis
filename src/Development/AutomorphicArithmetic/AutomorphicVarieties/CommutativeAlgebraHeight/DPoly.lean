module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem aeval_X_mul_C_X_monomial {A ι : Type} [CommRing A] (d : ι →₀ ℕ) (c : A) :
    MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) (MvPolynomial.monomial d c) =
      X ^ (Finsupp.degree d) * C (MvPolynomial.monomial d c) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod,
    map_pow, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from rfl]
  ring

private theorem scale_coeff {A ι : Type} [CommRing A] (P : MvPolynomial ι A) (k : ℕ) :
    (MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) P).coeff k =
      MvPolynomial.homogeneousComponent k P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [aeval_X_mul_C_X_monomial, Polynomial.coeff_X_pow_mul',
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl), Polynomial.coeff_C]
    split_ifs <;> first | rfl | omega
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq, map_add (f := _)]

theorem UpperTheory.V.CA.d_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {ι : Type} [Fintype ι] (x : ι → E), (D.poly x).IsHomogeneous n ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (s : ι → S), D.D S (∑ a, s a ⊗ₜ x a) = MvPolynomial.aeval s (D.poly x) := by
  intro n A E _ _ _ D ι _ x
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S),
      D.D S (∑ a, f (MvPolynomial.X a) ⊗ₜ x a) = f (D.poly x) := by
    intro S _ _ f
    rw [Det.poly, ← D.nat]
    congr 1

    simp [Det.gen, map_sum]
  refine ⟨?_, fun S _ _ s => by simpa using key S (MvPolynomial.aeval s)⟩
  let g : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := MvPolynomial.aeval fun a => X * C (MvPolynomial.X a)
  let t : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := IsScalarTower.toAlgHom A (MvPolynomial ι A) (MvPolynomial ι A)[X]
  have h1 := key _ g
  have h3 := key _ t
  have h2 : (∑ a, g (MvPolynomial.X a) ⊗ₜ[A] x a) = (X : (MvPolynomial ι A)[X]) • ∑ a, t (MvPolynomial.X a) ⊗ₜ[A] x a := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [g, t]
  rw [h2, D.homog, h3] at h1
  have hc := congrArg (fun p : (MvPolynomial ι A)[X] => p.coeff n) h1
  simp only [g, t, scale_coeff, IsScalarTower.coe_toAlgHom', Polynomial.coeff_X_pow_mul', le_refl, if_true,
    Nat.sub_self] at hc
  have hP : MvPolynomial.homogeneousComponent n (D.poly x) = D.poly x := by
    rw [← hc]
    simp
  exact hP ▸ MvPolynomial.homogeneousComponent_isHomogeneous n _
