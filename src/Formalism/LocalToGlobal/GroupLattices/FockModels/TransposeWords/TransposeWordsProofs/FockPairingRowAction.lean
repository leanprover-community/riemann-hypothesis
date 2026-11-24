module

public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.FockPairing

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

section general

variable {σ R : Type*} [CommRing R]

lemma tsact_eq_sum (f g : MvPolynomial σ R) (s : Finset (σ →₀ ℕ)) (h : f.support ⊆ s) :
    fockR f g = ∑ m ∈ s, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) :=
  FockPairing.pair_eq_sum f g s h

lemma tsact_symm (f g : MvPolynomial σ R) : fockR f g = fockR g f :=
  FockPairing.pair_comm f g

lemma tsact_add_left (f f' g : MvPolynomial σ R) :
    fockR (f + f') g = fockR f g + fockR f' g :=
  FockPairing.pair_add_left f f' g

lemma tsact_smul_left (c : R) (f g : MvPolynomial σ R) :
    fockR (c • f) g = c * fockR f g :=
  FockPairing.pair_smul_left c f g

lemma tsact_zero_left (g : MvPolynomial σ R) : fockR (0 : MvPolynomial σ R) g = 0 :=
  FockPairing.pair_zero_left g

lemma tsact_sum_left {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ s, F i) g = ∑ i ∈ s, fockR (F i) g :=
  FockPairing.pair_sum_left s F g

lemma tsact_sum_right {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR g (∑ i ∈ s, F i) = ∑ i ∈ s, fockR g (F i) :=
  FockPairing.pair_sum_right s g F

lemma tsact_smul_right (c : R) (f g : MvPolynomial σ R) :
    fockR f (c • g) = c * fockR f g :=
  FockPairing.pair_smul_right c f g

lemma tsact_monomial_left (m : σ →₀ ℕ) (a : R) (h : MvPolynomial σ R) :
    fockR (monomial m a) h = a * h.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) :=
  FockPairing.pair_monomial_left m a h

lemma tsact_fact_eq (m : σ →₀ ℕ) (s : Finset σ) (h : m.support ⊆ s) :
    ∏ k ∈ m.support, (m k).factorial = ∏ k ∈ s, (m k).factorial :=
  FockPairing.weight_eq_prod m s h

lemma tsact_fact_succ (m : σ →₀ ℕ) (v : σ) :
    ∏ k ∈ (m + Finsupp.single v 1).support, ((m + Finsupp.single v 1 : σ →₀ ℕ) k).factorial
      = (m v + 1) * ∏ k ∈ m.support, (m k).factorial :=
  FockPairing.weight_add_single m v

lemma tsact_X_mul (v : σ) (f h : MvPolynomial σ R) :
    fockR (f * X v) h = fockR f (pderiv v h) :=
  FockPairing.pair_mul_X v f h

end general

section what₂

variable {R : Type*} [CommRing R] {r n : ℕ}

lemma tsact_rowAct_X (G : Matrix (Fin r) (Fin r) R) (v : Fin r × Fin n) :
    rowAct R G (X v) = ∑ b : Fin r, C (G v.1 b) * X (b, v.2) := by
  simp [rowAct]

lemma tsact_coeff_zero (G : Matrix (Fin r) (Fin r) R) (h : MvPolynomial (Fin r × Fin n) R) :
    AddMonoidAlgebra.coeff (rowAct R G h) 0 = AddMonoidAlgebra.coeff h 0 := by
  show MvPolynomial.constantCoeff (rowAct R G h) = MvPolynomial.constantCoeff h
  induction h using MvPolynomial.induction_on
  next a => simp [rowAct]
  next p q hp hq => simp only [map_add (f := _), hp, hq]
  next p v hp => simp [rowAct]

lemma tsact_chain (G : Matrix (Fin r) (Fin r) R) (b : Fin r) (s : Fin n) (h : MvPolynomial (Fin r × Fin n) R) :
    pderiv (b, s) (rowAct R G h) = ∑ a : Fin r, G a b • rowAct R G (pderiv (a, s) h) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    obtain ⟨c, t⟩ := v
    have hL : pderiv (b, s) (∑ d : Fin r, C (G c d) * X (d, t) : MvPolynomial (Fin r × Fin n) R)
        = if t = s then C (G c b) else 0 := by

      rw [map_sum]
      simp only [pderiv_C_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [eq_comm]
      · simp [hts]
    have hR : ∑ a : Fin r, G a b • (rowAct R G p * rowAct R G (pderiv (a, s) (X (c, t))))
        = rowAct R G p * (if t = s then C (G c b) else 0) := by
      simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [apply_ite, Finset.sum_ite_eq, smul_eq_C_mul, mul_comm]
      · simp [hts]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), tsact_rowAct_X, hL, hp]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [hR]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm]

end what₂

theorem fock_pairing_row_action : FockRRowAct := by
  intro R _ r n g P
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro Q
    have h1 : rowAct R g (C a : MvPolynomial (Fin r × Fin n) R) = C a := by simp [rowAct]
    rw [h1, C_apply, tsact_monomial_left, tsact_monomial_left, tsact_coeff_zero]
  | add p q hp hq =>
    intro Q
    rw [map_add (f := _), tsact_add_left, tsact_add_left, hp, hq]
  | mul_X p v hp =>
    intro Q
    rw [map_mul, tsact_rowAct_X, Finset.mul_sum, tsact_sum_left, tsact_X_mul, tsact_chain, tsact_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : rowAct R g p * (C (g v.1 b) * X (b, v.2)) = g v.1 b • (rowAct R g p * X (b, v.2)) := by
      rw [smul_eq_C_mul]; ring
    rw [e, tsact_smul_left, tsact_X_mul, hp, tsact_smul_right, Matrix.transpose_apply]

end Formalism.L2.G.Model.TS
