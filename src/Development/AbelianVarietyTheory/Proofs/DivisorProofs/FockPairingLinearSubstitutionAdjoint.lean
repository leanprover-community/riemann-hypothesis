module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial Matrix Formalism.L2.DIV

namespace GlobalTheory.MinorFrame

variable {σ σ' : Type} [Fintype σ] [Fintype σ']

theorem constantCoeff_rsub (M : Matrix σ' σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (rsub M g) = constantCoeff g := by
  have : (constantCoeff : MvPolynomial σ' ℂ →+* ℂ).comp (rsub M).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [rsub_X]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* ℂ => φ g) this

theorem pderiv_rsub [DecidableEq σ] [DecidableEq σ'] (M : Matrix σ' σ ℂ) (s : σ') (g : MvPolynomial σ ℂ) :
    pderiv s (rsub M g) = ∑ w, C (M s w) * rsub M (pderiv w g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hX : pderiv s (rsub M (X k)) = C (M s k) := by

      rw [rsub_X, map_sum, Finset.sum_eq_single s]
      · simp [pderiv_X]
      · intro b _ hb
        rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne hb]
        simp
      · simp
    rw [map_mul, Derivation.leibniz, hX, hp, smul_eq_mul, smul_eq_mul]
    simp_rw [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self, map_one]; ring
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]
        simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem fockL_rsub_adj (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ) :
    fockL (rsub M F) F' = fockL F (rsub Mᴴ F') := by
  classical
  induction F using MvPolynomial.induction_on generalizing F' with
  | C a => rw [algHom_C, algebraMap_eq, fockL_C_left, fockL_C_left, constantCoeff_rsub]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | mul_X p v hp =>
    have e1 : rsub M (p * X v) = ∑ w, M w v • (X w * rsub M p) := by
      rw [map_mul, rsub_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]; ring

    rw [e1, map_sum, LinearMap.sum_apply]
    simp_rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, fockL_X_pderiv, hp]

    rw [mul_comm p, fockL_X_pderiv, pderiv_rsub, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, map_smul, Matrix.conjTranspose_apply, starRingEnd_apply]

theorem fockS_rsub_adj : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ)
    (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' =
      Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by
  intro σ σ' _ _ M F F'
  exact fockL_rsub_adj M F F'

end GlobalTheory.MinorFrame

end
