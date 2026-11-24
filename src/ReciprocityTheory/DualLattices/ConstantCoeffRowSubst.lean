module

public import ReciprocityTheory.DualLattices.FischerAdjointStatement
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
public import ReciprocityTheory.DualLattices.FischerSmulRight
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

theorem rowSubst_X (g : Matrix (Fin ν) (Fin ν) ℂ) (p : Fin ν × ι) :
    rowSubst g (X p) = ∑ l, C (g l p.1) * X (l, p.2) := by
  simp [rowSubst]

theorem rowSubst_C (g : Matrix (Fin ν) (Fin ν) ℂ) (c : ℂ) :
    rowSubst g (C c : MvPolynomial (Fin ν × ι) ℂ) = C c := by
  simp [rowSubst]

theorem constantCoeff_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    constantCoeff (rowSubst h Q) = constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [rowSubst_C]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp => simp [map_mul, hp, rowSubst_X]

theorem coeff_zero_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    AddMonoidAlgebra.coeff (rowSubst h Q) 0 = AddMonoidAlgebra.coeff Q 0 := by
  exact constantCoeff_rowSubst h Q

theorem pderiv_rowSubst_X (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι) (s : Fin ν × ι) :
    pderiv (k, a) (rowSubst h (X s : MvPolynomial (Fin ν × ι) ℂ)) =
      if s.2 = a then C (h k s.1) else 0 := by

  rw [rowSubst_X, map_sum]
  by_cases hs : s.2 = a
  · simp [pderiv_X, Pi.single_apply, hs]
  · simp [pderiv_X, hs]

theorem pderiv_rowSubst (h : Matrix (Fin ν) (Fin ν) ℂ) (k : Fin ν) (a : ι)
    (Q : MvPolynomial (Fin ν × ι) ℂ) :
    pderiv (k, a) (rowSubst h Q) = ∑ m, C (h k m) * rowSubst h (pderiv (m, a) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e1 : ∀ m, rowSubst h (pderiv (m, a) (X n : MvPolynomial (Fin ν × ι) ℂ)) =
        if n = (m, a) then 1 else 0 := by
      intro m
      rw [pderiv_X, Pi.single_apply]
      split_ifs <;> simp
    have e2 : ∑ m, C (h k m) * (rowSubst h p * (if n = (m, a) then 1 else 0)) =
        rowSubst h p * (if n.2 = a then C (h k n.1) else 0) := by
      by_cases hn : n.2 = a
      · rw [if_pos hn, Finset.sum_eq_single n.1]
        · rw [if_pos (show n = (n.1, a) from Prod.ext rfl hn)]
          ring
        · intro m _ hm
          rw [if_neg (fun h' => hm (congrArg Prod.fst h').symm)]
          ring
        · intro h'
          exact absurd (Finset.mem_univ _) h'
      · rw [if_neg hn, mul_zero]
        refine Finset.sum_eq_zero (fun m _ => ?_)
        rw [if_neg (fun h' => hn (congrArg Prod.snd h'))]
        ring
    rw [map_mul, Derivation.leibniz, hp, pderiv_rowSubst_X, smul_eq_mul, smul_eq_mul, ← e2,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Derivation.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, e1]
    ring

theorem fischer_rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) (P Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (rowSubst g P) Q = fischer P (rowSubst gᴴ Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    rw [rowSubst_C, fischer_C_left, fischer_C_left, coeff_zero_rowSubst]
  | add p q hp hq =>
    rw [map_add (f := _), fischer_add_left, fischer_add_left, hp, hq]
  | mul_X p n hp =>
    rcases n with ⟨k, a⟩
    rw [map_mul, rowSubst_X, Finset.mul_sum, fischer_sum_left, fischer_mul_X, pderiv_rowSubst,
      fischer_sum_right]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_left_comm, MvPolynomial.C_mul', fischer_smul_left, fischer_mul_X, hp, MvPolynomial.C_mul',
      fischer_smul_right]
    simp [Matrix.conjTranspose_apply]

end ReciprocityTheory.PGsh
