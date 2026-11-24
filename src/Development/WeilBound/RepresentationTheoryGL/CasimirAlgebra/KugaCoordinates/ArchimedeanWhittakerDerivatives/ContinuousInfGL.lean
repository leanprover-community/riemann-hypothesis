module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

namespace PositivityTheory.Rg.Cz

open NumberField Matrix GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def cu (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0) (t : ℝ) : GL (Fin a) (Cinf E) :=
  ⟨1 + t • M, 1 - t • M, by
    rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_comm, hM, smul_zero, sub_zero]; abel,
   by rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hM, smul_zero, add_zero]; abel⟩

theorem cu_val (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0) (t : ℝ) : (cu M hM t).val = 1 + t • M := rfl

theorem cu_add (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0) (s t : ℝ) :
    cu M hM (s + t) = cu M hM s * cu M hM t := by
  apply Units.ext
  simp only [Units.val_mul, cu_val, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hM, smul_zero, add_zero,
    add_smul]
  abel

theorem cu_zero (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0) : cu M hM 0 = 1 := by
  apply Units.ext
  simp [cu_val]

theorem hasDerivAt_cu (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0) (t : ℝ) :
    HasDerivAt (fun s => toL (cu M hM s).val) (toL M) t := by
  have h := ((hasDerivAt_id t).smul_const (toL M)).const_add (toL (1 : Matrix (Fin a) (Fin a) (Cinf E)))
  simp only [one_smul] at h
  exact h

variable (E a) in
theorem continuous_infGL' : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) := ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sInf E))) (continuous_const.add (continuous_id.matrix_map hs))

theorem continuous_cu (M : Matrix (Fin a) (Fin a) (Cinf E)) (hM : M * M = 0) : Continuous (cu M hM) :=
  Units.continuous_iff.2 ⟨continuous_const.add (continuous_id.smul continuous_const),
    continuous_const.sub (continuous_id.smul continuous_const)⟩

theorem infGL_apply (y : GL (Fin a) (Cinf E)) (i j : Fin a) :
    (infGL E a y).val i j = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E (y.val i j) := rfl


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
def sd (M : Matrix (Fin a) (Fin a) (Cinf E)) : Cinf E := ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, M p.1 p.2

end PositivityTheory.Rg.Cz
