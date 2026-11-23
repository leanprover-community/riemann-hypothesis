module

public import GroundTheory.AutomorphicForms.GL2Classical.IsWeightLevelAdelicLift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.NumberTheory.ModularForms.SlashActions

@[expose] public section

open NumberField Matrix CongruenceSubgroup UpperHalfPlane ModularForm Filter Topology
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem norm_archLift (f : ℍ → ℂ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    ‖archLift k f h‖ = Real.sqrt (h • I).im ^ k * ‖f (h • I)‖ := by
  have hj : denom h (I : ℂ) ≠ 0 := denom_ne_zero h I
  rw [archLift, norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), im_smul_I hpos, sqrt_div_normSq, div_zpow, _root_.zpow_neg,
    div_eq_mul_inv]
  ring

theorem sqrt_zpow_eq_rpow {y : ℝ} (hy : 0 < y) (k : ℤ) : Real.sqrt y ^ k = y ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hy.le]
  congr 1
  ring

end GL2Classical

end

end GroundTheory.Automorphic
