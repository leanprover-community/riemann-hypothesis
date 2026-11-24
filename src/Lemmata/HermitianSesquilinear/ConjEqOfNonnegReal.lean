module

public import Formalism.HermitianCurvature.LevelRecursionCondNeeded
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Bl.HermitianSesquilinear

private theorem conj_eq_of_nonneg_real {M : Type} [AddCommGroup M] [Module ℂ M] (Ξ : Formalism.FourierDecayAlt.F7.Sesq M)
    (h : ∀ m : M, 0 ≤ (Ξ m m).re ∧ (Ξ m m).im = 0) (x y : M) :
    starRingEnd ℂ (Ξ x y) = Ξ y x := by
  have h1 := (h (x + y)).2
  have h2 := (h (x + Complex.I • y)).2
  have hx := (h x).2
  have hy := (h y).2
  simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_I, Complex.neg_re,
    Complex.neg_im, RingHom.id_apply] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

theorem goal1 :
  ∀ {M : Type} [inst : AddCommGroup.{0} M] [inst_1 : Module.{0, 0} Complex M] (Ξ : Formalism.FourierDecayAlt.F7.Sesq M),
  (∀ (m : M),
      And (LE.le.{0} 0 (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ m) m).re)
        (Eq.{1} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ m) m).im 0)) →
    ∀ (x y : M),
      LE.le.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ x) y)) 2)
        (HMul.hMul.{0, 0, 0} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ x) x).re
          (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} Ξ y) y).re) := by
  intro M _ _ Ξ h x y
  let c : PreInnerProductSpace.Core ℂ M :=
    { inner := fun a b => Ξ b a
      conj_inner_symm := fun a b => conj_eq_of_nonneg_real Ξ h a b
      re_inner_nonneg := fun a => (h a).1
      add_left := fun a b z => map_add (Ξ z) a b
      smul_left := fun a b r => (map_smulₛₗ (Ξ b) r a).trans (smul_eq_mul _ _) }
  have key := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) (F := M) y x
  change ‖Ξ x y‖ * ‖Ξ y x‖ ≤ (Ξ y y).re * (Ξ x x).re at key
  rw [← conj_eq_of_nonneg_real Ξ h x y, RCLike.norm_conj] at key
  simpa only [sq, mul_comm (Ξ x x).re] using key

end Bl.HermitianSesquilinear
