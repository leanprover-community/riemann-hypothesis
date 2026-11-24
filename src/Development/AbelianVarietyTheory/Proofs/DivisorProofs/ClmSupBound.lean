module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
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

open GlobalTheory.SliceSchwartz
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOp

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def padL {κ κ' : Type} (h : κ → V) : κ ⊕ κ' → V := Sum.elim h 0

def qOp {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (s : κ ⊕ κ₁' → V) : ℂ :=
  P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr)

abbrev pd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) :
    SchwartzMap X ℂ →L[ℂ] SchwartzMap X ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap X ℂ) w

theorem pd_apply {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) (f : SchwartzMap X ℂ) (x : X) :
    pd w f x = fderiv ℝ f x w := by
  simp [pd, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem clm_sup_bound {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : SchwartzMap X ℂ →L[ℂ] SchwartzMap Y ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ (s' : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : SchwartzMap X ℂ,
      s.sup (schwartzSeminormFamily ℂ Y ℂ) (T f) ≤ C * s'.sup (schwartzSeminormFamily ℂ X ℂ) f := by
  have hp : Continuous ((s.sup (schwartzSeminormFamily ℂ Y ℂ)).comp T.toLinearMap) :=
    (Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ Y ℂ).continuous_seminorm i).comp
      T.continuous
  obtain ⟨s', C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X ℂ) _ hp
  refine ⟨s', C, C.2, fun f => ?_⟩
  have := hC f
  simpa [Seminorm.smul_apply, NNReal.smul_def] using this

end GlobalTheory.SliceOp
