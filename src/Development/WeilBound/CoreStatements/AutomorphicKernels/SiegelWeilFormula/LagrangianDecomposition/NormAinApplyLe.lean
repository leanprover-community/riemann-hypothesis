module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
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
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open scoped ContDiff
open MeasureTheory Set Filter Topology

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {κ' κ'' : Type} [Fintype κ'] [Fintype κ'']

def sc (s : ℝ) : κ' ⊕ κ'' → ℝ := Sum.elim (fun _ => 1) (fun _ => s)

def Ain (s : ℝ) : (κ' ⊕ κ'' → W) →L[ℝ] (κ' ⊕ κ'' → W) :=
  ContinuousLinearMap.pi fun j => sc s j • ContinuousLinearMap.proj j

theorem Ain_apply (s : ℝ) (x : κ' ⊕ κ'' → W) (j : κ' ⊕ κ'') : Ain s x j = sc s j • x j := rfl

theorem norm_Ain_apply_le {s : ℝ} (hs : |s| ≤ 1) (x : κ' ⊕ κ'' → W) : ‖Ain s x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => ?_
  rw [Ain_apply, norm_smul]
  have h1 : ‖sc s j‖ ≤ 1 := by
    cases j with
    | inl _ => simp [sc]
    | inr _ => simpa [sc, Real.norm_eq_abs] using hs
  calc ‖sc s j‖ * ‖x j‖ ≤ 1 * ‖x j‖ := by gcongr
    _ = ‖x j‖ := one_mul _
    _ ≤ ‖x‖ := norm_le_pi_norm x j

theorem norm_Ain_le {s : ℝ} (hs : |s| ≤ 1) : ‖(Ain s : (κ' ⊕ κ'' → W) →L[ℝ] (κ' ⊕ κ'' → W))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  exact (norm_Ain_apply_le hs x).trans (one_mul _).ge

theorem norm_le_max_Ain (s : ℝ) (x : κ' ⊕ κ'' → W) : ‖x‖ ≤ max ‖Ain s x‖ ‖x ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun j => ?_
  cases j with
  | inl i =>
    have h : Ain s x (Sum.inl i) = x (Sum.inl i) := by
      rw [Ain_apply]
      simp [sc]
    rw [← h]
    exact (norm_le_pi_norm (Ain s x) _).trans (le_max_left _ _)
  | inr i =>
    exact (norm_le_pi_norm (x ∘ Sum.inr) i).trans (le_max_right _ _)

theorem contDiff_Ain : ContDiff ℝ ∞ fun p : (κ' ⊕ κ'' → W) × ℝ => Ain p.2 p.1 := by
  refine contDiff_pi.2 fun j => ?_
  simp only [Ain_apply]
  rcases j with j | j
  · simp only [sc, Sum.elim_inl, one_smul]
    exact (contDiff_apply ℝ (fun _ : κ' ⊕ κ'' => W) (Sum.inl j)).comp contDiff_fst
  · simp only [sc, Sum.elim_inr]
    exact contDiff_snd.smul ((contDiff_apply ℝ (fun _ : κ' ⊕ κ'' => W) (Sum.inr j)).comp contDiff_fst)

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
