module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ActEMemSpanOmega
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitA

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

structure Good (X : PT E) (c : ℝ) (I : Submodule ℤ (Vsp X.dim)) : Prop where
  le : I ≤ X.L
  sat : ∀ x ∈ X.L, x ∈ IR I → x ∈ I
  stable : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I
  iso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0
  sep : ∀ x ∈ X.L, ∀ u, IsU I x u → u ≠ 0 → c < ‖u‖

private lemma act_zero_square_integrability {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : act α (0 : Vsp dim) = 0 := by
  first
  | (ext i; simp [act])

theorem Good.bot (X : PT E) (c : ℝ) : Good X c ⊥ := by
  refine { le := bot_le, sat := ?_, stable := ?_, iso := ?_, sep := ?_ }
  ·
    intro x _ hx
    have : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := by simp [IR]
    rw [this] at hx
    simpa using hx
  ·
    intro α x hx
    rw [Submodule.mem_bot] at hx ⊢
    subst hx
    rw [act_eq_actE, actE_zero_right]
  ·
    intro x hx y _
    rw [Submodule.mem_bot] at hx
    subst hx
    exact Hf_im_zero_left y
  ·
    intro x _ u hu hne
    exfalso
    have : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := by simp [IR]
    have h1 := hu.1
    rw [this, Submodule.mem_bot] at h1
    exact hne h1

private lemma act_add_square_integrability {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  first
  | (ext i; simp [act, mul_add])

private lemma act_real_smul {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (r : ℝ) (v : Vsp dim) :
    act α (r • v) = r • act α v := by
  first
  | (ext i; simp [act, Complex.real_smul]; ring)

theorem Good.IR_stable {X : PT E} {c : ℝ} {I : Submodule ℤ (Vsp X.dim)} (hI : Good X c I)
    (α : 𝓞 E) : ∀ v ∈ IR I, act α v ∈ IR I := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hI.stable α x hx)
  | zero => rw [act_zero_square_integrability]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [act_add_square_integrability]; exact add_mem hx hy
  | smul r x _ hx => rw [act_real_smul]; exact Submodule.smul_mem _ r hx

private lemma Hf_add_left' {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

private lemma Hf_add_right' {ι : Type} [Fintype ι] (v w w' : EuclideanSpace ℂ ι) :
    Hf v (w + w') = Hf v w + Hf v w' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

theorem Good.IR_iso {X : PT E} {c : ℝ} {I : Submodule ℤ (Vsp X.dim)} (hI : Good X c I) :
    ∀ v ∈ IR I, ∀ w ∈ IR I, (Hf v w).im = 0 := by
  intro v hv w hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    induction hw using Submodule.span_induction with
    | mem y hy => exact hI.iso x hx y hy
    | zero => simp [Hf]
    | add y y' _ _ h1 h2 => rw [Hf_add_right', Complex.add_im, h1, h2, add_zero]
    | smul r y _ h => rw [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf_im_smul_right, h, mul_zero]
  | zero => simp [Hf]
  | add x x' _ _ h1 h2 => rw [Hf_add_left', Complex.add_im, h1, h2, add_zero]
  | smul r x _ h => rw [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf_im_smul_left, h, mul_zero]

theorem im_eq_zero_of_lt (X : PT E) {x y : Vsp X.dim} (hx : x ∈ X.L) (hy : y ∈ X.L)
    (h : |(Hf x y).im| < 1) : (Hf x y).im = 0 := by
  obtain ⟨k, hk⟩ := X.integral x y hx hy
  rw [hk] at h ⊢
  have hk1 : |k| < 1 := by exact_mod_cast h
  have hk0 : k = 0 := by
    rw [abs_lt] at hk1
    omega
  simp [hk0]

theorem one_le_abs_im (X : PT E) {x y : Vsp X.dim} (hx : x ∈ X.L) (hy : y ∈ X.L)
    (h : (Hf x y).im ≠ 0) : 1 ≤ |(Hf x y).im| := by
  obtain ⟨k, hk⟩ := X.integral x y hx hy
  rw [hk] at h ⊢
  have hk0 : k ≠ 0 := by exact_mod_cast h
  exact_mod_cast Int.one_le_abs hk0

end

end ReciprocityTheory.ChartRestriction.G.I2
