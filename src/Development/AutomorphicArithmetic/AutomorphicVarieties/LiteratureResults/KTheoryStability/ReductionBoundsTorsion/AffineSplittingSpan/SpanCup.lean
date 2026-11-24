module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanPrism
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

section General

variable {Y : Type}

theorem dc_dc : ∀ (m : ℕ) (F : (Fin (m + 1) → Y) → ℝ), dc (dc F) = 0 := by
  intro m
  induction m with
  | zero =>
    intro F
    funext y
    simp [dc, Fin.sum_univ_succ]
    have hCD : (fun j : Fin 1 => y (Fin.succAbove 1 (Fin.succAbove 1 j))) =
        fun j => y (Fin.succAbove 2 (Fin.succAbove 1 j)) := by
      funext j
      rw [Subsingleton.elim j (0 : Fin 1)]
      rfl
    linear_combination congrArg F hCD
  | succ m ih =>
    intro F
    funext y
    rw [← Fin.cons_self_tail y, dc_cons]
    have e : (fun w' => dc F (Fin.cons (y 0) w')) = F - dc (fun w' => F (Fin.cons (y 0) w')) := by
      funext w'; rw [dc_cons]; rfl
    rw [e, dc_sub, ih]
    simp

theorem dc_neg {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : dc (-F) = -dc F := by
  funext y; simp [dc, Finset.sum_neg_distrib]

theorem prism_zero (φ : Y → Y) : ∀ {n : ℕ}, prism φ (0 : (Fin (n + 1) → Y) → ℝ) = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext y
    rw [prism_succ]
    change 0 - prism φ (0 : (Fin (n + 1) → Y) → ℝ) (Fin.tail y) = 0
    simp only [ih, Pi.zero_apply, sub_zero]

end General

section Grp

variable {P : Type} [Group P]

theorem dc_inv (S : Set P) {m : ℕ} (F : (Fin (m + 1) → P) → ℝ) (hF : InvS S F) : InvS S (dc F) := by
  intro g hg y
  simp only [dc]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg _ (hF g hg _)

def tcup (l : Additive P →+ ℝ) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) : (Fin (n + 2) → P) → ℝ :=
  fun y => l (Additive.ofMul ((y 0)⁻¹ * y 1)) * e (Fin.tail y)

theorem tail_eq' {α : Type} {k : ℕ} (q : Fin (k + 1) → α) : Fin.tail q = fun i => q i.succ := rfl

theorem dc_tcup (l : Additive P →+ ℝ) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) :
    dc (tcup l e) = -tcup l (dc e) := by
  funext y
  simp [dc, tcup, Fin.sum_univ_succ, tail_eq']
  simp only [pow_succ, mul_add, Finset.mul_sum, neg_add, ← Finset.sum_neg_distrib]
  ring_nf

theorem tcup_inv (l : Additive P →+ ℝ) (S : Set P) {n : ℕ} (e : (Fin (n + 1) → P) → ℝ) (he : InvS S e) :
    InvS S (tcup l e) := by
  intro g hg y
  simp only [tcup]
  rw [show (g * y 0)⁻¹ * (g * y 1) = (y 0)⁻¹ * y 1 by group]
  congr 1
  exact he g hg (Fin.tail y)

theorem tcup_add (l : Additive P →+ ℝ) {n : ℕ} (e f : (Fin (n + 1) → P) → ℝ) :
    tcup l (e + f) = tcup l e + tcup l f := by
  funext y; simp [tcup, mul_add]

theorem tcup_sum (l : Additive P →+ ℝ) {n k : ℕ} (a : Fin k → ℝ) (F : Fin k → (Fin (n + 1) → P) → ℝ) :
    tcup l (∑ i, a i • F i) = ∑ i, a i • tcup l (F i) := by
  funext y
  simp only [tcup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem tcup_cupH (l : Additive P →+ ℝ) {q : ℕ} (β : Fin q → (Additive P →+ ℝ)) :
    tcup l (cupH β) = cupH (Fin.cons l β) := by
  funext y
  simp [tcup, cupH, Fin.prod_univ_succ, Fin.tail]

end Grp

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
