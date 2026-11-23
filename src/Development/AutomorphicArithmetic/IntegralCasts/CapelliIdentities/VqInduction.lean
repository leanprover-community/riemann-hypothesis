module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
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

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk61.VQ :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → GlobalTheory.UPel.HT.Datum p → Type :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (D : GlobalTheory.UPel.HT.Datum p) ↦ TensorProduct ℤ ℚ D.La

theorem UpperTheory.Reformulated.B.Qk61.vq_induction :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {D : GlobalTheory.UPel.HT.Datum p}
      {P : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D) → Prop},
      P (0 : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D)) →
        (∀ (x y : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D)), P x → P y → P (x + y)) →
          (∀ (a : GlobalTheory.LKTrip.AfP p) (t : ℚ) (x : D.La), P (a ⊗ₜ[ℚ] (t ⊗ₜ[ℤ] x))) →
            ∀ (v : TensorProduct ℚ (GlobalTheory.LKTrip.AfP p) (UpperTheory.Reformulated.B.Qk61.VQ D)), P v := by
  intro p _ D P h0 hadd htmul v
  induction v using TensorProduct.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd x y hx hy
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero]; exact h0
    | tmul t x => exact htmul a t x
    | add x y hx hy => rw [TensorProduct.tmul_add]; exact hadd _ _ hx hy
