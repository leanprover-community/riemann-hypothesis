module

public import Formalism.DoubleCosetMeasures.StatementZ
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix

namespace Formalism.DoubleCosetMeasures

section Int

variable {F : Type} [Field F]

def intMat (O : Subring F) (n a : ℕ) : Set (Matrix (Fin n) (Fin a) F) := {y | ∀ i j, y i j ∈ O}

theorem isInt_mul' (O : Subring F) {a : ℕ} {x y : Matrix (Fin a) (Fin a) F} (hx : IsInt O x)
    (hy : IsInt O y) : IsInt O (x * y) := fun i j => by
  rw [Matrix.mul_apply]; exact O.sum_mem fun k _ => O.mul_mem (hx i k) (hy k j)

def GLint (O : Subring F) (a : ℕ) : Subgroup (GL (Fin a) F) where
  carrier := {g | IsInt O (g : Matrix (Fin a) (Fin a) F) ∧
    IsInt O ((g⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)}
  one_mem' := by
    constructor <;> intro i j <;> by_cases h : i = j <;> simp [h, O.one_mem, O.zero_mem]
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simpa using isInt_mul' O hx hy, ?_⟩
    simpa [_root_.mul_inv_rev] using isInt_mul' O hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨by simpa using hx', by simpa using hx⟩

def congSub (O : Subring F) (ϖ : F) (a : ℕ) : Subgroup (GL (Fin a) F) where
  carrier := {g | g ∈ GLint O a ∧ IsInt O (ϖ⁻¹ • ((g : Matrix (Fin a) (Fin a) F) - 1))}
  one_mem' := ⟨(GLint O a).one_mem, fun i j => by simp [O.zero_mem]⟩
  mul_mem' := by
    rintro x y ⟨hx, hx1⟩ ⟨hy, hy1⟩
    refine ⟨(GLint O a).mul_mem hx hy, ?_⟩
    have e : ϖ⁻¹ • (((x * y : GL (Fin a) F)) - 1 : Matrix (Fin a) (Fin a) F) =
        (ϖ⁻¹ • ((x : Matrix (Fin a) (Fin a) F) - 1)) * (y : Matrix (Fin a) (Fin a) F) +
          ϖ⁻¹ • ((y : Matrix (Fin a) (Fin a) F) - 1) := by
      simp only [Units.val_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, ← smul_add]
      congr 1; abel
    rw [e]; intro i j
    exact O.add_mem (isInt_mul' O hx1 hy.1 i j) (hy1 i j)
  inv_mem' := by
    rintro x ⟨hx, hx1⟩
    refine ⟨(GLint O a).inv_mem hx, ?_⟩
    have e : ϖ⁻¹ • (((x⁻¹ : GL (Fin a) F)) - 1 : Matrix (Fin a) (Fin a) F) =
        -(((x⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) *
          (ϖ⁻¹ • ((x : Matrix (Fin a) (Fin a) F) - 1))) := by
      rw [Matrix.mul_smul, Matrix.mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.mul_one, ← smul_neg, neg_sub]
    rw [e]; intro i j
    simpa using O.neg_mem (isInt_mul' O hx.2 hx1 i j)

abbrev kF (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) : Type := O ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : O)}

end Int

def IsLocalAt {F : Type} [Field F] (O : Subring F) (ϖ : F) : Prop :=
  ϖ⁻¹ ∉ O ∧ ∀ x ∈ O, (∀ o ∈ O, x ≠ ϖ * o) → x⁻¹ ∈ O

def GLRed : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → IsLocalAt O ϖ →
    Finite (kF O ϖ hϖ) → ∀ a : ℕ,
      Nat.card ((GLint O a) ⧸ (congSub O ϖ a).subgroupOf (GLint O a)) =
        Nat.card (GL (Fin a) (kF O ϖ hϖ))

def VolII : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
    [BorelSpace F] (O : Subring F), IsOpen (O : Set F) → ∀ (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 →
    Finite (kF O ϖ hϖ) → ∀ (n a : ℕ) (ν : Measure (Matrix (Fin n) (Fin a) F))
      [ν.IsAddLeftInvariant],
      ν (IIset O ϖ) * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (n * a) = ν (intMat O n a)

def VolJadd : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
    [BorelSpace F] (O : Subring F), IsOpen (O : Set F) → ∀ (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 →
    IsLocalAt O ϖ → Finite (kF O ϖ hϖ) → ∀ (a : ℕ) (ν : Measure (Matrix (Fin a) (Fin a) F))
      [ν.IsAddLeftInvariant] (J' : Subgroup (GL (Fin a) F)), congSub O ϖ a ≤ J' →
      J' ≤ GLint O a →
      ν (Jset J') * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (a * a) =
        (Nat.card (J' ⧸ (congSub O ϖ a).subgroupOf J') : ENNReal) * ν (intMat O a a)

end Formalism.DoubleCosetMeasures
