module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SuppFin

theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ (γ.1.val i j)‖ ≤ 1 := by
  have h : (γ.1.val.map (IsCMField.complexConj E).toRingEquiv.toRingHom)ᵀ * 1 * γ.1.val = 1 := γ.2
  have hjj := congrFun (congrFun h j) j
  simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.one_apply_eq] at hjj
  have h2 : ∑ k, ((‖τ (γ.1.val k j)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj

    rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    change _ = τ ((IsCMField.complexConj E) (γ.1.val k j)) * _
    rw [IsCMField.complexEmbedding_complexConj, Complex.conj_mul']
    push_cast; rfl
  have h3 : ∑ k, ‖τ (γ.1.val k j)‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 : ‖τ (γ.1.val i j)‖ ^ 2 ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (f := fun k => ‖τ (γ.1.val k j)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (τ (γ.1.val i j))]

end GlobalTheory.BCT.SuppFin
