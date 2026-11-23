module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

section
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem prodN_mul_apply {p : ℕ} {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} {g : GL (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (hg : InN p g) (r s : n ⊕ Fin c) (hrs : lev p s ≤ lev p r) :
    (h * g.val) r s = h r s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [hg s s le_rfl, Matrix.one_apply_eq, mul_one]
  · intro t _ hts
    by_cases hlt : lev p t < lev p r
    · rw [hh hlt, zero_mul]
    · rw [hg t s (hrs.trans (not_lt.mp hlt)), Matrix.one_apply_ne hts, mul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

theorem prodN_blockTriangular {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) :
    g.val.BlockTriangular (lev p) := by
  intro i j hij
  rw [hg i j hij.le, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

theorem prodN_inN_of_mem {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : InN p g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro r s _; simp
  | mul x y _ _ hx hy =>
    intro r s hrs
    rw [Units.val_mul, prodN_mul_apply (prodN_blockTriangular hx) hy r s hrs]
    exact hx r s hrs
  | inv x _ hx =>
    intro r s hrs
    have : Invertible x.val := ⟨x.inv, x.inv_val, x.val_inv⟩
    have hb : (x⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular (prodN_blockTriangular hx)
    have key := prodN_mul_apply hb hx r s hrs
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, eq_comm] at key

end

end GlobalTheory.RootEx
