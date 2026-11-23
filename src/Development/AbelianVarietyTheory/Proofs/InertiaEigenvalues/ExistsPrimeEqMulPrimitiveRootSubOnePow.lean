module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem le_pow_n0_mul (l : ℕ) [hl : Fact l.Prime] (H : ℕ) : H ≤ l ^ (n0 l H) * (l - 1) := by
  unfold n0
  apply Nat.sInf_mem (s := {n | H ≤ l ^ n * (l - 1)})
  have h2 : 2 ≤ l := hl.out.two_le
  refine ⟨H, ?_⟩
  show H ≤ l ^ H * (l - 1)
  calc H ≤ l ^ H := (Nat.lt_pow_self (by omega : 1 < l)).le
    _ ≤ l ^ H * (l - 1) := Nat.le_mul_of_pos_right _ (by omega)

theorem exists_prime_eq_mul_primitiveRoot_sub_one_pow (l : ℕ) [hl : Fact l.Prime] (H : ℕ)
    (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ (1 + n0 l H))) :
    ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hH : (H : ℝ) ≤ (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have h := le_pow_n0_mul l H
    have h1 : 1 ≤ l := hl.out.one_lt.le
    calc (H : ℝ) ≤ ((l ^ n0 l H * (l - 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by push_cast [Nat.cast_sub h1]; ring
  have hDpos : 0 < (l : ℝ) ^ (n0 l H) * ((l : ℝ) - 1) := by
    have : (0 : ℝ) < (l : ℝ) - 1 := by linarith
    positivity
  have hnorm := norm_primitiveRoot_sub_one l (1 + n0 l H) (by omega) ζ hζ
  rw [Nat.add_sub_cancel_left] at hnorm
  have hpos : 0 < ‖ζ - 1‖ := by rw [hnorm]; positivity
  have hne : ζ - 1 ≠ 0 := norm_pos_iff.mp hpos
  refine ⟨(l : PadicComplex l) / (ζ - 1) ^ H, ?_, (div_mul_cancel₀ _ (pow_ne_zero H hne)).symm⟩
  rw [norm_div, norm_pow, norm_natCast_prime_padicComplex, div_le_one (pow_pos hpos H), hnorm,
    ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le hl1.le
  rw [neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, one_mul, div_le_one hDpos]
  exact hH

end GlobalTheory.Cyc.Decomp
