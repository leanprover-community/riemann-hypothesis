module

public import Mathlib.FieldTheory.Separable
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolySmul
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

namespace UpperTheory

theorem charpoly_smul_alt {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) {c : k} (hc : c ≠ 0) :
    (c • M).charpoly =
      C (c ^ Fintype.card ι) * M.charpoly.comp (C c⁻¹ * X) :=
  _root_.UpperTheory.Reformulated.B.Qh50.charpoly_smul_alt M hc

theorem charpoly_smul_separable :
    ∀ (k : Type) [Field k] (n : ℕ) (c : k), c ≠ 0 → ∀ M : Matrix (Fin n) (Fin n) k, M.charpoly.Separable → (c • M).charpoly.Separable := by
  intro k _ n c hc M h
  have hcc : (C c : k[X]) * C c⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hc, C_1]
  rw [charpoly_smul_alt M hc]
  have hcomp : (M.charpoly.comp (C c⁻¹ * X)).Separable := by
    obtain ⟨a, b, hab⟩ := h
    refine ⟨a.comp (C c⁻¹ * X), b.comp (C c⁻¹ * X) * C c, ?_⟩
    have h1 := congrArg (fun p : k[X] => p.comp (C c⁻¹ * X)) hab
    simp only [add_comp, mul_comp, one_comp] at h1
    rw [derivative_comp, ← h1]
    simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, mul_one]
    linear_combination ((b.comp (C c⁻¹ * X)) * (derivative M.charpoly).comp (C c⁻¹ * X)) * hcc
  have hu : IsUnit (C (c ^ Fintype.card (Fin n)) : k[X]) :=
    isUnit_C.2 (pow_ne_zero _ hc).isUnit
  rw [Polynomial.Separable, derivative_mul, derivative_C, zero_mul, zero_add]
  exact (isCoprime_mul_unit_left hu _ _).2 hcomp

end UpperTheory
