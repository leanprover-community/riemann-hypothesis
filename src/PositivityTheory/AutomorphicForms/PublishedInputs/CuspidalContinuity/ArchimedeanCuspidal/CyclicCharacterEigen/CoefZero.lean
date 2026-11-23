module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

namespace Ad3P.EigenformCoefficientExpansion

theorem exp_of {k N : ℕ} [NeZero N] (f : CuspForm (Gamma1 N) (k : ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ => coef f n * Complex.exp (2 * Real.pi * Complex.I * n * τ)) (f τ) := by
  have hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hp)
    f.holo' (ModularFormClass.bdd_at_infty f) τ
  refine cast (congrArg (HasSum · (f τ)) (funext fun n => ?_)) h
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul, coef]
  congr 2
  push_cast
  ring

theorem coef_zero {k N : ℕ} [NeZero N] (f : CuspForm (Gamma1 N) (k : ℤ)) : coef f 0 = 0 := by
  have hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  exact CuspFormClass.qExpansion_coeff_zero f one_pos hp

end Ad3P.EigenformCoefficientExpansion

open Ad3P.EigenformCoefficientExpansion in
theorem Ad3P.sEig : Ad3P.SEig := by
  intro k N _ _ χ g
  refine ⟨⟨fun γ hγ => g.char γ hγ, fun τ => exp_of g.f τ⟩, coef_zero g.f, g.one, fun p n hp => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Eigenform.a, mul_zero, dvd_zero, if_true, Nat.zero_div, coef_zero, add_zero]
  · have h := g.eig p hp n hn
    simp only [Eigenform.a]
    rw [← h]
    split_ifs <;> ring
