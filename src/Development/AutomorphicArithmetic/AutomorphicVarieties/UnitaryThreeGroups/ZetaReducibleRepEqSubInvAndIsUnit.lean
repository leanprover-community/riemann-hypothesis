module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
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

open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.zeta_reducible_rep_eq_sub_inv_and_isUnit :
    ∀ {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (c g₁ : G), Marks η Ψ c g₁ →
    zeta c g₁ (r0 η Ψ) = ((Ψ g₁ : Rˣ) : R) - (((Ψ g₁)⁻¹ : Rˣ) : R) ∧ IsUnit (zeta c g₁ (r0 η Ψ)) := by
  intro G R _ _ η Ψ c g₁ hm
  have hz : zeta c g₁ (r0 η Ψ) = ((Ψ g₁ : Rˣ) : R) - (((Ψ g₁)⁻¹ : Rˣ) : R) := by
    have hs : Ψ (gstar c g₁) = (Ψ g₁)⁻¹ := by
      simp [gstar, map_mul, map_inv, hm.Ψc]
    simp only [zeta, zmat, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.sub_apply, Matrix.diagonal_apply_eq, hs]
    simp [wt1]
  refine ⟨hz, ?_⟩
  rw [hz]
  have key : ((Ψ g₁ : Rˣ) : R) - (((Ψ g₁)⁻¹ : Rˣ) : R)
      = (((Ψ g₁)⁻¹ : Rˣ) : R) * (((Ψ g₁ : Rˣ) : R) ^ 2 - 1) := by
    rw [mul_sub, mul_one, pow_two, ← mul_assoc, Units.inv_mul, one_mul]
  rw [key]
  exact (Units.isUnit _).mul hm.Ψg
