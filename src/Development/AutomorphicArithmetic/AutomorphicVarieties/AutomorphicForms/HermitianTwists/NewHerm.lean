module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open Polynomial UpperTheory.V UpperTheory.V.Af Formalism.ConjugateSelfDual
open scoped ComplexConjugate

private theorem quad_inj {a b c d : ℂ} (h : (X ^ 2 - C a * X + C b : ℂ[X]) = X ^ 2 - C c * X + C d) : a = c ∧ b = d := by
  have h0 := congrArg (Polynomial.eval 0) h
  have h1 := congrArg (Polynomial.eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at h0 h1
  constructor
  · linear_combination h0 - h1
  · linear_combination h0

theorem UpperTheory.V.Af.Rn.newHerm :
    UpperTheory.V.Published.NewformRep → UpperTheory.V.Af.Rn.UnitTw → UpperTheory.V.Af.Rn.HermOf → UpperTheory.V.Af.Rn.SatHerm → UpperTheory.V.Af.Rn.NewHerm := by
  intro hN hT hO hS k hk f w hw
  obtain ⟨π, hi, hs⟩ := hN k hk f 0
  obtain ⟨π₀, hi₀, ht⟩ := hT k (by omega) 0 π hi
  obtain ⟨H, hH⟩ := hO _ π₀ hi₀
  obtain ⟨B, hB, e⟩ := hs w hw
  obtain ⟨t, h5, h6⟩ := ht w
  obtain ⟨γ, δ, rfl⟩ := Multiset.card_eq_two.1 (TR.CuspSub.HasSat.card hB)
  obtain ⟨α, rfl⟩ : ∃ α, γ = α * t := ⟨γ * t⁻¹, by simp⟩
  obtain ⟨β, rfl⟩ : ∃ β, δ = β * t := ⟨δ * t⁻¹, by simp⟩
  have h0 : π₀.HasSat w {α, β} := (h5 _).2 (by simpa using hB)
  have h1 := hS π₀ H hH w α β h0
  rw [h6, Newform.heckePoly] at e
  obtain ⟨h2, h3⟩ := quad_inj e
  have hp : (normV w : ℂ) ^ (k - 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (UpperTheory.V.Af.Nf.places w).1.ne_zero)
  rw [← h2, ← mul_right_cancel₀ hp h3, map_mul, Complex.conj_ofReal, mul_assoc, h1]
