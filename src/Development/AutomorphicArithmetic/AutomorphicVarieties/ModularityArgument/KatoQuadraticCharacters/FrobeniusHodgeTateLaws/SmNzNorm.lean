module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V.Z.Kato.Joint

private lemma smNz_unit {l : ℕ} [Fact l.Prime] {n : ℕ} (h : ¬ l ∣ n) : IsUnit (n : ZMod l) := by
  rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  exact h

private lemma smNz_norm {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) {n : ℕ} (h : ¬ l ∣ n) :
    ‖χ (n : ZMod l)‖ = 1 := by
  have hu := smNz_unit (l := l) h
  have := χ.unit_norm_eq_one hu.unit
  rwa [IsUnit.unit_spec] at this

theorem UpperTheory.V.Z.Kato.Joint.smNz :
    UpperTheory.V.Z.Kato.Joint.SmNz := by
  intro l _ ι e N c d ψ a b hN hN0 hc0 hd0 hc hd ha hce hdb
  have hp : l.Prime := Fact.out
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> simp [smT, hp.dvd_mul, hN, hc, hd]
  · simp only [Fin.sum_univ_four, smB, smT, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_mul,
      map_neg, map_pow, map_zpow₀, map_natCast, RingEquiv.apply_symm_apply, Nat.cast_mul,
      MulChar.inv_apply_eq_inv', mul_pow]
    have hC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    have hD : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hψN : ψ (N : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hN
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hψc : ψ (c : ZMod l) ≠ 0 := by
      intro h0
      have := smNz_norm ψ hc
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have hCe : (c : ℂ) ^ e ≠ 0 := pow_ne_zero _ hC
    have hw : (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) * (c : ℂ) ^ e = (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ := by
      rw [← zpow_natCast (c : ℂ) e, ← zpow_add₀ hC, ← zpow_natCast (c : ℂ) 2, ← zpow_neg,
        ← zpow_add₀ hC]
      congr 1
      push_cast
      ring
    set w := (c : ℂ) ^ ((3 : ℤ) - ((2 * e + 1 : ℕ) : ℤ)) with hwdef
    have hfac : (c : ℂ) ^ 2 * (d : ℂ) ^ 2 * (ψ (N : ZMod l))⁻¹ * (N : ℂ) ^ e +
        -(w * a * (d : ℂ) ^ 2) * (ψ (N : ZMod l) * ψ (c : ZMod l))⁻¹ * ((N : ℂ) ^ e * (c : ℂ) ^ e) +
        -((c : ℂ) ^ 2 * ((d : ℂ) * b)) * (ψ (N : ZMod l) * ψ (d : ZMod l))⁻¹ * ((N : ℂ) ^ e * (d : ℂ) ^ e) +
        w * a * ((d : ℂ) * b) * (ψ (N : ZMod l) * ψ (c : ZMod l) * ψ (d : ZMod l))⁻¹ *
          ((N : ℂ) ^ e * (c : ℂ) ^ e * (d : ℂ) ^ e) =
        (N : ℂ) ^ e * (ψ (N : ZMod l))⁻¹ *
          ((c : ℂ) ^ 2 - w * (c : ℂ) ^ e * a * (ψ (c : ZMod l))⁻¹) *
          ((d : ℂ) ^ 2 - (d : ℂ) * b * (d : ℂ) ^ e * (ψ (d : ZMod l))⁻¹) := by
      ring
    rw [hfac, hw]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hNc) (inv_ne_zero hψN)) ?_) ?_
    · have h1 : (c : ℂ) ^ 2 - (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * a * (ψ (c : ZMod l))⁻¹ =
          (c : ℂ) ^ 2 * ((c : ℂ) ^ e)⁻¹ * ((c : ℂ) ^ e - a * (ψ (c : ZMod l))⁻¹) := by
        field_simp
      rw [h1]
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hC) (inv_ne_zero hCe)) ?_
      rw [sub_ne_zero]
      apply hce
      rw [norm_mul, norm_inv, ha, smNz_norm ψ hc]
      norm_num
    · intro h0
      apply hdb
      rw [zpow_neg_one, pow_succ]
      linear_combination h0
