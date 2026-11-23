module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BLprim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.FeLFunctionConstMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Parity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primlevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.NumberTheory.LSeries.Nonvanishing
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_nzC :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ), 1 ≤ k → χ (-1) = (-1) ^ k → Bprim k χ ≠ 0 ∧ (2 ≤ k → genB k χ ≠ 0) := by
  intro N _ χ k hk hpar
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hpar' : χ.primitiveCharacter (-1) = (-1) ^ k := by rw [(b_parity k χ).2, hpar]
  have hne1 : χ.primitiveCharacter⁻¹ ≠ 1 ∨ (k : ℂ) ≠ 1 := by
    rcases Nat.lt_or_ge 1 k with h | h
    · right
      exact_mod_cast (ne_of_gt h)
    · left
      have hk1 : k = 1 := le_antisymm h hk
      intro h1
      have h1' : χ.primitiveCharacter = 1 := inv_eq_one.mp h1
      rw [h1', MulChar.one_apply isUnit_one.neg, hk1, pow_one] at hpar'
      norm_num at hpar'
  have hL := b_fe χ.primitiveCharacter k hprim hk hpar'
  have hLne : DirichletCharacter.LFunction χ.primitiveCharacter⁻¹ (k : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _ hne1 (by simp; exact_mod_cast hk)
  have hB : Bprim k χ ≠ 0 := by
    intro h0
    have hl := (b_lprim χ.primitiveCharacter k hk).1
    have hg : genB k ⇑χ.primitiveCharacter = 0 := h0
    rw [hg, neg_zero, zero_div] at hl
    rw [hl, norm_zero] at hL
    have hc : (0 : ℝ) < (χ.conductor : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
    have hpos : (0 : ℝ) < 2 * ((k - 1).factorial : ℝ) * (χ.conductor : ℝ) ^ ((k : ℝ) - 1 / 2)
        / (2 * Real.pi) ^ k * ‖DirichletCharacter.LFunction χ.primitiveCharacter⁻¹ (k : ℂ)‖ := by
      apply mul_pos
      · apply div_pos
        · apply mul_pos
          · positivity
          · exact Real.rpow_pos_of_pos hc _
        · positivity
      · exact norm_pos_iff.mpr hLne
    linarith
  refine ⟨hB, fun hk2 => ?_⟩
  rw [b_primlevel k χ (Nat.pos_of_ne_zero (NeZero.ne N)) hk]
  refine mul_ne_zero hB ?_
  rw [Finset.prod_ne_zero_iff]
  intro p hp h0
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have heq : primVal χ p * (p : ℂ) ^ (k - 1) = 1 := by linear_combination -h0
  have hv : ‖primVal χ p‖ = 0 ∨ ‖primVal χ p‖ = 1 := by
    by_cases hu : IsUnit (p : ZMod χ.conductor)
    · right
      have := χ.primitiveCharacter.unit_norm_eq_one hu.unit
      rwa [IsUnit.unit_spec] at this
    · left
      simp [primVal, MulChar.map_nonunit _ hu]
  have hn := congrArg norm heq
  rw [norm_mul, norm_pow, Complex.norm_natCast, norm_one] at hn
  rcases hv with h | h
  · rw [h, zero_mul] at hn
    exact zero_ne_one hn
  · rw [h, one_mul] at hn
    have hn' : p ^ (k - 1) = 1 := by exact_mod_cast hn
    rcases Nat.pow_eq_one.mp hn' with h1 | h1
    · exact hpp.one_lt.ne' h1
    · omega
