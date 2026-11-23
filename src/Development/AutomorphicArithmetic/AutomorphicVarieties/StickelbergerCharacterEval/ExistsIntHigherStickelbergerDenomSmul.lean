module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denint
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem primorial_dvd_fact (n : ℕ) : primorial n ∣ n.factorial := by
  rw [primorial, ← Finset.prod_Ico_id_eq_factorial]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  simp only [Finset.mem_Ico]
  exact ⟨hp.2.one_lt.le, hp.1⟩

private theorem denY_Ek (N k : ℕ) (hN : 0 < N) (hk : 1 ≤ k) (b : ZMod N) :
    ∃ z : ℤ, (z : ℚ) = (denY N k : ℚ) * Ek N k b := by
  obtain ⟨z, hz⟩ := b_denint N k b.val hN
  obtain ⟨c, hc⟩ := primorial_dvd_fact (k + 1)
  refine ⟨c * z, ?_⟩
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  simp only [denY, Ek, den] at hz ⊢
  push_cast [hc] at hz ⊢
  rw [← hz]
  field_simp

theorem UpperTheory.V.B5.exists_int_higherStickelbergerDenom_smul :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 1 ≤ k → ∃ z : MonoidAlgebra ℤ Γ, coefMap ℚ Γ z = (denY N k : ℚ) • yEl k a ha π := by
  intro N _ Γ _ π a ha k hk
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  choose w hw using fun b : ZMod N => denY_Ek N k hN hk b
  refine ⟨(1 - MonoidAlgebra.single (π (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℤ) ^ k)) *
    -∑ b : (ZMod N)ˣ, MonoidAlgebra.single (π b)⁻¹ (w b), ?_⟩

  simp only [yEl, thetaEl, sumEl, map_mul, map_sub, map_one, map_neg, map_sum, coefMap_single, hw]
  push_cast
  rw [← mul_smul_comm, smul_neg, Finset.smul_sum]
  simp only [MonoidAlgebra.smul_single']
