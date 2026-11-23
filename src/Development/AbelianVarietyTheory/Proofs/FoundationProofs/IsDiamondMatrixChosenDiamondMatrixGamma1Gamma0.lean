module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

private lemma exists_isDiam_of_coprime (N l d : ℕ) (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  obtain ⟨k, hkN, hkl⟩ := Nat.chineseRemainder hNl d 1
  have hk1 : Nat.Coprime k N := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkN]
    exact hd
  have hk2 : Nat.Coprime k l := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkl]
    simp
  have hk : Nat.Coprime k (N * l) := Nat.Coprime.mul_right hk1 hk2
  have hg : Int.gcd (k : ℤ) ((N * l : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hk
  have hb := Int.gcd_eq_gcd_ab (k : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  have hdet : (!![Int.gcdA (k : ℤ) ((N * l : ℕ) : ℤ), -Int.gcdB (k : ℤ) ((N * l : ℕ) : ℤ);
      ((N * l : ℕ) : ℤ), (k : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  refine ⟨(⟨_, hdet⟩ : SL(2, ℤ)), Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · simp only [en]
    simp
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hkN

theorem isDiam_sgD_of_prime : ∀ (N l d : ℕ), l.Prime → 0 < N → Nat.Coprime N l → Nat.Coprime d N →
    IsDiam N l d (sgD N l d) := by
  intro N l d _ _ hNl hd
  exact Classical.epsilon_spec (exists_isDiam_of_coprime N l d hNl hd)

end GlobalTheory.KZ
