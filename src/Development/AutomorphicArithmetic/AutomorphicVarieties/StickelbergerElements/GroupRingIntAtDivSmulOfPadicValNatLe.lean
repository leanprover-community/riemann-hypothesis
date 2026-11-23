module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V

theorem UpperTheory.V.Stk.groupRing_intAt_div_smul_of_padicValNat_le :
    ∀ (l : ℕ) [Fact l.Prime] (M D t : ℕ), 0 < M → 0 < D → t + padicValNat l D ≤ padicValNat l M →
      ∀ (Γ : Type) [CommGroup Γ] (z : MonoidAlgebra ℤ Γ), B4.IntAt l t (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z) := by
  intro l _ M D t hM hD ht Γ _ z g
  have hp : l.Prime := Fact.out
  have hcoef : (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z).coeff g = ((M : ℚ) / (D : ℚ)) * (z.coeff g : ℚ) := by
    simp [Stk.cf]
  rw [hcoef]
  have hdvdM : l ^ (padicValNat l D + t) ∣ M :=
    (pow_dvd_pow l (by omega)).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hdvdD : l ^ padicValNat l D ∣ D := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  obtain ⟨k, hk⟩ := hdvdM
  obtain ⟨E, hE⟩ := hdvdD
  have hnd : ¬ l ∣ E := by
    intro hl
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    conv_rhs => rw [hE]
    rw [pow_succ]
    simpa only [Nat.padicValNat_def] using Nat.mul_dvd_mul_left (l ^ padicValNat l D) hl
  have hE0 : E ≠ 0 := by
    rintro rfl
    simp at hE
    omega
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hEq : (E : ℚ) ≠ 0 := by exact_mod_cast hE0
  have hMq : (M : ℚ) = (l : ℚ) ^ (padicValNat l D + t) * k := by exact_mod_cast hk
  have hDq : (D : ℚ) = (l : ℚ) ^ padicValNat l D * E := by exact_mod_cast hE
  have heq : (M : ℚ) / (D : ℚ) * (z.coeff g : ℚ) / (l : ℚ) ^ t = ((k : ℚ) / (E : ℚ)) * (z.coeff g : ℚ) := by
    rw [hMq, hDq, pow_add]
    field_simp
  rw [heq]
  refine (B4.Zl l).mul_mem ?_ (intCast_mem _ _)
  rw [B4.mem_Zl]
  intro hden
  apply hnd
  have h1 : (((k : ℤ) : ℚ) / ((E : ℤ) : ℚ)).den ∣ E := by
    rw [← Rat.divInt_eq_div]
    exact_mod_cast Rat.den_dvd (k : ℤ) (E : ℤ)
  push_cast at h1
  exact hden.trans h1
