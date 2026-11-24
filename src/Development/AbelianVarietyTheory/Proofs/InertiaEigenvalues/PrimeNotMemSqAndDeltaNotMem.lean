module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.LSq

def cInt (l : ℕ) (n : ℕ) : ℤ := ((n : ℤ) - (n : ℤ) ^ l) / l

theorem l_mul_cInt (l : ℕ) [hl : Fact l.Prime] (n : ℕ) : (l : ℤ) * cInt l n = (n : ℤ) - (n : ℤ) ^ l := by
  unfold cInt
  apply Int.mul_ediv_cancel'
  have h : (((n : ℤ) - (n : ℤ) ^ l : ℤ) : ZMod l) = 0 := by
    push_cast; rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h

theorem δ_natCast (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (n : ℕ) :
    D.δ (n : A) = ((cInt l n : ℤ) : A) := by
  induction n with
  | zero =>
    have : cInt l 0 = 0 := by
      unfold cInt; simp [zero_pow hl.out.ne_zero]
    simp [this, Delta.δ_zero]
  | succ n ih =>
    have h := D.δ_add (n : A) 1
    rw [D.δ_one, ih] at h
    push_cast
    rw [h]
    have key : cInt l (n + 1) = cInt l n - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k := by
      have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
      apply mul_left_cancel₀ h0
      have e1 := l_mul_cInt l (n + 1)
      have e2 := l_mul_cInt l n
      have h5 : ((n : ℤ) + 1) ^ l = (n : ℤ) ^ l + 1 ^ l + (l : ℤ) *
          ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k * (1 : ℤ) ^ (l - k) := by
        rw [add_pow_prime_eq' hl.out]
        congr 2
        refine Finset.sum_congr rfl fun k _ => by ring
      simp only [one_pow, mul_one] at h5
      push_cast at e1
      rw [mul_sub, e1, e2, h5]; ring
    rw [key, Int.cast_sub, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, one_pow, mul_one, add_zero]

theorem cInt_self (l : ℕ) [hl : Fact l.Prime] : cInt l l = 1 - (l : ℤ) ^ (l - 1) := by
  have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  apply mul_left_cancel₀ h0
  rw [l_mul_cInt, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hl.out.one_le]

theorem δ_l (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) :
    D.δ (l : A) = 1 - (l : A) ^ (l - 1) := by
  rw [δ_natCast, cInt_self]; push_cast; ring

theorem δ_mem_of_mem_sq (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (m : Ideal A)
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.δ x ∈ m := by
  rw [sq] at hx
  have hl0 := hl.out.ne_zero
  suffices x ∈ m ∧ D.δ x ∈ m from this.2
  refine Submodule.mul_induction_on hx (fun a ha b hb => ⟨m.mul_mem_right b ha, ?_⟩) ?_
  · rw [D.δ_mul]
    refine m.add_mem (m.add_mem (m.mul_mem_right _ (m.pow_mem_of_mem ha _ (Nat.pos_of_ne_zero hl0)))
      (m.mul_mem_right _ (m.pow_mem_of_mem hb _ (Nat.pos_of_ne_zero hl0)))) ?_
    exact m.mul_mem_right _ (m.mul_mem_right _ hlm)
  · rintro x y ⟨hx, hδx⟩ ⟨hy, hδy⟩
    refine ⟨m.add_mem hx hy, ?_⟩
    rw [D.δ_add]
    refine m.sub_mem (m.add_mem hδx hδy) (m.sum_mem fun k hk => ?_)
    obtain ⟨hk0, hkl⟩ := Finset.mem_Ioo.1 hk
    exact m.mul_mem_left _ (m.pow_mem_of_mem hy _ (Nat.sub_pos_of_lt hkl))

theorem l_not_mem_sq : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (m : Ideal A),
    m ≠ ⊤ → (l : A) ∈ m → (l : A) ∉ m ^ 2 ∧ D.δ (l : A) ∉ m := by
  intro l hl A _ D m hm hlm
  have hδ : D.δ (l : A) ∉ m := by
    intro h
    rw [δ_l] at h
    have h2 : (l : A) ^ (l - 1) ∈ m :=
      m.pow_mem_of_mem hlm _ (Nat.sub_pos_of_lt hl.out.one_lt)
    exact hm ((Ideal.eq_top_iff_one _).2 (by simpa using m.add_mem h h2))
  exact ⟨fun h => hδ (δ_mem_of_mem_sq l D m hlm h), hδ⟩

end GlobalTheory.BSP.LSq
