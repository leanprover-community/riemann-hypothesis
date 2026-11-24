module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
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
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

open Polynomial IsDiscreteValuationRing

theorem associated_primitiveRoot_sub_one_pow_totient_prime_pow {O : Type} [CommRing O] [IsDomain O]
    {l k : ℕ} (hl : l.Prime) {ζ : O} (hζ : IsPrimitiveRoot ζ (l ^ (k + 1))) :
    Associated ((ζ - 1) ^ Nat.totient (l ^ (k + 1))) (l : O) := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h1 := Polynomial.eval_one_cyclotomic_prime_pow (R := O) (p := l) k
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
  rw [← h1, ← hζ.card_primitiveRoots, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun μ hμ => ?_
  have hμ' : IsPrimitiveRoot μ (l ^ (k + 1)) :=
    (mem_primitiveRoots (pow_pos hl.pos _)).1 hμ
  obtain ⟨i, -, hi, rfl⟩ := (hζ.isPrimitiveRoot_iff).1 hμ'
  simpa using (hζ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right

theorem nval_primitiveRoot_prime_pow_sub_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l k : ℕ), l.Prime → 1 ≤ k → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ ζ : O, IsPrimitiveRoot ζ (l ^ k) → ζ - 1 ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (ζ - 1) = 1 / (Nat.totient (l ^ k) : ℝ) := by
  intro O _ _ _ l k hl hk hl0 hlu ζ hζ
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hass := associated_primitiveRoot_sub_one_pow_totient_prime_pow hl hζ
  have hφ : 0 < Nat.totient (l ^ (k + 1)) := Nat.totient_pos.2 (pow_pos hl.pos _)
  have hne : ζ - 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hφ.ne'] at hass
    exact hl0 ((associated_zero_iff_eq_zero _).1 hass.symm)
  refine ⟨hne, ?_⟩
  have hv : addVal O ((ζ - 1) ^ Nat.totient (l ^ (k + 1))) = addVal O (l : O) :=
    (addVal_eq_iff_associated _ _).2 hass
  rw [addVal_pow] at hv
  have ht : addVal O (ζ - 1) ≠ ⊤ := fun h => hne (addVal_eq_top_iff.1 h)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 ht
  have hl1 : addVal O (l : O) ≠ 0 := fun h => hlu (addVal_eq_zero_iff.1 h)
  have hv' : addVal O (l : O) = ((Nat.totient (l ^ (k + 1)) * a : ℕ) : ℕ∞) := by
    rw [← hv, ← ha]; simp
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hl1
    rw [hv']; simp
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  rw [hv', ← ha, ENat.toNat_coe, ENat.toNat_coe]
  have : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
  have : (Nat.totient (l ^ (k + 1)) : ℝ) ≠ 0 := by exact_mod_cast hφ.ne'
  push_cast
  field_simp

end GlobalTheory
