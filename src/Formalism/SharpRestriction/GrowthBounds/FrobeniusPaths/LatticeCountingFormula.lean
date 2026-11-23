module

public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Frob

variable (p f : ℕ) [Fact p.Prime]

lemma cc_frob_pow (n : ℕ) (x : WF p f) :
    WittVector.constantCoeff (((WittVector.frobenius : WF p f →+* WF p f) ^ n) x) =
      (WittVector.constantCoeff x) ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change WittVector.constantCoeff (WittVector.frobenius
      (((WittVector.frobenius : WF p f →+* WF p f) ^ n) x)) = _
    rw [WittVector.constantCoeff_apply,
      WittVector.coeff_frobenius_charP, ← WittVector.constantCoeff_apply, ih, ← pow_mul, ← pow_succ]

lemma gf_pow (hf : f ≠ 0) (x : GaloisField p f) (t : ℕ) : x ^ (p ^ (f * t)) = x := by
  let _ : Fintype (GaloisField p f) := Fintype.ofFinite _
  rw [pow_mul, ← GaloisField.card p f hf, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]

theorem frobCong (hf : 1 ≤ f) : FrobCong p f := by
  intro s s' hss β
  have hf0 : f ≠ 0 := by omega
  have hfz : (0 : ℤ) < f := by exact_mod_cast hf
  have ha_z : (((s % (f : ℤ)).toNat : ℕ) : ℤ) = s % f := Int.toNat_of_nonneg (Int.emod_nonneg _ hfz.ne')
  have ha'_z : (((s' % (f : ℤ)).toNat : ℕ) : ℤ) = s' % f :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hfz.ne')
  have hd_z : (((s' - s).toNat : ℕ) : ℤ) = s' - s := Int.toNat_of_nonneg (by linarith)
  have hq : s / f ≤ s' / f := Int.ediv_le_ediv hfz hss
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (s % (f : ℤ)).toNat + (s' - s).toNat = (s' % (f : ℤ)).toNat + f * t := by
    refine ⟨(s' / f - s / f).toNat, ?_⟩
    have ht_z : (((s' / f - s / f).toNat : ℕ) : ℤ) = s' / f - s / f := Int.toNat_of_nonneg (by linarith)
    have e1 := Int.emod_add_mul_ediv s f
    have e2 := Int.emod_add_mul_ediv s' f
    zify
    rw [ha_z, ha'_z, hd_z, ht_z]
    linear_combination e1 - e2
  have hz0 : ((sigPow p f s β) ^ (p ^ (s' - s).toNat) - sigPow p f s' β).coeff 0 = 0 := by
    rw [← WittVector.constantCoeff_apply, map_sub, map_pow]
    simp only [sigPow]
    rw [cc_frob_pow, cc_frob_pow, ← pow_mul, ← pow_add, ht, pow_add, pow_mul, gf_pow p f hf0, sub_self]
  have hmem := (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).2 hz0
  obtain ⟨τ, hτ⟩ := Ideal.mem_span_singleton.1 hmem
  exact ⟨τ, hτ⟩

end Frob

end Formalism.MainNotions.LemmaBAlt
