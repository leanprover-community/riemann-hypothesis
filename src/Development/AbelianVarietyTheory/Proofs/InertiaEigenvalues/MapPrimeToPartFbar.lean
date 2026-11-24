module

public import Formalism.CyclotomicNorms.StatementT
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

private theorem pow_pow_factorization_mul_inv_val_eq_self {K : Type} [Field K] {l : ℕ} [Fact l.Prime] [CharP K l] (y : K) (n : ℕ)
    (hy : y ^ n = 1) :
    y ^ (l ^ n.factorization l * (((l ^ n.factorization l : ℕ) : ZMod (n / l ^ n.factorization l))⁻¹).val) = y := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [ZMod.val_one_eq_one_mod]
  set q := l ^ n.factorization l with hq_def
  set m := n / q with hm_def
  have hnqm : q * m = n := Nat.ordProj_mul_ordCompl_eq_self n l
  have hm0 : m ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hnqm
    omega
  haveI : NeZero m := ⟨hm0⟩
  have hcop : Nat.Coprime q m := (Nat.coprime_ordCompl hl hpos.ne').pow_left _
  have hym : y ^ m = 1 := by
    have h1 : (y ^ m) ^ q = 1 := by rw [← pow_mul, mul_comm, hnqm, hy]
    have h2 : (y ^ m - 1) ^ q = 0 := by
      rw [hq_def, sub_pow_char_pow, ← hq_def, h1, one_pow, sub_self]
    have hq0 : q ≠ 0 := pow_ne_zero _ hl.ne_zero
    exact sub_eq_zero.1 ((pow_eq_zero_iff hq0).1 h2)
  have hmod : q * ((q : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one q hcop
  have hdvd : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hym
  have hmod' := hmod.of_dvd hdvd
  calc y ^ (q * ((q : ZMod m)⁻¹).val) = y ^ ((q * ((q : ZMod m)⁻¹).val) % orderOf y) := (pow_mod_orderOf _ _).symm
    _ = y ^ (1 % orderOf y) := by rw [hmod']
    _ = y := by rw [pow_mod_orderOf, pow_one]

theorem map_primeToPart_fbar {g l : ℕ} [Fact g.Prime] [Fact l.Prime] {K : Type} [Field K] [CharP K l]
    (ι : Formalism.CyclotomicNorms.Fbar g →* K) (x : Formalism.CyclotomicNorms.Fbar g) : ι (Formalism.CyclotomicNorms.primeToPart l x) = ι x := by
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [map_pow]
  exact pow_pow_factorization_mul_inv_val_eq_self _ _ (by rw [← map_pow, pow_orderOf_eq_one, map_one])

end GlobalTheory.TypeLeaf
