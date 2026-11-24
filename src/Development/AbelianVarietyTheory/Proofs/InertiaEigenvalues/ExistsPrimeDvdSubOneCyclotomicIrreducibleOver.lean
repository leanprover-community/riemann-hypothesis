module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicIrreducibleOfNotDvdDiscr
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

@[expose] public section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

private lemma natAbs_eq_one_of_dvd_prime_pow_not_dvd {d : ℤ} {m k : ℕ} (hm : m.Prime) (h1 : d ∣ (m : ℤ) ^ k)
    (h2 : ¬ (m : ℤ) ∣ d) : d.natAbs = 1 := by
  have h1' : d.natAbs ∣ m ^ k := by
    have := Int.natAbs_dvd_natAbs.mpr h1
    simpa [Int.natAbs_pow] using this
  have hc : Nat.Coprime m d.natAbs := by
    rw [hm.coprime_iff_not_dvd]
    intro h
    exact h2 (Int.natCast_dvd.mpr h)
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hc).symm h1'

theorem irreducible_cyclotomic_of_not_dvd_discr (K : Type) [Field K] [NumberField K] (m : ℕ)
    (hm : m.Prime) (hd : ¬ (m : ℤ) ∣ discr K) : Irreducible (cyclotomic m K) := by
  apply GlobalTheory.cyclotomic_irreducible_of_not_dvd_discr <;> assumption

theorem exists_prime_dvd_sub_one_irreducible_cyclotomic :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 →
      ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by
  intro K _ _ n hn
  obtain ⟨m, hmp, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (NumberField.discr K).natAbs hn
  refine ⟨m, hmp, (Nat.modEq_iff_dvd' hmp.one_le).mp hmod.symm, ?_⟩
  apply irreducible_cyclotomic_of_not_dvd_discr K m hmp
  intro h
  have hne : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natCast_dvd.mp h)
  omega

end GlobalTheory
