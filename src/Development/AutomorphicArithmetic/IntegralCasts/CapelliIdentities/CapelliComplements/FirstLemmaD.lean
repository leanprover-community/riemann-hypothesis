module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Bl.FirstLemmaD

theorem goal1 :
  ∀ {F : Type} [inst : Field.{0} F] [NumberField.{0} F]
  (v : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} F)),
  Exists.{1} fun (p : Nat) ↦
    And (Nat.Prime p) (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} v) (Nat.cast.{0} p)) := by
  intro F _ _ v
  have := v.isPrime
  have hne : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    fun h => v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
  have hpr : (v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F))).IsPrime :=
    Ideal.comap_isPrime _ _
  obtain ⟨x, hx, hxp⟩ := hpr.exists_mem_prime_of_ne_bot hne
  refine ⟨x.natAbs, Int.prime_iff_natAbs_prime.mp hxp, ?_⟩
  obtain ⟨c, hc⟩ : x ∣ (x.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  have hmem : ((x.natAbs : ℤ)) ∈ v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) := by
    rw [hc]
    exact Ideal.mul_mem_right c _ hx
  rw [Ideal.mem_comap, map_natCast] at hmem
  exact hmem

end Bl.FirstLemmaD
