module

public import Mathlib.RingTheory.Jacobson.Ring
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.InvSubmonoid
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
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Int.Basic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VeryDenseClosedPointObjectsOfMinimalPrimes

@[expose] public section

namespace GlobalTheory

theorem isJacobsonRing_integers : IsJacobsonRing ℤ := by
  apply _root_.GlobalTheory.ClosedPts.jacobson_int <;> assumption

theorem closedPt_of_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  intro R _ _ _ f hf
  haveI := isJacobsonRing_integers
  let S := Localization.Away f
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : Nontrivial S := hinj.nontrivial
  haveI : Algebra.FiniteType R S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) S
  haveI : Algebra.FiniteType ℤ S := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ n) := Ideal.Quotient.field n
  haveI : Algebra.FiniteType ℤ (S ⧸ n) := inferInstance
  haveI hfin := finite_of_finite_type_of_isJacobsonRing ℤ (S ⧸ n)
  have hZ : (algebraMap ℤ (S ⧸ n)).IsIntegral := fun x => IsIntegral.of_finite ℤ x
  let ψ : R →+* S ⧸ n := (Ideal.Quotient.mk n).comp (algebraMap R S)
  have hcomp : ψ.comp (Int.castRingHom R) = algebraMap ℤ (S ⧸ n) := RingHom.ext_int _ _
  have hψ : ψ.IsIntegral := RingHom.IsIntegral.tower_top (Int.castRingHom R) ψ (hcomp ▸ hZ)
  haveI hbot : (⊥ : Ideal (S ⧸ n)).IsMaximal := Ideal.bot_isMaximal
  let M : Ideal R := (⊥ : Ideal (S ⧸ n)).comap ψ
  have hM : M.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ψ hψ ⊥
  refine ⟨M, hM, ?_, ?_⟩
  · intro hfM
    have h0 : ψ f = 0 := by simpa [M] using hfM
    have hu : IsUnit (algebraMap R S f) := IsLocalization.Away.algebraMap_isUnit f
    have hu' : IsUnit (ψ f) := hu.map (Ideal.Quotient.mk n)
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  · have hMZ : (M.comap (Int.castRingHom R)).IsMaximal := by
      have : M.comap (Int.castRingHom R) = (⊥ : Ideal (S ⧸ n)).comap (algebraMap ℤ (S ⧸ n)) := by
        rw [← hcomp, ← Ideal.comap_comap]
      rw [this]
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hZ ⊥
    obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (M.comap (Int.castRingHom R))
    change _ = Ideal.span {a} at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
      exact Ring.ne_bot_of_isMaximal_of_not_isField hMZ Int.not_isField ha
    have hpr : Prime a := by
      rw [← Ideal.span_singleton_prime ha0, ← ha]
      exact hMZ.isPrime
    refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.1 hpr, ?_⟩
    have hmem : (a.natAbs : ℤ) ∈ M.comap (Int.castRingHom R) := by
      rw [ha, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    have h2 := Ideal.mem_comap.1 hmem
    simpa only [eq_intCast, Int.cast_natCast] using h2

end GlobalTheory
