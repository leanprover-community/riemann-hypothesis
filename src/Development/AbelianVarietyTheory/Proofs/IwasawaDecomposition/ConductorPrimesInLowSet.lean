module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem GlobalTheory.LamTie.cond0_primes_lowAll : ∀ (D : D7) (Z : GlobalTheory.LamTie.LamDat D), Z.Ok → Z.q0 = AbsolutelyIrreducibleSpan.q0 D → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → ∃ p ∈ lowAll D, P ∈ placesOver D.host.E p := by
  intro D Z hZ hq P hP
  have hPr : Prime (GlobalTheory.ToricDenom.below P).asIdeal := (GlobalTheory.ToricDenom.below P).prime

  have key : ∀ n : ℕ, ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) →
      ((n : 𝓞 D.host.E) ∈ P.asIdeal) := by
    intro n hn
    have h1 : algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal := hn
    simpa using h1
  have key' : ∀ n : ℕ, ((n : 𝓞 D.host.E) ∈ P.asIdeal) →
      ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) := by
    intro n hn
    show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal
    simpa using hn
  unfold GlobalTheory.LamTie.cond0 at hP
  rcases hPr.dvd_or_dvd hP with h | h
  · have h2 := hPr.dvd_of_dvd_pow h
    rw [Ideal.dvd_span_singleton] at h2
    have h3 := key _ (by exact_mod_cast h2)
    push_cast at h3
    have hpr := P.isPrime
    rcases hpr.mem_or_mem h3 with h4 | h4
    · rcases hpr.mem_or_mem h4 with h5 | h5
      · rcases hpr.mem_or_mem h5 with h6 | h6
        · exact ⟨D.host.g 0, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
        · exact ⟨D.host.g 1, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
      · exact ⟨D.host.pde, by simp [GlobalTheory.HeightCounting.lowAll], h5⟩
    · exact ⟨D.host.pde', by simp [GlobalTheory.HeightCounting.lowAll], h4⟩
  · have hle : (GlobalTheory.ToricDenom.below Z.w0).asIdeal ≤ (GlobalTheory.ToricDenom.below P).asIdeal :=
      Ideal.le_of_dvd h
    have heq : (GlobalTheory.ToricDenom.below Z.w0).asIdeal = (GlobalTheory.ToricDenom.below P).asIdeal :=
      ((GlobalTheory.ToricDenom.below Z.w0).isMaximal).eq_of_le (GlobalTheory.ToricDenom.below P).isPrime.ne_top hle
    have hw : ((Z.q0 : ℕ) : 𝓞 D.host.E) ∈ Z.w0.asIdeal := hZ.places.referencePlaceOverPrime
    have hb : ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below Z.w0).asIdeal := by
      show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ Z.w0.asIdeal
      simpa using hw
    rw [heq] at hb
    refine ⟨Z.q0, ?_, key _ hb⟩
    rw [hq]
    simp [GlobalTheory.HeightCounting.lowAll, lowPr]
