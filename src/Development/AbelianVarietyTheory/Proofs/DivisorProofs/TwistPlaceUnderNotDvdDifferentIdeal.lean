module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Mathlib.Algebra.AffineMonoid.Basic
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistPlDiff

theorem natAbs_discr_dvd_pow (D : D7) : ∃ M : ℕ,
    (discr D.host.E).natAbs ∣ (D.host.QS * D.host.q * D.host.d) ^ M := by
  have hD : (discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  have hN : D.host.QS * D.host.q * D.host.d ≠ 0 := D.host.condN_ne_zero
  refine ⟨(discr D.host.E).natAbs, (Nat.dvd_pow_self_iff hD hN).2 fun p hp => ?_⟩
  have h := Nat.mem_primeFactors.1 hp
  exact Nat.mem_primeFactors.2
    ⟨h.1, D.host.der.discr_primes.1 p h.1 (Int.natCast_dvd.2 h.2.1), hN⟩

theorem under_not_dvd_differentIdeal : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T), ∀ PP ∈ Lc.Q t, ¬ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D T Lc μ₀ hL t PP hPP hdvd
  obtain ⟨h2qdT, -⟩ := hL.Q_off t PP hPP
  set P := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hPdef

  have h1 : Ideal.absNorm P.asIdeal ∣ (discr D.host.E).natAbs := by
    have ha : Ideal.absNorm P.asIdeal ∣ (discr D.host.F).natAbs := by
      rw [← NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F)]
      exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
    exact ha.trans (Int.natAbs_dvd_natAbs.2 (NumberField.discr_dvd_discr _ _))
  obtain ⟨M, hM⟩ := natAbs_discr_dvd_pow D

  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have := Ideal.absNorm_mem P.asIdeal
    have h' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (Ideal.absNorm P.asIdeal : 𝓞 D.host.F) ∈ PP.asIdeal := this
    simpa using h'
  have hpow : (((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)) ^ M ∈ PP.asIdeal := by
    obtain ⟨c, hc⟩ := h1.trans hM
    rw [← Nat.cast_pow, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have hx := PP.isPrime.mem_of_pow_mem M hpow
  apply h2qdT
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hx

end GlobalTheory.TwistPlDiff
