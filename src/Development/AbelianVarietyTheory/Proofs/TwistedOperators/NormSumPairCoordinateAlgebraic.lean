module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.NormSum.CoordAlg

open Classical Formalism.UG Formalism.UG.P Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem

theorem exists_prime_integralOver_gt (D : D7) (N : ℕ) (h : GA D N) (Q : ℕ) :
    ∃ p : ℕ, Q < p ∧ p.Prime ∧ IntegralOver D p h := by
  set g : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hg
  choose m hm0 hm using fun ij : Fin N × Fin N => denom (F := ℚ) (E := D.host.E) (g ij.1 ij.2)
  set M := ∏ ij, m ij with hMdef
  have hM0 : 0 < M := Finset.prod_pos fun ij _ => hm0 ij
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + Q + 1)
  have hpM' : ¬ p ∣ M := fun hd => by have := Nat.le_of_dvd hM0 hd; omega
  obtain ⟨v, hv, hw⟩ := exists_place p hp
  have hMv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hm'
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM'))).map
      (Int.castRingHom (𝓞 ℚ))
    refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hm')) (Ideal.mul_mem_left _ _ (by simpa using hv))
  have hi : ∀ i j, afsplitEps D.host.E v * g i j ∈ OhE D := fun i j => eps_mul_mem v M hMv _ (by
    rw [hMdef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ _) (hm (i, j)))
  obtain ⟨k, hk, hint, htriv⟩ := exists_int (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) v
    (h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) h.2 (Units.inv_eq_of_mul_eq_one_left ((mem_GA D _).1 h.2)) hi
  refine ⟨p, by omega, hp, ⟨k, hk⟩, (mem_intG _).2 hint, fun i j l => ?_⟩
  have := zero_at (F := ℚ) (E := D.host.E) v p hp hw (g i j - (1 : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) l
  rw [← htriv i j] at this
  exact this

end GlobalTheory.NormSum.CoordAlg
