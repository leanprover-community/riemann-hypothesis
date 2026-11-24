module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LeafHypothesesConst
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj.SqNum

theorem conj_smul_int {D : D7} (x : 𝓞 D.host.E) : (D.host.conj • x : 𝓞 D.host.E) = Formalism.L2.Col.cO _ x := by
  apply RingOfIntegers.ext
  rw [show ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) from rfl,
    Formalism.BasicNotions.bridge_star_holds D.R D.host]
  rfl

theorem exists_prime_notInert_place : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)),
    v ∈ P.S0 → ∃ q : ℕ, q.Prime ∧ ¬ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  intro D T L P v hv
  obtain ⟨e, he⟩ := P.w_split v hv
  have hunder := P.w_over v hv
  obtain ⟨q, hq, hqv⟩ : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    have := v.isMaximal
    have : Finite (𝓞 D.host.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    letI := Ideal.Quotient.field v.asIdeal
    refine ⟨ringChar (𝓞 D.host.F ⧸ v.asIdeal), CharP.char_is_prime (𝓞 D.host.F ⧸ v.asIdeal) _, ?_⟩
    exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 D.host.F ⧸ v.asIdeal) (ringChar _))
  refine ⟨q, hq, fun hin => ?_, hqv⟩
  have hqQ : ((q : ℕ) : 𝓞 D.host.E) ∈ (P.w v).asIdeal := by
    have h1 : ((q : ℕ) : 𝓞 D.host.F) ∈ ((P.w v).under (𝓞 D.host.F)).asIdeal := by rw [hunder]; exact hqv
    simpa [HeightOneSpectrum.under] using h1
  have hfix := hin (P.w v).asIdeal (P.w v).isPrime (P.w v).ne_bot hqQ
  have hf : ∀ x, x ∈ (P.w v).asIdeal → Formalism.L2.Col.cO _ x ∈ (P.w v).asIdeal := fun x hx => by
    rw [← conj_smul_int, ← hfix]
    exact Ideal.smul_mem_pointwise_smul _ _ _ hx
  have hmem : ∀ x, x ∈ (P.w v).asIdeal ↔ Formalism.L2.Col.cO _ x ∈ (P.w v).asIdeal := fun x =>
    ⟨hf x, fun hx => by simpa [Formalism.L2.Col.cO_cO] using hf _ hx⟩
  have hc := GlobalTheory.MovedIdem.isIdemAt_conj he hmem
  have e1 : e = Formalism.L2.Theta.cA D e := (GlobalTheory.ExportSeries.idemAt_eq he).symm.trans (GlobalTheory.ExportSeries.idemAt_eq hc)
  have e0 : e = 0 := by
    calc e = e * e := he.1.1.symm
      _ = e * Formalism.L2.Theta.cA D e := by rw [← e1]
      _ = 0 := he.1.2.1
  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (P.w v).ne_bot
  have h2 := (he.2 x hx0).1 hxQ
  rw [e0, zero_mul, map_zero] at h2
  exact h2 (zero_mem _)

end GlobalTheory.FunObj.SqNum
