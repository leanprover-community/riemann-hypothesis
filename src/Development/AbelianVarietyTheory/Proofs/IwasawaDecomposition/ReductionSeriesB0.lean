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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem exists_Sx (D : D7) : ∃ Sx : Finset (PlE D.host), (∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑Sx) ∧
    OverSet D Sx (lowAll D) ∧ (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) := by
  have hne : ∀ p ∈ lowAll D, p ≠ 0 := by
    intro p hp
    simp only [lowAll, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl
    · exact lowPr_ne_zero D p hp
    · exact (D.host.g_prime 0).ne_zero
    · exact (D.host.g_prime 1).ne_zero
    · exact D.host.pde_prime.ne_zero
    · exact D.host.pde'_prime.ne_zero
  have hfin : (⋃ p ∈ (lowAll D : Set ℕ), placesOver D.host.E p).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => Formalism.L2.TwC.placesOver_finite' D.host.E p (hne p hp)
  refine ⟨hfin.toFinset, fun p hp Q hQ => ?_, fun Q hQ => ?_, fun Q Q' hQ hc => ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 hp) hQ
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact ⟨p, hp, hQp⟩
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact (Set.Finite.mem_toFinset hfin).2 (Set.mem_biUnion hp (placesOver_conj D p hQp hc))


end GlobalTheory.HeightCounting.Up.PointwiseSettings
