module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing in
theorem UpperTheory.V.Pr.globOfCharts :
    UpperTheory.V.Pr.GlobOfCharts := by
  intro X _ M hTI hG x R _ _ _ f hC L hLT hLG hConcl
  have eG : ∀ P, P ∈ L.Good ↔ f P ∈ M.Good := fun P => by rw [hLG]; rfl
  have eT : ∀ P, P ∈ L.TI ↔ f P ∈ M.TI := fun P => by rw [hLT]; rfl
  have hsub : ∀ P : PrimeSpectrum R, f P ∈ M.Good → closure {f P} ⊆ M.Good :=
    fun P h => hG.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  have hmeet : ∀ P : PrimeSpectrum R, (closure {f P} ∩ M.TI).Nonempty → f P ∈ M.TI := by
    rintro P ⟨y, hy, hyT⟩
    obtain ⟨z, hzT, hz⟩ := mem_closure_iff.mp hy _ hTI hyT
    rw [Set.mem_singleton_iff] at hz
    rw [← hz]
    exact hzT
  refine ⟨?_, ?_, ?_⟩
  · intro hD Y Y' hY hY' hxY hxY' hYg
    obtain ⟨P, hPm, rfl⟩ := hC.onto Y hY.1 hxY
    obtain ⟨P', hP'm, rfl⟩ := hC.onto Y' hY'.1 hxY'
    have hPG : P ∈ L.Good := (eG P).mpr (hYg (subset_closure (Set.mem_singleton _)))
    have hPT : P ∈ L.TI := (eT P).mpr (hmeet P hY.2)
    have h' := hConcl P hPG hPT (hD P hPm) P' ((eT P').mpr (hmeet P' hY'.2)) hP'm
    exact hsub P' ((eG P').mp h')
  · intro hall
    refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents x, ?_⟩,
      mem_irreducibleComponent⟩
    obtain ⟨P, hPm, hPY⟩ :=
      hC.onto _ (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent
    refine ⟨f P, ?_, (eT P).mp (hall P hPm)⟩
    rw [← hPY]
    exact subset_closure (Set.mem_singleton _)
  · rintro ⟨I, hIG, hIT, hID⟩
    obtain ⟨p, hpm, hpI⟩ :=
      Ideal.exists_minimalPrimes_le (J := I.asIdeal) (bot_le : (⊥ : Ideal R) ≤ I.asIdeal)
    haveI hpp : p.IsPrime := hpm.1.1
    let P : PrimeSpectrum R := ⟨p, hpp⟩
    have hPmin : P.asIdeal ∈ minimalPrimes R := hpm
    have hopen : IsOpen L.TI := by
      rw [hLT]
      exact hTI.preimage hC.cont
    have hPT : P ∈ L.TI := by
      have hcl : I ∈ closure ({P} : Set (PrimeSpectrum R)) :=
        (PrimeSpectrum.le_iff_mem_closure P I).mp hpI
      obtain ⟨z, hzT, hz⟩ := mem_closure_iff.mp hcl _ hopen hIT
      rw [Set.mem_singleton_iff] at hz
      rw [← hz]
      exact hzT
    have hPG := hConcl I hIG hIT hID P hPT hPmin
    exact ⟨closure {f P}, ⟨hC.min P hPmin, f P, subset_closure (Set.mem_singleton _), (eT P).mp hPT⟩,
      hsub P ((eG P).mp hPG)⟩
