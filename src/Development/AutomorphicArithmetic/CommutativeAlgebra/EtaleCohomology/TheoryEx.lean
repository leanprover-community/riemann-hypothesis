module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GFaceSnGCastSucc
public import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsCoefficientEquivCohomologyOfElements
public import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsCohomologyZeroEquivSectionsNatural
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

@[expose] public section

theorem UpperTheory.Ru.crystallineComparison.theoryEx :
    UpperTheory.Ru.crystallineComparison.TheoryEx := by
  intro C _
  obtain ⟨z, hz₁, hz₂⟩ := UpperTheory.exists_cohomology_zero_equiv_sections_natural C
  refine ⟨{ H := UpperTheory.Ru.crystallineComparison.Th.TH
            ab := fun _ _ _ => inferInstance
            pull := fun u F j => UpperTheory.Ru.crystallineComparison.Th.tPull u F j
            map := fun P _ _ α j => UpperTheory.Ru.crystallineComparison.Th.tMap P α j
            pull_map := fun u _ _ α j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tMap u α j x
            δ := UpperTheory.Ru.crystallineComparison.Th.tδ
            pull_δ := fun u S h j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tδ u S h j x
            ex₃ := UpperTheory.Ru.crystallineComparison.Th.ex₃
            ex₁ := UpperTheory.Ru.crystallineComparison.Th.ex₁
            zero := z
            zero_pull := hz₁
            zero_map := hz₂
            inj := UpperTheory.Ru.crystallineComparison.Th.vanish }, fun R _ F => ?_⟩
  obtain ⟨F', c, e, h₁, h₂⟩ := UpperTheory.exists_coefficient_equiv_cohomology_of_elements C R F
  exact ⟨F', c, e, h₁, h₂⟩
