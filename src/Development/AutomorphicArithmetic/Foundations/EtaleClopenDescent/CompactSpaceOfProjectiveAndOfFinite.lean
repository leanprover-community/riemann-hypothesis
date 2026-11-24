module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem UpperTheory.Cb.adjoin_degree_zero_variables_eq_top (N : ℕ) :
    Algebra.adjoin (↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
      (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have hC : MvPolynomial.C a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0 :=
      MvPolynomial.isHomogeneous_C _ a
    exact Subalgebra.algebraMap_mem _ (⟨_, hC⟩ : ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0))
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p i hp =>
    exact Subalgebra.mul_mem _ (hp trivial) (Algebra.subset_adjoin ⟨i, rfl⟩)

private theorem UpperTheory.Cb.compactSpace_projective_space (N : ℕ) : CompactSpace (PSpace ℂ N) := by
  have hX : ∀ i : Fin (N + 1), (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 1 :=
    fun i => MvPolynomial.isHomogeneous_X ℂ i
  have hcov := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) ℂ) (fun i => ⟨1, hX i⟩)
    (UpperTheory.Cb.adjoin_degree_zero_variables_eq_top N)
  refine ⟨?_⟩
  have huniv : (Set.univ : Set (PSpace ℂ N)) =
      ⋃ i, ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)
        (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) : (PSpace ℂ N).Opens) : Set (PSpace ℂ N)) := by
    have := congrArg (fun U : (PSpace ℂ N).Opens => (U : Set (PSpace ℂ N))) hcov
    simpa using this.symm
  rw [huniv]
  exact isCompact_iUnion fun i =>
    (Proj.isAffineOpen_basicOpen _ _ (hX i) Nat.one_pos).isCompact

theorem UpperTheory.Cb.compactSpace_of_projective_and_of_finite :
    (∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ), IsProjOver s → CompactSpace Z) ∧ ∀ (Y Z : Scheme.{0}) (c : Y ⟶ Z), IsFinite c → CompactSpace Z → CompactSpace Y := by
  refine ⟨?_, ?_⟩
  · rintro Z s ⟨N, i, hi, -⟩
    haveI := UpperTheory.Cb.compactSpace_projective_space N
    exact QuasiCompact.compactSpace_of_compactSpace i
  · intro Y Z c hc hZ
    exact QuasiCompact.compactSpace_of_compactSpace c
