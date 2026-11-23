module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MainFin
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J.ChevalleyRestriction

private theorem main_fin (A : Type) [CommRing A] [IsDomain A] (s : Finset A) :
    ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B A],
      Algebra.adjoin B (s : Set A) = ⊤ → Function.Injective (algebraMap B A) →
      ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
        y b ≠ 0 → ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Ra5.main_fin A s

end UpperTheory.V.J.ChevalleyRestriction

theorem UpperTheory.V.J.chev :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
        ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K), y b ≠ 0 →
          ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 := by
  intro B A _ _ _ _ _ hft hinj a ha
  obtain ⟨s, hs⟩ := hft.out
  exact UpperTheory.V.J.ChevalleyRestriction.main_fin A s B hs hinj a ha
