module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.ESOrdM

theorem stalk_normal_of_smooth (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f (fun y => ?_) x
  have : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  let _ : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have h : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have hle : y.asIdeal.primeCompl ≤ nonZeroDivisors R := y.asIdeal.primeCompl_le_nonZeroDivisors
  have hd : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk y) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  exact ⟨hd, isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory.ESOrdM
