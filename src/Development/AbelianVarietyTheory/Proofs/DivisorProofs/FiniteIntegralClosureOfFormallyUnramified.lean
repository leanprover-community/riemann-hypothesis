module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Unramified.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Unramified.Field

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct



namespace GlobalTheory.AbhFin

theorem finite_integralClosure_of_formallyUnramified (R K C : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing C] [Algebra K C] [Algebra R C] [IsScalarTower R K C] [FiniteDimensional K C]
    [Algebra.FormallyUnramified K C] : Module.Finite R (integralClosure R C) := by
  classical
  haveI : IsArtinianRing C := IsArtinianRing.of_finite K C
  haveI : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field K C
  haveI := Fintype.ofFinite (MaximalSpectrum C)
  haveI : ∀ m : MaximalSpectrum C, Module.Finite R (integralClosure R (C ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    haveI : Algebra.FormallyUnramified K (C ⧸ m.asIdeal) :=
      Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal) Ideal.Quotient.mk_surjective
    haveI : Algebra.IsSeparable K (C ⧸ m.asIdeal) := Algebra.FormallyUnramified.isSeparable K _
    exact IsIntegralClosure.finite R K (C ⧸ m.asIdeal) _
  let red : ∀ m : MaximalSpectrum C, integralClosure R C →ₗ[R] integralClosure R (C ⧸ m.asIdeal) := fun m =>
    (((Ideal.Quotient.mkₐ R m.asIdeal).comp (integralClosure R C).val).codRestrict
      (integralClosure R (C ⧸ m.asIdeal))
      (fun a => (show IsIntegral R (a : C) from a.2).map (Ideal.Quotient.mkₐ R m.asIdeal))).toLinearMap
  refine Module.Finite.of_injective (LinearMap.pi red) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  apply Subtype.ext
  apply (IsArtinianRing.equivPi C).injective
  show _ = IsArtinianRing.equivPi C 0
  rw [map_zero]
  funext m
  exact congrArg Subtype.val (congrFun ha m)

end GlobalTheory.AbhFin
