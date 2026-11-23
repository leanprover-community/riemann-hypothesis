module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullCubicalOfGenericOfExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseUnitRigidifiedGenericGeneratorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqGeneratorFactorialBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalGeneratorDivBaseUnitEqGenericStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.MvPowerSeries.Equiv
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCubExt

theorem extendGenAt_chartRing : ∀ (k : Type) [Field k] (m n : ℕ),
    GlobalTheory.ChartCubExt.ExtendGenAt (ChartRing k m n) (FractionRing (ChartRing k m n)) := by
  intro k _ m n
  have : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  have := GlobalTheory.isRegularRing_of_isRegularLocalRing (ChartRing k m n)
  have : IsDomain (ChartRing k m n) :=
    (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (ChartRing k m n)).1
  have : UniqueFactorizationMonoid (ChartRing k m n) := GlobalTheory.ThetaExtend.ufd_of_regular _
  intro G _ _ hG eA heA N r hr hc
  have := hG.smooth
  have := hG.quasiCompact
  have := hG.geomConnected
  obtain ⟨a, u, hu, hf⟩ := GlobalTheory.T.exists_const_mul_eq_generator_factorial_base _ _ G _ _ _ N.L r inferInstance inferInstance inferInstance
    (IsPullback.of_hasPullback _ _) N.isLB hr
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_baseUnit_rigidifiedGenericGenerator _ _ G (eSec G) (Over.w η[G]) eA heA N.L N.rig r N.isLB N.rigGen hc a u hu hf
  exact GlobalTheory.T.exists_globalGenerator_div_baseUnit_eq_generic _ _ G _ _ _ pullback.condition N.L r a b hb u hu hf

end GlobalTheory.ChartCubExt
