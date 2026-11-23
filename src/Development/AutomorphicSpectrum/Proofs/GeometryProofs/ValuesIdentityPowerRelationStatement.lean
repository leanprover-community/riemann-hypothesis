module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesIdentityPowerRelation
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem _root_.GlobalTheory.T.values_identity_power_relation : ∀ {C : Type} [CommRing C] (m N : ℕ) (T T' th sv d : C) (Wk1 Wkz Wkx Wm1 Wmx A B up u0 e0 R R' Wo Wy bo bz : Cˣ), T' * ((Wk1 : C) * (R : C) ^ ((N * m) ^ 2)) = th ^ ((N * m) ^ 2) * (Wkz : C) → T * ((Wo : C) * (R' : C) ^ (N ^ 2)) ^ (m ^ 2) = sv ^ (N ^ 2) * (Wy : C) ^ (m ^ 2) → A = bo * (bz ^ (N ^ 2))⁻¹ * Wy → B = bo * (bo ^ (N ^ 2))⁻¹ * Wo → R = bo * R' → ((bz ^ (m ^ 2) : Cˣ) : C) * sv = d * (th * ((up⁻¹ : Cˣ) : C)) → Wkz * up ^ ((N * m) ^ 2) * (A ^ ((m ^ 2) ^ 2))⁻¹ = Wkx * u0 ^ ((N * m) ^ 2) * (B ^ ((m ^ 2) ^ 2))⁻¹ → Wkx * Wm1 ^ (N ^ 2) = Wk1 * Wmx ^ (N ^ 2) → u0 = e0 * (R ^ (m ^ 2))⁻¹ → e0 ^ (m ^ 2) * Wmx * Wm1⁻¹ * (R ^ (m ^ 2))⁻¹ = 1 → T ^ (m ^ 2) = d ^ ((N * m) ^ 2) * T' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_identity_units | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_identity_units | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.values_identity_units <;> assumption)
