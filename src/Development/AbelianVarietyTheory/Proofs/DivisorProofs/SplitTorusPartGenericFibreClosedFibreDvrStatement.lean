module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusPartGenericFibreClosedFibreDvr
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8


theorem _root_.GlobalTheory.T.splitTorusPart_generic_fibre_closed_fibre_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (X₁ : Type) [AddCommGroup X₁] [Module.Free ℤ X₁] [Module.Finite ℤ X₁] (j : splitTorus (Sp V) X₁ ⟶ G₁), IsMonHom j → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (t₀ : splitTorus (Sp κ) X₀ ⟶ G₀), IsTorPart t₀ → Module.finrank ℤ X₀ = Module.finrank ℤ X₁ → IsTorPart (pullTorus hψ₀ j) := by
  first | exact @GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed | exact GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed | (intros; apply GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed <;> assumption)
