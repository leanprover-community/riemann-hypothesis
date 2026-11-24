module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.exists_integral_orbit_series : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (σ : MaximalUnramifiedExtension Lc.l →+* MaximalUnramifiedExtension Lc.l) (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension Lc.l)) (om oms : Fin (Lc.d / 2) → MaximalUnramifiedExtension Lc.l) (ζ : MaximalUnramifiedExtension Lc.l), BeData Lc.l Lc.d σ F be0 om oms ζ → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) (beOf Lc.l Lc.d σ be0 om oms ζ) → ∃ U0 : MvPowerSeries (Bool × Fin (Lc.d / 2) × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l], Formalism.DworkPowerSeriesWeights.Integral U0 ∧ (MvPowerSeries.subst (fun v : ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1 => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l])) Lc.Th : MvPowerSeries (ZMod Lc.d × Fin Lc.N0 × Fin Lc.N1) ℂ_[Lc.l]) = thetaInZ (d := Lc.d) Lc.l (MaximalUnramifiedExtension Lc.l).subtype σ om oms (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension Lc.l).subtype be0))) * U0) := by
  first | exact @GlobalTheory.KerStd.integral_cofactor_converse | exact GlobalTheory.KerStd.integral_cofactor_converse | (intros; apply GlobalTheory.KerStd.integral_cofactor_converse <;> assumption)
