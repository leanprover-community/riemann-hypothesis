module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitIdentityAllOfIntegralClassHostLog
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

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.orbitIdentity_all_of_integralClass_hostLog_alt : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → OrbitPlaces.OrbOK D p → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p (nP D p) σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' r : ℕ) (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p), HypPair σ f f' → ∀ (Θ : MvPowerSeries (Fin r) ℂ_[p]), HostLog p g2 g3 s2 ε Θ → ∀ (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') Θ → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) Th := by
  first | exact @GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog | exact GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog | (intros; apply GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog <;> assumption)
