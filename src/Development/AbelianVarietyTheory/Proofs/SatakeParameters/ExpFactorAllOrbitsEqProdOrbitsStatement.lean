module

public import Formalism.GaussJetBounds.StatementP
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbits
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

theorem _root_.GlobalTheory.T.expFactor_allOrbits_eq_prod_orbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  first | exact @GlobalTheory.ExpFacOrbits.expFactor_allOrbits | exact GlobalTheory.ExpFacOrbits.expFactor_allOrbits | (intros; apply GlobalTheory.ExpFacOrbits.expFactor_allOrbits <;> assumption)
