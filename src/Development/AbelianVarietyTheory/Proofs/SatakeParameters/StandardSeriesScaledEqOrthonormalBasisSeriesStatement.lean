module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesScaledEqOrthonormalBasisSeries
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.standardSeries_scaled_eq_orthonormalBasisSeries : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' r : ℕ) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hz : Fin r → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (hz i) = 0) → (∀ k, ∑ i, MvPowerSeries.C (Formalism.L2.KerInert.RepFrame.lamB D lam b k i) * hz i = ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C (chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) * MvPowerSeries.X j) → ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst hz (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth | exact GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth | (intros; apply GlobalTheory.KerStd.HypCoord.stdSer_scaled_eq_thOrth <;> assumption)
