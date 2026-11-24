module

public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesLinearCoordsEqFlatTaylor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem _root_.GlobalTheory.T.padicSeries_linearCoords_eq_flatTaylor : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ G : TaylorLogMetric.VC D N N' → ℂ, AnalyticOnNhd ℂ G Set.univ → TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm G) = Formalism.L2.Th1.G.linSub (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
  first | exact @GlobalTheory.FlatTaylorBridge.bridge | exact GlobalTheory.FlatTaylorBridge.bridge | (intros; apply GlobalTheory.FlatTaylorBridge.bridge <;> assumption)
