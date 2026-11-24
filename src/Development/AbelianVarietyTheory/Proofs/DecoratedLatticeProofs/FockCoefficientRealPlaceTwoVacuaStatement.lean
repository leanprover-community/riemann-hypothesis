module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacua
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockCoefficient_realPlace_two_vacua : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ (τ : D.what₂.Tau) (f F F' : WO V W → ℂ), (∀ x ∈ [f, F, F'], IsThetaFunO ψ V W x ∧ IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) x) → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ P Q : LPol W.rank V.rank, let pt := GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ); GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt F P)) (pt F' Q) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X f f = GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (atTau θ V τ g, 1) (pt f P)) (pt f Q) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X F F' := by
  first | exact @GlobalTheory.VacCoefAtPlace.coef_at_place | exact GlobalTheory.VacCoefAtPlace.coef_at_place | (intros; apply GlobalTheory.VacCoefAtPlace.coef_at_place <;> assumption)
