module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOperatorsDistinctRealPlacesCommuteTheta
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockOperators_distinct_real_places_commute_theta : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ F, IsThetaFunO ψ V W F → let pt := fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W ρ (cart M ρ) (cart M' ρ) (onb M ρ) (onb M' ρ); let vac := IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)); (∀ P, IsThetaFunO ψ V W (pt τ' F P)) ∧ (∀ P, vac F → vac (pt τ' F P)) ∧ (∀ P Q, pt τ (pt τ' F Q) P = pt τ' (pt τ F P) Q) ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), (vac F → vac (ω (atTau θ V τ' g, 1) F)) ∧ ∀ P, ω (atTau θ V τ' g, 1) (pt τ F P) = pt τ (ω (atTau θ V τ' g, 1) F) P := by
  first | exact @GlobalTheory.TwoPlaceComm.twoPlace_comm | exact GlobalTheory.TwoPlaceComm.twoPlace_comm | (intros; apply GlobalTheory.TwoPlaceComm.twoPlace_comm <;> assumption)
