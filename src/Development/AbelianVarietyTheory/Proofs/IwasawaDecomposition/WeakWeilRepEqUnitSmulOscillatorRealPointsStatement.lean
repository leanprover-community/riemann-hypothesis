module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPoints
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ Ω : GA D S × GA D T → GlobalTheory.RealWeil.BB ψ S T → GlobalTheory.RealWeil.BB ψ S T, GlobalTheory.RealWeil.IsOsc (GlobalTheory.RealWeil.rhoV hψ σ S T) (fun p v => GlobalTheory.RealWeil.mM θ S T p *ᵥ v) Ω → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → om (g, h) F.1 = c • ((Ω (g, h) F).1 : WO S T → ℂ) := by
  first | exact @GlobalTheory.Mem.LiftCmp.weil_eq_smul_osc | exact GlobalTheory.Mem.LiftCmp.weil_eq_smul_osc | (intros; apply GlobalTheory.Mem.LiftCmp.weil_eq_smul_osc <;> assumption)
