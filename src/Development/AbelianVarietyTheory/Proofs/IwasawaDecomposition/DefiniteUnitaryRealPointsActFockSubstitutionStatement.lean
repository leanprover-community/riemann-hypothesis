module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryRealPointsActFockSubstitution
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteUnitary_realPoints_act_fock_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (θ : InfFam D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsWeilDatumO ψ V W χS χT ω → IsInfFam θ → V.SigOK → W.SigOK → AllPlus M → AllPlus M' → IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) → ∀ τ, (∀ g : Matrix.unitaryGroup (Fin V.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (atTau θ V τ (unfr M τ g), 1) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (colSub W.rank τ g P)) ∧ ∀ u : Matrix.unitaryGroup (Fin W.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (1, atTau θ W τ (unfr M' τ u)) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (rowSub V.rank τ u P) := by
  first | exact @GlobalTheory.DefLift.FockAct.fock_act | exact GlobalTheory.DefLift.FockAct.fock_act | (intros; apply GlobalTheory.DefLift.FockAct.fock_act <;> assumption)
