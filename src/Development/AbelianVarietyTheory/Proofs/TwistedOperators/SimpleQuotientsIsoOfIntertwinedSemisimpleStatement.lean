module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleQuotientsIsoOfIntertwinedSemisimple
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

theorem _root_.GlobalTheory.T.simple_quotients_iso_of_intertwined_semisimple : ∀ (ι Fm Q Q' Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup Pi] [Module ℂ Pi]
  (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (ρ' : ι → Module.End ℂ Q') (C' : Submodule ℂ Q') (σ : ι → Module.End ℂ Pi)
  (β : Fm → Q →ₗ[ℂ] Pi) (β₁ : Q' →ₗ[ℂ] Pi),
  (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ i, β₁ ∘ₗ ρ' i = σ i ∘ₗ β₁) →
  (∀ f, GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker (β f)) → GlobalTheory.RealQuot.rad ρ' C' ≤ LinearMap.ker β₁ → β₁ ≠ 0 →
  (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Q, GlobalTheory.RealQuot.IsStab ρ N → GlobalTheory.RealQuot.rad ρ C ≤ N → N = GlobalTheory.RealQuot.rad ρ C ∨ N = ⊤) →
  (∀ N : Submodule ℂ Q', GlobalTheory.RealQuot.IsStab ρ' N → GlobalTheory.RealQuot.rad ρ' C' ≤ N → N = GlobalTheory.RealQuot.rad ρ' C' ∨ N = ⊤) →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  ∃ e : (Q ⧸ GlobalTheory.RealQuot.rad ρ C) ≃ₗ[ℂ] (Q' ⧸ GlobalTheory.RealQuot.rad ρ' C'),
    ∀ i, e.toLinearMap ∘ₗ GlobalTheory.RealQuot.radAct ρ C i = GlobalTheory.RealQuot.radAct ρ' C' i ∘ₗ e.toLinearMap := by
  first | exact @GlobalTheory.RealQuot.simpleQuot_iso_of_intertwined | exact GlobalTheory.RealQuot.simpleQuot_iso_of_intertwined | (intros; apply GlobalTheory.RealQuot.simpleQuot_iso_of_intertwined <;> assumption)
