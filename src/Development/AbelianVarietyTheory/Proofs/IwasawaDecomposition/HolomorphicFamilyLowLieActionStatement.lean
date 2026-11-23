module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFamilyLowLieAction
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.holomorphic_family_low_lie_action : ∀ (D : D7) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) → Module.End ℂ P), IsHolFam M.ε B ϖ → ∃ m : LowT M →ₗ[ℂ] Module.End ℂ P, (∀ A : Module.End ℂ P, (∀ k, (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → Commute A (ϖ k)) → ∀ x, Commute A (m x)) ∧ (∀ κ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, κ τ ∈ Formalism.REAL.Kset (M.ε τ)) → ∃ v : ∀ τ, lowT M τ, (∀ τ, v τ ≠ 0) ∧ ∀ y, IsBotFam M.ε ϖ (fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) y → m (PiTensorProduct.tprod ℂ v) y = ϖ (fun τ => (κ τ).map star) y) ∧ ∀ y, IsBotFam M.ε ϖ (fun τ => -Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) y → ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ), ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → m (PiTensorProduct.tprod ℂ (Function.update v τ u)) y = ϖ (Pi.mulSingle τ (k.map star)) (m (PiTensorProduct.tprod ℂ v) y) := by
  first | exact @GlobalTheory.JointHarm.MultiOp.lowest_types_act | exact GlobalTheory.JointHarm.MultiOp.lowest_types_act | (intros; apply GlobalTheory.JointHarm.MultiOp.lowest_types_act <;> assumption)
