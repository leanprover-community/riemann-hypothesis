module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin.St

def SimpleIffIrr : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrr τ.ρ) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v)

def CentralIdemAct : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W), IsIrr ρ → IsIrr σ →
    σ.asAlgebraHom (centralIdem ρ) = (open Classical in if Nonempty (Representation.Equiv ρ σ) then 1 else 0)

def SepIrr : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (x : MonoidAlgebra ℂ Γ), (∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = 0) → x = 0

def ZIdemFacts : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Simple τ → Simple σ → ¬ Nonempty (τ ≅ σ) → zIdem τ * zIdem σ = 0) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Simple τ → Simple σ → Nonempty (τ ≅ σ) → Representation.asAlgebraHom σ.ρ (zIdem τ) = 1) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (I : Type) [Fintype I] (V : I → FDRep ℂ Γ), (∀ i, Simple (V i)) →
    (∀ i j, Nonempty (V i ≅ V j) → i = j) → (∀ W : FDRep ℂ Γ, Simple W → ∃ i, Nonempty (W ≅ V i)) → ∑ i, zIdem (V i) = 1

def CuspWh : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (τ : FDRep ℂ (GL (Fin d) K)), ψ₀ ≠ 1 → IsCuspidal K τ →
    (Module.finrank ℂ τ : ℂ) = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ τ.character *
      ∏ i ∈ Finset.Ico 1 d, ((Fintype.card K : ℂ) ^ i - 1)

end ReciprocityTheory.Ty.Fin.St
