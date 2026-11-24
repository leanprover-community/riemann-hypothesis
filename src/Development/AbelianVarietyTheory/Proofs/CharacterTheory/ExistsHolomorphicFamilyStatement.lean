module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsHolomorphicFamily
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Topology

theorem _root_.GlobalTheory.T.exists_holomorphic_family_of_ringHom_near : ∀ (K A : Type) [Field K] [CharZero K] [CommRing A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ) (φ₀ : A →+* ℂ), φ₀.comp (algebraMap K A) = σ → ∃ (m : ℕ) (s : Fin m → A) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)) (S : Finset A) (ε : ℝ), IsOpen B ∧ 0 < ε ∧ (∀ b ∈ B, (φ b).comp (algebraMap K A) = σ ∧ ∀ i, φ b (s i) = b i) ∧ (∀ a : A, DifferentiableOn ℂ (fun b => φ b a) B) ∧ ∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → (∀ a ∈ S, ‖ψ a - φ₀ a‖ < ε) → (fun i => ψ (s i)) ∈ B ∧ φ (fun i => ψ (s i)) = ψ := by
  first | exact @GlobalTheory.SmoothPointFamily.exists_holomorphic_family | exact GlobalTheory.SmoothPointFamily.exists_holomorphic_family | (intros; apply GlobalTheory.SmoothPointFamily.exists_holomorphic_family <;> assumption)
