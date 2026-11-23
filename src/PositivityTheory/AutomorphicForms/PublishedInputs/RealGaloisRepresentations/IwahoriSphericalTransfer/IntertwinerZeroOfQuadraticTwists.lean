module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntertwinerZeroOfQuadraticTwists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.MainNotions.N
theorem _root_.GlobalTheory.T.intertwiner_zero_of_quadratic_twists : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ ρ ρ' : Γ →* GL (Fin n) k) (η₀ χ₁ χ₂ : Γ →* ℤˣ), (∀ g, η₀ g = 1 → ρ g = ρ₀ g) → (∀ g, η₀ g = 1 → ρ' g = ρ₀ g) → IsSSRep ρ → IsSSRep ρ' → (∀ c : Γ →* ℤˣ, (c = χ₁ ∨ c = χ₂ ∨ c = χ₁ * χ₂ ∨ c = χ₁ * η₀ ∨ c = χ₂ * η₀ ∨ c = χ₁ * χ₂ * η₀) → ∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((c g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ g, χ₁ g = 1 → χ₂ g = 1 → ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∀ g, ((ρ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((ρ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace := by
  first | exact @GlobalTheory.trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner | exact GlobalTheory.trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner | (intros; apply GlobalTheory.trace_eq_of_agree_on_index_two_of_no_twisted_intertwiner <;> assumption)
