module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeOne
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module Matrix

variable {F : Type} [Field F] {r : ℕ}

section Nonvanishing

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

end Nonvanishing

section Embedding

variable {d d' : ℕ}

variable (b : Fin r → ℕ) (c : ℕ)

end Embedding

section Main

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

theorem leviWh_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → leviWh ψ b σ = 1 := by
  first
  | exact @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | (apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one ..)

end Main

end GlobalTheory.FinGL.LeviWh
