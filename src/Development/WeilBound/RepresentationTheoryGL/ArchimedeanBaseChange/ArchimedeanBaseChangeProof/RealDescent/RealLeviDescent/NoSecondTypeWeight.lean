module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real
open Formalism.REAL (GlRel)

variable {n : ℕ}

def wtB (B : Finset (Fin n × Fin n)) : Fin n → ℝ := fun c =>
  ((B.filter fun p => p.1 = c).card : ℝ) - ((B.filter fun p => p.2 = c).card : ℝ)

def IsSecondTypeWeight (lam : Fin n → ℤ) (lev : Fin n → ℕ) (ν : Fin n → ℝ) : Prop :=
  ∃ B : Finset (Fin n × Fin n), B.Nonempty ∧ (∀ p ∈ B, lev p.1 < lev p.2) ∧ StrictAnti (ν + rhoV n) ∧
    ∃ w : Equiv.Perm (Fin n), ν + rhoV n = (muQ lam lev + rhoV n - wtB B) ∘ w

structure AdmFor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (lam : Fin n → ℤ) (lev : Fin n → ℕ)
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) : Prop where
  gl1 : GlRel E1
  gl2 : GlRel E2
  comm : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b
  unitK : ∀ a b (x y : V), ⟪kF E1 E2 a b x, y⟫_ℂ = ⟪x, kF E1 E2 b a y⟫_ℂ
  locFin : ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF E1 E2 a b w ∈ S
  ch1 : ∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x
  ch2 : ∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x
  no_second_type_weight : ∀ ν, IsSecondTypeWeight lam lev ν → hwSp E1 E2 ν = ⊥

def MultFor : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      AdmFor lam lev E1 E2 → ∀ v w : V, v ∈ hwSp E1 E2 (muQ lam lev) → w ∈ hwSp E1 E2 (muQ lam lev) → v ≠ 0 →
        (∃ x ∈ alg E1 E2, x v = w) → ∃ c : ℂ, w = c • v

end PositivityTheory.RgBcC.RealD
