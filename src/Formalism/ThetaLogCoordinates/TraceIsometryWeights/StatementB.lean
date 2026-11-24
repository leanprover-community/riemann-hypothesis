module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.HasLatBasis
public import Mathlib.LinearAlgebra.Trace
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

namespace Formalism.InvariantFactorPaths.PW

open Finset Formalism.GM.DimensionMonotonicity

def HomInv : Prop :=
  ∀ (K V₁ V₂ : Type) [Field K] [CharZero K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] (n : ℕ)
    (G₁ : GlW K V₁ n) (G₂ : GlW K V₂ n) (W : Submodule K V₂) (l : ℕ), G₂.Stable W → WtBound2 G₁ G₂ W l →
    ∀ φ : V₁ →ₗ[K] V₂, (∀ x, φ x ∈ W) → (∀ c, homAct G₁.E G₂.E c c φ = 0) →
      (∀ a b x, InvOp (homAct G₁.E G₂.E) l (List.finRange n) φ (G₁.E a b x) =
        G₂.E a b (InvOp (homAct G₁.E G₂.E) l (List.finRange n) φ x)) ∧
      (∀ x, InvOp (homAct G₁.E G₂.E) l (List.finRange n) φ x ∈ W) ∧
      InvOp (homAct G₁.E G₂.E) l (List.finRange n) φ - φ ∈
        ⨆ (a : Fin n) (b : Fin n) (_ : a ≠ b), LinearMap.range (homAct G₁.E G₂.E a b)

def SchurTrace : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (G : GlW K V n) (W : Submodule K V)
    (l : ℕ), G.Stable W → FiniteDimensional K W → G.FinW W →
    (∀ (μ ν : Fin n → ℤ) (x y : V), x ≠ 0 → y ≠ 0 → x ∈ W → y ∈ W → G.IsWt μ x → G.IsWt ν y →
      ∀ c, |ν c - μ c| ≤ (l : ℤ)) →
    ∀ (la : Fin n → ℤ) (h : V), G.IsHW la h → h ∈ W → h ≠ 0 →
    ∀ φ : (G.gS {h}) →ₗ[K] (G.gS {h}),
      (∀ c, homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E c c φ = 0) →
      InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ =
        (LinearMap.trace K _ φ / (Module.finrank K (G.gS {h}) : K)) • LinearMap.id

def TypeInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module ℚ_[p] V] (n : ℕ) (G : GlW ℚ_[p] V n)
    (W : Submodule ℚ_[p] V) (M : AddSubgroup V) (l : ℕ), LatData p G W M l → ∀ la : Fin n → ℤ,
    ∃ Q : V →ₗ[ℚ_[p]] V, (∀ x ∈ IsoW G W la, Q x = x) ∧ (∀ mu, mu ≠ la → ∀ x ∈ IsoW G W mu, Q x = 0) ∧
      ∀ m ∈ M, m ∈ W → ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • Q m ∈ M

def WeylInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module ℚ_[p] V] (n : ℕ) (G : GlW ℚ_[p] V n)
    (W : Submodule ℚ_[p] V) (M : AddSubgroup V) (l : ℕ), LatData p G W M l → ∀ la : Fin n → ℤ,
    ∀ x ∈ IsoW G W la, x ∈ M →
      ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • x ∈ DeltaLat p G {h | G.IsHW la h ∧ h ∈ W ∧ h ∈ M}

end Formalism.InvariantFactorPaths.PW
