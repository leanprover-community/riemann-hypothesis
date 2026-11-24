module

public import Formalism.PeriodIntegrals.AdelClassFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace PIW.AdelClassFin

open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

def StCong : Prop :=
  ∀ (I : AutInst) (U : Subgroup I.Gf), IsOpen (U : Set I.Gf) → ∃ g : ℕ, 1 ≤ g ∧ I.Kg g ⊆ (U : Set I.Gf)

def StKFin : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ T : Finset I.Gf, ∀ k ∈ I.Kset, ∃ t ∈ T, ∃ u ∈ I.Kg g, k = t * u

def StGenus : Prop :=
  ∀ I : AutInst, ∃ S : Finset I.Gf, ∀ x : I.Gf, ∃ γ ∈ GFf I, ∃ s ∈ S, ∃ k ∈ I.Kset, x = γ * s * k

def StTop : Prop := StCong → StKFin → StGenus → PI.AdelClassFin.AdelClassFin

def SelfDual {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (M : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ x : Fin n → E, x ∈ M ↔ ∀ y ∈ M, Formalism.UG.hform (starRingEnd E) J y x ∈ (algebraMap (𝓞 E) E).range

def IsImg {E : Type} [Field E] [NumberField E] {n : ℕ} (γ : GL (Fin n) E) (M₀ M : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v : Fin n → E, v ∈ M ↔ ∃ w ∈ M₀, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v

def StH : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Formalism.UG.IsHerm (starRingEnd E) J → J.det ≠ 0 →
    ∃ T : Finset (Submodule (𝓞 E) (Fin n → E)), ∀ M : Submodule (𝓞 E) (Fin n → E), M.FG →
      Submodule.span E (M : Set (Fin n → E)) = ⊤ → SelfDual J M →
      ∃ γ : GL (Fin n) E, γ ∈ Formalism.UG.UJ (starRingEnd E) J ∧ ∃ M₀ ∈ T, IsImg γ M₀ M

def StDict : Prop :=
  ∀ I : AutInst, ∃ Λ : I.Gf → Submodule (𝓞 I.E) (Fin I.n → I.E),
    (∀ x, (Λ x).FG ∧ Submodule.span I.E ((Λ x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) = ⊤ ∧ SelfDual I.J (Λ x)) ∧
    (∀ x y, Λ x = Λ y → ∃ k ∈ I.Kset, y = x * k) ∧
    (∀ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J →
      ∃ c ∈ GFf I, I.fmat c = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) ∧
        ∀ x, IsImg γ (Λ x) (Λ (c * x)))

def StGenusOf : Prop := StDict → StH → StGenus

end PIW.AdelClassFin
