module

public import GroundTheory.AutomorphicForms.WhittakerLSpace
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.NumberTheory.LocalField.Basic

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

abbrev Sp (k : Type) [Field k] (n : ℕ) : Type := Matrix (Fin n) (Fin n) k × (Fin n → k)

def Bz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Set (Matrix (Fin n) (Fin n) k) := {x | ∀ a ∈ Z, a * x = x * a}

def Gz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Set (GL (Fin n) k) := {g | ∀ a ∈ Z, a * g.val = g.val * a}

def act (g : GL (Fin n) k) (p : Sp k n) : Sp k n := (g.val * p.1 * g⁻¹.val, g.val *ᵥ p.2)

def CR (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Prop := (∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) ∧ IsReduced Z

def Supp (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (C : Set (Sp k n)) : Prop :=
  ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), (∀ p ∈ C, f p = 0) → ξ f = 0

def Inv (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ g ∈ Gz Z, ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ξ (fun p => f (act g p)) = ξ f

def Kills (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) (U : Set (Sp k n)) : Prop := ∀ f ∈ supportedIn U, ξ f = 0

def Van (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Prop :=
  ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → Kills ξ {p | p.2 ≠ 0}

def ZN (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Set (Matrix (Fin n) (Fin n) k) := {x | ∃ c ∈ Z, IsNilpotent (x - c)}

def pZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) :
    Fin (2 * n + 1) × Fin (Module.finrank k Z) → k :=
  fun ij => trace (((Module.finBasis k Z ij.2 : Z) : Matrix (Fin n) (Fin n) k) * x ^ (ij.1 : ℕ))

def adj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (s : Matrix (Fin n) (Fin n) k) : Subalgebra k (Matrix (Fin n) (Fin n) k) :=
  Algebra.adjoin k (insert s (Z : Set (Matrix (Fin n) (Fin n) k)))

def Dich : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ y,
    (∃ c ∈ Z, ∀ x ∈ Bz Z, pZ Z x = y → IsNilpotent (x - c)) ∨
    ∃ s ∈ Bz Z, s ∉ Z ∧ Module.End.IsSemisimple (Matrix.toLin' s) ∧ ∀ x ∈ Bz Z, pZ Z x = y →
      ∃ g ∈ Gz Z, IsNilpotent (g.val * x * g⁻¹.val - s) ∧ Commute (g.val * x * g⁻¹.val) s

def Adj : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ s ∈ Bz Z, s ∉ Z → Module.End.IsSemisimple (Matrix.toLin' s) →
    CR (adj Z s) ∧
      Module.finrank k (Subalgebra.centralizer k (adj Z s : Set (Matrix (Fin n) (Fin n) k))) <
        Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)))

def LocStep : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ,
    Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ →
    (∀ y, (∃ c ∈ Z, ∀ x ∈ Bz Z, pZ Z x = y → IsNilpotent (x - c)) ∨
      ∀ ξ' : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ' ((Bz Z ∩ pZ Z ⁻¹' {y}) ×ˢ Set.univ) → Inv Z ξ' → Kills ξ' {p | p.2 ≠ 0}) →
    Kills ξ ({p | p.2 ≠ 0} ∩ {p | p.1 ∉ ZN Z})

def DescA : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ s ∈ Bz Z, s ∉ Z → Module.End.IsSemisimple (Matrix.toLin' s) →
    Van (adj Z s) → ∀ y, (∀ x ∈ Bz Z, pZ Z x = y →
      ∃ g ∈ Gz Z, IsNilpotent (g.val * x * g⁻¹.val - s) ∧ Commute (g.val * x * g⁻¹.val) s) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ ((Bz Z ∩ pZ Z ⁻¹' {y}) ×ˢ Set.univ) → Inv Z ξ → Kills ξ {p | p.2 ≠ 0}

def NilpB : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z →
    (∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → Kills ξ ({p | p.2 ≠ 0} ∩ {p | p.1 ∉ ZN Z})) →
    Van Z

end PositivityTheory.RgUd.T
