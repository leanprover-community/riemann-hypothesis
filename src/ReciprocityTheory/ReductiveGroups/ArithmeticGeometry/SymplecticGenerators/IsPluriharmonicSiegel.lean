module

public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.SymplecticGroup
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Complex Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key

open ReciprocityTheory.PTheta

def phSym {g : ℕ} (x : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (1 / 2 : ℂ) • (x + xᵀ)

def phDom (g : ℕ) : Set (Fin g → Fin g → ℂ) :=
  {x | phSym (Matrix.of x) ∈ SiegelH (Fin g)}

def IsHoloSiegel (g : ℕ) (H : Matrix (Fin g) (Fin g) ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (Matrix.of x))) (phDom g)

def phActC {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (γ.toBlocks₁₁ * τ + γ.toBlocks₁₂) * (γ.toBlocks₂₁ * τ + γ.toBlocks₂₂)⁻¹

def phAct {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  phActC (γ.map (Int.cast : ℤ → ℂ)) τ

def IsSpInvariant {α : Type*} (g : ℕ) (f : Matrix (Fin g) (Fin g) ℂ → α) : Prop :=
  ∀ γ ∈ Matrix.symplecticGroup (Fin g) ℤ, ∀ τ ∈ SiegelH (Fin g), f (phAct γ τ) = f τ

def PhKoecherStatement : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ N : ℕ, 1 ≤ N → ∀ F : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g F →
    (∀ B : Matrix (Fin g) (Fin g) ℤ, B.IsSymm → ∀ τ ∈ SiegelH (Fin g),
        F (τ + (N : ℂ) • B.map (Int.cast : ℤ → ℂ)) = F τ) →
    (∀ U : Matrix (Fin g) (Fin g) ℤ, U.det = 1 → (∀ i j, (N : ℤ) ∣ U i j - (1 : Matrix (Fin g) (Fin g) ℤ) i j) →
        ∀ τ ∈ SiegelH (Fin g),
          F (U.map (Int.cast : ℤ → ℂ) * τ * (U.map (Int.cast : ℤ → ℂ))ᵀ) = F τ) →
    ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖F τ‖ ≤ K

def PhHoloStatement : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ H : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g H → IsSpInvariant g H →
    ∃ c : ℂ, ∀ τ ∈ SiegelH (Fin g), H τ = c

end ReciprocityTheory.ChartRestriction.G.Key
