module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Mathlib.LinearAlgebra.SymplecticGroup
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

def cMat {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ :=
  γ.map (fun x : ℤ => (x : ℂ))

def jAut {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (cMat γ).toBlocks₂₁ * τ + (cMat γ).toBlocks₂₂

def spAct {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  ((cMat γ).toBlocks₁₁ * τ + (cMat γ).toBlocks₁₂) * (jAut γ τ)⁻¹

def zAct {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) : Fin g → ℂ :=
  ((jAut γ τ)⁻¹)ᵀ *ᵥ z

def expArg {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) : ℂ :=
  z ⬝ᵥ (((jAut γ τ)⁻¹ * (cMat γ).toBlocks₂₁) *ᵥ z)

def SpActStatement : Prop :=
  ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ →
    ∀ τ ∈ SiegelH (Fin g), IsUnit (jAut γ τ).det ∧ spAct γ τ ∈ SiegelH (Fin g)

def ChiAt (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) : Prop :=
  ∀ n n' : Fin g → ℤ, ∃ (k k' : Fin g → ℤ) (c : ℂ),
    (∀ i, k i = 0 ∨ k i = 1) ∧ (∀ i, k' i = 0 ∨ k' i = 1) ∧ c ^ 4 = 1 ∧
    ∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
      theta (halfVec k) (halfVec k') (zAct γ τ z) (spAct γ τ) ^ 2 =
        c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec n) (halfVec n') z τ ^ 2

def ChiStatement : Prop :=
  ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ →
    ChiAt g γ

def InversionStatement : Prop :=
  ∀ (g : ℕ) (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
    ∀ z : Fin g → ℂ,
      theta a b (τ⁻¹ *ᵥ z) (-τ⁻¹) ^ 2 =
        (-I) ^ g * τ.det * eC (z ⬝ᵥ (τ⁻¹ *ᵥ z)) * eC (2 * (ofRealVec a ⬝ᵥ ofRealVec b)) *
          theta b (-a) z τ ^ 2

end ReciprocityTheory.ChartRestriction.G.Key.Chi
