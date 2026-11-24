module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.IsUnitaryK
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {n : Type} [Fintype n] [DecidableEq n]

def bd4 {R : Type*} [Zero R] (P : Matrix n n R) : Matrix (Fin 4 × n) (Fin 4 × n) R :=
  fun x y => if x.1 = y.1 then P x.2 y.2 else 0

def bmv0 {R : Type*} [Zero R] [One R] (k : Fin 4) : Matrix (Fin 4 × n) (Fin 4 × n) R :=
  fun x y => if x.1 = 0 ∧ y.1 = k ∧ x.2 = y.2 then 1 else 0

def gmat (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
  fun x w => g.symm (Pi.single w 1) x

end Blocks

def sq (d : ℕ) : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ)

def kmat {m m' : Type} (d : ℕ) (A B : Matrix m m' ℚ) : Matrix m m' ℂ :=
  A.map (fun q => (q : ℂ)) + sq d • B.map (fun q => (q : ℂ))

def lmat {l : ℕ} [Fact l.Prime] {m m' : Type} (δ : MaximalUnramifiedExtension l) (A B : Matrix m m' ℚ) : Matrix m m' (MaximalUnramifiedExtension l) :=
  A.map (fun q => (q : MaximalUnramifiedExtension l)) + δ • B.map (fun q => (q : MaximalUnramifiedExtension l))

def FrobStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (dK : ℕ), 5 ≤ l → ¬ l ∣ dK → dK.Prime → dK % 8 = 7 →
    (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ (ι : ℂ ≃+* ℂ_[l]) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l), UnrOK (MaximalUnramifiedExtension l) l σ →
    (∀ x, ‖σ x‖ = ‖x‖) ∧ ∃ δ : MaximalUnramifiedExtension l, (δ : ℂ_[l]) = ι (sq dK) ∧ σ δ = -δ

def RatStep : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g₀ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∃ (P₀ : Matrix n n ℂ) (M₁ M₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ) (R₁ R₂ : Matrix n n ℚ) (c : ℚ),
      padicNorm l c = 1 ∧
      gmat g₁ = lam⁻¹ • (bd4 P₀ * kmat dK M₁ M₂) ∧
      (kmat dK M₁ M₂).transpose * bd4 (kmat dK R₁ R₂) * kmat dK M₁ (-M₂) = (c : ℂ) • 1 ∧
      ∀ k : Fin 4, ∃ U₁ U₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ,
        (∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) ∧
        bmv0 k * kmat dK M₁ M₂ = kmat dK M₁ M₂ * kmat dK U₁ U₂

def LocCore : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (dK : ℕ) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (δ : MaximalUnramifiedExtension l), 5 ≤ l → ¬ l ∣ dK →
    (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) → (∀ x, ‖σ x‖ = ‖x‖) → δ ^ 2 = -(dK : MaximalUnramifiedExtension l) → σ δ = -δ →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (M₁ M₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ) (R₁ R₂ : Matrix n n ℚ)
    (c : ℚ), padicNorm l c = 1 →
    (lmat δ M₁ M₂).transpose * bd4 (lmat δ R₁ R₂) * lmat δ M₁ (-M₂) = (c : MaximalUnramifiedExtension l) • 1 →
    (∀ k : Fin 4, ∃ U₁ U₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ,
        (∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) ∧
        bmv0 k * lmat δ M₁ M₂ = lmat δ M₁ M₂ * lmat δ U₁ U₂) →
    ∃ T Ti : Matrix n n (MaximalUnramifiedExtension l), T * Ti = 1 ∧ IsUnitaryK σ (bd4 Ti * lmat δ M₁ M₂)

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
