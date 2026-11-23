module

public import GroundTheory.AutomorphicForms.GL2.GJFERat
public import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
public import GroundTheory.AutomorphicForms.GL2.GJLeviZeta
public import GroundTheory.AutomorphicForms.GL2.GJParabolicFubini
public import GroundTheory.AutomorphicForms.InductionParabolic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic MeasureTheory
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]


variable (F) in
def centralUnif (m : ℕ) : GL (Fin m) F := Cartan.diagPow F m fun _ => 1

section Block

variable {m : ℕ} [MeasurableSpace (GL (Fin m) F)] {H : Type*} [Group H]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

def blockA (μ : Measure (GL (Fin m) F)) (σ : Representation ℂ (GL (Fin m) F × H) W)
    (Φ : Matrix (Fin m) (Fin m) F → ℂ) (v : W) (ℓ : Module.Dual ℂ W) (s : ℂ) : ℂ :=
  ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * ℓ (σ (g, 1) v) ∂μ

def blockB (μ : Measure (GL (Fin m) F)) (σ : Representation ℂ (GL (Fin m) F × H) W)
    (Φ : Matrix (Fin m) (Fin m) F → ℂ) (v : W) (ℓ : Module.Dual ℂ W) (s : ℂ) : ℂ :=
  ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g (m - s) * ℓ (σ (g⁻¹, 1) v) ∂μ

end Block

section Levi

variable {n : ℕ} {α : Type*} [LinearOrder α] {W : Type*} [AddCommGroup W] [Module ℂ W]

variable (β : Fin n → α)

def leviTensor (φ : LeviIndex n β → F → ℂ) (X : Matrix (Fin n) (Fin n) F) : ℂ :=
  ∏ ij : LeviIndex n β, φ ij (X ij.1.1 ij.1.2)

def leviModulus (m : levi F n β) : ℝ≥0 :=
  ∏ a : Set.range β,
    LocalField.modulus ((leviBlock F m a : Matrix (Fiber β a) (Fiber β a) F).det) ^ blockSize β a

variable [MeasurableSpace F] [BorelSpace F]

def leviTensorHat (ψ : AddChar F Circle) (φ : LeviIndex n β → F → ℂ)
    (Y : Matrix (Fin n) (Fin n) F) : ℂ :=
  ∏ ij : LeviIndex n β, LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (φ ij) (Y ij.1.2 ij.1.1)

variable {β}

def leviIntegrandB (σ : Representation ℂ (levi F n β) W) (κ : levi F n β →* ℝ≥0)
    (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) : ℂ :=
  Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (((κ m)⁻¹ * leviModulus β m : ℝ≥0) : ℂ) *
    detPow (m : GL (Fin n) F) (-s) * ℓ (σ m⁻¹ w)


variable (F) in
def LeviFE (σ : Representation ℂ (levi F n β) W) (κ : levi F n β →* ℝ≥0)
    (μM : Measure (levi F n β)) (ψ : AddChar F Circle) (γ : RatFunc ℂ) : Prop :=
  ∀ φ : LeviIndex n β → F → ℂ, (∀ ij, φ ij ∈ LocalField.schwartzBruhat F) → ∀ w : W,
    ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      (∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → Integrable (leviIntegrand σ κ (leviTensor β φ) w ℓ s) μM) ∧
      (∃ s₁ : ℝ, ∀ s : ℂ, s.re < s₁ →
        Integrable (leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s) μM) ∧
      RatFE F γ (fun s => ∫ m, leviIntegrand σ κ (leviTensor β φ) w ℓ s m ∂μM)
        (fun s => ∫ m, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s m ∂μM)

end Levi

section Induced

variable {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] [MeasurableSpace F] [BorelSpace F]


variable (F) in
def InducedFE [MeasurableSpace (GL (Fin n) F)] (σ : Representation ℂ (levi F n β) W)
    (μG : Measure (GL (Fin n) F)) (ψ : AddChar F Circle) (γ : RatFunc ℂ) : Prop :=
  ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ φ ∈ parabolicIndSpace F n β σ,
    ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      (∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → Integrable (fun g : GL (Fin n) F =>
        Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g)) μG) ∧
      (∃ s₁ : ℝ, ∀ s : ℂ, s.re < s₁ → Integrable (fun g : GL (Fin n) F =>
        GJMatrix.localMatrixFourier ψ Φ (g : Matrix (Fin n) (Fin n) F) *
          detPow g (1 - s + ((n : ℂ) - 1) / 2) * ℓ (φ g⁻¹)) μG) ∧
      RatFE F γ
        (fun s => ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) *
          ℓ (φ g) ∂μG)
        (fun s => ∫ g, GJMatrix.localMatrixFourier ψ Φ (g : Matrix (Fin n) (Fin n) F) *
          detPow g (1 - s + ((n : ℂ) - 1) / 2) * ℓ (φ g⁻¹) ∂μG)

end Induced

end GodementJacquet

end GroundTheory.Automorphic
