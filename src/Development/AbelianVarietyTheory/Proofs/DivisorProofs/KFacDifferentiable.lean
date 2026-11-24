module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.HeckeTwo

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

variable {F : Type} [Field F] [NumberField F]

def NZ (I : FractionalIdeal (𝓞 F)⁰ F) : Type := {b : F // b ∈ I ∧ b ≠ 0}

def unitRel (I : FractionalIdeal (𝓞 F)⁰ F) : Setoid (NZ I) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1 = ((ε : 𝓞 F) : F) * p.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun {p q} ⟨ε, h⟩ => ⟨ε⁻¹, by rw [h, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h⟩ ⟨ε', h'⟩ => ⟨ε' * ε, by rw [h', h, ← mul_assoc]; simp⟩ }

def phi (σ w : ℂ) : ℂ := w⁻¹ ^ 2 * ((‖w‖ : ℝ) : ℂ) ^ (-2 * σ)

def hTrans (σ : ℂ) (ν y : ℝ) : ℂ :=
  ∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

def cConst (σ : ℂ) : ℂ := hTrans σ 0 1


variable (F) in
def kFac (σ : ℂ) : ℂ :=
  ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))

def fTerm (σ : ℂ) (z : Emb F → ℂ) (b ν : F) : ℂ :=
  ∏ τ : Emb F, (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ)) *
    hTrans σ (τ ν) (τ b * (z τ).im))

def aPart (𝔞 : Frac F) (σ : ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 (c.out.1, 0)

def bOne (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1

def bZero (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  if σ = 0 then 0 else
    kFac (F := F) σ * ((omegaFactor (F := F) 𝔞) : ℂ) * (((nrm (F := F) 𝔟) : ℝ) : ℂ) ^ (-1 - 2 * σ) * Zb (1 + 2 * σ) *
      ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))

def gFun (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  aPart 𝔞 σ + bZero Zb 𝔞 𝔟 σ z + kFac (F := F) σ * ((omegaFactor (F := F) 𝔞) : ℂ) * bOne 𝔞 𝔟 σ z

def IsGood (P : ℂ → (Emb F → ℂ) → ℂ) : Prop :=
  (∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (P σ) (upperHalf F)) ∧
  (∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (P σ) z) halfPlane)

theorem kFac_differentiable : Differentiable ℂ (kFac (F := F)) := by
  intro σ
  unfold kFac
  rw [show (fun σ : ℂ => ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))) =
      fun σ => ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ)) ^ Fintype.card (Emb F) from
    funext fun σ => Finset.prod_const _]
  refine DifferentiableAt.pow (DifferentiableAt.const_mul ?_ _) _
  refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
  exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'

end GlobalTheory.HeckeTwo
