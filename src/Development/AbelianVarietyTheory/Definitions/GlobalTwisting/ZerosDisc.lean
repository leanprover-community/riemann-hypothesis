module

public import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
public import Mathlib.Analysis.Analytic.Order
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

open Finset ArithmeticFunction

namespace GlobalTheory.Lin

def zerosBox {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : Set ℂ :=
  {ρ | σ ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T ∧ DirichletCharacter.LFunction χ ρ = 0}

def ord {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

def zerosDisc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (c : ℂ) (R : ℝ) : Set ℂ :=
  {w | ‖w - c‖ ≤ R ∧ (χ ≠ 1 ∨ w ≠ 1) ∧ DirichletCharacter.LFunction χ w = 0}

def derSeries (c : ℕ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (n : ℂ) ^ (-s)

def primesIoc (x y : ℝ) : Finset ℕ := (Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime

def psiAP (M b : ℕ) (u : ℝ) : ℝ := ∑ n ∈ (Icc 1 ⌊u⌋₊).filter (fun n => n ≡ b [MOD M]), Λ n

def IsExc (c₁ : ℝ) {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (β : ℝ) : Prop :=
  χ ^ 2 = 1 ∧ 1 - c₁ / Real.log M < β ∧ β < 1 ∧
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    DirichletCharacter.LFunction χ.primitiveCharacter β = 0

def ExcData (c₁ : ℝ) (M : ℕ) [NeZero M] (b : ℕ) (θ : ℤ) (β : ℝ) : Prop :=
  (θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M) (β' : ℝ), ¬ IsExc c₁ χ β') ∨
    ∃ χ : DirichletCharacter ℂ M, IsExc c₁ χ β ∧ χ (b : ZMod M) = (θ : ℂ)

def PrimesRel : Prop :=
  ∃ c₁ c₂ c₃ CA cS : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 8 ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < CA ∧ 0 < cS ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M →
    (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExc c₁ χ β → IsExc c₁ χ' β' → χ = χ' ∧ β = β') ∧
    (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExc c₁ χ β → cS / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧
    ∀ (b : ℕ) (θ : ℤ) (β : ℝ), Nat.Coprime b M → ExcData c₁ M b θ β →
      ∀ X : ℝ, (M : ℝ) ^ c₂ ≤ X →
        |(M.totient : ℝ) * (((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤
          CA * (Real.exp (-c₃ * Real.log X / Real.log M) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X

end GlobalTheory.Lin

end
