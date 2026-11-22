module

public import Mathlib
public import Formalism.LandauZeroFreeBounds.Statement

@[expose] public section

open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

noncomputable section

namespace Formalism.HermitianLattices.GL2PrimeSums

def psum (a : ℕ → ℂ) (u : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n

def psumR (a : ℕ → ℝ) (u : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n

def Gchi (a : ℕ → ℂ) (S : ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ) - (y : ℂ) * S

def Gone (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y / (n : ℝ) - 1) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def SmoothedRemainderIntegralFormula : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ),
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℂ,
      Tendsto (fun U : ℝ => ∫ u in y..U, psum a u / (u : ℂ) ^ 2) atTop (𝓝 I) ∧
      Gchi a S y = -(y : ℂ) * I

def SmoothedRemainderRealIntegralFormula : Prop :=
  ∀ a : ℕ → ℝ,
    Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumR a u - u) / u ^ 2) atTop
      (𝓝 (-1 - Real.eulerMascheroniConstant)) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℝ,
      Tendsto (fun U : ℝ => ∫ u in y..U, (psumR a u - u) / u ^ 2) atTop (𝓝 I) ∧
      Gone a y = -y * I

def Li (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def Emain (θ : ℤ) (β X : ℝ) : ℝ := Li X - θ * Li (X ^ β)

def rhoErr (C c B X : ℝ) : ℝ :=
  C * Real.exp (-c * Real.log X / Real.log B) + C * Real.exp (-c * Real.sqrt (Real.log X))

def PrimesAPInterval (C₀ Cr cr c : ℝ) : Prop :=
  ∀ (m a : ℕ), 3 ≤ m → Nat.Coprime a m → ∀ Y h : ℝ, (4 * (m : ℝ)) ^ C₀ ≤ Y → h ≤ 1 →
    rhoErr Cr cr (4 * m) Y ≤ h / 100 → (4 * (m : ℝ)) ^ (7 : ℝ) ≤ h * Y ^ ((1 : ℝ) / 3) →
    c * h * (4 * (m : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y ≤
      (((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ)

end Formalism.HermitianLattices.GL2PrimeSums
