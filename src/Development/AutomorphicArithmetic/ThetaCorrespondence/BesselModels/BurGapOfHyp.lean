module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec Matrix GlobalTheory.RealBessel

namespace UpperTheory.Lit.Bur

def IsGapDS {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : ℝ) : Prop :=
  ∃ (ε : Fin n → Bool) (lam : Fin n → ℝ) (fr : Matrix (Fin n) (Fin n) ℂ), IsUnit fr ∧
    frᴴ * Formalism.REAL.Jm ε * fr = J ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧
    Formalism.MainNotions.S.IsDS ε lam (fun g => σ (fr⁻¹ * g * fr))

def IsCompactCfg {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (z : Fin n → ℂ) : Prop :=
  1 ≤ m ∧
    (((Formalism.QuantumDeterminants.herm J z z).re < 0 ∧ ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) ∨
      (0 < (Formalism.QuantumDeterminants.herm J z z).re ∧ ∀ x : Fin m → ℂ, x ≠ 0 → (Formalism.QuantumDeterminants.herm J₀ x x).re < 0))

def BurGap : Prop :=
  ∀ (n m r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ), IsFrame J J₀ F e z → IsCompactCfg J J₀ z →
    ∀ χ : Matrix (Fin n) (Fin n) ℂ → ℂ, IsGeneric J e z χ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UH J) σ →
      IsIrredOn (UH J) σ → ∀ h : ℝ, 120 * (n : ℝ) ^ 3 ≤ h → IsGapDS J σ h →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W), IsContIrred (UH J₀) π₀ →
      Module.rank ℂ (besselForms J J₀ F e χ σ π₀ (smSub J σ)) ≤ 1

def BurGapPos : Prop :=
  ∀ (n m r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ), IsFrame J J₀ F e z → 1 ≤ m → (Formalism.QuantumDeterminants.herm J z z).re < 0 →
    (∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) →
    ∀ χ : Matrix (Fin n) (Fin n) ℂ → ℂ, IsGeneric J e z χ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UH J) σ →
      IsIrredOn (UH J) σ → ∀ h : ℝ, 120 * (n : ℝ) ^ 3 ≤ h → IsGapDS J σ h →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W), IsContIrred (UH J₀) π₀ →
      Module.rank ℂ (besselForms J J₀ F e χ σ π₀ (smSub J σ)) ≤ 1

end UpperTheory.Lit.Bur
