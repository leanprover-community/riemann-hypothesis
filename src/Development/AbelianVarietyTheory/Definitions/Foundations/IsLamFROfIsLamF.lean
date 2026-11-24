module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoIOfEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.LambdaValuationPowers

namespace GlobalTheory.KummerEisensteinGalois

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def InChi (X : Tower Ω ε) (N w : ℕ) (χ : ℕ → ℤ_[l]) (b : X.Fn l) : Prop :=
  b ∈ X.B N l w ∧ ∀ d : ℕ, Nat.Coprime d N → X.diam N l d b = χ d • b

def IsLamFR (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (χ : ℕ → ℤ_[l]) (j : Ω →+* Qbar l)
    (pr : X.Fn l → Fin 2 → Qbar l) (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) ∧
    ∃ (cL : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n) ∧ FixIc c (per n)) ∧
      ∀ (n : ℕ), cL ≤ n → ∀ (b : X.Fn l), InChi X N w χ b → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
        Cg (n - cL) (lam (seqN 1 j φ)) (per n * pr b 1)

section Induced

variable {X : Tower Ω ε} {A : ValuationSubring Ω} {N w : ℕ} {χ : ℕ → ℤ_[l]} {j : Ω →+* Qbar l}
  {pr : X.Fn l → Fin 2 → Qbar l} {c : Coef l} {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l}

end Induced

end GlobalTheory.KummerEisensteinGalois

end
