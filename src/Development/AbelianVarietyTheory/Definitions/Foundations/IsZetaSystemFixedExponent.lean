module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
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

@[expose] public section

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def IsZetaSystemFixedExponent (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∀ r n : ℕ, ∃ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
    (∀ σ ∈ fixMu Ω (topMu l n r N), LiftB X l N (k - 2) n c₀ (clsBmu X l n r N x c d k g σ) (bB σ)) ∧
    ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
      Cv n (Y r s y) (YfB X l pr W e ψ n r N bB s y +
        (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

def IsZTc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N l' : ℕ) [NeZero N] [NeZero l'] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (YT : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∀ r n : ℕ, ∃ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
    (∀ σ ∈ fixMu Ω (topMT l n r N l'), LiftB X l N (k - 2) n c₀ (clsBTmu X l n r N l' x c d k g σ) (bB σ)) ∧
    ∃ b : (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
      Cv n (YT r s y) (YfBT X l pr W e ψ n r N l' bB s (y.1 * lsqInv l l' (r + n), y.2) + (rhoK W e ψ s *ᵥ b (y * cycT l r l' s) - b y))

def IsZWc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∃ Yx : ZMod N → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
    (∀ x, IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf c₀ (Yx x)) ∧ ∀ r s y, Y r s y = ∑ x, cw x • Yx x r s y

end GlobalTheory.K4
