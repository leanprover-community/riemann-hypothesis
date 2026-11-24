module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

section One

variable {F : Type} [Field F] [Fintype F] (k : ℕ)

def IsUni (x : GL (Fin k) F) : Prop :=
  (∀ i : Fin k, (x : Matrix (Fin k) (Fin k) F) i i = 1) ∧
    ∀ i j : Fin k, j < i → (x : Matrix (Fin k) (Fin k) F) i j = 0

def superdiag (x : Matrix (Fin k) (Fin k) F) : F :=
  ∑ i : Fin k, ∑ j : Fin k, if (j : ℕ) = (i : ℕ) + 1 then x i j else 0

variable {k}

def psiU (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) : ℂ := ψ₀ (superdiag k (u : Matrix (Fin k) (Fin k) F))

def IsWhit (ψ₀ : AddChar F ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) (ℓ : Module.Dual ℂ V) : Prop :=
  ∀ u : GL (Fin k) F, IsUni k u → ∀ v : V, ℓ (π u v) = psiU ψ₀ u * ℓ v

end One

def GelfandGraevMultOne : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible →
      ∀ ℓ₁ ℓ₂ : Module.Dual ℂ V, IsWhit ψ₀ π ℓ₁ → IsWhit ψ₀ π ℓ₂ → ℓ₁ ≠ 0 → ∃ c : ℂ, ℓ₂ = c • ℓ₁

end

end Formalism.L2.SG.GGMirabolic
