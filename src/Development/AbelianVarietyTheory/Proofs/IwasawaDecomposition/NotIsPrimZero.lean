module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Mult

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]

def cellMult {m : ℕ} (δ : Fin m → balForms bar X) : ℕ :=
  Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ Submodule.span ℤ (Set.range δ)))

def IsPrim (β : balForms bar X) : Prop :=
  ∀ (k : ℕ) (β' : balForms bar X), β = k • β' → k = 1

def maxMult (q : ℕ) (φ : InvFun O) : ℕ∞ :=
  ⨆ (X : Type) (_ : AddCommGroup X) (_ : Module O X) (_ : Module.Finite O X) (_ : Module.Projective O X)
    (_ : Module.finrank O X ≤ q) (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ)
    (_ : LinearIndependent ℤ δ) (_ : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)),
    ((cellMult bar fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) : ℕ∞)

variable {bar}

theorem not_isPrim_zero : ¬ IsPrim bar (0 : balForms bar X) := fun h => by
  have := h 0 0 (by simp)
  exact zero_ne_one this

end Mult

end GlobalTheory.PolFan
