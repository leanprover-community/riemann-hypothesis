module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
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

section Round

variable {O : Type} [CommRing O] (bar : O → O)

def IsMultCell (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ h : IsCell bar φ δ, LinearIndependent ℤ δ ∧ (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) ∧
    cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) = M


variable (O) in
structure FormFamily : Type 1 where

  X : Type
  [acg : AddCommGroup X]
  [mod : Module O X]

  m : ℕ

  δ : Fin m → LinearMap.BilinForm ℤ X

attribute [instance] FormFamily.acg FormFamily.mod

variable {bar}

def FormFamily.Carries (c : FormFamily O) {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ (e : X ≃ₗ[O] c.X) (s : Fin m ≃ Fin c.m), ∀ i, δ i = pull e.toLinearMap (c.δ (s i))


variable (bar) in
def MultCellsAmong (q : ℕ) (φ : InvFun O) (M n : ℕ) : Prop :=
  ∃ R : Fin n → FormFamily O, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → ∃ k, (R k).Carries δ

end Round

end GlobalTheory.PolFan
