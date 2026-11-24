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

section Sub

variable {O : Type} [CommRing O] (bar : O → O) (q : ℕ)

def LinOnCells (φ χ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ → χ.LinearOn γ

def Subordinate (φ' φ : InvFun O) : Prop :=
  ∀ χ : InvFun O, LinOnCells bar q φ χ → LinOnCells bar q φ' χ

def SimpLab (φ lab : InvFun O) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ k : ℕ, 0 < k → lab.evalZ ((k : ℤ) • β) = lab.evalZ β) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), IsCell bar φ δ ∧ LinearIndependent ℤ δ ∧
        Function.Injective (fun i => lab.evalZ (δ i)) ∧
        ∀ j, ∃ a : Fin m' → ℝ, (∀ i, 0 ≤ a i) ∧ toReal (γ j) = ∑ i, a i • toReal (δ i)

variable {bar q}

theorem linOnCells_self (φ : InvFun O) : LinOnCells bar q φ φ := fun _ _ _ _ _ _ _ _ h => h.linear

theorem Subordinate.refl (φ : InvFun O) : Subordinate bar q φ φ := fun _ h => h

theorem Subordinate.trans {φ'' φ' φ : InvFun O} (h₁ : Subordinate bar q φ'' φ') (h₂ : Subordinate bar q φ' φ) :
    Subordinate bar q φ'' φ := fun χ h => h₁ χ (h₂ χ h)

theorem Subordinate.linearOn {φ' φ : InvFun O} (h : Subordinate bar q φ' φ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar φ' γ) : φ.LinearOn γ :=
  h φ (linOnCells_self φ) X hX m γ hγ

end Sub

section Inhab

def zeroFun (O : Type) [CommRing O] : InvFun O where
  toFun _ _ := 0
  inv _ _ _ _ _ := rfl
  zero _ := rfl

@[simp] theorem zeroFun_evalZ {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    (β : LinearMap.BilinForm ℤ X) : (zeroFun O).evalZ β = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  simp only [InvFun.evalZ, (zeroFun O).eval_eq hr]
  rfl

end Inhab

end GlobalTheory.PolFan
