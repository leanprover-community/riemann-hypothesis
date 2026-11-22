module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

@[expose] public section

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.Poinc

def qW {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (y : Fin s → X) : ℤ :=
  ∑ u, ∑ v, W u v * β (y u) (y v)

def PosW {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) : Prop := ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef

def CongMod {X : Type} [AddCommGroup X] (N : ℕ) (x y : X) : Prop := ∃ w, x = y + N • w

section Orbit

variable (O : Type) [CommRing O] {X₀ X : Type} [AddCommGroup X₀] [Module O X₀] [AddCommGroup X] [Module O X]

def IsUnimodMod (N : ℕ) (k : X₀ →ₗ[ℤ] X) : Prop :=
  (∀ (c : O) x, CongMod N (k (c • x)) (c • k x)) ∧ ∃ ε : X ≃ₗ[ℤ] X₀, (N : ℤ) ∣ LinearMap.det (ε.toLinearMap ∘ₗ k) - 1

def orbit (N₁ N : ℕ) (k : X₀ →ₗ[ℤ] X) {ι : Type} (a : ι → X₀) : Set (ι → X) :=
  {μ | ∃ γ : X₀ →ₗ[ℤ] X₀, (∀ (c : O) x, CongMod N (γ (c • x)) (c • γ x)) ∧ (N : ℤ) ∣ LinearMap.det γ - 1 ∧
    (∀ x, CongMod N₁ (γ x) x) ∧ ∀ i, CongMod N (μ i) (k (γ (a i)))}

end Orbit

attribute [instance] FSys.add FSys.mod FSys.fin FSys.proj FSys.freeZ FSys.finZ

structure Supports {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (d : ℕ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {r : ℕ} (γ : Fin r → LinearMap.BilinForm ℤ X) {m : ℕ} (a : Fin m → X) : Prop where
  span : Submodule.span ℤ (Set.range a) = ⊤
  le : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → d * φ.evalZ β ≤ (∑ i, β (a i) (a i) : ℤ)
  eq : ∀ j, d * φ.evalZ (γ j) = (∑ i, γ j (a i) (a i) : ℤ)
  only : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → d * φ.evalZ β = (∑ i, β (a i) (a i) : ℤ) →
    ∃ (k : ℕ) (c : Fin r → ℕ), 0 < k ∧ k • β = ∑ j, c j • γ j

def HasSupports {O : Type} [CommRing O] (bar : O → O) (q : ℕ) (φ : InvFun O) (d : ℕ) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone bar φ γ → ∃ (m : ℕ) (a : Fin m → X), Supports bar φ d γ a

def BddAct {O : Type} [CommRing O] (bar : O → O) : Prop :=
  ∀ c : O, ∃ C : ℤ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
    ∀ x, β (c • x) (c • x) ≤ C * β x x

end GlobalTheory.Poinc
