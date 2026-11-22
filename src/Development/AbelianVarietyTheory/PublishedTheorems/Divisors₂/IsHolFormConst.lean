module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

variable (F : Type) [Field F] [NumberField F]

abbrev FracId : Type := (FractionalIdeal (𝓞 F)⁰ F)ˣ

variable {F}

abbrev FracId.elt (𝔠 : FracId F) : Submodule (𝓞 F) F := (𝔠 : FractionalIdeal (𝓞 F)⁰ F)

def HasGen {X : Scheme.{0}} (L : LB X) : Prop := ∃ t : L.Gen, t.IsGen

attribute [instance] Obj.grp Obj.comm

namespace Obj

variable {𝔠 : FracId F} {S S' : Scheme.{0}}

variable {R R' : Type} [CommRing R] [CommRing R']

abbrev Lie (X : Obj F 𝔠 (Sp R)) : Type := Serre.Lie X.rm

@[reducible] def lieModule (X : Obj F 𝔠 (Sp R)) : Module (R ⊗[ℤ] 𝓞 F) X.Lie :=
  TensorProduct.Algebra.module

end Obj

def rapObj (𝔠 : FracId F) : ObjClass 𝔠 := fun _ _ X ↦ X.IsRapoport

@[ext] structure Rule {𝔠 : FracId F} (Q : ObjClass 𝔠) (R₀ : Type) [CommRing R₀] (k : ℕ) where

  val : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), Q R X → X.DetGen → R
  homog : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (hX : Q R X) (δ δ' : X.DetGen) (c : R),
    δ'.1 = c • δ.1 → c ^ k * val R X hX δ' = val R X hX δ
  baseChange : ∀ (R R' : Type) [CommRing R] [Algebra R₀ R] [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R')
    (X : Obj F 𝔠 (Sp R)) (hX : Q R X) (X' : Obj F 𝔠 (Sp R')) (hX' : Q R' X') (φ : X'.A.left ⟶ X.A.left)
    (δ : X.DetGen) (δ' : X'.DetGen), X'.IsPullBy X (spMap (σ : R →+* R')) φ →
    Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1 → val R' X' hX' δ' = σ (val R X hX δ)

namespace Rule

variable {𝔠 : FracId F} {Q Q' : ObjClass 𝔠} {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] {k l : ℕ}

end Rule

variable (F) in
def halfSpace : Set ((F →+* ℝ) → ℂ) := {z | ∀ τ, 0 < (z τ).im}

def qPower (ξ : F) (z : (F →+* ℝ) → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ τ, (τ ξ : ℂ) * z τ)

end GlobalTheory.RealMult
