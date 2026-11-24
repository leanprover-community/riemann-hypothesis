module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
noncomputable section
namespace GlobalTheory.KS

def IsDer {R : Type} [CommRing R] (x₀ : R →+* ℂ) (D : R → ℂ) : Prop :=
  (∀ a b, D (a + b) = D a + D b) ∧ ∀ a b, D (a * b) = x₀ a * D b + x₀ b * D a

structure PtDer {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  add : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f + f') = δ W f + δ W f'
  mul : ∀ W, ⊤ ≤ y ⁻¹ᵁ W → ∀ f f', δ W (f * f') = valAt' y W f * δ W f' + valAt' y W f' * δ W f
  res : ∀ W W' (h : W' ≤ W), ⊤ ≤ y ⁻¹ᵁ W' → ∀ f, δ W' (resG X h f) = δ W f

structure LocDer {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp ℂ) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → ℂ)
    (W₀ : X.Opens) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)) : Prop where
  add : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f'
  mul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f
  res : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = resG Y (fun _ hy => h hy) (d W f)
  base : ∀ W, W ≤ W₀ → ∀ r, d W (constFn p W r) = constFn q (m ⁻¹ᵁ W) (D r)
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}

def dom (m : A₀.left ⟶ X) (W : X.Opens) : Set (Fin g → ℂ) := {z | ⊤ ≤ ((u.ex z).left ≫ m) ⁻¹ᵁ W}

def fn (m : A₀.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) (z : Fin g → ℂ) : ℂ := valAt' ((u.ex z).left ≫ m) W f

structure GoodU (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop where
  ah : u.IsAH Hm χ
  tan₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v
  tan₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v
  endo : ∀ f : A₀ ⟶ A₀, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f
  sec : ∀ (n : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ

structure KSRel {R : Type} [CommRing R] (p : X ⟶ Sp R) (m : A₀.left ⟶ X) (D : R → ℂ) (Θ : Matrix (Fin g) (Fin g) ℂ)
    (s : (Fin g → ℂ) → ∀ W : X.Opens, Γ(X, W) → ℂ) : Prop where
  der : ∀ z, PtDer ((u.ex z).left ≫ m) (s z)
  base : ∀ z r, s z ⊤ (constFn p ⊤ r) = D r
  hol : ∀ W f, DifferentiableOn ℂ (fun z => s z W f) (dom u m W)
  per : ∀ (l : u.Λ) W f, ∀ z ∈ dom u m W,
    s (z + l) W f = s z W f + fderiv ℂ (fn u m W f) z (Θ.mulVec (star (l : Fin g → ℂ)))

def IsSymm (Hm Θ : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ z w, hermForm Hm (Θ.mulVec (star z)) w = hermForm Hm (Θ.mulVec (star w)) z

def Comm (Θ : Matrix (Fin g) (Fin g) ℂ) (F : (Fin g → ℂ) → (Fin g → ℂ)) : Prop :=
  ∀ z, F (Θ.mulVec (star z)) = Θ.mulVec (star (F z))

def IsConst (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (A₀ : Over (Sp ℂ)) [GrpObj A₀] (ρ : A'.left ⟶ A₀.left)
    (j : A₀.left ⟶ A'.left) : Prop :=
  IsGrpPullback A' A₀ (spMap (algebraMap ℂ (DualNumber ℂ))) ρ ∧
    IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j ∧ j ≫ ρ = 𝟙 _
end GlobalTheory.KS
end
