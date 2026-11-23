module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfPowEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem isActOf_of_fibreIso : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) [IsIso f] (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt).left = (translT A' θ'.pt).left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (σ σ' : LB.Sec (LPow A' L' k T')) (τ τ' : LB.Sec (LPow A L k T)) (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ q z J') (hσ' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ' (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ' q z J') (hact : IsActOf A' L' k θ' σ σ'), IsActOf A L k θ τ τ' := by
  intro S S' A A' _ _ L L' hL hL' T T' f _ k θ θ' Ψ hT H σ σ' τ τ' hσ hσ' hact
  refine GlobalTheory.ThetaNu.isActOf_of_sval hL fun y J hJ => ?_
  choose J' hJ' using fun χ : (T ⊗ A).left ⟶ A'.left => exists_chart hL' (χ y)
  have gJ' : Good L' y J' := hJ'
  have e1 := hσ' _ (inv f) y J J' hJ gJ'
  have e2 := twist_val hact (inv f) y gJ'
  have e3 := H _ (inv f) y J J' hJ gJ'
  have e4 := hσ _ (inv f ≫ (translT A' θ'.pt).left) y J J' hJ gJ'
  have c : (inv f ≫ (translT A' θ'.pt).left) ≫ f = 𝟙 _ ≫ (translT A θ.pt).left := by
    rw [Category.assoc, ← hT, ← Category.assoc, IsIso.inv_hom_id]
  rw [IsIso.inv_hom_id] at e1 e3
  rw [c] at e4
  rw [e1, e2, e4, e3]
  generalize Ψ (inv f ≫ (translT A' θ'.pt).left) y J J' ^ k = a
  generalize Ψ (inv f) y J J' ^ k = b
  generalize val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ (inv f) y J' = v
  generalize sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ
    (inv f ≫ (translT A' θ'.pt).left) y J' = w
  rw [Units.val_mul, Units.val_mul]
  linear_combination (-(b.val * v.val * w)) * a.mul_inv

end GlobalTheory.ThetaMove
