module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)

def IsAddLawHom (m : schemeOver W ⊗ schemeOver W ⟶ schemeOver W) : Prop :=
  ∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (hT : IsUnimodularSol (W.map ρ) T),
    (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧
      Proportional T (diagXYZ (W.map ρ).toProjective P Q)) →
    ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP →
      y.left = ptHom W ρ Q hQ → (lift x y ≫ m).left = ptHom W ρ T hT

variable [W.IsElliptic]

theorem isAddLawHom_mul : IsAddLawHom W μ[schemeOver W] := by
  intro A _ ρ P Q T hP hQ hT h x y hx hy
  let : Algebra R A := ρ.toAlgebra
  obtain rfl : x = ptOver W (A := A) P hP := Over.OverMorphism.ext hx
  obtain rfl : y = ptOver W (A := A) Q hQ := Over.OverMorphism.ext hy
  exact congrArg (·.left) (ptOver_mul_ptOver W (A := A) hP hQ hT ⟨h.1, h.2⟩)

theorem ptHom_grpObj_inv {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hP.neg :=
  (congrArg (_ ≫ ·) (inv_left W)).trans (ptHom_negHom W ρ P hP)


omit [W.IsElliptic] in
theorem exists_grpObj_isAddLawHom (hΔ : IsUnit W.Δ) :
    ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ η[schemeOver W].left = zero W ∧
      IsAddLawHom W μ[schemeOver W] ∧
      ∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P),
        ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P),
          ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN :=
  haveI : W.IsElliptic := ⟨hΔ⟩
  ⟨grpObj W, isCommMonObj W, one_left W, isAddLawHom_mul W,
    fun _ _ ρ P hP => ⟨hP.neg, ptHom_grpObj_inv W ρ P hP⟩⟩

end GlobalTheory.WeierstrassCurve
