module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv

attribute [local instance] Over.cartesianMonoidalCategory

section Lie

variable {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G]
  {OE : Type} [CommRing OE] (io : Out.RingAct G OE)

def lieAct (a : OE) (x : LieG G) : LieG G :=
  ⟨x.1 ≫ io.act a, by
    rw [← Category.assoc, x.2, Category.assoc]
    haveI := io.hom a
    rw [IsMonHom.one_hom]⟩

theorem fst_scale (c : O) :
    ptMap (TrivSqZeroExt.fstHom O O O) ≫ ptMap (dualScale c) = ptMap (TrivSqZeroExt.fstHom O O O) := by

  have h : ((TrivSqZeroExt.fstHom O O O).toRingHom).comp (dualScale c).toRingHom =
      (TrivSqZeroExt.fstHom O O O).toRingHom := by
    refine RingHom.ext fun x => ?_
    simp [dualScale]
  apply Over.OverMorphism.ext
  simp only [ptMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

def lieScale (c : O) (x : LieG G) : LieG G :=
  ⟨ptMap (dualScale c) ≫ x.1, by rw [← Category.assoc, fst_scale]; exact x.2⟩

def IsEig (τ : OE →+* O) (x : LieG G) : Prop := ∀ a : OE, lieAct G io a x = lieScale G (τ a) x

def LieTau (τ : OE →+* O) : Type := {x : LieG G // IsEig G io τ x}

variable (p : ℕ)

end Lie

section Place

variable (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [StarRing OE]

def sig : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE) :=
  Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p])
    (((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom.toIntAlgHom)

structure Place where
  e : ℤ_[p] ⊗[ℤ] OE
  idem : e * e = e
  ne_zero : e ≠ 0
  prim : ∀ f : ℤ_[p] ⊗[ℤ] OE, f * f = f → f * e = f → f = 0 ∨ f = e
  split : sig p OE e ≠ e

variable {p OE}

def Place.bar (w : Place p OE) : ℤ_[p] ⊗[ℤ] OE := sig p OE w.e

def Place.Ow (w : Place p OE) : Submodule ℤ_[p] (ℤ_[p] ⊗[ℤ] OE) :=
  LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)

def Place.n (w : Place p OE) : ℕ := Module.finrank ℤ_[p] w.Ow

variable {O : Type} [CommRing O] [Algebra ℤ_[p] O]

def tauExt (τ : OE →+* O) : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] O) τ.toIntAlgHom (fun _ _ => Commute.all _ _)

def Emb (e : ℤ_[p] ⊗[ℤ] OE) : Set (OE →+* O) := {τ | tauExt τ e = 1}

end Place

section Signature

variable (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G]
  {OE : Type} [CommRing OE] [StarRing OE] (io : Out.RingAct G OE)

def HasVd {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C] (w : Place p OE)
    (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ) : Prop :=
  ∃ b : Module.Basis (Fin w.n) ℤ_[p] w.Ow,
    (v (algebraMap O C (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)) ^ 2)) : ℝ) =
      (v (algebraMap O C (p : O)) : ℝ) ^ ((w.n : ℝ) * vd)

end Signature

section Statement

structure PlaceU (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] where
  e : ℤ_[p] ⊗[ℤ] OE
  idem : e * e = e
  ne_zero : e ≠ 0
  prim : ∀ f : ℤ_[p] ⊗[ℤ] OE, f * f = f → f * e = f → f = 0 ∨ f = e

def PlaceU.n {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] (w : PlaceU p OE) : ℕ :=
  Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))

end Statement

end ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
