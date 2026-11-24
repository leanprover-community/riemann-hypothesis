module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}

abbrev proj {T : Scheme.{0}} (y : (functor A B r).obj (op T)) : y.2.1.subscheme ⟶ T :=
  y.2.1.subschemeι ≫ pullback.snd _ y.1

def gens {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) : Fin r → Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) :=
  fun k => ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ (proj y ⁻¹ᵁ U) (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (e (σ k)))

def bad {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) : Set (PrimeSpectrum Γ(T, U)) :=
  letI := ((proj y).app U).hom.toAlgebra
  Module.support Γ(T, U)
    (Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) ⧸ Submodule.span Γ(T, U) (Set.range (gens e σ y U)))

def goodSet {N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Set T :=
  ⋃ U : T.affineOpens, U.2.fromSpec '' (bad e σ y U)ᶜ

def pbMap {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    ((functor A B r).map a.op y).2.1.subscheme ⟶ y.2.1.subscheme :=
  (y.2.1.comapIso (bc A B y.1 a)).hom ≫ pullback.snd _ _

theorem isPullback_pbMap {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    IsPullback (pbMap a y) (proj ((functor A B r).map a.op y)) (proj y) a := by
  have H : IsPullback (pullback.snd (bc A B y.1 a) y.2.1.subschemeι)
      (pullback.fst (bc A B y.1 a) y.2.1.subschemeι ≫ pullback.snd _ (a ≫ y.1))
      (y.2.1.subschemeι ≫ pullback.snd _ y.1) a :=
    (IsPullback.of_hasPullback (bc A B y.1 a) y.2.1.subschemeι).flip.paste_vert
      (isPullback_bc A B y.1 a)
  refine IsPullback.of_iso H (y.2.1.comapIso (bc A B y.1 a)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [pbMap, Iso.symm_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (Iso.inv_hom_id_assoc _ _).symm
  · change _ = (y.2.1.comapIso (bc A B y.1 a)).inv ≫
      (y.2.1.comap (bc A B y.1 a)).subschemeι ≫ pullback.snd _ (a ≫ y.1)
    rw [Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc]
    simp
  · simp
  · simp

theorem pbMap_fst {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    pbMap a y ≫ y.2.1.subschemeι ≫ pullback.fst _ y.1 =
      ((functor A B r).map a.op y).2.1.subschemeι ≫ pullback.fst _ ((functor A B r).map a.op y).1 := by
  change (y.2.1.comapIso (bc A B y.1 a)).hom ≫ pullback.snd _ _ ≫
      y.2.1.subschemeι ≫ pullback.fst _ y.1 =
    (y.2.1.comap (bc A B y.1 a)).subschemeι ≫ pullback.fst _ (a ≫ y.1)
  rw [← pullback.condition_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  congr 1
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.HilbAff
