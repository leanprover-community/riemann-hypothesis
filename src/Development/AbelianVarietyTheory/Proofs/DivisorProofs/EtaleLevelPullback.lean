module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem isEtLevOver_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T T' : Over S) (l : D.La → (T ⟶ o.A)) (f : T' ⟶ T), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => f ≫ l y) := by
  intro p _ D R _ b N S s o w0 r T T' l f h
  obtain ⟨hadd, hlin, hker, hgeo⟩ := h
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ?_⟩
  · simp only [hadd, MonObj.comp_mul]
  · simp only [hlin, Category.assoc]
  · simp only [hker x hx, MonObj.comp_one]
  · obtain ⟨hinj, hsurj⟩ := hgeo k (x ≫ f.left)
    let e : Over.mk (x ≫ T'.hom) ≅ Over.mk ((x ≫ f.left) ≫ T.hom) :=
      Over.isoMk (Iso.refl _) (by simp [Over.w f])
    have hfac : (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ f =
        e.hom ≫ (Over.homMk (x ≫ f.left) rfl : Over.mk ((x ≫ f.left) ≫ T.hom) ⟶ T) := by
      ext; simp [e]
    refine ⟨fun y hy => hinj y ?_, fun g hg => ?_⟩
    · have h1 : e.hom ≫ (Over.homMk (x ≫ f.left) rfl : Over.mk ((x ≫ f.left) ≫ T.hom) ⟶ T) ≫ l y = 1 := by
        rw [← Category.assoc, ← hfac, Category.assoc]; exact hy
      have h2 := congrArg (fun z => e.inv ≫ z) h1
      simpa [MonObj.comp_one] using h2
    · obtain ⟨y, hy⟩ := hsurj (e.inv ≫ g) (fun c hc => by
        exact (Category.assoc _ _ _).trans (by rw [hg c hc, MonObj.comp_one]))
      refine ⟨y, ?_⟩
      rw [← Category.assoc, hfac, Category.assoc, hy, Iso.hom_inv_id_assoc]

end GlobalTheory.UPel.HT.EtLev
