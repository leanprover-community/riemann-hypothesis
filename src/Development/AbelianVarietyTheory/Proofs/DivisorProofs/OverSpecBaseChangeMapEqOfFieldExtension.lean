module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus)

namespace GlobalTheory

theorem baseChange_map_eq_of_fieldExtension : ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f g : V ⟶ W), (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map g → (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map g := by
  intro R k Ω _ _ _ _ _ _ _ V W f g h
  have hu : Spec.map (CommRingCat.ofHom (algebraMap R Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h1 : pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ f.left =
      pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ g.left := by
    have := congrArg (fun φ => φ.left ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) h
    simp only [Over.pullback_map_left, pullback.lift_fst] at this
    exact this
  set s := Spec.map (CommRingCat.ofHom (algebraMap R k)) with hs
  set t := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with ht
  rw [hu] at h1
  have f₁ : Flat t := by
    rw [ht, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField k) _
  have f₂ : Surjective t :=
    ⟨fun y => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have : Epi (pullback.fst (pullback.snd V.hom s) t) := Flat.epi_of_flat_of_surjective _
  have key : pullback.fst V.hom s ≫ f.left = pullback.fst V.hom s ≫ g.left := by
    rw [← cancel_epi (pullback.fst (pullback.snd V.hom s) t)]
    have hc : (pullback.fst (pullback.snd V.hom s) t ≫ pullback.fst V.hom s) ≫ V.hom =
        pullback.snd (pullback.snd V.hom s) t ≫ t ≫ s := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
    have he := pullback.lift_fst _ _ hc
    rw [← Category.assoc, ← Category.assoc, ← he, Category.assoc, Category.assoc, h1]
  apply Over.OverMorphism.ext
  simp only [Over.pullback_map_left]
  apply pullback.hom_ext
  · erw [pullback.lift_fst, pullback.lift_fst]
    exact key
  · erw [pullback.lift_snd, pullback.lift_snd]

end GlobalTheory
