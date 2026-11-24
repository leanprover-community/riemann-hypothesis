module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem chartCover_toTerm {S : Scheme.{0}} {A : Over S} (f : A ⟶ Over.mk (𝟙 S)) :
    f = Over.homMk A.hom (by simp) := by
  ext1
  simpa using Over.w f

theorem comp_transl {S : Scheme.{0}} {G A : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) (h : A ⟶ G) :
    h ≫ transl y = h * (Over.homMk A.hom (by simp) ≫ y) := by
  unfold transl
  rw [comp_mul, Category.comp_id, ← Category.assoc]
  congr 2
  exact chartCover_toTerm _

theorem chart_cover : ∀ {R : Type} [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G']
    (N : Near π G') (n : ℕ) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')),
    (∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨
      ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u) →
    ∀ p : G'.left, ∃ j, p ∈ Set.range (N.chart x j) := by
  intro R _ _ S π G' _ N n x H p
  let t : Sp (G'.left.residueField p) ⟶ G'.left := G'.left.fromSpecResidueField p
  let s : Sp (G'.left.residueField p) ⟶ S := t ≫ G'.hom
  let g : Over.mk s ⟶ G' := Over.homMk t rfl
  have hp : g.left (IsLocalRing.closedPoint _) = p := Scheme.fromSpecResidueField_apply p _
  rcases H (G'.left.residueField p) s g with h1 | ⟨i, h2⟩
  · exact ⟨none, by simpa [Near.chart] using h1 ⟨_, hp⟩⟩
  · let c : Over.mk s ⟶ G' := (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i
    obtain ⟨b, hb⟩ := h2 ⟨IsLocalRing.closedPoint _, rfl⟩
    have key : (g * c) ≫ transl (x i)⁻¹ = g := by
      rw [comp_transl]
      have e : (Over.homMk (Over.mk s).hom (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ (x i)⁻¹ = c⁻¹ := by
        rw [GrpObj.comp_inv]; rfl
      rw [e, mul_inv_cancel_right]
    refine ⟨some i, b, ?_⟩
    rw [Near.chart_some, Scheme.Hom.comp_apply, hb]
    have e2 : ((g * c) ≫ transl (x i)⁻¹).left (IsLocalRing.closedPoint _) = p := by rw [key]; exact hp
    rw [Over.comp_left] at e2
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e2

end GlobalTheory.Mum
