module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeRelationOfPullbackIsoThickening
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.multiplicative_relation_of_pullback_iso_thickening : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ Y Y₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : Y ⟶ Sp R) (i : X₀ ⟶ X) (i' : Y₀ ⟶ Y) (φ₀ φ₁ φ₂ : Y ⟶ X) (w₀ : φ₀ ≫ s = s' ≫ spMap (RingHom.id R)) (w₁ : φ₁ ≫ s = s' ≫ spMap (RingHom.id R)) (w₂ : φ₂ ≫ s = s' ≫ spMap (RingHom.id R)) (ψ₀ ψ₁ ψ₂ : Y₀ ⟶ X₀) (L : LB X₀) (hL : L.IsLB) (u : C1 (smallG i L ⋙ OAff s)), IsThick I s' i' → IsBasis (smallG i L) → IsLift s i L u → ψ₀ ≫ i = i' ≫ φ₀ → ψ₁ ≫ i = i' ≫ φ₁ → ψ₂ ≫ i = i' ≫ φ₂ → GlobalTheory.CechPic.pull ψ₀ (cls L hL) = GlobalTheory.CechPic.pull ψ₁ (cls L hL) + GlobalTheory.CechPic.pull ψ₂ (cls L hL) → ∃ (T : Type) (_ : Category.{0} T) (_ : Quiver.IsThin T) (H : T ⥤ AffOp Y) (K₀ K₁ K₂ : T ⥤ (Small i L)ᵒᵖ) (le₀ : ∀ t, (H.obj t).unop.1 ≤ φ₀ ⁻¹ᵁ ((smallG i L).obj (K₀.obj t)).unop.1) (le₁ : ∀ t, (H.obj t).unop.1 ≤ φ₁ ⁻¹ᵁ ((smallG i L).obj (K₁.obj t)).unop.1) (le₂ : ∀ t, (H.obj t).unop.1 ≤ φ₂ ⁻¹ᵁ ((smallG i L).obj (K₂.obj t)).unop.1) (v : C0 (H ⋙ OAff s')), IsBasis H ∧ (∀ t, IsUnit (v t)) ∧ MulRel I (pullMap w₀ _ H K₀ le₀) (pullMap w₁ _ H K₁ le₁) (pullMap w₂ _ H K₂ le₂) u v := by
  first | exact @GlobalTheory.LBLift.IsoRel.mulRel_of_iso | exact GlobalTheory.LBLift.IsoRel.mulRel_of_iso | (intros; apply GlobalTheory.LBLift.IsoRel.mulRel_of_iso <;> assumption)
