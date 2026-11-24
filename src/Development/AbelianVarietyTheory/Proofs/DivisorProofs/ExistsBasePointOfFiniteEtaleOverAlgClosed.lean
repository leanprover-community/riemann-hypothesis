module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.FinEtPoints

theorem epi_spMap_field (k L : Type) [Field k] [Field L] (f : k →+* L) : Epi (spMap f) := by
  exact Flat.epi_of_flat_of_surjective _

theorem exists_point_of_finite_etale (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K]
    [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀) : IsFinite p → Etale p →
    ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) →
      ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := by
  intro hf he x hx
  let Ω := AlgebraicClosure K
  let i : K →+* Ω := algebraMap K Ω
  let j : k₀ →+* K := algebraMap k₀ K
  let t : Sp Ω ⟶ Sp k₀ := spMap (i.comp j)
  have ht : spMap i ≫ spMap j = t := by
    simp only [t, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hti : Epi t := epi_spMap_field _ _ _
  have hii : Epi (spMap i) := epi_spMap_field _ _ _
  obtain ⟨zΩ⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨z₀⟩ : Nonempty (Sp k₀) := inferInstance
  obtain ⟨hfin₁, hc₁⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t zΩ
  obtain ⟨hfin₀, hc₀⟩ := GlobalTheory.FinEt.card_points_eq_finrank p (𝟙 (Sp k₀)) z₀
  let F : {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _} → {y : Sp Ω ⟶ X // y ≫ p = t} :=
    fun y ↦ ⟨t ≫ y.1, by rw [Category.assoc, y.2, Category.comp_id]⟩
  have hFi : Function.Injective F := by
    intro a b hab
    exact Subtype.ext ((cancel_epi t).mp congr(($hab).1))
  have hcard : Nat.card {y : Sp Ω ⟶ X // y ≫ p = t} ≤ Nat.card {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _} := by
    rw [hc₁, hc₀, Subsingleton.elim (t zΩ) ((𝟙 (Sp k₀) : Sp k₀ ⟶ Sp k₀) z₀)]
  have hFb : Function.Bijective F := hFi.bijective_of_nat_card_le hcard
  obtain ⟨⟨x₀, hx₀⟩, hF⟩ := hFb.2 ⟨spMap i ≫ x, by rw [Category.assoc, hx, ht]⟩
  refine ⟨x₀, hx₀, ?_⟩
  have h1 : spMap i ≫ (spMap j ≫ x₀) = spMap i ≫ x := by
    rw [← Category.assoc, ht]
    exact congr(($hF).1)
  exact (cancel_epi (spMap i)).mp h1

end GlobalTheory.FinEtPoints
