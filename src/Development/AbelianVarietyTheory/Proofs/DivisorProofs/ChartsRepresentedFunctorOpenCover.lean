module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem charts_represented_open_cover : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1) (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∀ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) → ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro F Ix U x hinj hW hcov B x₀ hrep
  have uniq : ∀ (T : Scheme.{0}) (g g' : T ⟶ B), F.map g.op x₀ = F.map g'.op x₀ → g = g' :=
    fun T g g' h => (hrep T (F.map g'.op x₀)).unique h rfl
  choose j hj using fun i => (hrep (U i) (x i)).exists
  refine ⟨j, fun i => ?_, fun p => ?_, hj⟩
  · obtain ⟨W, hWi⟩ := hW i B x₀

    have hjW : Set.range (j i) ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      exact ((hWi (U i) (j i)).1 ⟨𝟙 _, by rw [hj i]; simp⟩) q
    obtain ⟨u, hu⟩ := (hWi W.toScheme W.ι).2 (fun q => by
      have : W.ι q ∈ Set.range W.ι := ⟨q, rfl⟩
      rwa [Scheme.Opens.range_ι] at this)
    set l := IsOpenImmersion.lift W.ι (j i) hjW with hldef
    have hl : l ≫ W.ι = j i := IsOpenImmersion.lift_fac _ _ _
    have huj : u ≫ j i = W.ι := by
      apply uniq
      rw [op_comp, Functor.map_comp_apply, hj i, hu]
    have hlu : l ≫ u = 𝟙 _ := by
      apply hinj i
      rw [op_comp, Functor.map_comp_apply, ← hu, ← Functor.map_comp_apply, ← op_comp, hl, hj i]
      simp
    have hul : u ≫ l = 𝟙 _ := by
      rw [← cancel_mono W.ι, Category.assoc, hl, huj, Category.id_comp]
    haveI : IsIso l := ⟨⟨u, hlu, hul⟩⟩
    rw [← hl]
    infer_instance
  · obtain ⟨i, Y, a, u, ⟨q, rfl⟩, ha⟩ := hcov B x₀ p
    refine ⟨i, u q, ?_⟩
    have : a = u ≫ j i := by
      apply uniq
      rw [ha, op_comp, Functor.map_comp_apply, hj i]
    rw [this]
    rfl

end GlobalTheory
