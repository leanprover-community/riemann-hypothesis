module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem bcMap_hom {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    (bcMap L f).hom = (Over.pullback (spMap (algebraMap K L))).map f.hom := rfl

instance spMap_surjective {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] :
    Surjective (spMap (algebraMap K L)) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

theorem bcMap_left_fst {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f : A ⟶ B) :
    (bcMap L f).hom.left ≫ pullback.fst B.X.hom (spMap (algebraMap K L)) =
      pullback.fst A.X.hom (spMap (algebraMap K L)) ≫ f.hom.left := by
  rw [bcMap_hom]
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem bcMap_injective {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K) :
    Function.Injective (bcMap L : (A ⟶ B) → _) := by
  intro f g h
  have : Epi (pullback.fst A.X.hom (spMap (algebraMap K L))) := Flat.epi_of_flat_of_surjective _
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change f.hom.left = g.hom.left
  rw [← cancel_epi (pullback.fst A.X.hom (spMap (algebraMap K L))), ← bcMap_left_fst, ← bcMap_left_fst, h]

theorem bcMap_add {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B : AbVar K} (f g : A ⟶ B) :
    bcMap L (f + g) = bcMap L f + bcMap L g :=
  Subtype.ext (Functor.map_mul (Over.pullback (spMap (algebraMap K L))) f.hom g.hom)

theorem bcMap_comp {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] {A B C : AbVar K} (f : A ⟶ B)
    (g : B ⟶ C) : bcMap L (f ≫ g) = bcMap L f ≫ bcMap L g :=
  Subtype.ext ((Over.pullback (spMap (algebraMap K L))).map_comp f.hom g.hom)

theorem bcMap_id {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) :
    bcMap L (𝟙 A) = 𝟙 _ :=
  Subtype.ext ((Over.pullback (spMap (algebraMap K L))).map_id A.X)

theorem bcMap_functorial : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B C : AbVar K),
    (∀ f g : A ⟶ B, bcMap L (f + g) = bcMap L f + bcMap L g) ∧
    (∀ (f : A ⟶ B) (g : B ⟶ C), bcMap L (f ≫ g) = bcMap L f ≫ bcMap L g) ∧ bcMap L (𝟙 A) = 𝟙 _ ∧
    Function.Injective (bcMap L : (A ⟶ B) → _) :=
  fun _ _ L _ _ A B _ => ⟨bcMap_add L, bcMap_comp L, bcMap_id L A, bcMap_injective L A B⟩

end GlobalTheory.AV.AbVar

end
