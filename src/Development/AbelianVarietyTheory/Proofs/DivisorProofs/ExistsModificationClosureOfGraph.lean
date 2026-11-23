module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralImageOfField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_modif_graph : ∀ (R : Type) [CommRing R] [IsDomain R] (o : Type) [CommRing o] (b : o →+* R) (Z : Scheme.{0}) (s : Z ⟶ Sp o), IsProper s → ∀ y : Sp (FractionRing R) ⟶ Z, y ≫ s = jK R ≫ spMap b → ∃ (M : Modif R) (h : M.S ⟶ Z), M.gp ≫ h = y ∧ h ≫ s = M.π ≫ spMap b := by
  intro R _ _ o _ b Z s hs y hy
  let ℓ : Sp (FractionRing R) ⟶ pullback s (spMap b) := pullback.lift y (jK R) hy
  have : QuasiCompact ℓ := inferInstance
  have : IsProper (pullback.snd s (spMap b)) := inferInstance
  refine ⟨{ S := ℓ.image
            π := ℓ.imageι ≫ pullback.snd s (spMap b)
            proper := inferInstance
            integral := isIntegral_image_of_field ℓ
            gp := ℓ.toImage
            gp_π := by rw [ℓ.toImage_imageι_assoc, pullback.lift_snd]
            dominant := inferInstance }, ℓ.imageι ≫ pullback.fst s (spMap b), ?_, ?_⟩
  · show ℓ.toImage ≫ ℓ.imageι ≫ pullback.fst s (spMap b) = y
    rw [ℓ.toImage_imageι_assoc, pullback.lift_fst]
  · show (ℓ.imageι ≫ pullback.fst s (spMap b)) ≫ s = (ℓ.imageι ≫ pullback.snd s (spMap b)) ≫ spMap b
    rw [Category.assoc, Category.assoc, pullback.condition]

end GlobalTheory.Mum
