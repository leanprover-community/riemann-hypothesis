module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ZM.IsGaloisCover

theorem eq_of_local_eq_pullback : ∀ (X Y S Z : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (g : S ⟶ Y) (h₁ h₂ : S ⟶ Z), GlobalTheory.ZM.IsGaloisCover Ga ρ π → (∀ q : ↥(pullback g π), ∃ V : (pullback g π).Opens, q ∈ V ∧ V.ι ≫ pullback.fst g π ≫ h₁ = V.ι ≫ pullback.fst g π ≫ h₂) → h₁ = h₂ := by
  intro X Y S Z π Ga _ ρ g h₁ h₂ h hloc
  have hp : IsPullback (pullback.snd g π) (pullback.fst g π) π g := (IsPullback.of_hasPullback g π).flip
  have : Etale (pullback.fst g π) := MorphismProperty.of_isPullback (P := @Etale) hp h.etale
  have : IsFinite (pullback.fst g π) := MorphismProperty.of_isPullback (P := @IsFinite) hp h.fin
  have : Surjective (pullback.fst g π) := MorphismProperty.of_isPullback (P := @Surjective) hp h.onto
  have e : pullback.fst g π ≫ h₁ = pullback.fst g π ≫ h₂ :=
    Scheme.hom_ext_of_forall _ _ fun q ↦ hloc q
  exact (cancel_epi (pullback.fst g π)).1 e

end GlobalTheory.ZM.IsGaloisCover
