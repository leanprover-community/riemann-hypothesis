module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.isFinite_of_isPullback_fpqc :
    ∀ {X Y X' Y' : Scheme.{0}} (a : X' ⟶ X) (q : X' ⟶ Y') (p : X ⟶ Y) (t : Y' ⟶ Y), IsPullback a q p t → Surjective t → Flat t → QuasiCompact t → IsFinite q → IsFinite p := by
  intro X Y X' Y' a q p t h h₁ h₂ h₃ hq
  have := GlobalTheory.isAffineHom_descendsAlong_fpqc.{0}
  have ht : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) t :=
    ⟨⟨h₁, h₂⟩, h₃⟩
  have hA : IsAffineHom p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) h.flip ht inferInstance
  have hU : UniversallyClosed p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip ht inferInstance
  have hL : LocallyOfFiniteType p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip ht inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).2
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hU, hA⟩, hL⟩
