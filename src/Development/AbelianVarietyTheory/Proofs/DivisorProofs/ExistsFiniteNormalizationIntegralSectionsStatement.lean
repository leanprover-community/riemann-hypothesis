module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfCompEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalizationIntegralSections
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_finite_normalization_integral_sections : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsIntegral S] [IsDominant gp]
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)), IsFinSub gp F →
    ∃ (S' : Scheme.{0}) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  first | exact @GlobalTheory.Mum.exists_finite_of_isFinSub | exact GlobalTheory.Mum.exists_finite_of_isFinSub | (intros; apply GlobalTheory.Mum.exists_finite_of_isFinSub <;> assumption)
