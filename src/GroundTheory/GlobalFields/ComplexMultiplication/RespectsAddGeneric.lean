module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsTranslate
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
public import GroundTheory.GlobalFields.ComplexMultiplication.RespectsAddUniversal
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
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialBaseChange

@[expose] public section

namespace GroundTheory.Global

noncomputable section

open Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian IntermediateField

universe u

variable {F : Type u} [Field F]

theorem exists_algebraMap_eq_of_isAlgebraic_ff (E : WeierstrassCurve F) [E.IsElliptic]
    {u : E.toAffine.FunctionField} (hu : IsAlgebraic F u) :
    ∃ a : F, algebraMap F E.toAffine.FunctionField a = u := by
  classical
  have hu' : IsAlgebraic (AlgebraicClosure F) (bcEmb (F' := AlgebraicClosure F) E u) :=
    (hu.algHom (bcEmb (F' := AlgebraicClosure F) E)).tower_top (AlgebraicClosure F)
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic (E.baseChange (AlgebraicClosure F)) hu'
  exact exists_algebraMap_eq_of_bcEmb E hc.symm

variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isGenPt_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsGenPt E' Q := by
  classical
  rcases Q with _ | ⟨x, y, h⟩
  · exact absurd rfl h0
  · by_contra hx
    have hx' : IsAlgebraic F x := not_not.mp hx
    obtain ⟨a, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hx'
    have hy' : IsAlgebraic F y := by
      have := isIntegral_y E' F h.1 (mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap a))
      exact mem_algebraicClosure_iff.1 this
    obtain ⟨b, rfl⟩ := exists_algebraMap_eq_of_isAlgebraic_ff E hy'
    have hc : (E'.baseChange F).toAffine.Nonsingular a b :=
      (E'.toAffine.baseChange_nonsingular (f := Algebra.ofId F E.toAffine.FunctionField)
        (algebraMap F _).injective a b).mp h
    have hQc : (Point.some _ _ h : (E'.baseChange E.toAffine.FunctionField).toAffine.Point) =
        Point.map (Algebra.ofId F E.toAffine.FunctionField) (Point.some _ _ hc) := by
      rw [Point.map_some, Point.some.injEq]; exact ⟨rfl, rfl⟩
    have key := (respectsAdd_iff _).mp hQ (univField E) (univPt₁ E) (univPt₂ E)
      (isGenPt_univPt₁ E) (isGenPt_univPt₂ E) (isGenPt_univPt₁₂ E)
    have hconst : ∀ (σ : E.toAffine.FunctionField →ₐ[F] univField E),
        Point.map σ (Point.some _ _ h) =
          Point.map (Algebra.ofId F (univField E)) (Point.some _ _ hc) := fun σ => by
      rw [hQc, Point.map_map]
      have e : σ.comp (Algebra.ofId F E.toAffine.FunctionField) = Algebra.ofId F (univField E) :=
        AlgHom.ext fun z => by
          rw [AlgHom.comp_apply, Algebra.ofId_apply, Algebra.ofId_apply, σ.commutes]
      rw [e]
    rw [hconst, hconst, hconst, left_eq_add] at key
    have := Point.map_injective (W' := E') (Algebra.ofId F (univField E))
      (key.trans (map_zero _).symm)
    exact Point.some_ne_zero hc this

theorem isIsogeny_of_respectsAdd
    {Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point} (hQ : RespectsAdd E E' Q)
    (h0 : Q ≠ 0) : IsIsogeny E E' Q :=
  (isIsogeny_iff Q).mpr ⟨isGenPt_of_respectsAdd hQ h0, hQ⟩

end

end GroundTheory.Global
