module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImage
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

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

theorem _root_.GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z), IsFinite π → IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) →
    CharZero Γ(Y, ⊤) → ∀ I : Y.IdealSheafData, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ ξ : Sp V ⟶ Z, ξ (closedPoint V) ∈ Set.range π →
        ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
          (f : V →+* V') (ψ : Fin d → (Sp V' ⟶ Y)), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧
          IsLocalHom f ∧ (∀ j, ψ j ≫ π = spMap f ≫ ξ) ∧ (idlAlong J ξ).map f = ∏ j, idlAlong I (ψ j) := by
  first | exact @GlobalTheory.NormSheaf.normDescentSheaf | exact GlobalTheory.NormSheaf.normDescentSheaf | (intros; apply GlobalTheory.NormSheaf.normDescentSheaf <;> assumption)
