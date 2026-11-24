module

public import Development.EtaleCohomology.EtaleSheaves.SysOf
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.HasLimPf

theorem hasLimit_of_affine {K : Type} [SmallCategory K] (F : K ⥤ Scheme.{0}) (hF : ∀ k, IsAffine (F.obj k)) :
    HasLimit F := by
  have : HasLimit (F ⋙ Scheme.Γ.rightOp) := inferInstance
  have : PreservesLimitsOfSize.{0, 0} Scheme.Spec.{0} := ΓSpec.adjunction.rightAdjoint_preservesLimits
  have : HasLimit (F ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec) :=
    HasLimit.mk ⟨_, isLimitOfPreserves Scheme.Spec (limit.isLimit (F ⋙ Scheme.Γ.rightOp))⟩
  have : ∀ k, IsIso ((Functor.whiskerLeft F ΓSpec.adjunction.unit).app k) := fun k => by
    have := hF k
    dsimp; infer_instance
  have : IsIso (Functor.whiskerLeft F ΓSpec.adjunction.unit) := NatIso.isIso_of_isIso_app _
  exact hasLimit_of_iso (asIso (Functor.whiskerLeft F ΓSpec.adjunction.unit)).symm

def Loc : Prop := ∀ {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (j₀ : J),
  (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) →
  (∀ U : (D.obj j₀).Opens, IsAffineOpen U → HasLimit (opensDiagram D j₀ U)) → HasLimit (Over.forget j₀ ⋙ D)

theorem HasLim_of (hL : Loc) : LateralTheory.E.SysPf.HasLim := by
  intro J _ _ D hD
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  have : HasLimit (Over.forget j₀ ⋙ D) := hL D j₀ hD (fun U hU => by
    refine hasLimit_of_affine _ (fun j => ?_)
    have := hD j.hom
    exact hU.preimage (D.map j.hom))
  have : HasLimit D := Functor.Initial.hasLimit_of_comp (Over.forget j₀)
  exact ⟨limit.cone D, ⟨limit.isLimit D⟩⟩

end LateralTheory.E.HasLimPf
