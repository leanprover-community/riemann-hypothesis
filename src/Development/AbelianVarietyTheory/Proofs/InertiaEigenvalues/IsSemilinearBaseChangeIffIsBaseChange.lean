module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP


open TensorProduct in
theorem _root_.GlobalTheory.BSP.semiBC_iff_isBaseChange (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] (M : Type)
    [AddCommGroup M] [Module A M] (N : Type) [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] (u : M →ₛₗ[algebraMap A B] N) (u' : M →ₗ[A] N)
    (h : ∀ x, u' x = u x) : _root_.GlobalTheory.Prism.SemiBC u ↔ IsBaseChange B u' := by
  constructor
  · intro hu
    refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g => ?_
    letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup B
    let v : M →ₛₗ[algebraMap A B] Q :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun a x => by simp [algebraMap_smul] }
    obtain ⟨w, hw, hw'⟩ := hu Q v
    refine ⟨w, ?_, fun w₂ hw₂ => hw' w₂ fun x => ?_⟩
    · ext x
      simp [h, hw x, v]
    · rw [← h]
      exact LinearMap.congr_fun hw₂ x
  · intro hb Q _ _ v
    letI : Module A Q := Module.compHom Q (algebraMap A B)
    haveI : IsScalarTower A B Q :=
      ⟨fun a b q => by
        show (a • b) • q = algebraMap A B a • b • q
        rw [Algebra.smul_def, mul_smul]⟩
    let g : M →ₗ[A] Q :=
      { toFun := v
        map_add' := v.map_add
        map_smul' := fun a x => by
          rw [v.map_smulₛₗ]
          rfl }
    refine ⟨hb.lift g, fun x => ?_, fun w hw => hb.algHom_ext _ _ fun x => ?_⟩
    · rw [← h, hb.lift_eq]
      rfl
    · rw [hb.lift_eq, h, hw]
      rfl

end GlobalTheory.BSP
