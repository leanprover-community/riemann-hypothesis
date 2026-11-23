module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Mathlib.Analysis.Asymptotics.Arith
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem hasFDerivAt_of_comp_immersion : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (Φ : E → F) (ψ : E → E) (x : E) (A D : E →L[ℝ] F), HasStrictFDerivAt Φ A (ψ x) → Function.Injective A → ContinuousAt ψ x → HasFDerivAt (fun y => Φ (ψ y)) D x → ∃ P : E →L[ℝ] E, HasFDerivAt ψ P x ∧ A.comp P = D := by
  intro E F _ _ _ _ _ _ Φ ψ x A D hA hinj hψ hD

  obtain ⟨g, hg⟩ := (A : E →ₗ[ℝ] F).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  let L : F →L[ℝ] E := LinearMap.toContinuousLinearMap g
  have hLA : ∀ v, L (A v) = v := fun v => by
    have h := LinearMap.congr_fun hg v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe] at h
    first
      | exact h
      | simpa [L] using h
      | (rw [show (L : F → E) = g from LinearMap.coe_toContinuousLinearMap' g]; exact h)

  have hr : (fun y => Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)) =o[nhds x] (fun y => ψ y - ψ x) :=
    hA.hasFDerivAt.isLittleO.comp_tendsto hψ
  have hs : (fun y => Φ (ψ y) - Φ (ψ x) - D (y - x)) =o[nhds x] (fun y => y - x) :=
    hD.isLittleO
  have hLr : (fun y => L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x))) =o[nhds x] (fun y => ψ y - ψ x) :=
    (L.isBigO_comp _ _).trans_isLittleO hr

  have hu : (fun y => ψ y - ψ x) =O[nhds x] (fun y => y - x) := by
    have h1 := hLr.right_isBigO_add
    have hsum : (fun y => L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)) + (ψ y - ψ x))
        = fun y => L (Φ (ψ y) - Φ (ψ x)) := by
      funext y
      simp only [map_sub, hLA]
      abel
    rw [hsum] at h1
    exact h1.trans ((L.isBigO_comp _ _).trans hD.isBigO_sub)

  have hP : HasFDerivAt ψ (L.comp D) x := by
    rw [hasFDerivAt_iff_isLittleO]
    have hdiff : (fun y => L (Φ (ψ y) - Φ (ψ x) - D (y - x)) - L (Φ (ψ y) - Φ (ψ x) - A (ψ y - ψ x)))
        = fun y => ψ y - ψ x - (L.comp D) (y - x) := by
      funext y
      simp only [map_sub, hLA, ContinuousLinearMap.comp_apply]
      abel
    rw [← hdiff]
    exact ((L.isBigO_comp _ _).trans_isLittleO hs).sub (hLr.trans_isBigO hu)
  refine ⟨L.comp D, hP, ?_⟩
  exact (hA.hasFDerivAt.comp x hP).unique hD

end GlobalTheory
