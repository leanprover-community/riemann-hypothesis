module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HderEntry
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LgCpt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem UpperTheory.RealTr.kerReg :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T → KerReg E k := by
  intro n _ _ μ _ E k val T hM
  obtain ⟨m, c, w, g, ks, hks, hsum, -⟩ := hM
  have hmem : ∀ x : Mat n, x ∈ GLs n ↔ IsUnit x := (UpperTheory.RealTr.basic n).2.1
  have hG : ∀ y : G n, (y : Mat n) ∈ GLs n := fun y => (hmem _).2 y.isUnit
  have hfun : (fun y : G n => k (y : Mat n)) = fun y : G n => ∑ i, c i • ks i (y : Mat n) := by
    funext y
    exact hsum _ (hG y)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    refine continuous_finsetSum _ fun i _ => ?_
    have hc : ContinuousOn (ks i) (GLs n) := (hks i).2.1.continuousOn
    exact (hc.comp_continuous Units.continuous_val hG).const_smul (c i)
  · choose R hR using fun i => (hks i).2.2.1
    refine HasCompactSupport.intro (K := {y : G n | lg (y : Mat n) ≤ ∑ i, |R i|})
      (UpperTheory.RealTr.lgCpt n _) ?_
    intro y hy
    simp only [Set.mem_setOf_eq, not_le] at hy
    rw [hsum _ (hG y)]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hle : R i ≤ ∑ j, |R j| :=
      (le_abs_self (R i)).trans
        (Finset.single_le_sum (f := fun j => |R j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    rw [hR i _ (hG y) (lt_of_le_of_lt hle hy), smul_zero]
  · intro y hy k₁ k₂
    have hu : IsUnit ((k₁ : Mat n) * y * (k₂ : Mat n)) :=
      ((Unitary.toUnits k₁).isUnit.mul ((hmem y).1 hy)).mul (Unitary.toUnits k₂).isUnit
    rw [hsum _ ((hmem _).2 hu), hsum _ hy, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hks i).2.2.2.1 y hy k₁ k₂, mul_smul_comm, smul_mul_assoc]
