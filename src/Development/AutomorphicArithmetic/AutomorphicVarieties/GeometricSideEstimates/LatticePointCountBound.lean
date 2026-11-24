module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.DerivSimilitudeCharAtOneEqTrace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PointEvaluationMultiplicativeTsum
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

private theorem gauss_sum_determines_value_and_deviation {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (L : AddSubgroup (Fin a → Af E)) (g g' : GA E a)
    (hR : gsum L gauss g' = gsum L gauss g)
    (hC : ∀ F : (Fin a → Cinf E) → ℂ, gsum L F g' = gsum L F g) :
    fn L g' = fn L g ∧ dev L g' = dev L g := by
  have hT : Th L g' = Th L g := hR
  have hm : ∀ P, mean L P g' = mean L P g := fun P => by
    unfold mean
    rw [hT, hC]
  have hmom : mom L g' = mom L g := by
    apply Subtype.ext
    ext i j w
    exact hm _
  refine ⟨?_, ?_⟩
  · unfold fn
    rw [hT]
  · unfold dev
    rw [hmom]

theorem UpperTheory.lattice_point_count_bound :
    FnInv := by
  intro E _ _ _ a ha L
  refine ⟨fun γ t g => gauss_sum_determines_value_and_deviation L _ _ ((UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).1 γ t g)
      (fun F => (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ F).1 γ t g),
    fun U hU hL u hu g => gauss_sum_determines_value_and_deviation L _ _ ((UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.2 U hU hL u hu g)
      (fun F => (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ F).2.2 U hU hL u hu g), fun k g => ?_⟩
  have h1 := (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.1 g (Unitary.toUnits k)
  have hk : (Unitary.toUnits k : GL (Fin a) (Cinf E)).val = k.1 := rfl
  have hs : sc k.1 = 1 := (UpperTheory.deriv_similitudeChar_at_one_eq_trace E a).2.2.2.2 k
  have hq := UpperTheory.geometric_side_quadraticForm_identity E a
  unfold Th
  rw [h1]
  unfold gsum
  refine tsum_congr fun v => ?_
  rw [hk, hs, one_smul]
  unfold gauss
  rw [hq.2.2.1, (Unitary.mem_iff.1 k.2).2, hq.1]
