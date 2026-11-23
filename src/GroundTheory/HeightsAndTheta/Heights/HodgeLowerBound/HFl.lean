module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFSGeomDegPos
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PGrassHeightE
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem GrassmannianHeightZTwo.proof (hZ2 : SuccessiveMinimaUpperBound) (hPush : FlagGrassPush.Statement)
    (hDeg : HilbertSamuel.FSGeomDegPos.Statement) : GrassmannianHeightZTwo.Statement := by
  intro II Ψ _ _ N j cf e hII hN hj1 hjN hJ hZ
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · have hmu : muPoly Ψ N j = 0 := by
      unfold muPoly
      exact Finset.sum_eq_zero fun p _ => (IsEmpty.false p.1).elim
    have hFA : FA Ψ N j cf = 0 := by
      unfold FA
      rw [hmu, zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [hFA, Fintype.card_eq_zero]
    simp [hFl]
  · set f := Fintype.card Ψ with hfdef
    have hf : 1 ≤ f := Fintype.card_pos
    have hP := hPush II Ψ N j cf hII hN hj1 hjN
    have hG := GrassHeightE.full hZ2 f j (N - j) e hf hZ II hII
    have hD : 0 < geomDeg (grassIdeal f j (N - j)) (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j)))
        (f * j * (N - j)) :=
      hDeg (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j)) (f * j * (N - j))
        (GrassArithVar.full f j (N - j) hf)
    have hJ' : (0 : ℝ) < (Jint Ψ N j cf : ℝ) := Rat.cast_pos.mpr hJ
    change -hFl Ψ N II (FA Ψ N j cf) * geomDeg (grassIdeal f j (N - j))
        (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) (f * j * (N - j)) =
      (Jint Ψ N j cf : ℝ) * II (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j))
        (f * j * (N - j) + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) at hP
    change -hFl Ψ N II (FA Ψ N j cf) ≤ ((f * j * (N - j) + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (f : ℝ) * e
    have h1 := mul_le_mul_of_nonneg_left hG hJ'.le
    refine le_of_mul_le_mul_right ?_ hD
    rw [hP]
    calc _ ≤ _ := h1
      _ = _ := by ring

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
