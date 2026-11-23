module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftNefBig
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefPlusAmpleDegree
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaSection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbSemipos
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ZcombIsConjInvariantH
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace ShiftedNefBig

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoNum_one_add (W : Ideal (MRing ι)) (a b : K → ℤ) (q : ℤ) :
    geoNum 1 W (fun _ => q • a + b) = q * geoNum 1 W (fun _ => a) + geoNum 1 W (fun _ => b) := by
  simp only [geoNum]
  split_ifs with h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc]
  · simp

theorem geoNum_one_one_nonneg (W : Ideal (MRing ι)) : 0 ≤ geoNum 1 W (fun _ => (1 : K → ℤ)) := by
  simp only [geoNum]
  split_ifs with h
  · refine Finset.sum_nonneg fun k _ => mul_nonneg zero_le_one ?_
    refine finsum_nonneg fun W' => finsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) ?_
    split_ifs <;> positivity
  · exact le_rfl

end ShiftedNefBig


open ShiftedNefBig in
theorem ShiftNefBig.proof (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement)
    (hB : NefPlusAmpleDegree.Statement) : ShiftNefBig.Statement := by
  intro K _ ι _ Ω _ y D A P0 _ har _ hP0 hs hnef hc q _
  have ha : (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a = (q : ℤ) • A.a + 1 := by
    show (q : ℤ) • A.a + (1 : ℤ) • (fsH ι).a = _
    rw [one_smul]
    rfl
  refine ⟨hP0, PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hs (Nat.cast_nonneg q) zero_le_one,
    HermLine.zcomb_isConjInvariantH hc (fsH_isConjInvariantH ι) _ _, ?_, ?_⟩
  · rw [ha]
    intro W hW hPW hch hdim
    rw [geoNum_one_add]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg q) (hnef W hW hPW hch hdim)) (geoNum_one_one_nonneg W)
  · rw [ha]
    exact hB K ι (mCoordIdeal y) D A.a har (nefOnGenericDeg_of_semipos NefOnGenericOfSemipos.proof hD hP0 hs) q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
