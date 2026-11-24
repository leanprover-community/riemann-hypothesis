module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample.Objects
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ConservationDegreeFormOfExistence
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPtsIntegralPoints
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.LineField

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo Line

section Curve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem inter_constLine_eq [Nonempty K] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) {W : Ideal (MRing ι)} (hW : IsArithVar W 1)
    (hH : IsMultiHomogIdeal W) (hdeg : 0 < degC W) (M : ℝ) (hM : 0 < M) :
    I W 1 ![constLine M hM] = Real.log M * degC W := by
  obtain ⟨c, hc⟩ := exists_chartMon_notMem hW
  rw [inter_eq_recR I hI hW (isSmoothHerm_constLine M hM) (d := 0) (fun k ↦ rfl)
    (isMultiHomog_chartMon c 0) (hc 0), chartMon_zero, recR_one]
  have h : logNorm (constLine (ι := ι) M hM) 1 = fun _ ↦ -Real.log M := by
    funext z
    simp [logNorm, constLine, Real.log_inv]
  have hfin : Finite (projPts W) := by
    rw [degC_eq_card_projPts] at hdeg
    exact (Nat.card_pos_iff.mp hdeg).2
  have key : ∀ φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ, ptsIntegral W φ (fun _ ↦ (1 : ℝ)) = degC W := by
    intro φ
    obtain rfl : φ = Fin.elim0 := funext fun j ↦ j.elim0
    rw [PtsIntegralPoints.homogProof K ι W (fun _ ↦ 1) hH hfin (fun _ _ _ _ ↦ rfl),
      degC_eq_card_projPts]
    have := Fintype.ofFinite (projPts W)
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  unfold arInt
  rw [h, Inter.Conservation.ptsIntegral_const, key]
  ring

end Curve

section Point

def ptIdeal : Ideal (MRing (PBlk 2)) := orbitIdeal samplePoint

end Point

section Shift


end Shift

section Main

end Main

end GroundTheory.Heights₂.Heights.LowerBoundFree
