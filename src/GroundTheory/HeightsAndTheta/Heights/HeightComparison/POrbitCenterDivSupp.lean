module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterDivSupp
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterPrime
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterMemIff
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightSubringPrimeMaximal
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSuppLemmas
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem OrbitCenterDivSupp.proof (hMI : OrbitCenterMemIff.Statement)
    (hPr : OrbitCenterPrime.Statement) (hSP : SubringPrimeMaximal.Statement) :
    OrbitCenterDivSupp.Statement := by
  intro ι _ _ n x s a hx hs hsW v hsv
  obtain ⟨c, hc⟩ := exists_chart_ciSup x hx v
  have hrel : Geo.IsRelevant (ι := blockIdx n) (orbitCenter x v) := fun k ↦ ⟨c k, fun h ↦ by
    have := (hMI ι n x hx v _ _ ((geoMultiHomog_iff _ _).mpr
      (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩))).mp h
    simp [evalCone, coordDeg, Pi.single_apply, pow_ite, (hc k).1] at this⟩
  have hW : orbitIdeal x ≤ orbitCenter x v := by
    obtain ⟨S, hS, hspan⟩ := OrbitCurve.isMultiHomogIdeal_orbitIdeal x
    have hSW : ∀ F ∈ S, F ∈ orbitIdeal x := fun F hF ↦ by rw [hspan]; exact Ideal.subset_span hF
    rw [hspan]
    refine Ideal.span_le.mpr fun F hF ↦ ?_
    obtain ⟨d, hd⟩ := hS F hF
    refine Ideal.subset_span ⟨d, hd, ?_⟩
    rw [(mem_orbitIdeal_iff_of_isMultiHomog x F d hd).mp (hSW F hF), map_zero]
    exact Finset.prod_pos fun k _ ↦ pow_pos (hc k).2 _
  refine ⟨⟨⟨hPr ι n x hx v, sup_le hW ((Ideal.span_singleton_le_iff_mem _).mpr hsv)⟩,
    fun Q hQ hle ↦ ?_⟩, hrel⟩
  have := hQ.1
  exact orbitCenter_le_of_le hMI hSP x hx v c hc s a hs hsW Q (le_sup_left.trans hQ.2)
    (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))) hle

end GroundTheory.Heights₂.Heights
