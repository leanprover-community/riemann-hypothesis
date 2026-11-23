module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitLocalSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartRing
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMax
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartResidue
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMult
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalLengthPlaces
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterChart
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPlaceCentredSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartTerm
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem OrbitLocalSum.proof (hR : OrbitChartRing.Statement) (hM : OrbitChartMax.Statement)
    (hF : OrbitChartResidue.Statement) (hU : OrbitChartMult.Statement)
    (hP : LocalLengthPlaces.Statement) (hC : OrbitCenterChart.Statement)
    (hS : PlaceCentredSum.Statement) (hT : OrbitChartTerm.Statement) :
    OrbitLocalSum.Statement := by
  intro ι _ _ _ n A x s hx hs V hV
  obtain ⟨hVmin, hVrel⟩ := id hV
  choose c hc using hVrel
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hxc : ∀ k, x k (c k) ≠ 0 := fun k h ↦ hc k (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h]))
  obtain ⟨hft, hfr⟩ := hR ι n x c hxc
  have := hM ι n A x s hx hs V hV c hc
  obtain ⟨hf0, hterm⟩ := hT ι n A x s hs c hxc
  let _ : Algebra (ratioField x) (coordField x) :=
    (IntermediateField.inclusion (ratioField_le_coordField x)).toRingHom.toAlgebra
  have hset : {v : FinitePlace (coordField x) | orbitCenter x v = V} =
      {v : FinitePlace (coordField x) | AbsCentredAt (chartRing x c) (chartPoint x c V)
        fun u ↦ v (algebraMap (ratioField x) (coordField x) u)} :=
    Set.ext fun v ↦ hC ι n A x s hx hs V hV c hc v
  have hsum : ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
        -Real.log (v (algebraMap (ratioField x) (coordField x) (chartEval x c s))) :=
    finsum_mem_congr rfl fun v hv ↦ hterm v fun k hk ↦ hc k (by
      rw [← (show orbitCenter x v = V from hv)]
      exact hk)
  have hdeg := (letI : Module.Free (ratioField x) (coordField x) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (ratioField x) (coordField x))
  rw [hsum, hset, hS (ratioField x) (coordField x) (chartRing x c) (chartPoint x c V),
    hU ι n A x s hx hs V hV c hc, hF ι n A x s hx hs V hV c hc,
    ← hP (ratioField x) (chartRing x c) hft hfr (chartPoint x c V) (chartEval x c s) hf0, ← hdeg]
  push_cast
  ring_nf
  rfl

end GroundTheory.Heights₂.Heights
