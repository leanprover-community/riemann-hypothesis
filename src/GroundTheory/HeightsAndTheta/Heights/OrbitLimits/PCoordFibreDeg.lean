module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CoordFibreDeg
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.FibreMultiHomog
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CoordRatioDeg
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GenFibreChartDeg
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem CoordFibreDeg.proof (hM : FibreMultiHomog.Statement) (hD : GenFibreChartDeg.Statement)
    (hR : CoordRatioDeg.Statement) : CoordFibreDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y d G i hb hZ' hZ hi
  have : CharZero G.Φ' := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      simpa using hn
    simp only [mCoordIdeal, RingHom.mem_ker, mConeMap] at hmem
    simpa using hmem
  have hMH : IsMultiHomogIdeal (mCoordIdeal y) := hZ'.2.1.2.1
  choose c hc using hZ.2.1.2.2
  have hx : ∀ k, G.x ⟨k, c k⟩ ≠ 0 := fun k h => hc k (by
    rw [← G.ker_x, RingHom.mem_ker, aeval_X]
    exact h)
  have hi' : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [fibreIdeal, RingHom.mem_ker, aeval_X]
    exact h)
  have h1 := Inter.ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ'
    (fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩) i hi'
    (hM K ι K' ι' κ v (mCoordIdeal y) G hb hMH)
  exact h1.trans ((hD K ι K' ι' κ v (mCoordIdeal y) G c i hb hMH hx hi').trans
    (hR K ι K' ι' κ v Ω y G.Φ' G.x' hb G.genericFibre_ker_target))

end GroundTheory.Heights₂.Heights.Targets
