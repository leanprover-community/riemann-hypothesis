module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterZero
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterLe
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterMemIff
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterDivSupp
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

theorem OrbitCenterZero.proof (hLe : OrbitCenterLe.Statement)
    (hIff : OrbitCenterMemIff.Statement) (hDiv : OrbitCenterDivSupp.Statement) :
    OrbitCenterZero.Statement := by
  intro ι _ _ _ n A x s hx ⟨a, ha, hs, hsW⟩ v hv
  have hsc : s ∉ orbitCenter x v := fun h ↦ hv (hDiv ι n x s a hx hs hsW v h)
  have heq : v (evalCone (coordVec x) s) = ∏ k, (⨆ i, v (coordVec x k i)) ^ a k :=
    le_antisymm (hLe ι n x v s a hs) (not_lt.mp (mt (hIff ι n x hx v s a hs).mpr hsc))
  have hne : v (evalCone (coordVec x) s) ≠ 0 :=
    (FinitePlace.pos_iff.mpr (evalCone_coordVec_ne_zero x s a hs hsW)).ne'
  rw [heq] at hne ⊢
  rw [Real.log_prod (fun k _ ↦ Finset.prod_ne_zero_iff.mp hne k (Finset.mem_univ k)),
    finiteTerm, sub_eq_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Real.log_pow, show (A.deg k : ℝ) = (a k : ℝ) by exact_mod_cast ha k]

end GroundTheory.Heights₂.Heights
