module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFSGeomDegPos
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMultiDegreePositive
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreDegreeSum
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem FSGeomDegPos.proof (hDeg : DegreeStatement) (hPos : MultiDegreePositive.Statement) :
    FSGeomDegPos.Statement := by
  intro K _ ι _ P e hP
  classical
  have hS : ∀ j : Fin e, IsSmoothHerm ((fun _ : Fin e => fsH ι) j) := fun _ =>
    GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have ha : (fun j : Fin e => ((fun _ : Fin e => fsH ι) j).a) = fun _ : Fin e => fun _ : K => (1 : ℤ) := by
    funext j k
    simp [fsH, HermLine.ofMetrics]
  obtain ⟨hq, hd⟩ := ZCombLimit.genericFibre hP
  have hpos := hPos ℚ K ι _ e hq hd
  rw [GroundTheory.Heights₂.Heights.Targets.FibreDegreeSum.proof K ι P e _ 2 hP Nat.prime_two,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)] at hpos
  rw [hDeg K ι P e (fun _ => fsH ι) 2 hP hS Nat.prime_two, ha,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
  exact_mod_cast hpos

end GroundTheory.Heights₂.Heights.HilbertSamuel
