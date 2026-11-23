module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InitialLevelFormula
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.NumBase
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FourDepthLtConductorOfBounds
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OddTops
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SegStartSpec
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem TLP_pos (K : Cst) : 0 < K.TLP := by
  unfold Cst.TLP
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _))

theorem thrLP_of (hO : RestOddTops) (K : Cst) (hK : K.Pos) : TransportedAlt K (FactsLP K) := by
  have hK' := hK
  unfold Cst.Pos at hK'
  have hCt : 0 < K.Ct := hK'.2.2.2.2.2.2.2.1
  refine ⟨K.TLP, 4 * K.Ct + 4, TLP_pos K, by linarith, ?_⟩
  intro CH hCH C hC X h
  have B := base_of K hK CH hCH X h
  have h' := h
  unfold Dat.Hyp HypI at h'
  obtain ⟨-, -, -, -, -, -, hm, -, hb, -, -, -, -, -, -, -, -, -, -, -, -, -, hcs, -⟩ := h'
  have hd := dle_of hK hCH h B
  have hp := B.hp25
  exact
    { cst := hcs
      bpos := hb
      ppos := by exact_mod_cast (show (0 : ℝ) < X.p by linarith)
      m2 := by omega
      D1nn := D1nn_of hK B
      four_depth_lt_conductor := four_depth_lt_conductor_of_bounds hd hcs
      dle := hd
      a8 := second_moment_of_columns hCH B
      eps := eps_of hCH B
      lowa := lowa_of B
      lowb := lowb_of h
      tle := fun aw bw hw => tle_of hO hK hC h B aw bw hw }

theorem thrLP (K : Cst) (hK : K.Pos) : TransportedAlt K (FactsLP K) := by
  exact thrLP_of restOddTops K hK

end Formalism.MainNotions.flipOneThree.Pf

end
