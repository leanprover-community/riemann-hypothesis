module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NonnegGT
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SupRatioLeOfPhaseZero

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

theorem tOf (hx : Ext.All) (hs : SplitStatement) (hS : GSupStatement) (hd : DimStatement) :
    TStatement := by
  intro E _ _ _ X DF P r1 hr1 a ha hgen s hsmem hs0
  refine ⟨fun hph => ?_, fun h0 => ?_⟩
  · obtain ⟨I, hI⟩ := hs E X DF P
    exact t_assemble P hI (perFactor_of hx hS P hI hph hsmem) r1 hr1 a ha hgen hph
  · calc ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s)
        ≤ ∏ _j : Fin X.r, Real.exp P.p1 :=
          Finset.prod_le_prod₀ (fun j _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (fun j _ => sup_ratio_le_of_phase_zero P hS hsmem h0 (a j))
      _ = Real.exp (X.r * P.p1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]

end ReciprocityTheory.ChartRestriction.G.I2
