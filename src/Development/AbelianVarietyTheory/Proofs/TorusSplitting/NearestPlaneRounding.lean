module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.AbsTwoMulInnerLeOfNormSubEqInfDist
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

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem nearestPlane_rounding : Ext.NearestPlane := by
  intro V _ _ n v _ x hx
  obtain ⟨w, hw, hle⟩ := exists_int_comb_norm_sub_sq_le n v hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hw
  refine ⟨c, ?_⟩
  have hsum : ∑ i, ((c i : ℤ) : ℝ) • v i = ∑ i, c i • v i := by
    simp only [Int.cast_smul_eq_zsmul]
  rw [hsum]
  linarith

end GlobalTheory
