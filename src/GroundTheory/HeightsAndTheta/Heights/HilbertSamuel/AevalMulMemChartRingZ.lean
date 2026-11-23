module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.HSClosing
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
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory
  Topology

noncomputable section

namespace ArithmeticVolumeResolution

variable {ι0 : Type} [Fintype ι0]

theorem error_isLittleO (D : ℕ) (K₁ K₂ : ℝ) :
    (fun n : ℕ => K₁ * (n : ℝ) ^ D + K₂ * ((n : ℝ) ^ D * Real.log n)) =o[atTop] pw D := by
  have h1 : (fun n : ℕ => (n : ℝ) ^ D) =o[atTop] pw D := by
    have := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto
      tendsto_natCast_atTop_atTop
    exact this
  have h2 : (fun n : ℕ => (n : ℝ) ^ D * Real.log n) =o[atTop] pw D := by
    have := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO
      (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop)
    refine this.congr_right fun n => ?_
    simp [pw, pow_succ]
  exact (h1.const_mul_left K₁).add (h2.const_mul_left K₂)

end ArithmeticVolumeResolution


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
