module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem AmpleOfGenTwist.proof (hGen : GenTwistGenerated.Statement) (hVan : GenTwistVanish.Statement) :
    AmpleOfGenTwist.Statement := by
  intro S _ K _ _ ι _ _ V α p q hV hα hp
  refine ⟨1, le_rfl, ?_, fun e => ?_⟩
  · rw [one_smul]
    exact hGen S K ι V α q p hα
  · obtain ⟨c₀, hc₀⟩ := hVan S K ι V α hV hα e
    refine ⟨c₀, fun c hc => ?_⟩
    have hN : e + (c * 1) • ((q : ℤ) • α + fun _ => (p : ℤ)) =
        e + ((c * q : ℕ) : ℤ) • α + fun _ => ((c * p : ℕ) : ℤ) := by
      funext k
      change e k + (c * 1) • ((q : ℤ) • α k + (p : ℤ)) = e k + ((c * q : ℕ) : ℤ) • α k + ((c * p : ℕ) : ℤ)
      simp only [nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
    rw [hN]
    exact hc₀ (c * q) (c * p) (le_trans hc (Nat.le_mul_of_pos_right c hp))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
