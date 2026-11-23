module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedBridge
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

theorem BlockResolutionMixedBridge.proof : BlockResolutionMixedBridge.Statement := by
  intro D K _ _ ι _ Ω _ _ d L A₁ hL hdeg hA₁
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (mCoordIdeal d.y) Ψ :=
    goodProjExists K ι (mCoordIdeal d.y) D d.arith
  set B : HermLine ι := A₁.tensor d.A.inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, HermLine.tensor, HermLine.inv, hdeg, d.deg]
  have hgl : (fun z => Real.log (A₁.h z / d.A.h z)) = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, HermLine.tensor, HermLine.inv, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor hA₁ (isSmoothHerm_inv d.semipos.1))
  have hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose L B.inv 1 d.arith hex.choose_spec hL hBs hsec
  have hgr : (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x))) =
      fun x => logNorm B.inv 1 (d.R.lift x x) :=
    funext fun x => congrFun hgl (d.R.lift x x)
  unfold ptsIntegral
  rw [dite_eq_left hex, hgl, hgr]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
