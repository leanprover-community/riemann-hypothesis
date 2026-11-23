module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem rt_infGL_mul_lie (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (g : GL (Fin a) (Cinf E)) (X : Lie E a) :
    rt E a (infGL E a g) * lie E a X =
      lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g) := by
  refine LinearMap.ext fun ψ => Subtype.ext <| funext fun x => ?_
  have hd : DifferentiableAt ℝ (chart ψ.1 x) (toL g.val) :=
    (contDiffAt_chart ψ.2 x (val_mem_invSet g)).differentiableAt (by simp)
  have e1 : lmul (toL g.val) (oneL E a) = toL g.val := mul_one g.val
  have e2 : rmul (toL g.val) (oneL E a) = toL g.val := one_mul g.val
  have e3 : lmul (toL g.val) X = rmul (toL g.val) (toL (g.val * Matrix.of X * (g⁻¹).val)) := by
    change g.val * Matrix.of X = g.val * Matrix.of X * (g⁻¹).val * g.val
    rw [mul_assoc (g.val * Matrix.of X), ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  change fderiv ℝ (chart ψ.1 (x * infGL E a g)) (oneL E a) X =
    fderiv ℝ (chart (fun y => ψ.1 (y * infGL E a g)) x) (oneL E a)
      (toL (g.val * Matrix.of X * (g⁻¹).val))
  rw [chart_mul, chart_rt_inf,
    fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL g.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL g.val)).differentiableAt,
    e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [e3]

end GlobalTheory.CompanionTheory.SmoothRep
