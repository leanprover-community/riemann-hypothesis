module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementH
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementL
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalL
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KJoint
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
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
import Mathlib.Tactic.Linter.Style
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
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.A (logSer expSer)
open Formalism.G (unitBall)

theorem IntOpTwoOrth_of (h : Formalism.L2.Th1.B.ThetaZeroTwoCM) : IntOpTwoOrth := by
  intro d L hd hCM ι W hU hI ha1 ω₀ hω hn1 hn2 n _ κ _ r s N hr hN hodd hs
  obtain ⟨-, -, hG⟩ := h d L hd hCM ι W hU hI ha1 ω₀ hω hn1 hn2
  set R := unitBall ℂ_[2] with hR
  have hmem : ∀ a : ℂ_[2], a ∈ R ↔ ‖a‖ ≤ 1 := fun a => Iff.rfl
  obtain ⟨h1, h2, h3, h4, h6, -⟩ := hI
  have hco := Formalism.L2.Th1.A.coeffMem ℂ_[2] W R ((hmem _).2 h1) ((hmem _).2 h2) ((hmem _).2 h3)
    ((hmem _).2 h4) ((hmem _).2 h6)
  have hlog := Formalism.L2.Th1.A.logSpec ℂ_[2] W
  have hexp := Formalism.L2.Th1.A.expSpec ℂ_[2] W
  have hLP : C.IsLogPair (logSer W) (expSer W) :=
    ⟨hlog.1, hlog.2.1, hexp.1, hexp.2.2.2.1, hexp.2.2.1⟩
  have hOU : C.IsOneUnit R (PowerSeries.derivative (R := ℂ_[2]) (logSer W)) := by
    rw [hlog.2.2.1]
    refine ⟨?_, hco.2.2.2.2.1⟩
    simp [Formalism.L2.Th1.A.om]
  set T : κ → n → PowerSeries ℂ_[2] :=
    fun k i => E.inW 2 ι W (F.opU L (s k i) (F.th0 L (ω₀ / 2))) with hT
  have hTI : ∀ k i, E.IntS (T k i) := fun k i => (hG (s k i) N hN hodd (hs k i)).1
  have hInt : DworkPowerSeriesWeights.Integral (E.thetaProd r T) := (E.prodInt ℂ_[2] κ n 0 r T (by simp) hr hTI).2
  have hIM : C.IntMv R (E.thetaProd r T) := fun m => (hmem _).2 (hInt m)
  have hJ := G.jetsIn_toZ hLP hOU hIM
  have heq : G.toZ (expSer W) (E.thetaProd r T) = thetaZ 2 L ι ω₀ r s := by
    rw [KJ.toZ_thetaProd hexp.1]
    unfold thetaZ
    congr 1
    funext k i
    simp only [hT, E.inW]
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlog.1)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hexp.1), hexp.2.2.1, PowerSeries.X_subst]
  rw [heq] at hJ
  have hJI : DworkPowerSeriesWeights.JetsIntegral (thetaZ 2 L ι ω₀ r s) := (G.jets_in_norm_holds ℂ_[2] n _).2 hJ
  refine ⟨hJI, fun P hP => ?_⟩
  show DworkPowerSeriesWeights.jetPair P (thetaZ 2 L ι ω₀ r s) ∈ R
  unfold DworkPowerSeriesWeights.jetPair
  refine Subring.sum_mem _ fun m _ => ?_
  rw [mul_assoc]
  exact Subring.mul_mem _ ((hmem _).2 (hP m)) ((hmem _).2 (hJI m))

theorem integral_operator_two_orthogonal : IntOpTwoOrth := IntOpTwoOrth_of Formalism.L2.Th1.B.th0TwoCM

end Formalism.L2.Th1.Top
