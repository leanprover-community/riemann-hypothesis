module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedWeierstrassCurveTransformCoefficientsW
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.unramifiedWeierstrassCurve_transform_coefficients_wellFormed : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  first | exact @GlobalTheory.CoefWfUnram.coefWf_phW | exact GlobalTheory.CoefWfUnram.coefWf_phW | (intros; apply GlobalTheory.CoefWfUnram.coefWf_phW <;> assumption)
