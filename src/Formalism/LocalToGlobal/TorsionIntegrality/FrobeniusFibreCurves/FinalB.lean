module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalA
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffEqZeroOfParallelogram
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InvariantDerivationSubstLawThree
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LogSigmaOnePullbackSpec
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SimeqPadicIntegers
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassSeriesIntegral
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.Th1.B

theorem halfExists : HalfExists := by
  exact formal_halving_exists
theorem cobRules : CobRules := by
  exact coboundary_rules_hold
theorem simeqInt : SimeqInt := by
  exact Sim.simeq_integral_series
theorem simeqLog : SimeqLog := by
  exact Sim.simeq_formal_log
theorem phODef : PhODef := by
  exact Ph.logSigmaPullbackSpec
theorem phEDef : PhEDef := by
  exact Ph.logSigmaOnePullbackSpec
theorem wIntegral : WIntegral := by
  exact ParE.weierstrass_series_integral
theorem parO : ParO := by
  exact ParO.ParO_of addSgStar phODef simeqLog
theorem diffPh : DiffPh := by
  exact ParO.DiffPh_of sigma1Sq simeqLog
theorem cube : Cube := by
  exact Cube_of halfExists simeqInt
theorem jetsThree : JetsThree := by
  exact Jets.jets_three_variables_holds

theorem f1O : LogSigmaPullbackCocycle := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2
  have hl := hF.2.2
  have h0 := (phODef K s2 P l hl.1 hl.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF h0
  have hd := cube K F l i (phO s2 P l) hF hi h2 (parO K g2 g3 s2 c0 P l i ep F hP hF hi hC)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩

end Formalism.L2.Th1.B
