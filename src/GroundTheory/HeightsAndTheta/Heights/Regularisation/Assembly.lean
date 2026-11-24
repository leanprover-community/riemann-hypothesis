module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.StLogCoverDescent
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.StPuncturedExpOrder
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.StRiemannSlices
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PAnalyticDerivBound
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramEntryDeriv
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryBound
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryDeriv
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramDeriv
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PMatrixDetDeriv
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PExpExtension
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PHodgeDerivative
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PImTauBounds
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PKernelPositive
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

theorem GlueRegularised.full : GlueRegularised.Statement :=
  GlueRegularised.proof

theorem KernelPositive.full : KernelPositive.Statement :=
  kernelPositive_statement

theorem Tau0Holomorphic.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    Tau0Holomorphic.Statement :=
  Tau0Holomorphic.proof (ExpQuadMonomial.proof hE hO hD)

theorem ImTauBounds.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    ImTauBounds.Statement :=
  ImTauBounds.proof (Tau0Holomorphic.cond hE hO hD) KernelPositive.full

theorem HodgeDerivative.cond (hE : RiemannExtensionSlices.Statement)
    (hO : PuncturedExpOrder.Statement) (hD : LogCoverDescent.Statement) :
    HodgeDerivative.Statement :=
  have hInv : InvEntryDeriv.Statement := InvEntryDeriv.proof InvEntryBound.proof
  HodgeDerivative.proof (ImTauBounds.cond hE hO hD) (Tau0Holomorphic.cond hE hO hD)
    AnalyticDerivBound.proof hInv
    (LogDetGramDeriv.proof InvEntryBound.proof hInv MatrixDetDeriv.proof GramEntryDeriv.proof)

end GroundTheory.Heights₂.Heights.Regular
