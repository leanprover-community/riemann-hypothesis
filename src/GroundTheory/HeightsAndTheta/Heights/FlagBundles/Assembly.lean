module

public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsSphereLongitude
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalPairing
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalReduction
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreConstantClosedForm
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreIntegralInvariant
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGHatIdentity
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGKernelIdentity
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalBilinearFormula
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalHeightReduction
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernel
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernelPairing
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

namespace GroundTheory.Heights₂.Heights.FlagBundles

theorem GKernelIdentity.full : GKernelIdentity.Statement :=
  GKernelIdentity.proof

theorem ZonalKernel.full : ZonalKernel.Statement :=
  ZonalKernel.proof

theorem SphereLongitudeCoordinates.full : SphereLongitudeCoordinates.Statement :=
  SphereLongitudeCoordinates.proof

theorem ZonalHeightReduction.full : ZonalHeightReduction.Statement :=
  ZonalHeightReduction.proof SphereLongitudeCoordinates.full ZonalKernel.full

theorem ZonalKernelPairing.full : ZonalKernelPairing.Statement :=
  ZonalKernelPairing.proof

theorem ZonalBilinearFormula.full : ZonalBilinearFormula.Statement :=
  ZonalBilinearFormula.proof ZonalHeightReduction.full ZonalKernelPairing.full

theorem GHatIdentity.full : GHatIdentity.Statement :=
  GHatIdentity.proof GKernelIdentity.full

theorem FibreConstantClosedForm.full : FibreConstantClosedForm.Statement :=
  FibreConstantClosedForm.proof ZonalBilinearFormula.full GHatIdentity.full

theorem fibreConstant_eq (k : ℕ) :
    fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1) :=
  FibreConstantClosedForm.full.1 k

theorem FibreIntegralInvariant.full : FibreIntegralInvariant.Statement :=
  FibreIntegralInvariant.proof FibreConstantClosedForm.full

end GroundTheory.Heights₂.Heights.FlagBundles
