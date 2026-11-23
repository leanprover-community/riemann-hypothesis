module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrass
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussConstant
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDetFactor
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDualMin
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussFourierSelf
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCoords
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCovolume
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeIsLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPacking
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonDual
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShell
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShellSum
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussSqrt
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussTermBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussTop
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHadamardPSD
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerKernel
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerNormSq
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerUnitBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootsOfUnityDense
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCharIntegral
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaConstants
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCubeParseval
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaFirstCoordSplit
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaInnerMean
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaMean
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaNormMajorant
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaSummandNorm
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaTop
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

namespace GroundTheory.Heights₂.Heights

theorem GaussianSum.full : GaussianSum.Statement :=
  GaussianSum.proof
    (GaussPoissonDual.proof GaussSqrt.proof
      (GaussPoissonBound.proof GaussLatticeIsLattice.proof
        (GaussLatticeCovolume.proof GaussLatticeIsLattice.proof) GaussLatticeCoords.proof
        GaussFourierSelf.proof)
      GaussDualMin.proof GaussDetFactor.proof)
    (GaussShellSum.proof (GaussShell.proof GaussPacking.proof GaussTermBound.proof))
    GaussConstant.proof

theorem ThetaMean.full : ThetaMean.Statement :=
  ThetaMean.proof
    (ThetaInnerMean.proof ThetaSummandNorm.proof
      (ThetaCubeParseval.proof ThetaCharIntegral.proof))

theorem ThetaBound.full : ThetaBound.Statement :=
  ThetaBound.proof GaussianSum.full ThetaMean.full
    (ThetaNormMajorant.proof ThetaSummandNorm.proof) ThetaFirstCoordSplit.proof ThetaConstants.proof

theorem PlueckerNormSq.full : PlueckerNormSq.Statement := PlueckerNormSq.proof CauchyBinet.proof

theorem PlueckerUnitBound.full : PlueckerUnitBound.Statement :=
  PlueckerUnitBound.proof HadamardPSD.proof

theorem PlueckerKernel.full : PlueckerKernel.Statement :=
  PlueckerKernel.proof PlueckerNormSq.full PlueckerUnitBound.full

theorem RootsOfUnityDense.full : RootsOfUnityDense.Statement := RootsOfUnityDense.proof

end GroundTheory.Heights₂.Heights
