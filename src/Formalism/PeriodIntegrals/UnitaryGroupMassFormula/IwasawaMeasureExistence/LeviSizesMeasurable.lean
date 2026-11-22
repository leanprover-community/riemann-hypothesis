module

public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
public import Formalism.PeriodIntegrals.LatCountG
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Mathlib
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
public import Formalism.HermitianLattices.StatementMass

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.Nrm

open Matrix NumberField Topology Filter MeasureTheory Formalism.MainNotions.S
  Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.GLOne
open scoped TensorProduct nonZeroDivisors

section Top

variable (I : AutInst)

attribute [local instance] AfT.tAf

attribute [local instance] topRing t2

attribute [local instance] mAf

attribute [local instance] borel_mAf

end Top

attribute [local instance] AfT.tAf topRing t2 mAf borel_mAf

end PI.IwaMeasEx.Nrm

end
