module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinMapEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Harmonic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapSingleAtEmb
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.DeterminantDerivative.BigRep
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.EmbeddingConjugation.CoordConjEmbedding
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.FrameExistence.FrameHolds
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.GelfandValueOne.CasVal
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.MatrixConjugateSums.Summand
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.TensorFormCoordinates.CoordConjAtEmb
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.TensorFormCoordinates.TensForm
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryTwistCoordinates.UnitTw
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.Rg.Cz

theorem clozelCohomological_of_rest (h1 : KType) (hgk : GKData) (hw : WhitLie) (hka : KugaAbs) (hkg : KugaGlue)
    (hcg : CoefGlue) (hco : Cochain) (hcb : CasBound) : GlobalTheory.Published.ClozelCohomological :=
  clozelCohomological_of h1 J.kData_holds hgk hw GlobalTheory.CompanionTheory.RgCz.charInt J.unitTw_holds
    (hcg hcb J.bigRep_holds J.bigCx_holds J.summand_holds hco J.casVal_holds)
    (hkg hka J.frame_holds GlobalTheory.CompanionTheory.FrameCasimir.frameCas J.cxExpand_holds J.tensForm_holds GlobalTheory.CompanionTheory.GKHarmonic.harmonic)

end PositivityTheory.Rg.Cz
