module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivSupport
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.HilbEventuallyPolyQualified
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRational
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivCycleSupport
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PEventuallyPolyShift
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PEventuallyPolyUnique
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PGradedFinite
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbDegreeBound
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbExactDivide
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PHilbIrrelevantZero
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumAdd
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBase
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumUnique
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumZeroSlot
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMixedDiffConst
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMultEqualsCoeff
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFDegree
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPolyOfDiffs
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPrimeFiltration
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRelevantPrimeDimGe
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameHilbFn
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRenameIntNum
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

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem GradedFinite.full : GradedFinite.Statement.{u} := GradedFinite.proof

theorem HilbExactDivide.full : HilbExactDivide.Statement.{u} :=
  HilbExactDivide.proof GradedFinite.full

theorem PolyOfDiffs.full : PolyOfDiffs.Statement := PolyOfDiffs.proof

theorem HilbEventuallyPoly.full : HilbEventuallyPoly.Statement.{u} :=
  HilbEventuallyPoly.of_exactDivide_polyOfDiffs HilbExactDivide.full PolyOfDiffs.full

theorem PrimeFiltration.full : PrimeFiltration.Statement.{u} :=
  PrimeFiltration.proof HilbExactDivide.full

theorem EventuallyPolyUnique.full : EventuallyPolyUnique.Statement := EventuallyPolyUnique.proof

theorem EventuallyPolyShift.full : EventuallyPolyShift.Statement := EventuallyPolyShift.proof

theorem HilbIrrelevantZero.full : HilbIrrelevantZero.Statement.{u} := HilbIrrelevantZero.proof

theorem RelevantPrimeDimGe.full : RelevantPrimeDimGe.Statement.{u} := RelevantPrimeDimGe.proof

theorem HilbDegreeBound.full : HilbDegreeBound.Statement.{u} :=
  HilbDegreeBound.proof HilbEventuallyPoly.full HilbExactDivide.full PolyOfDiffs.full
    PrimeFiltration.full EventuallyPolyUnique.full EventuallyPolyShift.full
    HilbIrrelevantZero.full RelevantPrimeDimGe.full

theorem MixedDiffConst.full : MixedDiffConst.Statement.{u} :=
  MixedDiffConst.proof HilbDegreeBound.full HilbEventuallyPoly.full

theorem IntNumSymm.full : IntNumSymm.Statement := IntNumSymm.proof

theorem IntNumAdd.full : IntNumAdd.Statement.{u} := IntNumAdd.proof MixedDiffConst.full

theorem IntNumZeroSlot.full : IntNumZeroSlot.Statement.{u} :=
  IntNumZeroSlot.proof MixedDiffConst.full HilbEventuallyPoly.full HilbDegreeBound.full

theorem IntNumBase.full : IntNumBase.Statement.{u} := IntNumBase.proof MixedDiffConst.full

theorem MultEqualsCoeff.full : MultEqualsCoeff.Statement.{u} :=
  MultEqualsCoeff.proof PrimeFiltration.full MixedDiffConst.full RelevantPrimeDimGe.full

theorem CutRegular.full : CutRegular.Statement.{u} :=
  CutRegular.proof HilbExactDivide.full MultEqualsCoeff.full IntNumSymm.full

theorem CutRational.full : CutRational.Statement.{u} :=
  CutRational.proof CutRegular.full IntNumAdd.full

theorem ExistsForm.full : ExistsForm.Statement.{u} := ExistsForm.proof

theorem DivCycleSupport.full : DivCycleSupport.Statement.{u} := DivCycleSupport.proof

theorem IntNumUnique.full : IntNumUnique.Statement.{u} :=
  IntNumUnique.proof CutRational.full IntNumBase.full ExistsForm.full DivCycleSupport.full

theorem ProjectionFormulaContracted.full : ProjectionFormulaContracted.Statement.{u} :=
  PFContracted.proof MixedDiffConst.full CutRational.full

theorem ProjectionFormulaDegree.of_divPushForward (h : DivPushForward.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} :=
  ProjectionFormulaDegree.proof CutRational.full IntNumBase.full ProjectionFormulaContracted.full h

theorem RenameHilbFn.full : RenameHilbFn.Statement.{u} := RenameHilbFn.proof

theorem RenameIntNum.full : RenameIntNum.Statement.{u} := RenameIntNum.proof RenameHilbFn.full

end GroundTheory.Heights₂.Heights.FieldNumbers
