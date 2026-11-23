module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCentral
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentHorizontal
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineEigenvalue
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectHaar
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusEmbedding
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusModulus
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnitsInvHaar
public import Mathlib.Topology.Algebra.Group.Units
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MainOf
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementArchCocompact
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PImaginaryLatticeCocompact
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineEigenvalue
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PRadicalTorusModulus
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PRationalUnipotent
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PSemidirectHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLevi
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusEmbedding
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusModulus
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipRadicalOfRational
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentCentral
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentCoordProper
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentHorizontal
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulus
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnitsInvHaar
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.SWFin

open NumberField GroundTheory.Automorphic Module GroundTheory.Heights₂.Heights.FiniteCovolume

universe u

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

section steps

variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (h : HermitianForm F E W) (v : Basis ι E W)

theorem te : TorusEmbedding.Statement h v :=
  TorusEmbedding.proof h v (HermAtPlace.full h v) (GramAtData.full h v)

theorem le : LineEigenvalue.Statement h v := LineEigenvalue.proof h v (VecAtNeZero.full v)

theorem sh : SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ) := SemidirectHaar.proof _ _

theorem tm : TorusModulus.Statement h v :=
  TorusModulus.proof h v (HermAtPlace.full h v) (GramAtData.full h v) (ComplementForm.full h)
    (StabilizerLevi.proof h v) (UnipotentModulus.proof h v) (RadicalTorusModulus.proof h v)
    fun _ _ _ _ _ => SemidirectHaar.proof _ _

theorem uh : UnipotentHorizontal.Statement h v :=
  UnipotentHorizontal.proof h v (RationalUnipotent.proof h) (UnipRadicalOfRational.proof h v)
    (ComplementArchCocompact.proof h v)

theorem uz : UnipotentCentral.Statement h v :=
  UnipotentCentral.proof h v (RationalUnipotent.proof h) (UnipRadicalOfRational.proof h v)
    ImaginaryLatticeCocompact.proof

end steps

theorem adelicCovolumeFinite {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : HermitianForm F E W) (v : Basis ι E W) : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_remaining (fun _ _ _ _ h _ v => te h v) (fun _ _ _ _ h _ v => le h v)
    (fun _ _ _ _ h _ v => tm h v) (fun _ _ _ _ h _ v => sh h v) (UnitsInvHaar.proof _)
    (fun _ _ _ _ h _ v => UnipotentCoordProper.proof h v) (fun _ _ _ _ h _ v => uh h v)
    (fun _ _ _ _ h _ v => uz h v) h v (te h v) (le h v) (tm h v) (sh h v) (UnipotentCoordProper.proof h v)
    (uh h v) (uz h v)

end CompanionTheory.SWFin
