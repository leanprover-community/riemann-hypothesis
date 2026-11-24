module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
noncomputable section
open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion
namespace GlobalTheory.BigOn.Exp.ProjRd
attribute [local instance] GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.algKK
end GlobalTheory.BigOn.Exp.ProjRd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp


theorem GlobalTheory.BigOn.Exp.canProj_alt : _root_.GlobalTheory.BigOn.Exp.CanonicalProjection₂ := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p _ _ w _ j rd hrd y => ?_⟩⟩
  obtain ⟨-, -, -, hid, -⟩ := p.grpRecPin
  exact GlobalTheory.BigOn.Exp.ProjRd.rd_eOp (Fm.ex x hx i).nch_tie (p.R.eG.trans p.cG) p.Sx ((j : ℕ) + 1) ((R2 p).FW j)
    (p.nexp.fi j) (GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.isKsForm_of_iso (p.nexp.fi j) (p.fw.ks j)) (p.nexp.geq j) (p.nexp.rho _ (Nat.le_add_left _ _) j.2) (p.nexp.chi _ (Nat.le_add_left _ _) j.2)
    (p.nexp.eF _ _ _ (Nat.le_add_left _ _) j.2) (p.nexp.act _ _ _ (Nat.le_add_left _ _) j.2)
    (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    (fun g => (Fm.D x i).what₂.embLL.injective ((hid g).trans ((Fm.D x i).nStage_trivialCharacter_coeff_eq _).symm)) rd hrd y
end
end
