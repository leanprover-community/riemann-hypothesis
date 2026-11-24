module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesWithOfIsSquareConstOfTriple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionCommutesOnGrid
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SquareComm
open GlobalTheory.RowClaim
end GlobalTheory.SquareComm
namespace GlobalTheory.SquareComm
open GlobalTheory.RowClaim
theorem square_commutes_with_all : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
      ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t) := by
  intro hPr hWC hK
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ t i j => ?_⟩⟩
  exact commutesWith_of_isSquareConst hWC hK hPr.cuspDecayBound s.core.lev
    (squareStanding_of_setting s s.size.2.1.eleven_le ch.G t) (hch.const i j t)
end GlobalTheory.SquareComm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_square_commutes : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t) := by
  first | exact @_root_.GlobalTheory.SquareComm.square_commutes_with_all | exact _root_.GlobalTheory.SquareComm.square_commutes_with_all | (intros; apply _root_.GlobalTheory.SquareComm.square_commutes_with_all <;> assumption)
end
