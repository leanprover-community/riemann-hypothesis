module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HasTypeAtCuspOfCuspValueType
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.CuspValueTypeAt
theorem cusp_value_hasTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau),
    IsInfFam θ → N.V.SigOK → GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) →
    ∀ F ∈ N.Cusp θ, ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  intro hP D θ N τ hθ hN _ F hF w
  exact _root_.GlobalTheory.CuspValueType.hasTypeAt_cusp_of_cusp_value_type hP θ hθ N hN F hF w τ
end GlobalTheory.CuspValueTypeAt
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.twist_cusp_value_hasTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau), IsInfFam θ → N.V.SigOK → GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) → ∀ F ∈ N.Cusp θ, ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ N.V τ (N.S τ) (F w) := by
  first | exact @_root_.GlobalTheory.CuspValueTypeAt.cusp_value_hasTypeAt | exact _root_.GlobalTheory.CuspValueTypeAt.cusp_value_hasTypeAt | (intros; apply _root_.GlobalTheory.CuspValueTypeAt.cusp_value_hasTypeAt <;> assumption)
end
