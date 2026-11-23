module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerDownArrowTransportAdjoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.realIntertwiner_downArrow_transport_adjoint : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χ : (AE D)ˣ →* Circle)
    (ω : GlobalTheory.Grid.WRep S.V T.V) (f : WO S.V T.V → ℂ), IsInfFam θ → GlobalTheory.Grid.IsWeil ψ true S.V T.V χ χ ω →
    GlobalTheory.Grid.IsVac ψ θ true S T f →
    ∃ (ω₀ : GlobalTheory.Grid.WRep T.V S.V) (f₀ : WO T.V S.V → ℂ) (χ₀ : (AE D)ˣ →* Circle)
      (e : GlobalTheory.Grid.Pol S T ≃ₗ[ℂ] PolF D S.V.rank T.V.rank),
      IsWeilDatumO ψ T.V S.V χ₀ χ₀ ω₀ ∧ (∀ τ a, HasInfExp D χ τ a → HasInfExp D χ₀ τ (-a)) ∧
      IsVacVec ψ θ T.M S.M f₀ ∧
      ∀ It : PolF D S.V.rank T.V.rank →ₗ[ℂ] SmT S.M →ₗ[ℂ] SmT T.M, IsItW θ T.M S.M ω₀ (ptOf ψ θ T.M S.M f₀) It →
        GlobalTheory.Grid.IsIntw θ T.M S.M ω.swap (GlobalTheory.Grid.fock ψ θ true S T f) (It ∘ₗ e.toLinearMap) := by
  first | exact @GlobalTheory.AdjTr.downArrow_transport | exact GlobalTheory.AdjTr.downArrow_transport | (intros; apply GlobalTheory.AdjTr.downArrow_transport <;> assumption)
