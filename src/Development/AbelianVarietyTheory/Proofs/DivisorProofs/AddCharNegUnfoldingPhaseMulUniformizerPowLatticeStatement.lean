module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegUnfoldingPhaseMulUniformizerPowLattice
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.addChar_neg_unfoldingPhase_mul_uniformizerPowLattice : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k)
    (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (ϖ : kˣ), IsUnif ϖ → ∀ (n : ℕ) (x : ColArgs G) (v l l' : Vars G),
    l ∈ varLat G ϖ n → l' ∈ varLat G ϖ n →
    (ψ (-phase x (v + l + l')) : ℂ) * (ψ (-phase x v) : ℂ) = (ψ (-phase x (v + l)) : ℂ) * (ψ (-phase x (v + l')) : ℂ) := by
  first | exact @GlobalTheory.UnfoldLoss.PhaseQuad.psi_phase_mul | exact GlobalTheory.UnfoldLoss.PhaseQuad.psi_phase_mul | (intros; apply GlobalTheory.UnfoldLoss.PhaseQuad.psi_phase_mul <;> assumption)
