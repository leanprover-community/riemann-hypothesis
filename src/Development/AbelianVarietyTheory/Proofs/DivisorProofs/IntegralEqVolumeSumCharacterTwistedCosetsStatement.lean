module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqVolumeSumCharacterTwistedCosets
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw


theorem _root_.GlobalTheory.T.integral_eq_volume_sum_characterTwistedCosets : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (U : AddSubgroup X), IsOpen (U : Set X) → μ (U : Set X) ≠ ⊤ →
    ∀ g : X → ℂ, HasCompactSupport g → (∀ y, ∀ u ∈ U, ∀ u' ∈ U, g (y + u + u') * g y = g (y + u) * g (y + u')) →
    ∃ s : Finset X, ∫ y, g y ∂μ = (∑ γ ∈ s, g γ) * ((μ.real (U : Set X) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.TwistedCosetSum.integral_eq_sum_twisted | exact GlobalTheory.TwistedCosetSum.integral_eq_sum_twisted | (intros; apply GlobalTheory.TwistedCosetSum.integral_eq_sum_twisted <;> assumption)
