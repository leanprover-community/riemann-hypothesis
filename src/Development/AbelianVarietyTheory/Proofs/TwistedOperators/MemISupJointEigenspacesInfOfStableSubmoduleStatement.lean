module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemISupJointEigenspacesInfOfStableSubmodule
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.mem_iSup_jointEigenspaces_inf_of_stableSubmodule : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (G P : Submodule ℂ E) (C : Finset (ι → ℂ)),
    (∀ i, ∀ x ∈ G, F i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x) → P ≤ G → (∀ i, ∀ x ∈ P, F i x ∈ P) →
    (∀ x ∈ G, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h}) →
    ∀ x ∈ P, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
  first | exact @GlobalTheory.mem_iSup_jointEigen_inf_of_stable | exact GlobalTheory.mem_iSup_jointEigen_inf_of_stable | (intros; apply GlobalTheory.mem_iSup_jointEigen_inf_of_stable <;> assumption)
