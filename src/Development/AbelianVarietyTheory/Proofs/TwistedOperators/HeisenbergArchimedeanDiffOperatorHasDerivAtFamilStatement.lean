module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamil
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

theorem _root_.GlobalTheory.T.heisenbergArchimedeanDiffOperator_hasDerivAt_family : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F))
    (g' : SInf F κ) (P' Q' : κ → mixedEmbedding.mixedSpace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    (∀ y, HasDerivAt (fun t => G t y) (g' y) 0) → HasDerivAt P P' 0 → HasDerivAt Q Q' 0 → ∀ y,
    HasDerivAt (fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) (GlobalTheory.HeisOrbit.dOp (P 0) (Q 0) g' y + GlobalTheory.HeisOrbit.dOp P' Q' (G 0) y) 0 := by
  first | exact @GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt | exact GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt | (intros; apply GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt <;> assumption)
