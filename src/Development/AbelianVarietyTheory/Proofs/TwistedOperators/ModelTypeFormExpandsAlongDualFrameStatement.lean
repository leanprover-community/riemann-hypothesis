module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelTypeFormExpandsAlongDualFrame
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

theorem _root_.GlobalTheory.T.modelType_form_expands_along_dualFrame : ∀ (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) {D : D7} (θ : InfFam D) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {m : ℕ} (k : Fin m → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : ∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (B : Fin m → (M.H τ →ₗ[ℂ] M.H τ))
    (hB : ∀ A : M.H τ →ₗ[ℂ] M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) *
          LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
    {φ : GA D V → ℂ} (hφ : IsTypeAt θ V τ (S τ) φ) (x : GA D V) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), φ (x * atTau θ V τ g) = ∑ j, φ (x * atTau θ V τ (k j)) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j) := by
  first | exact @GlobalTheory.TypeExpand.typeAt_expand | exact GlobalTheory.TypeExpand.typeAt_expand | (intros; apply GlobalTheory.TypeExpand.typeAt_expand <;> assumption)
