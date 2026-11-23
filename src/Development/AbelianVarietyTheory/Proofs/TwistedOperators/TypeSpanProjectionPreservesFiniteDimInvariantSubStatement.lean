module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeSpanProjectionPreservesFiniteDimInvariantSub
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
open scoped TensorProduct
open Classical

theorem _root_.GlobalTheory.T.typeSpanProjection_preserves_finiteDim_invariant_subspace : ∀ {M ι : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (G : Submodule ℂ M) (ρ : ι → M →ₗ[ℂ] M)
    (inv : ι → ι), (∀ x ∈ G, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ G, ∀ y ∈ G, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ G, ρ i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, b (ρ i x) y = b x (ρ (inv i) y)) →
    (∀ F : Submodule ℂ M, F ≤ G → FiniteDimensional ℂ F →
      ∃ π : M →ₗ[ℂ] M, (∀ x, π x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (π x) f = b x f) →
    ∀ (Y₀ : Submodule ℂ M) (e : M →ₗ[ℂ] M), (∀ x, e x ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G) →
    (∀ x, ∀ f ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G, b (e x) f = b x f) →
    ∀ Y : Submodule ℂ M, FiniteDimensional ℂ Y → Y ≤ G → (∀ i, ∀ y ∈ Y, ρ i y ∈ Y) → ∀ x ∈ Y, e x ∈ Y := by
  first | exact @GlobalTheory.KTypeProj.typeSpan_proj_mem | exact GlobalTheory.KTypeProj.typeSpan_proj_mem | (intros; apply GlobalTheory.KTypeProj.typeSpan_proj_mem <;> assumption)
