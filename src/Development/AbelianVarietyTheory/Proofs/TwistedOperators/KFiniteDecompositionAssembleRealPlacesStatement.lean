module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlaces
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Classical


theorem _root_.GlobalTheory.T.kFiniteDecomposition_assemble_realPlaces : ∀ (D : D7) (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop), (∀ f ∈ 𝒞, Continuous f) → (∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N 𝒞 Ty τ) → ∀ ψ ∈ 𝒞, (∀ τ, Ty τ ψ) → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j v, T₀ j v ∈ 𝒞) ∧ (∀ j, ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = N.M.rep τ k (v τ) → T₀ j (Function.update v τ w) = rTr N.V (atTau θ N.V τ k) (T₀ j v)) ∧ (∀ j, ∀ τ, ∀ X ∈ lieAt N.V τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = dRep (N.M.rep τ) X (v τ) → T₀ j (Function.update v τ w) = Rder θ N.V τ X (T₀ j v)) ∧ ψ = ∑ j, T₀ j (u j) := by
  first | exact @GlobalTheory.KFinDecomp.assemble_places | exact GlobalTheory.KFinDecomp.assemble_places | (intros; apply GlobalTheory.KFinDecomp.assemble_places <;> assumption)
