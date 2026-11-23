module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMulEndomorphismIsotypicRep
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.trace_mul_endomorphism_isotypicRep : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible → (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) → IsIsotypicAlg π ρ → ∀ H : X →ₗ[ℂ] X, (∀ g x, H (ρ g x) = ρ g (H x)) → (∃ s : Finset (π.IntertwiningMap ρ), LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) → ∃ c : ℂ, ∀ (A : N →ₗ[ℂ] N) (B : X →ₗ[ℂ] X), (∀ φ : π.IntertwiningMap ρ, B ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ A) → ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (H ∘ₗ B) (c * b) := by
  first | exact @GlobalTheory.IsoTrace.trace_mul_isotypic | exact GlobalTheory.IsoTrace.trace_mul_isotypic | (intros; apply GlobalTheory.IsoTrace.trace_mul_isotypic <;> assumption)
