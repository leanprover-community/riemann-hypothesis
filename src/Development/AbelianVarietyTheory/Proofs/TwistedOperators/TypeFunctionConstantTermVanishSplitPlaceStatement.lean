module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeFunctionConstantTermVanishSplitPlace
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
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.SplitWeil
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (radical)

theorem _root_.GlobalTheory.T.type_function_constant_term_vanish_split_place : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (a : ℕ), 0 < a → a < V.rank → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin V.rank) (ResF v)) W), τ.IsIrreducible → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ (radical (ResF v) V.rank a) → ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v)) [μ.IsHaarMeasure], ∀ φ ∈ CcLoc D.sp.cm.sig V.gram v, ∀ f : GLoc D.sp.cm.sig V.gram v → ℂ, (f = conv μ (s.idem μ τ) φ ∨ f = conv μ φ (s.idem μ τ)) → ∀ g : GL (Fin V.rank) (Fv D.host.F v), ∃ H : Subgroup (GLoc D.sp.cm.sig V.gram v), IsClosed (H : Set (GLoc D.sp.cm.sig V.gram v)) ∧ (∀ x, x ∈ H ↔ g⁻¹ * s.equiv x * g ∈ radical (Fv D.host.F v) V.rank a) ∧ ∃ ν : Measure H, ν.IsHaarMeasure ∧ ∀ x y, ∫ u : H, f (x * u * y) ∂ν = 0 := by
  first | exact @GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt | exact GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt | (intros; apply GlobalTheory.TypeConstLoc.unipIntegral_vanish_splitAt <;> assumption)
