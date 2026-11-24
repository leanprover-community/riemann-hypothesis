module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesMatchIsomorphicCMInstances
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.realPlaces_match_isomorphic_CM_instances : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E), (∀ y, e (star y) = star (e y)) → ∃ (β : InfinitePlace I.F ≃ InfinitePlace I.E) (σ : InfinitePlace I.F ≃ InfinitePlace I₀.F) (τ τ₀ : InfinitePlace I.F → (ℂ →+* ℂ)), (∀ v, τ v = RingHom.id ℂ ∨ τ v = starRingEnd ℂ) ∧ (∀ v, τ₀ v = RingHom.id ℂ ∨ τ₀ v = starRingEnd ℂ) ∧ (∀ v y, I.φ v y = τ v ((β v).embedding y)) ∧ ∀ v y, I.φ v (e y) = τ₀ v (I₀.φ (σ v) y) := by
  first | exact @GlobalTheory.LeviIso.Places.places_match | exact GlobalTheory.LeviIso.Places.places_match | (intros; apply GlobalTheory.LeviIso.Places.places_match <;> assumption)
