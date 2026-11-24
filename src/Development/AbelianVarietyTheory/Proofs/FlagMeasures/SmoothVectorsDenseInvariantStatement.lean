module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
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

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.smooth_vectors_dense_invariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H), IsURepOn (GG k r) σ → (∀ g ∈ GG k r, ∀ v ∈ DD σ w, σ g v ∈ DD σ w) ∧ (IsIrredOn (GG k r) σ → w ≠ 0 → Dense (DD σ w : Set H)) ∧ DD σ w ≤ Vinf σ w ∧ (∀ v, IsSmoothVec σ v → (∀ g ∈ GG k r, IsSmoothVec σ (σ g v)) ∧ ∀ Y, InLieHpk k r Y → IsSmoothVec σ (dsig σ Y v) ∧ ∀ g ∈ GG k r, InLieHpk k r (g * Y * g⁻¹) ∧ σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v)) ∧ (IsSmoothVec σ w → (∀ v ∈ Vinf σ w, IsSmoothVec σ v) ∧ (∀ g ∈ GG k r, ∀ v ∈ Vinf σ w, σ g v ∈ Vinf σ w) ∧ ∀ Y, InLieHpk k r Y → ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w) := by
  first | exact @GlobalTheory.SgInfDD.DD_stable_dense | exact GlobalTheory.SgInfDD.DD_stable_dense | (intros; apply GlobalTheory.SgInfDD.DD_stable_dense <;> assumption)
