module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLeadingTermOfSkewLayer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.exists_unitary_leading_term_of_skew_layer : ∀ (R K : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K] (n m : ℕ) (J : Matrix (Fin n) (Fin n) K) (A : ℕ → Submodule R (Matrix (Fin n) (Fin n) K)) (w : R), Jᴴ = J → J.det ≠ 0 → algebraMap R K w + star (algebraMap R K w) = 1 → (∀ c, A (c + 1) ≤ A c) → A m = ⊥ → (∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1)) → (∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J ∈ A c) → ∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J = -X → ∃ Y ∈ A (c + 1), (1 + X + Y)ᴴ * J * (1 + X + Y) = J := by
  first | exact @GlobalTheory.RadCov.exists_unitary_of_skew_layer | exact GlobalTheory.RadCov.exists_unitary_of_skew_layer | (intros; apply GlobalTheory.RadCov.exists_unitary_of_skew_layer <;> assumption)
