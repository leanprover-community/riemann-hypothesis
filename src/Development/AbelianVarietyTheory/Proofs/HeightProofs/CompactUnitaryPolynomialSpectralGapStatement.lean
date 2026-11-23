module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryPolynomialSpectralGap
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.compactUnitary_polynomial_spectral_gap : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ ∀ i : ℕ, 1 ≤ i → ∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) → c * (i : ℝ) ^ α * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.spectral_gap_rder | exact GlobalTheory.KFourier.spectral_gap_rder | (intros; apply GlobalTheory.KFourier.spectral_gap_rder <;> assumption)
