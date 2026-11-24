module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
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

@[expose] public section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.quadraticExt_norm_form_over_algebra : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ∃ δ : F, ¬ IsSquare δ ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ z : R ⊗[F] E, ∃ x y : R, Algebra.norm R z = x ^ 2 - algebraMap F R δ * y ^ 2 ∧ z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) ∧ ∀ x y : R, ∃ z : R ⊗[F] E, z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
  first | exact @GlobalTheory.QuadNormBase.norm_form | exact GlobalTheory.QuadNormBase.norm_form | (intros; apply GlobalTheory.QuadNormBase.norm_form <;> assumption)
