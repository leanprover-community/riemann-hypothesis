module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftAntidiagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_antidiagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.exists_lift_antidiag | exact GlobalTheory.SnMass.VolN.exists_lift_antidiag | (intros; apply GlobalTheory.SnMass.VolN.exists_lift_antidiag <;> assumption)
