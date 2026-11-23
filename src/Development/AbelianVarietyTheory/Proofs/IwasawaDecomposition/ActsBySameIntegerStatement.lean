module

public import Formalism.LocalRingCardinality.DataLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActsBySameInteger
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix

theorem _root_.GlobalTheory.T.acts_by_same_integer_statement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (T : ℕ), T.Prime → (T : 𝓞 F) ∈ w.asIdeal → ∀ (p : 𝓞 E), (∀ d : 𝓞 F, algebraMap F E (d : F) = (p : E) + σ (p : E) → d ∉ w.asIdeal) → ∀ (A B : Type) [AddCommGroup A] [Module (intV E w) A] [AddCommGroup B] [Module (intV E w) B], Nat.card A = T → Nat.card B = T → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : A, a • m = 0) → (∀ a : intV E w, (a : TensorProduct F E (w.adicCompletion F)) = inclE (F := F) (w.adicCompletion F) (p : E) → ∀ m : B, a • m = 0) → ∀ s : intV E w, ∃ k : ℤ, (∀ m : A, s • m = k • m) ∧ ∀ m : B, s • m = k • m := by
  first | exact @GlobalTheory.PrimeOrderScalar.acts_by_same_integer | exact GlobalTheory.PrimeOrderScalar.acts_by_same_integer | (intros; apply GlobalTheory.PrimeOrderScalar.acts_by_same_integer <;> assumption)
