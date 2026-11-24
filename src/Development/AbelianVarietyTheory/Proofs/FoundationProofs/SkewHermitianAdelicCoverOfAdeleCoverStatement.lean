module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SkewHermitianAdelicCoverOfAdeleCover
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

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

theorem _root_.GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (b C₀ : ℝ) (Ω₀ : Set (AF F)), IsCompact Ω₀ → (∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C₀ * b ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω₀, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω) → ∀ n : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : Fin n → ℕ, ∃ Y : Finset (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ C * ∏ i, (b ^ 2) ^ (n * m i) ∧ ∀ S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) S = -S → ∃ S₀ : Matrix (Fin n) (Fin n) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin n) (Fin n) (AF F ⊗[F] E), (∀ i j, ω i j ∈ Ω) ∧ S = S₀.map (inclR (F := F) (AF F)) + y + Matrix.diagonal (fun i => (halfE F E).1 ^ m i) * ω * Matrix.diagonal (fun i => (halfE F E).1 ^ m i) := by
  first | exact @GlobalTheory.Eis.Conv.CovSkew.cover_skew | exact GlobalTheory.Eis.Conv.CovSkew.cover_skew | (intros; apply GlobalTheory.Eis.Conv.CovSkew.cover_skew <;> assumption)
