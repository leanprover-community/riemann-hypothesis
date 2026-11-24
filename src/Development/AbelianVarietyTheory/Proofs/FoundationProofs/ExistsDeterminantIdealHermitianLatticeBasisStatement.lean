module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeterminantIdealHermitianLatticeBasis
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_determinantIdeal_hermitianLattice_basis : ∀ (D : D7) (N N' r : ℕ) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (b₀ : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ x ∈ Y, ∀ y ∈ Y, hYY D x y ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → (∀ i, ∃ s : ℕ, 0 < s ∧ (s : D.host.E) • b₀ i ∈ Y) → ∃ I : Submodule (𝓞 D.host.K) D.host.K, (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : D.host.K) * x ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) ∧ ∀ (p : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p Y b → (∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det ∈ I) ∧ ∀ x ∈ I, ∃ (s : ℕ) (c : 𝓞 D.host.K), Nat.Coprime s p ∧ (s : D.host.K) * x = (c : D.host.K) * (Matrix.of fun i j => hYY D (b j) (b₀ i)).det := by
  first | exact @GlobalTheory.NormSum.exists_detIdeal | exact GlobalTheory.NormSum.exists_detIdeal | (intros; apply GlobalTheory.NormSum.exists_detIdeal <;> assumption)
