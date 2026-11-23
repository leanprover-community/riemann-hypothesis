module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixFrobeniusSubOneBijectiveModSubring
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
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.matrix_frobenius_sub_one_bijective_mod_subring : ∀ (R EE A : Type) [CommRing R] [CommRing EE] [CommRing A] (j : EE →+* R) (ι : A →+* R) (φ : R →+* R) (S : Subring R) (p : ℕ) (t : R) (τ : A), ι τ = t → (∀ e, j e ∈ S) → (∀ x ∈ S, φ x ∈ S) → (∀ e, ∃ e', φ (j e) = j e') → (∀ a, ∃ a', φ (ι a) = ι a') → Near ι p t 2 (φ t) → (∀ e, ∃ c : ℕ, Near ι p t 0 (t ^ c * j e)) → (∀ x, (p : R) * x ∈ S → x ∈ S) → (∀ x e, (p : R) * x = j e → ∃ e', x = j e') → (∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) → (∀ i, Near ι p t (i + k) (f i)) → ∃ s ∈ S, ∀ m, Near ι p t (m + k) (s - ∑ i ∈ Finset.range m, f i)) → (∀ x, (∀ m, ∃ e, Near ι p t m (x - j e)) → ∃ e r, x - j e = (p : R) * r) → (∀ y ∈ S, ∀ m, ∃ (n : ℕ) (y0 : R) (e : EE) (r : R), φ^[n] y0 = j e + (p : R) * r ∧ Near ι p t m (y - y0)) → (∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ s ∈ S, ∀ k, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) → (∀ x, (∀ k : ℕ, ∃ e r, x - j e = (p : R) ^ k * r) → ∃ e, x = j e) → ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) EE), (∀ y : Fin d → R, (∀ i, y i ∈ S) → ∃ z : Fin d → R, (∀ i, z i ∈ S) ∧ ∀ i, ∃ e, y i - (∑ k, j (Pm i k) * φ (z k) - z i) = j e) ∧ (∀ z : Fin d → R, (∀ i, z i ∈ S) → (∀ i, ∃ e, ∑ k, j (Pm i k) * φ (z k) - z i = j e) → ∀ i, ∃ e, z i = j e) := by
  first | exact @GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective | exact GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective | (intros; apply GlobalTheory.DecomplMat.matrix_frob_sub_one_bijective <;> assumption)
