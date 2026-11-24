module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianRepresentationsResidue
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

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

theorem _root_.GlobalTheory.T.card_hermitian_representations_residue : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E), cT τ S = S → IsUnit S.det → cT τ T = T → IsUnit T.det → (Nat.card {x : Matrix (Fin m) (Fin n) E // cT τ x * S * x = T} : ℝ) = (q : ℝ) ^ (2 * m * n - n ^ 2) * ∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings | exact GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings | (intros; apply GlobalTheory.CompanionTheory.UnrDens.Emb.card_isometric_embeddings <;> assumption)
