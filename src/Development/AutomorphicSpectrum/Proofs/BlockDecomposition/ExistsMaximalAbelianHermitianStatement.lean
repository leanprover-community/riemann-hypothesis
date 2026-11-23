module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMaximalAbelianHermitian
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

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.exists_maximal_abelian_hermitian : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)), ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧ (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧ ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  first | exact @GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | exact GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | (intros; apply GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace <;> assumption)
