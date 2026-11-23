module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockSolutionExists
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

open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

theorem _root_.GlobalTheory.T.hermitian_block_solution_exists : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n r : ℕ}, r ≤ n → ∀ (c : Matrix (Fin r) (Fin n) K) (a C D : Matrix (Fin n) (Fin n) K) (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), IsCompl c a → C = T * c → L * T = 1 → C * cT σ D = D * cT σ C → ∃ b : Matrix (Fin r) (Fin r) K, cT σ b = b ∧ C * a⁻¹ * (1 - eId K n r - extB b) + D * cT σ a * eId K n r = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | exact GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft | (intros; apply GlobalTheory.CompanionTheory.BruhatCell.exists_hermitian_lowerLeft <;> assumption)
