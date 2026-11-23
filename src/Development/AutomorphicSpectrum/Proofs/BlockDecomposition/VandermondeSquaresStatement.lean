module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSquares
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

open Finset GlobalTheory.CompanionTheory.CoefId

theorem _root_.GlobalTheory.T.vandermonde_squares : ∀ {n : ℕ} (z : Fin n → ℂ), (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det = (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det * ∏ p ∈ prs n, (z p.1 + z p.2) := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq | exact GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq | (intros; apply GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq <;> assumption)
