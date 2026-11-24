module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiagHermitianTrivialOfSumFourSquares
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMoveDefiniteSimilitudePairMarked
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

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_polynomial_move_definiteSimilitudePair_marked : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (P0 : Polynomial G.F) (μ : ℂ) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → Irreducible P0 → P0.eval₂ v.embedding μ = 0 → ∃ A : Polynomial G.F, (∀ Q : DPair G, Q.pol = P0 → ∃ P : Pair G, P.γ = Q.γ ∧ P.c = Q.c ∧ (P.β : G.C) = Polynomial.aeval (Q.γ : G.C) A * Q.β ∧ P.Mark μ ∧ (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) ∧ (∀ P : Pair G, P.pol = P0 → P.Mark μ → ∃ Q : DPair G, Q.γ = P.γ ∧ Q.c = P.c ∧ (P.β : G.C) = Polynomial.aeval (P.γ : G.C) A * Q.β ∧ (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) := by
  first | (exact @GlobalTheory.LKDef.move_definite) | (exact GlobalTheory.LKDef.move_definite) | (intros; apply GlobalTheory.LKDef.move_definite  <;> assumption)
