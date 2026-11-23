module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentDivisibleCongruent
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

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.exists_orthogonalIdempotent_divisible_congruent : (∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w) → ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪) := by
  first | exact @GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit | exact GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit | (intros; apply GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit <;> assumption)
