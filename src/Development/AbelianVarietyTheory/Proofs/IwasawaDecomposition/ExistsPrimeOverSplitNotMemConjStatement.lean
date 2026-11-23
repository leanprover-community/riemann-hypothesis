module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralHalf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeOverSplitNotMemConj
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_prime_over_split_not_mem_conj : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → Th.SplitK H p → ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧ (β : H.K) = HostK.conjK H α := by
  first | exact @GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | exact GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj | (intros; apply GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj <;> assumption)
