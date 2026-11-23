module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPerfectRadical
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

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfClos

theorem exists_PQ : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S), (p : S) = 0 →
    ∃ (T : Type) (_ : CommRing T) (i : S →+* T), PQ p i I := by
  intro p hpf S _ I hp
  obtain ⟨T, inst, i, hc, hb, hpow, hker⟩ := exists_perfect_radical p S I hp
  refine ⟨T, inst, i, ⟨⟨hc, hb⟩, hpow, fun x => ?_⟩⟩
  rw [hker x]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, Ideal.pow_mem_of_pow_mem I hn ?_⟩
    exact (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  · rintro ⟨k, hk⟩
    exact ⟨p ^ k, hk⟩

end GlobalTheory.CompanionTheory.PerfClos
