module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealGeneratorAtPrimesOver
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

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_mem_fractionalIdeal_generator_at_primes_over' : ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  first | exact @GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over | exact GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over | (intros; apply GlobalTheory.exists_mem_fractionalIdeal_generator_at_primes_over <;> assumption)
