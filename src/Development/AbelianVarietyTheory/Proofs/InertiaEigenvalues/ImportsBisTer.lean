module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
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

namespace GlobalTheory.SingleStatement

theorem main : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {ι : Type} (s : Finset ι) (g : ι → ℂ_[p]) {r : ℝ},
    (0 : ℝ) ≤ r → (∀ k ∈ s, ‖g k‖ ≤ r) → ‖∑ k ∈ s, g k‖ ≤ r := by
  intro p _ ι s g r hr hg
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖g a‖ ≤ r := hg a (Finset.mem_insert_self a s)
    have h2 : ‖∑ k ∈ s, g k‖ ≤ r := ih (fun k hk => hg k (Finset.mem_insert_of_mem hk))
    exact (PadicComplex.isNonarchimedean p (g a) (∑ k ∈ s, g k)).trans (max_le h1 h2)

end GlobalTheory.SingleStatement
