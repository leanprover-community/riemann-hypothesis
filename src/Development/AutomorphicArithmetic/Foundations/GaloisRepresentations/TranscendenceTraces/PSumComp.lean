module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumComp_of :
    FibFin → SumComp := by
  intro hF W V U r p _ _ Ω _ x M _ c
  have hset : fib (r ≫ p) x = ⋃ y ∈ fib p x, fib r y := by
    ext z
    simp only [fib, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hz
      exact ⟨z ≫ r, by rw [Category.assoc]; exact hz, rfl⟩
    · rintro ⟨y, hy, hz⟩
      rw [← Category.assoc, hz, hy]
  have hdisj : (fib p x).PairwiseDisjoint (fun y => fib r y) := by
    intro y₁ _ y₂ _ hne
    refine Set.disjoint_left.mpr ?_
    intro z h₁ h₂
    apply hne
    simp only [fib, Set.mem_setOf_eq] at h₁ h₂
    rw [← h₁, ← h₂]
  change ∑ᶠ z ∈ fib (r ≫ p) x, c z = ∑ᶠ y ∈ fib p x, ∑ᶠ z ∈ fib r y, c z
  rw [hset]
  exact finsum_mem_biUnion hdisj (hF p Ω x) (fun y _ => hF r Ω y)
