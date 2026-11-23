module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

theorem UpperTheory.exists_eqns_of_weighted_generators :
    ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) (x : A →ₐ[O] O) (r s r' s' m : ℕ) {κ : Type} [Finite κ] (g : κ → A) (w : κ → ℤ),
          (∀ i, g i ∈ 𝒜 (w i)) → (∀ i, x (g i) = 0) → (∀ i, -2 ≤ w i ∧ w i ≤ 2) →
          Nat.card {i // w i = -1} = r + 1 → Nat.card {i // w i = -2} = s → Nat.card {i // w i = 1} = r' → Nat.card {i // w i = 2} = s' → Nat.card {i // w i = 0} = m →
          ∃ Q : Eqns 𝒜 x r s r' s' m, Q.ideal = Ideal.span (Set.range g) := by
  intro O A _ _ _ 𝒜 x r s r' s' m κ _ g w hg hx hw h1 h2 h3 h4 h5
  have key : ∀ (j : ℤ) (n : ℕ), Nat.card {i // w i = j} = n →
      ∃ F : Fin n → A, (∀ k, F k ∈ 𝒜 j ∧ x (F k) = 0) ∧ Set.range F = g '' {i | w i = j} := by
    intro j n hn
    let e := Finite.equivFinOfCardEq hn
    refine ⟨fun k => g (e.symm k).1, fun k => ⟨?_, hx _⟩, ?_⟩
    · have := hg (e.symm k).1
      rwa [(e.symm k).2] at this
    · ext a
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨(e.symm k).1, (e.symm k).2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨e ⟨i, hi⟩, by simp⟩
  obtain ⟨F, hF, rF⟩ := key _ _ h1
  obtain ⟨G, hG, rG⟩ := key _ _ h2
  obtain ⟨E, hE, rE⟩ := key _ _ h3
  obtain ⟨E', hE', rE'⟩ := key _ _ h4
  obtain ⟨Z, hZ, rZ⟩ := key _ _ h5
  refine ⟨⟨F, G, E, E', Z, fun i => (hF i).1, fun i => (hG i).1, fun i => (hE i).1, fun i => (hE' i).1, hZ⟩, ?_⟩
  show Ideal.span (Set.range F ∪ Set.range G ∪ Set.range E ∪ Set.range E' ∪ Set.range Z) = _
  rw [rF, rG, rE, rE', rZ, ← Set.image_union, ← Set.image_union, ← Set.image_union, ← Set.image_union,
    ← Set.image_univ]
  congr 2
  ext i
  have := hw i
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  omega
