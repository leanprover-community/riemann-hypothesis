module

public import Mathlib.RingTheory.Length
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.chain :
    ∀ (O V St : Type) [CommRing O] [AddCommGroup V] [Module O V] (S : St → Submodule O V) (j : St → ℕ) (J : ℕ), (∀ s, j s ≤ J) →
    (∀ s, S s ≠ ⊥ → ∃ s', j s < j s' ∧ Module.length O (S s) + j s ≤ Module.length O (S s') + j s') → ∀ s, Module.length O (S s) + j s ≤ J := by
  intro O V St _ _ _ S j J hJ hstep
  have key : ∀ (n : ℕ) (s : St), J - j s ≤ n → Module.length O (S s) + j s ≤ J := by
    intro n
    induction n with
    | zero =>
      intro s hs
      by_cases h : S s = ⊥
      · have h0 : Module.length O (S s) = 0 := by
          rw [h]; exact Module.length_eq_zero
        rw [h0, zero_add]
        exact_mod_cast hJ s
      · obtain ⟨s', h1, -⟩ := hstep s h
        have := hJ s'
        omega
    | succ n ih =>
      intro s hs
      by_cases h : S s = ⊥
      · have h0 : Module.length O (S s) = 0 := by
          rw [h]; exact Module.length_eq_zero
        rw [h0, zero_add]
        exact_mod_cast hJ s
      · obtain ⟨s', h1, h2⟩ := hstep s h
        have := hJ s'
        exact h2.trans (ih s' (by omega))
  intro s
  exact key _ s le_rfl
