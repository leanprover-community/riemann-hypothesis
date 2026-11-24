module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.cardUnion :
    ∀ (P : Type) (S : ℕ → Set P) (b : ℕ), Monotone S → (∀ x, ∃ n, x ∈ S n) → (∀ n, CardLe (S n) b) → CardLe P b := by
  intro P S b hmono hcov hcard
  choose m hm using hcov
  have key : ∀ T : Finset P, T.card ≤ b := by
    intro T
    classical
    obtain ⟨hfN, hbN⟩ := hcard (T.sup m)
    have hsub : (↑T : Set P) ⊆ S (T.sup m) := by
      intro x hx
      exact hmono (Finset.le_sup (f := m) hx) (hm x)
    have hfin : (S (T.sup m)).Finite := Set.toFinite _
    have h1 := Nat.card_mono hfin hsub
    have h2 : Nat.card (↑T : Set P) = T.card := by simp
    omega
  have hfin : Finite P := by
    by_contra hnot
    rw [not_finite_iff_infinite] at hnot
    obtain ⟨T, hT⟩ := Infinite.exists_subset_card_eq P (b + 1)
    have := key T
    omega
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite P
  classical
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact key _
