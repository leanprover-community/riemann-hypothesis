module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatShift

theorem flat_step {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) (ρ : E →+* ℂ) (i j : ℕ) (hi : i < Dw.mult ρ) (hj : j < Dw.mult ρ) :
    (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = (wtOf Dw (flatWt Dw τ) 0).1 (ρ, j) ∧
      -1 ≤ (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) := by
  simp only [wtOf, flatWt, parWt, Datum.mult] at hi hj ⊢
  split_ifs at hi hj ⊢ <;> omega

theorem exists_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H), Dom a n → (∀ ρ i, i < Dw.mult ρ → 2 ≤ a (ρ, i)) → ∃ a' : (E →+* ℂ) × ℕ → ℕ, Dom a' n ∧ (∀ ρ i, i < Dw.mult ρ → 1 ≤ a' (ρ, i)) ∧ exZ Dw (wtZ a' n) = exZ Dw (wtZ a n + wtOf Dw (flatWt Dw τ) 0) := by
  intro E _ _ _ H Dw a n τ hD ha
  refine ⟨fun x => if x.2 < Dw.mult x.1 then ((a x : ℤ) + (wtOf Dw (flatWt Dw τ) 0).1 x).toNat else 0,
    ⟨fun ρ i j hij => ?_, hD.2⟩, fun ρ i hi => ?_, ?_⟩
  · by_cases hj : j < Dw.mult ρ
    · have hi : i < Dw.mult ρ := lt_of_le_of_lt hij hj
      have h1 : a (ρ, j) ≤ a (ρ, i) := hD.1 ρ hij
      obtain ⟨e, -⟩ := flat_step Dw τ ρ i j hi hj
      simp only [if_pos hi, if_pos hj]
      omega
    · simp only [if_neg hj]; exact Nat.zero_le _
  · have h1 := ha ρ i hi
    have h2 := (flat_step Dw τ ρ i i hi hi).2
    simp only [if_pos hi]
    omega
  · funext x
    rcases x with _ | ⟨ρ, i⟩
    · simp [exZ, wtZ, wtOf_snd]
    · have h1 := ha ρ i i.2
      have h2 := (flat_step Dw τ ρ i i i.2 i.2).2
      simp only [exZ, wtZ, Prod.fst_add, Pi.add_apply, if_pos i.2]
      omega

end GlobalTheory.FlatShift
