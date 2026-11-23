module

public import Development.AutomorphicArithmetic.ThickFrames.MarkedLow
public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
public import Development.AutomorphicArithmetic.ThickFrames.topsGroup
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0

theorem UpperTheory.BernoulliSumsFrobeniusOrbits.topsFrame :
    ∀ eps Co Lb : ℝ, 0 < eps → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ x ≥ x₀, ∀ (φ : Formalism.HC.Frame) (L₂ : ℕ),
      x ^ hE eps / 2 ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ Co * x ^ hE eps → (φ.o : ℝ) ≤ Co → (L₂ : ℝ) ≤ Lb →
      ∀ bs : φ.A → φ.A → φ.A, (∀ h t, ∃ i : ℕ, bs h t + i • h = t) →
      ∀ (PP : Finset ℕ) (hp : ℕ → φ.A) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) →
      ∃ TT : Finset φ.A, dE eps x * φ.ord / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * dE eps x * φ.ord ∧
        φ.Shares TT (x ^ (-1 + eps)) ∧
        ∑ p ∈ PP, ω p * (({t : φ.A | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p))
            (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (KE eps) (rE eps)
            (dE eps x) (hE eps) x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * x ^ (-2 : ℝ)) * dE eps x * φ.ord * ∑ p ∈ PP, ω p := by
  intro eps Co Lb heps
  obtain ⟨Cb, x₀, hCb, hmain⟩ := topsGroup eps Co Lb heps
  refine ⟨Cb, x₀, hCb, ?_⟩
  intro x hx φ L₂ h1 h2 h3 h4 bs hbs PP hp ω hω hord
  classical
  have hcard : (Fintype.card φ.A : ℝ) = φ.ord := by
    rw [← Nat.card_eq_fintype_card, Formalism.HC.Frame.natCard_A]
  have hidx : (φ.A0.index : ℝ) = φ.o := by
    rw [Formalism.HC.Frame.index_A0_eq_o]
  obtain ⟨TT, t1, t2, t3, t4⟩ := hmain x hx φ.A φ.A0 L₂ (by rw [hcard]; exact h1)
    (by rw [hcard]; exact h2) (by rw [hidx]; exact h3) h4 bs hbs PP hp ω hω hord
  refine ⟨TT, ?_, ?_, ?_, ?_⟩
  · rw [← hcard]
    exact t1
  · rw [← hcard]
    exact t2
  · intro γ
    have := t3 γ
    rw [hidx] at this
    unfold Formalism.HC.Frame.lam
    convert this using 4
  · rw [← hcard]
    convert t4 using 6
