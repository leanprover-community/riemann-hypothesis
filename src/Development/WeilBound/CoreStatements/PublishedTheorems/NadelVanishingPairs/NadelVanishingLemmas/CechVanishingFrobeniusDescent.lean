module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTopPartEqZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosedStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem descend_vanishing : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : ℕ → CartierDiv X), Decomp p 𝒜 → (∀ e, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ G (e + 1) = p • G e + ∑ c, ρ c • E c) → ∀ e₀ : ℕ, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e₀) a) b) → ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G 0) a) b := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G hD hG e₀ h0
  have step : ∀ e, (∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G (e + 1)) a) b) →
      ∀ a b : ℕ, n < a + b → DI.CechZero (cechFam 𝒜 (G e) a) b := by
    intro e he a b hab
    obtain ⟨ρ, hρ, hGe⟩ := hG e
    refine hD (G e) ρ hρ a b ?_
    rw [← hGe]
    refine DI.hypZero_of_cechZero (extD X.functionField) _ (fun x => CechDR.dDR_dDR x) ?_ ?_ (a + b) ?_
    · intro q s t _ hst
      show latSec _ _ ≤ latSec _ _
      have hle : inter 𝒜.U t ≤ inter 𝒜.U s := Finset.inf_mono hst
      intro x hx
      simp only [latSec, AddSubgroup.mem_iInf] at hx ⊢
      exact fun y hy => hx y (hle hy)
    · intro q s x hx
      have := GlobalTheory.T.log_sections_differential_closed p 𝒜 (G e) ρ hρ q (inter 𝒜.U s) x (by rw [← hGe]; exact hx)
      rw [← hGe] at this
      exact this
    · intro q b' hqb
      exact he q b' (by omega)
  induction e₀ with
  | zero => exact h0
  | succ k ih => exact ih (step k h0)

end GlobalTheory.LogDR
