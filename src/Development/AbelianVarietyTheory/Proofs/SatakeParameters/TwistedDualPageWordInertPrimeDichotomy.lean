module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNegStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThickStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThickStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbeddingStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_inert_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ)
    (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 →
    (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨
      (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  intro D L C j ε τ φ l hR hl hφ
  refine ⟨GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR, ?_⟩
  by_cases h : φ = D.R.cc ∧ Thick D.host τ
  · obtain ⟨rfl, hτ⟩ := h
    exact Or.inr ⟨rfl, GlobalTheory.T.twistedDualOrbitPageWord_conj_hypAT_allThick L C j ε τ l hR hl hτ⟩
  · left
    have hLw : 3 ≤ D.host.Lw := by
      have := L.weightLength_ge_depth
      omega
    obtain ⟨h3, i, hi⟩ := GlobalTheory.T.inertPrime_nonthick_letter_no_three_thick D.host τ φ hLw hφ h
    have hth := GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR
    refine ⟨(GlobalTheory.T.embeddingSign_alternate_of_sign_neg ε τ φ hφ).2, ⟨i, fun h' => hi ((hth i).1 h')⟩, ?_⟩
    intro k hk
    exact h3 k ⟨(hth _).1 hk.1, (hth _).1 hk.2.1, (hth _).1 hk.2.2⟩

end GlobalTheory.HTW
