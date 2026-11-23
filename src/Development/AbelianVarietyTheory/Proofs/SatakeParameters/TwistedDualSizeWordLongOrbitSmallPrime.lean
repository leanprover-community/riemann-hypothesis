module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeParametersRoundedSizeBoundStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersClusterDepthAtPrimeEqLeastPowerDepthStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParametersLeastPowerDepthSpecStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement
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

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordsB_recWord_of_long_orbit : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (C C₂ : ℝ) (j : Fin D.R.m)
    (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 2 * C₂ ≤ C →
    11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → 4 * D.host.Lw < orderOf ψ.2 → WordsB L l C₂ (recWord L j ε g) := by
  intro D L hP C C₂ j ε n g ψ l hR hO hC hl hlA hord
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := by
    funext a
    rw [hg a]
    rfl
  generalize g 0 = τ at hgl
  subst hgl
  have hjA : jA L l = depth L l := GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth L l hl hlA
  have hA := GlobalTheory.T.twistedDualPageWord_clusterDepth_long_orbit L hP C j ε τ ψ l hR hl hlA hord
  obtain ⟨_, _, hjn, _, hcl⟩ := hA
  have hD := GlobalTheory.T.leastPowerDepth_spec L hP l hl
  have hth : ThickN (recWord L j ε (letter τ ψ)).b
      (recWord L j ε (letter τ ψ)).η (recWord L j ε (letter τ ψ)).sz =
      (pageWord L j ε τ ψ).thick := by
    funext a
    exact propext (GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR a).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hjA]; exact hjn
  · rcases le_or_gt 0 C₂ with h0 | h0
    · rw [hjA]
      exact GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L C₂ C (depth L l) hR h0 hC hD.2.1
    · have h1 : (0 : ℝ) ≤ ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) := by
        positivity
      have h2 : C₂ * ((jA L l : ℝ) + 1) * ((((recWord L j ε (letter τ ψ)).w +
          (recWord L j ε (letter τ ψ)).S + (recWord L j ε (letter τ ψ)).η : ℕ) : ℝ) + 1) ≤ 0 := by
        rw [mul_assoc]; exact mul_nonpos_of_nonpos_of_nonneg h0.le h1
      exact h2.trans (Nat.cast_nonneg _)
  · rw [hth, hjA]; exact hcl

end GlobalTheory.HTW.Rec
