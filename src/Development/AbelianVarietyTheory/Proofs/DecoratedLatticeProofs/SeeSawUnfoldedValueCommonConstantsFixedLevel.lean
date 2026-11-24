module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepValueFixedLevelPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlacesStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GValAll

theorem gValue_common : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → GValue (t := t) (v.withCG a) := by
  intro D c v n G hc hv hG
  classical
  refine ⟨fun j => if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose
    else if h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
      (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram then
      (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose else 1, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m
    · rw [dite_eq_left h1]; exact (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.1
    · rw [dite_eq_right h1]
      by_cases h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram
      · rw [dite_eq_left h2]; exact (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.1
      · rw [dite_eq_right h2]; exact one_ne_zero
  · intro t _ hw
    refine ⟨fun j σ h Ψ₁ Ψ₂ h₁ h₂ => ?_, fun j h Ψ₁ Ψ₂ h₁ h₂ => ?_⟩
    · have h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := ⟨σ, h⟩
      have hσ : h1.choose = σ := by have := h1.choose_spec; omega
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dite_eq_left h1]
      have key := (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.2
      revert key
      generalize (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose = C
      intro key
      subst hσ
      exact key _ _ Ψ₁ Ψ₂ h₁ h₂
    · have h1 : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := by rintro ⟨σ, hσ⟩; omega
      obtain ⟨hr, hτ⟩ := hw.tau j h
      have h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram := ⟨h, hr, hτ⟩
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dite_eq_right h1, dite_eq_left h2]
      exact (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.2 _ Ψ₁ Ψ₂ h₁ h₂

end GlobalTheory.SeeSaw.GValAll
