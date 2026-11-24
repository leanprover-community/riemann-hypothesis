module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonHeisenbergLevelWeilTransformCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateThetaFunLeSchwartzMajorantLevelStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section

namespace GlobalTheory.Unf

theorem mixS_om_compact_maj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ Kp : Set (GA D S × GA D T), IsCompact Kp → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ p ∈ Kp, ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ ≤ C * maj θ K N x := by
  intro D ψ S T χS χT om hω θ hθ S₀ ρ d v f hf Kp hKp
  obtain ⟨U, hU, hUK⟩ := GlobalTheory.T.exists_common_heisenbergLevel_weilTransform_compact D ψ S T χS χT om hω f hf Kp hKp
  obtain ⟨K, hK, hKN⟩ := GlobalTheory.T.mixedCoordinate_thetaFun_le_schwartz_majorant_level D ψ hω.std θ hθ S S₀ T ρ d v U hU
  refine ⟨K, hK, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hKN N
  obtain ⟨A, hA⟩ := GlobalTheory.WeilWordGrowth.sup_words_growth D ψ S T χS χT om hω θ hθ N
  obtain ⟨c, hc⟩ := hA f hf
  have hcont : Continuous fun p : GA D S × GA D T =>
      c * (GlobalTheory.Grow.height S p.1 * GlobalTheory.Grow.height T p.2) ^ A :=
    continuous_const.mul ((((GlobalTheory.Grow.continuous_height S).comp continuous_fst).mul
      ((GlobalTheory.Grow.continuous_height T).comp continuous_snd)).pow A)
  obtain ⟨B, hB⟩ := hKp.bddAbove_image hcont.continuousOn
  refine ⟨(C : ℝ) * max B 0, fun p hp x w => ?_⟩
  have h1 := hC (om p f) (hUK p hp) x w
  have h2 : supSob ψ θ N (om p f) ≤ ENNReal.ofReal (max B 0) :=
    (hc p.1 p.2).trans (ENNReal.ofReal_le_ofReal ((hB ⟨p, hp, rfl⟩).trans (le_max_left _ _)))
  have hm := maj_nonneg θ K N x
  have h3 : ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * max B 0 * maj θ K N x) := by
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
    gcongr
  rw [← ofReal_norm_eq_enorm] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

end GlobalTheory.Unf

end
