module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.CutSH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_derivative : CutSH.FamDeriv := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG v
  obtain ⟨hloc, hsupp⟩ := hG
  refine ⟨?_, ?_⟩
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hGf⟩ := hloc t₀ ht₀ γ₀ hγ₀
    refine ⟨U, fun p => fderiv ℝ f p ((v, 0) : ℂ × B.Mat P.k (P.r - (j + 1))), hU, hmem, ?_, ?_⟩
    · exact (hf.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
    · rintro ⟨t, γ⟩ hp hγ
      simp only [famP, Set.indicator_of_mem hγ]
      have hev : (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun u => f (u, γ) := by
        have hc : Continuous fun u : ℂ => (u, γ) := continuous_id.prodMk continuous_const
        have : ∀ᶠ u in 𝓝 t, (u, γ) ∈ U := hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)
        filter_upwards [this] with u hu
        exact hGf (u, γ) hu hγ
      rw [hev.fderiv_eq]
      have hfd : DifferentiableAt ℝ f (t, γ) :=
        (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
      have hin := hasFDerivAt_prodMk_left (𝕜 := ℝ) t γ
      rw [show (fun u : ℂ => f (u, γ)) = f ∘ fun u => (u, γ) from rfl, (hfd.hasFDerivAt.comp t hin).fderiv]
      rfl
  · intro K hK hK0
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (isOpen_compl_singleton (x := (0 : ℂ)))
      (fun t ht => by simpa using hK0 t ht)
    obtain ⟨C, hC, ε, hε, hCε⟩ := hsupp (Metric.cthickening δ K) hK.cthickening
      (fun t ht => by simpa using hsub ht)
    refine ⟨C, hC, ε, hε, fun t ht γ hne => ?_⟩
    have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := by
      by_contra h
      exact hne (by simp [famP, Set.indicator_of_notMem h])
    have hd : fderiv ℝ (fun u : ℂ => G u γ) t v ≠ 0 := by
      simpa [famP, Set.indicator_of_mem hγ] using hne
    have hex : ∃ u ∈ Metric.ball t δ, G u γ ≠ 0 := by
      by_contra hno
      push Not at hno
      have hev : (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Metric.ball_mem_nhds t hδ] with u hu using hno u hu
      exact hd (by rw [hev.fderiv_eq]; simp)
    obtain ⟨u, hu, hGu⟩ := hex
    have huK : u ∈ Metric.cthickening δ K :=
      Metric.mem_cthickening_of_dist_le u t δ K ht (le_of_lt (Metric.mem_ball.mp hu))
    obtain ⟨hγC, hε'⟩ := hCε u huK γ hGu
    exact ⟨hγC, fun _ => hε' hγ⟩

end Formalism.FourierDecayAlt.P
