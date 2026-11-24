module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_orbital_valid : FamJFOK := by
  intro Wp Wq _ _ _ _ _ _ P T j G hG t ht
  obtain ⟨hsm, hcpt⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hcpt {t} isCompact_singleton (by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact ht)
  have hzero : ∀ γ, γ ∉ C → G t γ = 0 := by
    intro γ hγ
    by_contra h
    exact hγ (hCε t rfl γ h).1
  have hCk : B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hsm t ht γ₀ hγ₀
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), ?_, hmem, ?_, ?_⟩
    · exact hU.preimage (continuous_const.prodMk continuous_id)
    · have hd : ContDiff ℝ ∞ (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
        contDiff_const.prodMk contDiff_id
      exact hf.comp hd.contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγV
      exact hfe (t, γ) hγ hγV
  refine ⟨⟨?_, ε, hε, ?_⟩, ?_⟩
  · exact JFxG.cptInCC_G hCk hC (fun g _ hg => hzero g hg)
  · intro g hg hne
    exact (hCε t rfl g hne).2 hg
  · refine HasCompactSupport.intro hC ?_
    exact hzero

end Formalism.FourierDecayAlt.P.CutSH
