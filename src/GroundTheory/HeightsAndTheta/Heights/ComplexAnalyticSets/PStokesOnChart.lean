module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOnChart
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffLimit
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOffDiscriminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnChart.proof (hD : ComplexSets.DiscriminantCover.Statement) (hL : CutOffLimit.Statement) :
    StokesOnChart.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
      (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → chartInt J A f (vecCons g φ) = chartInt J A g (vecCons f φ) := by
    intro n d J A f g φ hJ hdim hAf hf hg hφ hc
    obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

    have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
      intro x hx hPx
      obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
      obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
      refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
      · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
        exact hw'.1
      · rintro x' hx' -
        rw [hZV] at hx'
        obtain ⟨w, hw, rfl⟩ := hx'
        rw [hAs w hw]
    obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
    obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
    refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
    obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
    obtain ⟨V, hV, hZV, hfV⟩ := hf
    have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
    refine (StokesOffDiscriminant.proof n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
      ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
    rw [hχ0 x hx, zero_mul]
  intro n d J A f g φ hJ hdim hAf hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J A f g φ hJ hdim hAf hf hg hφ hc
  · exact (key n d J A g f φ hJ hdim hAf hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
