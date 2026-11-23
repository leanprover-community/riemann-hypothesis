module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_nonneg_of_compat_fixedBase : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (ph : X → ℝ) (U : Set X) (x₀ : X) (j : Fin B.n), A.Compatible B →
    IsPotential A th → IsOpen U → A.SmoothOn U ph → IsPshOn A U (th + LocPot.ofFun ph) →
    (B.chart j).source ⊆ th.U x₀ → ∀ y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
    ∀ w : Fin e → ℂ,
    0 ≤ levi (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) y w := by
  intro e X _ A B th ph U x₀ j hAB hth hU hph hpsh hsrc y hy w
  have hp : (B.chart j).symm y ∈ (B.chart j).source := (B.chart j).map_target hy.1
  obtain ⟨k, hk⟩ := A.cover ((B.chart j).symm y)
  have hτ : AnalyticAt ℂ (A.chart k ∘ (B.chart j).symm) y := hAB.2 j k y ⟨hy.1, hk⟩
  have hsymm : (A.chart k).symm ((A.chart k ∘ (B.chart j).symm) y) = (B.chart j).symm y :=
    (A.chart k).left_inv hk
  have htgt : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target := (A.chart k).map_source hk
  have hthU : (B.chart j).symm y ∈ th.U x₀ := hsrc hp
  have hO1 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀) :=
    (A.chart k).isOpen_inter_preimage_symm (th.isOpen_U x₀)
  have hO2 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).isOpen_inter_preimage_symm hU
  have hm1 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀ :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hthU⟩
  have hm2 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' U :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hy.2⟩
  have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hC1 : ContDiffAt ℝ 2 (th.φ x₀ ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hth.1 x₀ k).contDiffAt (hO1.mem_nhds hm1)).of_le h2
  have hC2 : ContDiffAt ℝ 2 (ph ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hph k).contDiffAt (hO2.mem_nhds hm2)).of_le h2
  have hC : ContDiffAt ℝ 2 (fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z))
      ((A.chart k ∘ (B.chart j).symm) y) := hC1.add hC2
  have hev : (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) =ᶠ[𝓝 y]
      ((fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z)) ∘
        (A.chart k ∘ (B.chart j).symm)) := by
    have h1 : ∀ᶠ z in 𝓝 y, (B.chart j).symm z ∈ (A.chart k).source :=
      ((B.chart j).continuousAt_symm hy.1).eventually ((A.chart k).open_source.mem_nhds hk)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply, (A.chart k).left_inv hz]
  rw [levi_congr hev w, levi_comp w hτ hC]
  exact hpsh x₀ k _ ⟨htgt, ⟨hm1.2, Set.mem_univ _⟩, hm2.2⟩ _

end GlobalTheory.CompanionTheory.LeviChart
