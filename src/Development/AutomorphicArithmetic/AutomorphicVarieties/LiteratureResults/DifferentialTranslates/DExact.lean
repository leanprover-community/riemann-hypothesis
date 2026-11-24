module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Poincare
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
import Mathlib.Tactic.Linter.Style
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

open UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Dr.dExact :
    DExact := by
  intro Γ V S _ _ _ _ d G hconv q y
  classical
  have hsm : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hmemy : ∀ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((y : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
      ∀ p ∉ G.Y, (y : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p = 0 := y.2
  constructor
  · intro hy
    have hcl : ∀ s, ∀ p ∈ G.Y,
        extDeriv ((y : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) p = 0 := by
      intro s p hp
      have h1 : G.Y.indicator (extDeriv ((y : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)) p = 0 :=
        congrArg (fun z : G.Om (q + 1 + 1) =>
          (z : S → V → V [⋀^Fin (q + 1 + 1)]→L[ℝ] (Fin d → ℂ)) s p) hy
      rwa [Set.indicator_of_mem hp] at h1
    choose η hηs hηd using fun s =>
      poincare V (Fin d → ℂ) G.Y G.isOpen hconv q
        ((y : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) (hmemy s).1 (hcl s)
    let x : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) := fun s => G.Y.indicator (η s)
    have hx : x ∈ G.Om q := by
      show ∀ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (x s) G.Y ∧ ∀ p ∉ G.Y, x s p = 0
      intro s
      refine ⟨(hηs s).congr fun p hp => ?_, fun p hp => ?_⟩
      · simp only [x, Set.indicator_of_mem hp]
      · simp only [x, Set.indicator_of_notMem hp]
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    funext s p
    show G.Y.indicator (extDeriv (x s)) p = (y : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p
    by_cases hp : p ∈ G.Y
    · rw [Set.indicator_of_mem hp]
      have hev : x s =ᶠ[nhds p] η s := by
        filter_upwards [G.isOpen.mem_nhds hp] with z hz
        simp only [x, Set.indicator_of_mem hz]
      rw [hev.extDeriv_eq, hηd s p hp]
    · rw [Set.indicator_of_notMem hp, (hmemy s).2 p hp]
  · rintro ⟨x, rfl⟩
    have hmemx : ∀ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((x : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ p ∉ G.Y, (x : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := x.2
    apply Subtype.ext
    funext s p
    show G.Y.indicator (extDeriv (G.Y.indicator
      (extDeriv ((x : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)))) p = 0
    by_cases hp : p ∈ G.Y
    · rw [Set.indicator_of_mem hp]
      have hev : G.Y.indicator (extDeriv ((x : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) =ᶠ[nhds p]
          extDeriv ((x : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) := by
        filter_upwards [G.isOpen.mem_nhds hp] with z hz
        rw [Set.indicator_of_mem hz]
      rw [hev.extDeriv_eq]
      exact extDeriv_extDeriv_apply ((hmemx s).1.contDiffAt (G.isOpen.mem_nhds hp)) hsm
    · rw [Set.indicator_of_notMem hp]
