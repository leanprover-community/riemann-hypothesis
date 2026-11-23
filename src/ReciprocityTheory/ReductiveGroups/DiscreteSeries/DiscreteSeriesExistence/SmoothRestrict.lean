module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isSmoothVecU_restrict {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (S : Submodule ℂ H) [S.HasOrthogonalProjection] (hSG : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S) (x : S) :
    IsSmoothVecU ε (fun g => (S.orthogonalProjectionOnto ∘L σ g ∘L S.subtypeL : S →L[ℂ] S)) x ↔
      IsSmoothVecU ε σ (x : H) := by
  set P := S.orthogonalProjectionOnto
  have hP : ∀ w : H, w ∈ S → ((P w : S) : H) = w := by
    intro w hw
    have e : P w = ⟨w, hw⟩ := by
      first
        | exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact Submodule.orthogonalProjection_mem_subspace_eq_self (⟨w, hw⟩ : S)
        | exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := S) ⟨w, hw⟩ : _)
        | (show P ((⟨w, hw⟩ : S) : H) = ⟨w, hw⟩; simp [P])
    rw [e]
  constructor
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => ((F g : S) : H), hU, hg₀U, (S.subtypeL.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    have hmem : σ g (x : H) ∈ S := hSG g hg x x.2
    dsimp only at e1 ⊢
    rw [← e1]
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact (hP _ hmem).symm
  · intro h g₀ hg₀
    obtain ⟨U, F, hU, hg₀U, hF, hFe⟩ := h g₀ hg₀
    refine ⟨U, fun g => P (F g), hU, hg₀U, (P.restrictScalars ℝ).contDiff.comp_contDiffOn hF, ?_⟩
    intro g hgU hg
    have e1 := hFe g hgU hg
    dsimp only at e1 ⊢
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [e1]

end ReciprocityTheory.ChartRestriction.DS
