module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.admitted

theorem isAdmissible_of_unitary_irreducible : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    PositivityTheory.Tls2.Iua.AdmG G → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn G σ → Formalism.MainNotions.S.IsIrredOn G σ →
    GlobalTheory.LinRed.IsAdmOn G σ := by
  intro n G hG hA H _ _ _ σ hσ hirr
  refine ⟨hσ.1, hσ.2.2, fun k hk v => hσ.2.1 k hk.1 v, ?_⟩
  intro S hfd hS _
  haveI := hfd
  let b := Module.finBasis ℂ S
  choose Y hYfd _ hvY hY using fun i => hA H σ hσ hirr S hS (b i) (b i).2
  haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYfd
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ, rfl, hΘ⟩
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap (Θ.domRestrict S)).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ GlobalTheory.LinRed.maxCpt G, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    have hks : k.conjTranspose ∈ GlobalTheory.LinRed.maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
    have hiso : ∀ x y, ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (σ k : H →ₗ[ℂ] H) (hσ.2.1 k hk.1)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (σ k u) : S) : H) = σ k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : σ k (σ k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hk.1 _ hks.1, hk1, hσ.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    have h := hΘ k hk _ (S.orthogonalProjectionOnto u).2
    simpa [T, hP] using h
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v = ((⟨v, hv⟩ : S) : H) := rfl
  rw [hv', ← b.sum_repr ⟨v, hv⟩]

  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T] using this

end GlobalTheory.CompanionTheory.admitted

end
