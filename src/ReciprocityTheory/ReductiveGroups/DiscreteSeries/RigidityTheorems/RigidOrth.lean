module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rigid_orth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (j' : V →ₗ[ℂ] H) (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j' w = σ k (j' v))
    (horth : ∀ v v' : V, inner ℂ (j' v') ((v : D) : H) = 0) :
    ∀ g ∈ UJset ε, ∀ v v' : V, inner ℂ (j' v') (σ g ((v : D) : H)) = 0 := by
  intro g hg v v'
  apply rigid_orth_closure hgap hσ hD hV hc hVK j' hj horth v'
  obtain ⟨k, hk, Y, hY, rfl⟩ := polar_UJ hg
  have hVf : FiniteDimensional ℂ V := hV.1
  have hVK' : IsKStableSub ε E V := hV.2.1
  have hv : (v : D) ∈ genSub E V := by
    unfold genSub
    exact Submodule.mem_sInf.mpr fun T hT => hT.1 v.2
  have hkU : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
  have hkJ : kᴴ * Jm ε * k = Jm ε := hkU
  have heU : NormedSpace.exp Y ∈ UJset ε := by
    have hg' : (k * NormedSpace.exp Y)ᴴ * Jm ε * (k * NormedSpace.exp Y) = Jm ε := hg
    rw [Matrix.conjTranspose_mul] at hg'
    calc (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y
        = (NormedSpace.exp Y)ᴴ * (kᴴ * Jm ε * k) * NormedSpace.exp Y := by rw [hkJ]
      _ = Jm ε := by simpa only [Matrix.mul_assoc] using hg'
  rw [hσ.1.2 k hkU _ heU, ContinuousLinearMap.comp_apply]
  have h1 := exp_apply_mem_topologicalClosure hσ hD hVf hVK' hc hY hv
  obtain ⟨Z, hZ, hZk⟩ := exists_exp_eq_of_mem_Kset hk
  refine closure_mapsTo_of_genSub (σ k) (fun w hw => ?_) h1
  simpa only [hZk] using exp_inK_apply_mem_closure hσ hD hVf hVK' hZ hw

end ReciprocityTheory.ChartRestriction.DS
