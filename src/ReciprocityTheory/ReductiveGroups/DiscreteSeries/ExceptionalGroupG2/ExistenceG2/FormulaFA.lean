module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumInj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaFA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.MultOne

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ} {ε : Fin n → Bool}

section General

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Smooth

end General


variable {Λ : Fin n → ℝ}


section Psi

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem ffa_kmap_zero (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (B : T.V →ₗ[ℂ] L2 ε) (hB : ∀ (k : S7.KG ε) (v : T.V), B (T.op k v) = rreg ε (S7.toMK k) (B v))
    (hrange : ∀ v, B v ∈ Hlam ε Ψ v₀)
    (horth : ∀ v v' : T.V, inner ℂ (B v') (uniformisationL2 ε Ψ v₀ v) = 0) : B = 0 := by
  have hσ := rreg_isURepOn ε
  have h0 := rigid_multOne hgap hσ (isDerivedOn_smE hσ) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
    (datumV_kStable hP v₀) (B ∘ₗ ffaJinvL hP hv₀) ?hj (fun v => hrange _) ?horth
  · refine LinearMap.ext fun v => ?_
    let xv : datumV ε Ψ v₀ := ⟨⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩, (mem_datumV_iff hP v₀ _).2 ⟨v, rfl⟩⟩
    have hxv : ffaJinvL hP hv₀ xv = v := uniformisationL2_injective hP hv₀ (ffaJinv_spec hP xv)
    have := LinearMap.congr_fun h0 xv
    rw [LinearMap.comp_apply, hxv] at this
    rw [this, LinearMap.zero_apply, LinearMap.zero_apply]
  · intro k hk v w hvw
    obtain ⟨k', rfl⟩ := ffa_Kset hk
    have e : ffaJinvL hP hv₀ w = T.op k' (ffaJinvL hP hv₀ v) := uniformisationL2_injective hP hv₀ (by
      rw [← rightRegular_datumEmbedding hP]
      show uniformisationL2 ε Ψ v₀ (ffaJinv hP w) = rreg ε _ (uniformisationL2 ε Ψ v₀ (ffaJinv hP v))
      rw [ffaJinv_spec, ffaJinv_spec]
      exact hvw)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, hB]
  · intro v v'
    show inner ℂ (B (ffaJinv hP v')) _ = 0
    rw [← ffaJinv_spec hP v]
    exact horth _ _

end Psi

end ReciprocityTheory.ChartRestriction.DS.G2
