module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Helpers

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Helpers

section Wt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

end Wt

section Key

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

end Key

section Data

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_kfin_le (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (S : Submodule ℂ H) (hS : S ≤ closGen E V) (hSf : FiniteDimensional ℂ S)
    (hSK : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S) : S ≤ (genSub E V).map D.subtype := by
  classical
  haveI := hSf
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hfin := kfin_wts_finite hσ S
  choose k hk using fun μ : Fin n → ℝ => khw_mem_layer hD.glRep hU hV hc hgap μ
  refine le_trans (kfin_key hσ hD hV.1 hV.2.1 S hS hSK (hfin.toFinset.sup k) ?_)
    (Submodule.map_mono (layer_le_genSub _))
  intro μ w hw hwμ hμS
  exact layer_mono (Finset.le_sup (hfin.mem_toFinset.2 hμS)) (hk μ w hw hwμ)

end Data

end ReciprocityTheory.ChartRestriction.DS.G2
