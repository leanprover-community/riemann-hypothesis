module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

theorem rigid_multOne {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (j' : V →ₗ[ℂ] H) (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j' w = σ k (j' v))
    (hrange : ∀ v : V, j' v ∈ closGen E V)
    (horth : ∀ v v' : V, inner ℂ (j' v') ((v : D) : H) = 0) :
    j' = 0 := by
  apply LinearMap.ext
  intro v'
  have h0 : ∀ y ∈ closGen E V, inner ℂ (j' v') y = 0 := by
    intro y hy
    have hcl : IsClosed {y : H | inner ℂ (j' v') y = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub : ((genSub E V).map D.subtype : Set H) ⊆ {y | inner ℂ (j' v') y = 0} := by
      rintro _ ⟨y, hy, rfl⟩
      exact rigid_orth_genSub hgap hσ hD hV hc hVK j' hj horth v' y hy
    have hy' : y ∈ closure ((genSub E V).map D.subtype : Set H) := by
      rwa [← Submodule.topologicalClosure_coe]
    exact closure_minimal hsub hcl hy'
  rw [LinearMap.zero_apply]
  exact inner_self_eq_zero.1 (h0 _ (hrange v'))

end ReciprocityTheory.ChartRestriction.DS.G2
