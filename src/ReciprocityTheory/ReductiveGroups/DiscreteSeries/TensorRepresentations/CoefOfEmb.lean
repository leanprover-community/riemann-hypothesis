module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefBTensSubKStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefETensGrpMul
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefDTensActPow

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def tensGrp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) : Fin n → H :=
  fun c => ∑ d, (cond dual ((g⁻¹) d c) (g c d)) • σ g (f d)

theorem coef_of_emb (dual : Bool) {lam lam' : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {V' : Submodule ℂ D} (hgap' : StdGap ε lam') (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι) :
    (∀ f ∈ tensSub (genSub E V), ∀ x' ∈ genSub E V', ∃ z ∈ genSub E V', ∀ g ∈ UJset ε,
      ∑ c, inner ℂ ((f c : D) : H) (tensGrp dual σ g (fun d => ((ι x' d : D) : H)) c) =
        inner ℂ ((z : D) : H) (σ g ((x' : D) : H))) ∧
    ∀ z ∈ genSub E V', ∀ x' ∈ genSub E V', ∃ f ∈ tensSub (genSub E V), ∀ g ∈ UJset ε,
      inner ℂ ((z : D) : H) (σ g ((x' : D) : H)) =
        ∑ c, inner ℂ ((f c : D) : H) (tensGrp dual σ g (fun d => ((ι x' d : D) : H)) c) := by
  have hVf : FiniteDimensional ℂ V := hV.1
  have hVk : IsKStableSub ε E V := hV.2.1
  have hV'f : FiniteDimensional ℂ V' := hV'.1
  have hV'k : IsKStableSub ε E V' := hV'.2.1

  have hT : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → H),
      tensGrp dual σ g u = coefTG dual σ g u := by
    intro g u
    funext c
    cases dual <;> rfl
  refine ⟨?_, ?_⟩
  · intro f hf x' hx'
    obtain ⟨z, hz, hzy⟩ := coefB_toSum_exists dual hσ hD hVf hVk hgap' hV' hc' hι f hf
    refine ⟨z, hz, fun g hg => ?_⟩
    have hq := coefE_all dual hσ hD hVf hVk hc hV'f hV'k hc' hι.1 hι.2.2.1 f z hzy g hg x' hx'
    rw [hT]
    exact hq
  · intro z hz x' hx'
    obtain ⟨f, hf, hfy⟩ := coefB_ofSum_exists dual hσ hD hgap' hV' hc' hι z hz
    refine ⟨f, hf, fun g hg => ?_⟩
    have hq := coefE_all dual hσ hD hVf hVk hc hV'f hV'k hc' hι.1 hι.2.2.1 f z hfy g hg x' hx'
    rw [hT]
    exact hq.symm

end ReciprocityTheory.ChartRestriction.DS
