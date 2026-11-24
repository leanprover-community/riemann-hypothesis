module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefBTensSubKStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefETensGrpMul
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefDTensActPow
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefOfEmb

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

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
  have hVf := hV.1
  have hVst := hV.2.1
  have hV'f := hV'.1
  have hV'st := hV'.2.1
  have hTG : ∀ g : Matrix (Fin n) (Fin n) ℂ, ∀ w : Fin n → H,
      tensGrp dual σ g w = coefTG dual σ g w := by
    intro g w
    cases dual <;> rfl
  have hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x) :=
    hι.2.2.1
  have key : ∀ f ∈ tensSub (genSub E V), ∀ z ∈ genSub E V',
      (∀ y ∈ genSub E V', inner ℂ z y = ∑ c, inner ℂ (f c) (ι y c)) →
      ∀ x' ∈ genSub E V', ∀ g ∈ UJset ε,
        ∑ c, inner ℂ ((f c : D) : H) (tensGrp dual σ g (fun d => ((ι x' d : D) : H)) c) =
          inner ℂ ((z : D) : H) (σ g ((x' : D) : H)) := by
    intro f _ z _ hz x' hx' g hg
    rw [hTG]
    exact coefE_all dual hσ hD hVf hVst hc hV'f hV'st hc' hι.1 hιE f z hz g hg x' hx'
  refine ⟨fun f hf x' hx' => ?_, fun z hz x' hx' => ?_⟩
  · obtain ⟨z, hzm, hz⟩ :=
      ReciprocityTheory.ChartRestriction.DS.G2.coefB_toSum_exists dual hσ hD hVf hVst hgap' hV' hc' hι f hf
    exact ⟨z, hzm, key f hf z hzm hz x' hx'⟩
  · obtain ⟨f, hf, hzf⟩ :=
      ReciprocityTheory.ChartRestriction.DS.G2.coefB_ofSum_exists dual hσ hD hgap' hV' hc' hι z hz
    exact ⟨f, hf, fun g hg => (key f hf z hz hzf x' hx' g hg).symm⟩

end ReciprocityTheory.ChartRestriction.DS.G2
