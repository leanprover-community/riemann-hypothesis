module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccDAdj
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccCExistsPs
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDTensKStable

@[expose] public section

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Amb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjB_K (dual : Bool) (hσ : IsURepOn (UJset ε) σ) {M : Submodule ℂ D}
    (hMK : ∀ k ∈ Kset ε, ∀ x ∈ M, ∃ y ∈ M, (y : H) = σ k x) {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps3 : ∀ k ∈ Kset ε, ∀ f ∈ tensSub M, ∀ f' ∈ tensSub M,
      (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
      ((ps f' : D) : H) = σ k ((ps f : D) : H))
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) {x x'' : D} (hxx : (x'' : H) = σ k (x : H))
    {u : Fin n → D} (h : adjR ε M ps x u) {f' : Fin n → D} (hf' : f' ∈ tensSub M)
    (hff : (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((u c : D) : H))) :
    adjR ε M ps x'' f' := by
  apply ReciprocityTheory.ChartRestriction.DS.adjB_K <;> assumption

theorem adjB_emb (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {lam lam' : Fin n → ℝ} {V V' : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hgap' : StdGap ε lam')
    (hV' : IsKIrrHW ε E (lowK ε lam') V') (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v) {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps1 : ∀ f ∈ tensSub (genSub E V), ps f ∈ genSub E V')
    (hps2 : ∀ a b, ∀ f ∈ tensSub (genSub E V), ps (tensF dual E a b f) = E a b (ps f))
    (hps3 : ∀ k ∈ Kset ε, ∀ f ∈ tensSub (genSub E V), ∀ f' ∈ tensSub (genSub E V),
      (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
      ((ps f' : D) : H) = σ k ((ps f : D) : H))
    (hne : ∃ f ∈ tensSub (genSub E V), ps f ≠ 0) :
    ∃ ι : D →ₗ[ℂ] (Fin n → D), IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι := by
  classical
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hME : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => closure_E_mem_genSub a b hv
  have hME' : ∀ a b, ∀ v ∈ genSub E V', E a b v ∈ genSub E V' := fun a b v hv => closure_E_mem_genSub a b hv
  have hMK : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∃ y ∈ genSub E V, (y : H) = σ k x :=
    fun k hk x hx => occD_genSub_K hσ hD hV.1 hV.2.1 hk hx
  have hM'K : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V', ∃ y ∈ genSub E V', (y : H) = σ k x :=
    fun k hk x hx => occD_genSub_K hσ hD hV'.1 hV'.2.1 hk hx
  have hex : ∀ x ∈ genSub E V', ∃ u, adjR ε (genSub E V) ps x u := by
    intro x hx
    choose z hz hzr using fun c => adjA_rep dual hσ hD hgap hV hc hV'.1 hV'.2.1 hps2 hx c
    refine ⟨fun c => adjSg ε c • z c, tset_mem.2 fun c => Submodule.smul_mem _ _ (hz c), fun c y hy => ?_⟩
    rw [inner_smul_left, adjSg_conj, hzr c y hy]
  obtain ⟨ι, hι⟩ := adjR_linear hex
  have hEcl : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x) := fun a b x hx =>
    adjR_unique (hι _ (hME' a b x hx)) (adjB_E dual hU hME hps2 (hι x hx) a b)
  have hKcl : ∀ k ∈ Kset ε, ∀ x ∈ genSub E V', ∀ x'' ∈ genSub E V', (x'' : H) = σ k (x : H) →
      (fun c => ((ι x'' c : D) : H)) = kDiag dual σ k (fun c => ((ι x c : D) : H)) := by
    intro k hk x hx x'' hx'' hxx
    choose w hw hwe using fun d => hMK k hk _ (tset_mem.1 (hι x hx).1 d)
    set f' : Fin n → D := fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • w d
    have hf' : f' ∈ tensSub (genSub E V) :=
      tset_mem.2 fun c => Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hw d)
    have hff : (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((ι x c : D) : H)) := by
      funext c
      simp only [f', kDiag, Submodule.coe_sum, Submodule.coe_smul, hwe]
    rw [adjR_unique (hι x'' hx'') (adjB_K dual hσ hMK hps3 hk hxx (hι x hx) hf' hff)]
    exact hff
  refine ⟨ι, fun x hx => (hι x hx).1, ?_, hEcl, hKcl⟩
  intro x hx hx0
  set N : Submodule ℂ D := genSub E V' ⊓ LinearMap.ker ι
  have hNE : ∀ a b, ∀ y ∈ N, E a b y ∈ N := by
    intro a b y hy
    refine ⟨hME' a b y hy.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hEcl a b y hy.1, LinearMap.mem_ker.1 hy.2, map_zero]
  have hNK : ∀ k ∈ Kset ε, ∀ y ∈ N, ∃ y' ∈ N, (y' : H) = σ k y := by
    intro k hk y hy
    obtain ⟨y', hy'M, hy'⟩ := hM'K k hk y hy.1
    refine ⟨y', ⟨hy'M, ?_⟩, hy'⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have h1 := hKcl k hk y hy.1 y' hy'M hy'
    rw [LinearMap.mem_ker.1 hy.2] at h1
    funext c
    have h2 := congrFun h1 c
    simp only [kDiag, Pi.zero_apply, ZeroMemClass.coe_zero, map_zero, smul_zero, Finset.sum_const_zero] at h2
    exact Subtype.ext h2
  rcases data_genSub_irred hgap' hσ hD hV' hc' hVK' N inf_le_left hNE hNK with h | h
  · have : x ∈ N := ⟨hx, LinearMap.mem_ker.2 hx0⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · exfalso
    obtain ⟨f₀, hf₀, hps0⟩ := hne
    have hm : ps f₀ ∈ N := h ▸ hps1 f₀ hf₀
    have hR := hι _ (hps1 f₀ hf₀)
    rw [LinearMap.mem_ker.1 hm.2] at hR
    have h0 : ∀ c, inner ℂ (ps f₀) (ps (Pi.single c (f₀ c))) = (0 : ℂ) := by
      intro c
      rw [adjR_inv hR c (tset_mem.1 hf₀ c)]
      simp
    apply hps0
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    calc inner ℂ (ps f₀) (ps f₀) = ∑ c, inner ℂ (ps f₀) (ps (Pi.single c (f₀ c))) := by

          rw [← inner_sum, ← map_sum, Finset.univ_sum_single]
      _ = 0 := Finset.sum_eq_zero fun c _ => h0 c

end Amb

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occAdj_emb (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    {ps : (Fin n → smD ε (rreg ε)) →ₗ[ℂ] smD ε (rreg ε)}
    (hps : occPsOK dual ε (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ps)
    (hne : ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ps f ≠ 0) :
    ∃ ι : smD ε (rreg ε) →ₗ[ℂ] (Fin n → smD ε (rreg ε)),
      IsGKEmb dual ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
        (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ι := by
  have hσ := rreg_isURepOn ε
  exact adjB_emb dual hσ (isDerivedOn_smE hσ) hgap (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀) hgap'
    (datumV_isKIrrHW hP' hv₀') (datumV_casimir hP' v₀') (datumV_kStable hP' v₀') hps.1 hps.2.1 hps.2.2 hne

end Psi

end ReciprocityTheory.ChartRestriction.DS.G2
