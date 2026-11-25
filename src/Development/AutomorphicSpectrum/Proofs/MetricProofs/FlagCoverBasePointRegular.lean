module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem sum_mapDomain_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1)
    (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  have e1 : ∀ q : (Σ k, ι' k) →₀ ℕ, ∑ i, q ⟨k', i⟩ = q.sum (fun r x => if r.1 = k' then x else 0) := by
    intro q
    rw [Finsupp.sum_fintype _ _ (fun r => by simp), Fintype.sum_sigma,
      Finset.sum_eq_single k' (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have e2 : ∑ p : Σ k, ι k, (if κ p.1 = k' then m p else 0) = m.sum (fun p x => if κ p.1 = k' then x else 0) := by
    rw [Finsupp.sum_fintype _ _ (fun r => by simp)]
  rw [e1, e2, Finsupp.sum_mapDomain_index (fun r => by simp) (fun r a b => by split_ifs <;> simp)]
  simp only [hv]

theorem isMultiHomog_rename_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) {f : MRing ι}
    {b : K → ℕ} (hf : IsMultiHomog f b) : IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  rw [sum_mapDomain_block hb.2.2.1]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, ← hf m0 hm0 k]
    simp only [hb.1.eq_iff]
    rw [Fintype.sum_sigma, Finset.sum_eq_single k (fun b _ hb' => by simp [hb']) (by simp)]
    simp
  · rw [Function.extend_apply' _ _ _ hk, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg (fun h => hk ⟨p.1, h⟩)]

theorem mConeMap_rename {Ω : Type} [Field Ω] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    (y : (Σ k, ι' k) → Ω) (g : MRing ι) : mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  simp only [mConeMap]
  rw [aeval_rename]
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp [hp, hq]
  | mul_X p i hp =>
    simp [hp, hb.2.2.1 i]

theorem mConeMap_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    mConeMap (φ ∘ x) g = map φ (mConeMap x g) := by
  simp only [mConeMap]
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [hp]
    simp only [aeval_X, Function.comp_apply, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

theorem aeval_comp_ringHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (φ ∘ x) g = φ (aeval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, Function.comp_apply]

theorem eval_rename_block (v : (Σ k, ι k) → Σ k, ι' k) (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v f)) = eval (z ∘ v) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]

theorem rename_notMem {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    {z : (Σ k, ι' k) → ℂ} {h : MRing ι} (hn : h ∉ mCoordIdeal (z ∘ v)) : rename v h ∉ mCoordIdeal z := by
  intro hmem
  apply hn
  rw [mCoordIdeal, RingHom.mem_ker] at hmem ⊢
  rw [mConeMap_rename hb] at hmem
  exact rename_injective κ hb.1 (by rw [hmem, map_zero])

theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hb : IsBlockMap κ v) (φ : Ω →+* Ω') {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : x' ∘ v = φ ∘ x)
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) := by
  unfold mcPts at hz ⊢
  simp only [Set.mem_ofPred_eq] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz1 (κ k)
    obtain ⟨⟨k0, i⟩, hp⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h0 := hb.2.2.1 ⟨k0, i⟩
    rw [hp] at h0
    have hk0 : k0 = k := hb.1 h0.symm
    subst hk0
    refine ⟨i, ?_⟩
    show z (v ⟨k0, i⟩) ≠ 0
    rw [hp]
    exact hi'
  · rw [← eval_rename_block v z f]
    apply hz2
    rw [mCoordIdeal, RingHom.mem_ker] at hf ⊢
    rw [mConeMap_rename hb, hx, mConeMap_comp, hf, map_zero, map_zero]

end Forms

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi
