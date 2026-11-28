module

public import TauCeti.Analysis.HeisenbergModel.OrthogonalSum
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Weil operators, orthogonal sums and transport: lemmas not in Tau Ceti

The Heisenberg data, vacua, the reproducing model and its Weil operators are Tau Ceti's
(`TauCeti.HeisenbergDatum`, `TauCeti.ReproducingModel`, `TauCeti.ReproducingModel.weilOp`,
`TauCeti.ReproducingModel.weilRep`, `TauCeti.HeisenbergDatum.OrthogonalSum`). This file adds three
facts about them that Tau Ceti does not state, and a membership criterion for the submodule
underlying the model.

## Main results

* `TauCeti.HeisenbergDatum.apply_mul_mul_apply_swap_mul`: the factors `β x y` and `β y x` of a
  product cancel.
* `TauCeti.mem_reproducingSubmodule_iff`: a function lies in the model if and only if it is
  integrable and reproduced by the kernel of the vacuum.
* `TauCeti.ReproducingModel.weilRep_eq_integral`: the Weil operator of `g` sends `v` to
  Δ(g) ∫ v(g⁻¹ • y) ρ(y) vac dμ(y).
* `TauCeti.HeisenbergDatum.Representation.integrated_tmul`: integrating a tensor product `v ⊗ w`
  against a representation is integrating `w`, then `v`, against its restrictions to the summands.
* `New.map_integral_and_map_vacuum`: change of variables along an isomorphism that matches two
  vacua, up to the identity or complex conjugation.

## Relation to the literature

This file contributes to the adelic Weil representation of a unitary group and the invariant theta
functional. See `Lib.Weil.MixedModel.ZeroTerm`. Sources: Weil; Kudla.

The usual proof of the product rule ω(g) ω(h) = ω(gh) compares ω with a Schrödinger model on a
Siegel parabolic subgroup of a split space, and then uses the Iwasawa decomposition and the sum
V ⊕ V⁻. The proof used here (`TauCeti.ReproducingModel.weilOp_inv_mul_weilOp_mul_weilOp`) does not
use a Schrödinger model. The scalar c(g, h) in ω(g) ω(h) = c(g, h) ω(gh) is an integral of three
vacua times values of the multiplier (`TauCeti.HeisenbergDatum.Multiplier.cocycle`). Later files
show directly that it is 1, from three local facts: a Gaussian determinant at the real places
(`New.Fock.realMultiplier_cocycle`), positivity at the split places and the sign of a Gauss sum at
the inert places (`New.stdLattice.mem_cocycleRadical`). The formulas of the Schrödinger model are
then proved for the slices in `Lib.Weil.MixedModel.ZeroTerm`.
-/

@[expose] public section

noncomputable section

open MeasureTheory TauCeti

namespace TauCeti

/-- The two factors `β x y` and `β y x` of a product cancel. -/
@[simp]
lemma HeisenbergDatum.apply_mul_mul_apply_swap_mul {W : Type*} [AddCommGroup W]
    [TopologicalSpace W] (β : HeisenbergDatum W) (x y : W) (a b : ℂ) :
    β x y * a * (β y x * b) = a * b := by
  rw [mul_mul_mul_comm, β.apply_mul_apply_swap, one_mul]

section Membership

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] {β : HeisenbergDatum W} {μ : Measure W} {e : W → ℂ}
  [β.IsVacuum μ e]

/-- A function lies in the submodule underlying the reproducing model if and only if it is
integrable and reproduced by the kernel of the vacuum. -/
lemma mem_reproducingSubmodule_iff {f : W → ℂ} :
    f ∈ reproducingSubmodule β μ e ↔
      Integrable f μ ∧ ∀ x, ∫ y, f y * (β y x * e (x - y)) ∂μ = f x := by
  refine ⟨fun hf ↦ ?_, fun ⟨hf, h⟩ ↦ ?_⟩
  · exact ⟨ReproducingModel.integrable (⟨f, hf⟩ : ReproducingModel β μ e),
      ReproducingModel.integral_mul_kernel (⟨f, hf⟩ : ReproducingModel β μ e)⟩
  · have h_val : Subtype.val (ReproducingModel.mk f hf h) = f :=
      funext fun x ↦ ReproducingModel.mk_apply x f hf h
    exact h_val ▸ (ReproducingModel.mk f hf h).property

end Membership

namespace ReproducingModel

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W]
  {β : HeisenbergDatum W} {μ : Measure W} [μ.IsAddLeftInvariant] {e : W → ℂ} [β.IsVacuum μ e]
  {G : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W] [ContinuousSMul G W]
  (Δ : β.Multiplier μ G) (hc : ∀ g h, Δ.cocycle e g h = 1) (g : G) (v : ReproducingModel β μ e)

/-- The Weil operator of `g` sends `v` to Δ(g) ∫ v(g⁻¹ • y) ρ(y) vac dμ(y). -/
lemma weilRep_eq_integral :
    weilRep e Δ hc g v = Δ g • ∫ y, v (g⁻¹ • y) • heisenbergRep y vacuum ∂μ := by
  -- Substitute `y ↦ g • y`, which preserves `μ`.
  rw [← (Δ.measurePreserving_smul g).integral_comp' (f := .smul g)]
  simp [weilRep_apply_eq, weilOp_apply_eq, TauCeti.HeisenbergDatum.Representation.integrated_apply]

end ReproducingModel

end TauCeti

namespace TauCeti.HeisenbergDatum.Representation

open ReproducingModel

variable {W W₁ W₂ : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] [LocallyCompactSpace W]
  [AddCommGroup W₁] [TopologicalSpace W₁] [MeasurableSpace W₁] [IsTopologicalAddGroup W₁]
  [BorelSpace W₁] [SecondCountableTopology W₁] [LocallyCompactSpace W₁]
  [AddCommGroup W₂] [TopologicalSpace W₂] [MeasurableSpace W₂] [IsTopologicalAddGroup W₂]
  [BorelSpace W₂] [SecondCountableTopology W₂] [LocallyCompactSpace W₂]
  {β : HeisenbergDatum W} {β₁ : HeisenbergDatum W₁} {β₂ : HeisenbergDatum W₂}
  {μ : Measure W} {μ₁ : Measure W₁} {μ₂ : Measure W₂} [μ.IsAddHaarMeasure] [μ₁.IsAddHaarMeasure]
  [μ₂.IsAddHaarMeasure] {e : W → ℂ} {e₁ : W₁ → ℂ} {e₂ : W₂ → ℂ} [β.IsVacuum μ e]
  [β₁.IsVacuum μ₁ e₁] [β₂.IsVacuum μ₂ e₂]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (ϱ : β.Representation X) (S : β.OrthogonalSum β₁ β₂ e e₁ e₂)
  (v : ReproducingModel β₁ μ₁ e₁) (w : ReproducingModel β₂ μ₂ e₂) (f : X)

/-- Integrating `v ⊗ w` against `ϱ` is integrating `w` against the restriction of `ϱ` to `W₂`, then
`v` against its restriction to `W₁`. -/
lemma integrated_tmul :
    ϱ.integrated μ e (S.tmul μ v w) f =
      (ϱ.restrictLeft S).integrated μ₁ e₁ v ((ϱ.restrictRight S).integrated μ₂ e₂ w f) := by
  -- Rewrite the left side by Fubini's theorem and simplify the iterated integral on the right.
  rw [integrated_apply, (ϱ.restrictLeft S).integrated_apply,
    S.integral_eq_integral_prod (μ₁ := μ₁) (μ₂ := μ₂)]
  simp_rw [TauCeti.HeisenbergDatum.OrthogonalSum.tmul_apply, S.equiv.symm_apply_apply]
  rw [integral_prod (fun x : W₁ × W₂ ↦ (v x.1 * w x.2) • ϱ (S.equiv x) f)
    ((v.integrable.mul_prod w.integrable).smul_bdd ‖f‖
      (ϱ.continuous_apply_apply S.equiv.continuous continuous_const).aestronglyMeasurable
      (by simp))]
  simp_rw [map_integrated, ← integral_smul, smul_smul, restrictLeft_apply_restrictRight_apply]

end TauCeti.HeisenbergDatum.Representation

/-!
## Transport of the model along a linear or conjugate linear isomorphism

Let `e`, `e'` be vacua for Heisenberg data on `W`, `W'`, and let `φ : W' ≃ W` be an isomorphism of
topological groups that matches the vacua. Tau Ceti's `TauCeti.ReproducingModel.transport` is the
`σ`-semilinear map `v ↦ σ ∘ v ∘ φ` between the models, for `σ` the identity or the conjugation of
`ℂ`; `New.map_integral_and_map_vacuum` is the change of variables behind it.
-/

namespace New

open Measure Complex

variable {W W' : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] [LocallyCompactSpace W]
  [AddCommGroup W'] [TopologicalSpace W'] [MeasurableSpace W'] [IsTopologicalAddGroup W']
  [BorelSpace W']
  {μ : Measure W} {e : W → ℂ} {μ' : Measure W'} {e' : W' → ℂ} [IsAddHaarMeasure μ]
  [IsAddHaarMeasure μ'] {σ : ℂ →+* ℂ} [RingHomIsometric σ] {φ : W' ≃ₜ+ W}

/-- Let `e`, `e'` be vacua of `β`, `β'` for the Haar measures `μ`, `μ'`. Change of variables along
an isometric ring map `σ` of `ℂ` (the identity or the conjugation) and an isomorphism `φ : W' ≃ W`
with `e ∘ φ = e'`: `σ (∫ f dμ) = ∫ σ ∘ f ∘ φ dμ'` for every `f`, and `σ ∘ e ∘ φ = e'`. -/
lemma map_integral_and_map_vacuum (β : HeisenbergDatum W) (β' : HeisenbergDatum W')
    [β.IsVacuum μ e] [he' : β'.IsVacuum μ' e'] (hφ : ∀ x : W', e (φ x) = e' x) :
    (∀ f : W → ℂ, σ (integral μ f) = ∫ x : W', σ (f (φ x)) ∂μ') ∧
      ∀ x : W', σ (e (φ x)) = e' x := by
  -- `φ` preserves the measures, and `σ`, the identity or the conjugation, commutes with integrals.
  have h_pres := ReproducingModel.measurePreserving_of_vacuum (β := β) (β' := β') μ μ' hφ
  refine ⟨fun f ↦ ?_, fun x ↦ ?_⟩
  · rw [← h_pres.integral_comp φ.measurableEmbedding f]
    rcases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
    · simp
    · simp [integral_conj]
  · rcases ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous with rfl | rfl
    · simp [hφ]
    · simp [hφ, he'.conj_apply]

end New

end
