import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviCentreInducedUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsInhabitant

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Published.LeviCentreModel

namespace GlobalTheory.Published.LeviInducedModel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_conj (hσ : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (a : AE F E) :
    piInf τ (cA σ a) = starRingEnd ℂ (piInf τ a) := by
  change _ = starRingEnd ℂ (infEmb τ _)
  rw [infEmb_sigR hσ]
  change infEmb τ _ = _
  congr 1
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem cont_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ : AE F E → ℂ) := by
  let L : AE F E →+ ℂ := (piInf τ).toAddMonoidHom
  refine IsModuleTopology.continuous_of_distribMulActionHomₑ (R := AF F) (σ := (piInf τ).toMonoidHom.comp (algebraMap (AF F) (AE F E)).toMonoidHom) ?_
    { L with map_smul' := fun r x => by simp [L, Algebra.smul_def] }
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp continuous_fst) |>.congr fun a => by
    change _ = infEmb τ (_ ⊗ₜ[F] (1 : E))
    rw [infEmb_tmul, map_one, mul_one]; rfl

def chi (hσ : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) : Chr F E where
  toFun t := ⟨piInf τ (t.1 * cA σ (t⁻¹).1), by
    have : piInf τ t.1 * piInf τ (t⁻¹).1 = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h2 := congrArg norm this
    simpa [Submonoid.unitSphere, piInf_conj hσ] using h2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change piInf τ ((a * b).1 * cA σ ((a * b)⁻¹).1) = piInf τ (a.1 * cA σ (a⁻¹).1) * piInf τ (b.1 * cA σ (b⁻¹).1)
    simp only [mul_inv_rev, Units.val_mul, map_mul]; ring)



example (hσ : IsCMExt F E σ) {δ : E} (hJ : IsHermND σ (δ • (big F δ).J.map σ)) :
    ∃ φ : GAd σ (δ • (big F δ).J.map σ) → ℂ, GlobalTheory.UAut.IsSm σ _ φ ∧ ¬ FiniteDimensional ℂ (Submodule.span ℂ
      {u | ∃ z, GlobalTheory.UAut.IsCentral σ (δ • (big F δ).J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ}) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  exact ⟨_, GlobalTheory.UAut.Model.not_zfin_exp hσ hJ τ 0⟩

end GlobalTheory.Published.LeviInducedModel

end
