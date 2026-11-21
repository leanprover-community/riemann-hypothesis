import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.SumUliftFinsetFinTwoExpand
import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.TransferenceGivesSecondBound
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

variable (D : D7)

instance totCx : IsTotallyComplex D.host.E :=
  (D.host.isCMField_hostE).to_isTotallyComplex

theorem conjugate_emb (g : D.R.GG) :
    ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  ext z
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  rw [show ((D.host.conj : D.host.E →+* D.host.E) z) = D.host.conj z from rfl, Formalism.MainNotions.WeightFamilies.emb_conj]
  rfl

theorem mk_tauEmb_injective : Function.Injective fun τ : D.what₂.Tau => InfinitePlace.mk (DV.tauEmb D τ) := by
  intro τ τ' h
  simp only at h
  rcases mk_eq_iff.1 h with h1 | h1
  · have h2 := (factEmb D.R D.host).1.1 h1
    exact D.eTau.injective (Subtype.ext h2)
  · exfalso
    unfold DV.tauEmb at h1
    rw [conjugate_emb] at h1
    have h2 := (factEmb D.R D.host).1.1 h1
    have hm := (D.eTau τ).2
    rw [Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem] at hm
    exact hm (h2 ▸ (D.eTau τ').2)

theorem card_places : Fintype.card (InfinitePlace D.host.E) = Fintype.card D.what₂.Tau := by
  have h1 := DualLatticeEmbeddings.nPl_mul_two (K := D.host.E)
  rw [D.host.finrank_cmField] at h1
  have h2 : D.R.f = 2 * D.R.ord := rfl
  rw [D.what₂.card_Tau, h2]
  omega

def ePl : D.what₂.Tau ≃ InfinitePlace D.host.E :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨mk_tauEmb_injective D, (card_places D).symm⟩)

theorem ePl_embedding (τ : D.what₂.Tau) :
    (ePl D τ).embedding = DV.tauEmb D τ ∨ (ePl D τ).embedding = ComplexEmbedding.conjugate (DV.tauEmb D τ) :=
  embedding_mk_eq _

theorem re_ePl (τ : D.what₂.Tau) (z : D.host.E) :
    ((ePl D τ).embedding z).re = (DV.tauEmb D τ z).re := by
  rcases ePl_embedding D τ with h | h <;> rw [h]
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem trF_eq (z : D.host.E) : Formalism.MainNotions.WeightFamilies.trF D z = ∑ v : InfinitePlace D.host.E, (v.embedding z).re := by
  unfold Formalism.MainNotions.WeightFamilies.trF
  rw [← (ePl D).sum_comp]
  exact Finset.sum_congr rfl fun τ _ => (re_ePl D τ z).symm

theorem finrank_E_eq : finrank ℚ D.host.E = 2 * D.R.f := by
  have h2 : D.R.f = 2 * D.R.ord := rfl
  rw [D.host.finrank_cmField, h2]
  ring

@[instance_reducible] def starE : StarRing D.host.E := starRingOfComm

attribute [local instance] starE

variable {D}

theorem exists_im_ne (v : InfinitePlace D.host.E) : ∃ z, (v.embedding z).im ≠ 0 := by
  have hc : v.IsComplex := IsTotallyComplex.isComplex v
  rw [isComplex_iff] at hc
  by_contra h
  simp only [not_exists, not_not] at h
  apply hc
  ext z
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (h z)

theorem frames {n : ℕ} (χ : Matrix (Fin n) (Fin n) D.host.E) (hH : Formalism.MainNotions.WeightFamilies.IsHerm D χ)
    (hP : Formalism.MainNotions.WeightFamilies.PosDefE D χ) :
    ∃ Xf : InfinitePlace D.host.E → Matrix (Fin n) (Fin n) ℂ,
      (∀ v, Xf v * (Xf v)ᴴ = χ.map v.embedding) ∧ ∀ v, IsUnit (Xf v).det := by
  have h : ∀ v : InfinitePlace D.host.E, ∃ X : Matrix (Fin n) (Fin n) ℂ,
      X * Xᴴ = χ.map v.embedding ∧ IsUnit X.det := by
    intro v
    obtain ⟨z, hz⟩ := exists_im_ne v
    obtain ⟨h1, h2⟩ := TraceQuadraticBound.psd_map (fun z => D.host.conj z) v.embedding
      (Formalism.MainNotions.WeightFamilies.emb_conj D v.embedding) (TraceQuadraticBound.denseRange_emb v.embedding z hz) χ hH
      (fun l hl => hP l hl v.embedding)
    exact TraceQuadraticBound.frame_exists h1 h2
  choose Xf h1 h2 using h
  exact ⟨Xf, h1, h2⟩

theorem star_mulVec_map {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    star (M *ᵥ w) = M.map star *ᵥ star w := by
  funext i
  simp only [Pi.star_apply, mulVec, dotProduct, star_sum, map_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul']


end Formalism.L2.Geo.Rec.StarEmbeddingNorm

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions
open scoped ComplexOrder

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

attribute [local instance] starE

variable {D : D7} {n : ℕ}





end Formalism.L2.Geo.Rec.StarEmbeddingNorm

open NumberField NumberField.InfinitePlace Module Matrix Formalism.BasicNotions
open scoped ComplexOrder

noncomputable section

namespace Formalism.L2.Geo.Rec.StarEmbeddingNorm

attribute [local instance] starE

variable {D : D7} {n : ℕ}




end Formalism.L2.Geo.Rec.StarEmbeddingNorm
