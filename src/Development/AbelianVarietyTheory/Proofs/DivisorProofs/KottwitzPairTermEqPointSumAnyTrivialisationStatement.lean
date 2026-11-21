import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormConjHermitianTripleRegulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivializationsDifferByGroupPoint

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.PointSumConj.pointSum_conj_data) | (exact GlobalTheory.PointSumConj.pointSum_conj_data) | (intros; apply GlobalTheory.PointSumConj.pointSum_conj_data  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTripleTrivializations_differ_by_group_point : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (x x' : (R ⊗[ℚ] G.C)ˣ) (t t' : Rˣ), Triv G R β x t → Triv G R β x' t' → ∃ g : UPts G.star R, (g : (R ⊗[ℚ] G.C)ˣ × Rˣ).1 = x' * x⁻¹ := by
  first | (exact @GlobalTheory.LKMid.triv_quot) | (exact GlobalTheory.LKMid.triv_quot) | (intros; apply GlobalTheory.LKMid.triv_quot  <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem term_eq_termAt : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r), IsNrm G r P.atP δ z → P.term Kf f r K φ = P.termAt Kf f r K φ x t hx δ z := by
  intro p _ G P Kf f r K φ hr hf hφ x t hx δ z hn
  have hex : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 := ⟨(δ, z), hn⟩
  unfold term
  rw [dif_pos hex]
  set x₀ := P.trivAf.choose
  set t₀ := P.trivAf.choose_spec.choose
  have h₀ : Triv G (AfP p) P.β x₀ t₀ := P.trivAf.choose_spec.choose_spec
  set δ₀ := hex.choose.1
  set z₀ := hex.choose.2
  have hn₀ : IsNrm G r P.atP δ₀ z₀ := hex.choose_spec
  obtain ⟨_, hreg, hcent⟩ := GlobalTheory.T.similitudePair_regular_image_at_p p G P
  obtain ⟨g, hgx⟩ := GlobalTheory.T.hermitianTripleTrivializations_differ_by_group_point p G (AfP p) (P.β : G.C) x x₀ t t₀ hx h₀
  obtain ⟨g₂, hδ, hcz⟩ := GlobalTheory.T.twistedConj_of_twistedNormConj_hermitianTriple_regular p G r P.atP δ z δ₀ z₀ hr hreg hn hn₀
  have htw := GlobalTheory.T.map_centralizer_regular_twistedCentraliser p G r P.atP δ z hr hreg hn
  have hAf : P.toAf x₀ t₀ h₀ = (MulAut.conj g⁻¹⁻¹).toMonoidHom.comp (P.toAf x t hx) := by
    ext y : 1
    apply Subtype.ext
    apply Prod.ext
    · have e : x₀ = (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x := by rw [hgx, inv_mul_cancel_right]
      simp only [toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [e]; group
    · simp only [toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [mul_comm, inv_mul_cancel_left]
  have hQr : P.toQr r z₀ = (MulAut.conj g₂⁻¹).toMonoidHom.comp (P.toQr r z) := by
    ext y : 1
    have := hcz (locC G y.1) (hcent y)
    simp only [toQr, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [this]
  have hself : P.toAf x₀ t₀ h₀ P.self = g⁻¹⁻¹ * P.toAf x t hx P.self * g⁻¹ := by
    rw [hAf]; simp [MulAut.conj_apply]
  unfold termAt
  rw [hself, hAf, hQr, hδ]
  refine GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data _ _ _ _ _ _ _ _ _ _ _ hf hφ ?_ ?_
  · intro y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · exact y.2.1
    · exact mul_comm _ _
  · intro y
    have hm : P.toQr r z y ∈ GlobalTheory.BCT.twCent (sigG G r) δ := by
      rw [← htw]; exact ⟨locC G y.1, hcent y, rfl⟩
    exact hm

end GlobalTheory.LKMid.Pair
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r), IsNrm G r P.atP δ z → P.term Kf f r K φ = P.termAt Kf f r K φ x t hx δ z := by
  first | (exact @GlobalTheory.LKMid.Pair.term_eq_termAt) | (exact GlobalTheory.LKMid.Pair.term_eq_termAt) | (intros; apply GlobalTheory.LKMid.Pair.term_eq_termAt <;> assumption)
end
