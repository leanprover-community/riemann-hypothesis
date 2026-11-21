import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateEigenSubDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldedEqOrbitalReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFormStabilizerFiniteAwayFromPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTestProductSupportFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLevelConjCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexPrincipalCongruenceNeZero

section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.HeckeTrace

variable {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]

theorem out_smul (K : Subgroup H) (k : H) (h : H ⧸ K) : ∃ κ ∈ K, ((k • h : H ⧸ K).out : H) = k * h.out * κ := by
  have e : (k • h : H ⧸ K) = QuotientGroup.mk (k * h.out) := by
    conv_lhs => rw [← QuotientGroup.out_eq' h]
    rfl
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul K (k * h.out)
  exact ⟨κ, κ.2, by rw [e, hκ]⟩

def heckeFun (K : Subgroup H) (F : H → ℂ) (φ : H → V) (g : H) : V :=
  ∑ᶠ h : H ⧸ K, F h.out • φ (g * h.out)

theorem support_sub (K : Subgroup H) (F : H → ℂ) (v : H ⧸ K → V) :
    Function.support (fun h : H ⧸ K => F h.out • v h) ⊆ Function.support (fun h : H ⧸ K => F h.out) :=
  Function.support_smul_subset_left _ _

theorem heckeFun_mul_right (K : Subgroup H) (F : H → ℂ) (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (φ : H → V) (hφ : ∀ k ∈ K, ∀ g, φ (g * k) = φ g) (g k : H) (hk : k ∈ K) :
    heckeFun K F φ (g * k) = heckeFun K F φ g := by
  unfold heckeFun
  rw [← finsum_comp_equiv (MulAction.toPerm (k⁻¹ : H) : Equiv.Perm (H ⧸ K)).symm.symm]
  refine finsum_congr fun h => ?_
  simp only [Equiv.symm_symm, MulAction.toPerm_apply]
  obtain ⟨κ, hκ, he⟩ := out_smul K k⁻¹ h
  rw [he]
  have h1 : F (k⁻¹ * h.out * κ) = F h.out := hF _ (K.inv_mem hk) _ hκ _
  have h2 : φ (g * k * (k⁻¹ * h.out * κ)) = φ (g * h.out) := by
    rw [show g * k * (k⁻¹ * h.out * κ) = g * h.out * κ by group, hφ _ hκ]
  rw [h1, h2]

theorem heckeFun_mul_left (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite)
    (φ : H → V) (hφ : ∀ γ g, φ (ι γ * g) = ξ γ (φ g)) (γ : Γ) (g : H) :
    heckeFun K F φ (ι γ * g) = ξ γ (heckeFun K F φ g) := by
  unfold heckeFun
  rw [map_finsum _ (hs.subset (support_sub K F _))]
  refine finsum_congr fun h => ?_
  rw [map_smul, mul_assoc, hφ]

def hecke (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite) :
    GlobalTheory.LKDef.HeckeTraceForms.forms ι K ξ →ₗ[ℂ] GlobalTheory.LKDef.HeckeTraceForms.forms ι K ξ where
  toFun φ := ⟨heckeFun K F (φ : H → V), fun γ g => heckeFun_mul_left ι K ξ F hs _ (φ.2.1) γ g,
    fun k hk g => heckeFun_mul_right K F hF _ (φ.2.2) g k hk⟩
  map_add' φ ψ := by
    apply Subtype.ext; funext g
    show heckeFun K F (fun x => (φ : H → V) x + (ψ : H → V) x) g = heckeFun K F (φ : H → V) g + heckeFun K F (ψ : H → V) g
    unfold heckeFun
    simp only [smul_add]
    exact finsum_add_distrib (hs.subset (support_sub K F _)) (hs.subset (support_sub K F _))
  map_smul' c φ := by
    apply Subtype.ext; funext g
    show heckeFun K F (fun x => c • (φ : H → V) x) g = c • heckeFun K F (φ : H → V) g
    unfold heckeFun
    rw [smul_finsum]
    refine finsum_congr fun h => ?_
    rw [smul_comm]

theorem isHecke_hecke (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite) :
    GlobalTheory.LKDef.HeckeTraceForms.IsHecke ι K ξ F (hecke ι K ξ F hF hs) := fun _ _ => rfl

theorem heckeTrace_eq (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite) :
    GlobalTheory.LKDef.HeckeTraceForms.heckeTrace ι K ξ F =
      LinearMap.trace ℂ (GlobalTheory.LKDef.HeckeTraceForms.forms ι K ξ) (hecke ι K ξ F hF hs) := by
  have h : ∃ T, GlobalTheory.LKDef.HeckeTraceForms.IsHecke ι K ξ F T := ⟨_, isHecke_hecke ι K ξ F hF hs⟩
  rw [GlobalTheory.LKDef.HeckeTraceForms.heckeTrace, dif_pos h]
  congr 1
  apply LinearMap.ext; intro φ; apply Subtype.ext; funext g
  rw [h.choose_spec φ g]; rfl

end GlobalTheory.HeckeTrace

namespace GlobalTheory.HeckeTrace

variable {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V]

theorem isConj_map {A B : Type} [Group A] [Group B] (e : A ≃* B) {a b : A} (h : IsConj a b) : IsConj (e a) (e b) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨e c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩

theorem mk_out_conj (c : ConjClasses Γ) : ConjClasses.mk (Quotient.out c) = c := Quotient.out_eq c

theorem heckeTrace_eq_orbital [FiniteDimensional ℂ V] (ι : Γ →* H) (hι : Function.Injective ι) (K : Subgroup H)
    (ξ : Representation ℂ Γ V) (F : H → ℂ)
    (hF : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F (k * g * k') = F g)
    (hs : (Function.support (fun q : H ⧸ K => F q.out)).Finite)
    (hQ : Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H)))
    (hloc : ∀ x : H, Finite (GlobalTheory.LKLoc.locPart ι.range K x)) :
    GlobalTheory.LKDef.HeckeTraceForms.heckeTrace ι K ξ F =
      ∑ᶠ c : ConjClasses Γ, LinearMap.trace ℂ V (ξ (Quotient.out c)) *
        ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {ι (Quotient.out c)} ⊓ ι.range : Subgroup H) : Set H) (K : Set H),
          (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {ι (Quotient.out c)} ⊓ ι.range) K q.out) : ℂ)) *
            F (q.out⁻¹ * ι (Quotient.out c) * q.out) := by
  let e : Γ ≃* ι.range := MonoidHom.ofInjective hι
  have he : ∀ γ : Γ, ((e γ : ι.range) : H) = ι γ := fun γ => MonoidHom.ofInjective_apply hι
  let ξ' : Representation ℂ ι.range V := ξ.comp e.symm.toMonoidHom
  have hξ : ∀ γ : Γ, ξ' (e γ) = ξ γ := fun γ => by
    simp only [ξ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  have hM : ∀ φ : H → V, φ ∈ GlobalTheory.LKDef.HeckeTraceForms.forms ι K ξ ↔
      (∀ γ : ι.range, ∀ g, φ ((γ : H) * g) = ξ' γ (φ g)) ∧ ∀ k ∈ K, ∀ g, φ (g * k) = φ g := by
    intro φ
    change ((∀ γ g, φ (ι γ * g) = ξ γ (φ g)) ∧ ∀ k ∈ K, ∀ g, φ (g * k) = φ g) ↔ _
    refine and_congr_left' ⟨fun h γ' g => ?_, fun h γ g => ?_⟩
    · obtain ⟨γ, rfl⟩ := e.surjective γ'
      rw [he, hξ, h]
    · rw [← he, h, hξ]
  rw [heckeTrace_eq ι K ξ F hF hs,
    GlobalTheory.FinTF.finite_trace_formula H ι.range K V ξ' hQ hloc F hF hs _ hM _ (isHecke_hecke ι K ξ F hF hs)]
  let R : Set ι.range := Set.range (fun c : ConjClasses Γ => e (Quotient.out c))
  have hcls : ∀ (c : ConjClasses Γ) (γ : Γ), IsConj (e γ) (e (Quotient.out c)) → c = ConjClasses.mk γ := by
    intro c γ h
    have h' : IsConj γ (Quotient.out c) := by
      simpa using isConj_map e.symm h
    rw [← mk_out_conj c]
    exact (ConjClasses.mk_eq_mk_iff_isConj.2 h').symm
  have hR : ∀ γ' : ι.range, ∃! ρ, ρ ∈ R ∧ IsConj γ' ρ := by
    intro γ'
    obtain ⟨γ, rfl⟩ := e.surjective γ'
    refine ⟨e (Quotient.out (ConjClasses.mk γ)), ⟨⟨_, rfl⟩, isConj_map e ?_⟩, ?_⟩
    · exact ConjClasses.mk_eq_mk_iff_isConj.1 (mk_out_conj (ConjClasses.mk γ)).symm
    · rintro ρ ⟨⟨c, rfl⟩, hρ⟩
      rw [hcls c γ hρ]
  have hinj : Function.Injective (fun c : ConjClasses Γ => e (Quotient.out c)) := fun a b h => by
    rw [← mk_out_conj a, ← mk_out_conj b, e.injective h]
  rw [GlobalTheory.FinTrace.unfolded_eq_orbital_reps H ι.range K V ξ' hQ hloc F hF hs R hR, finsum_mem_range hinj]
  refine finsum_congr fun c => ?_
  simp only [hξ, he]
  rfl

end GlobalTheory.HeckeTrace

namespace GlobalTheory.HeckeTrace

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

theorem mem_map_conj {H : Type} [Group H] (K : Subgroup H) (x g : H) :
    g ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * g * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem locPart_map_eq (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (C : Subgroup Γ) (x : G₁ × G₂) :
    GlobalTheory.LKLoc.locPart (C.map (ι₁.prod ι₂)) (K₁.prod K₂) x = (stab ι₁ ι₂ K₁ K₂ x ⊓ C).map (ι₁.prod ι₂) := by
  ext δ
  rw [GlobalTheory.FinTF.mem_locPart_iff]
  simp only [Subgroup.mem_map, Subgroup.mem_inf, stab, Subgroup.mem_comap, mem_map_conj, Subgroup.mem_prod]
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
    exact ⟨w, ⟨⟨(mem_map_conj _ _ _).2 (by simpa using h1), (mem_map_conj _ _ _).2 (by simpa using h2)⟩, hw⟩, rfl⟩
  · rintro ⟨w, ⟨⟨h1, h2⟩, hw⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, by simpa using (mem_map_conj _ _ _).1 h1, by simpa using (mem_map_conj _ _ _).1 h2⟩

theorem cent_map_eq (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (hι : Function.Injective (ι₁.prod ι₂)) (γ : Γ) :
    Subgroup.centralizer {(ι₁.prod ι₂) γ} ⊓ (ι₁.prod ι₂).range =
      (Subgroup.centralizer {γ}).map (ι₁.prod ι₂) := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨hc, w, rfl⟩
    refine ⟨w, hι ?_, rfl⟩
    rw [map_mul, map_mul, hc]
  · rintro ⟨w, hw, rfl⟩
    exact ⟨by rw [← map_mul, ← map_mul, hw], w, rfl⟩

theorem orbital_eq_centSum (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (hι : Function.Injective (ι₁.prod ι₂))
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ) (γ : Γ) :
    ∑ᶠ q : DoubleCoset.Quotient ((Subgroup.centralizer {(ι₁.prod ι₂) γ} ⊓ (ι₁.prod ι₂).range : Subgroup (G₁ × G₂)) :
        Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)),
      (1 / (Nat.card (GlobalTheory.LKLoc.locPart (Subgroup.centralizer {(ι₁.prod ι₂) γ} ⊓ (ι₁.prod ι₂).range)
          (K₁.prod K₂) q.out) : ℂ)) *
        (fun h : G₁ × G₂ => f₁ h.1 * f₂ h.2) (q.out⁻¹ * (ι₁.prod ι₂) γ * q.out) =
      centSum ι₁ ι₂ (MonoidHom.id G₂) K₁ K₂ 1 f₁ f₂ γ := by
  rw [cent_map_eq ι₁ ι₂ hι γ, centSum]
  refine finsum_congr fun q => ?_
  rw [locPart_map_eq, Subgroup.card_map_of_injective hι, one_div]
  simp [term]

end GlobalTheory.HeckeTrace

namespace GlobalTheory.HeckeTrace

variable {p : ℕ} [Fact p.Prime]

theorem emb_injective {G : HTGroup p} (B : GlobalTheory.LKDef.DForm G) : Function.Injective B.emb := by
  haveI : Nontrivial (AfP p) := GlobalTheory.LKMid.finiteAdeleRingAway_nontrivial p
  have hinj : Function.Injective (inC G (AfP p)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (AfP p)).injective
  have hq : Function.Injective (algebraMap ℚ (AfP p)) := (algebraMap ℚ (AfP p)).injective
  intro y z h
  have h1 := congrArg (fun w : G.GAf × Gr G 1 => ((w.1 : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) h
  simp only [GlobalTheory.LKDef.DForm.emb, GlobalTheory.LKDef.DForm.embAt, MonoidHom.prod_apply, GlobalTheory.LKCx.toAfF,
    MonoidHom.codRestrict_apply] at h1
  obtain ⟨ha, hb⟩ := Prod.ext_iff.1 h1
  simp at ha hb
  have ha' := congrArg (fun u : (AfP p ⊗[ℚ] G.C)ˣ => (u : AfP p ⊗[ℚ] G.C)) ha
  have hb' := congrArg (fun u : (AfP p)ˣ => (u : AfP p)) hb
  simp only [Units.coe_map, MonoidHom.coe_coe] at ha' hb'
  exact Subtype.ext (Prod.ext (Units.ext (hinj ha')) (Units.ext (hq hb')))

end GlobalTheory.HeckeTrace

namespace GlobalTheory.HeckeTrace

theorem dform_trace_eq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ B : GlobalTheory.LKDef.DForm G,
      B.trace ξ L.K.toSubgroup f K' f' =
        ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G B.β),
          LinearMap.trace ℂ V (ξ (Quotient.out c : GlobalTheory.LKCx.grp G B.β).1) *
            centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c) := by
  intro p _ G ha V _ _ _ ξ L f hfT hf K' f' hf'T hf' B
  have hinj := emb_injective B
  have hF : ∀ k ∈ L.K.toSubgroup.prod K', ∀ k' ∈ L.K.toSubgroup.prod K', ∀ g : G.GAf × Gr G 1,
      (fun h : G.GAf × Gr G 1 => f h.1 * f' h.2) (k * g * k') = (fun h : G.GAf × Gr G 1 => f h.1 * f' h.2) g := by
    intro k hk k' hk' g
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [hf _ hk.1 _ hk'.1, hf' _ hk.2 _ hk'.2]
  rw [GlobalTheory.LKDef.DForm.trace, heckeTrace_eq_orbital B.emb hinj _ _ _ hF
    (GlobalTheory.T.heckeTestProduct_support_finite_leftCosets p G L f hfT hf K' f' hf'T hf') (GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level p G ha L K' hf'T.1 B)
    (GlobalTheory.T.definiteForm_stabilizer_finite_away_from_p p G ha L K' hf'T.1 B)]
  refine finsum_congr fun c => ?_
  congr 1
  exact orbital_eq_centSum _ _ hinj _ _ f f' _

end GlobalTheory.HeckeTrace
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_definiteForm_eq_sum_conjClasses : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ B : GlobalTheory.LKDef.DForm G,
      B.trace ξ L.K.toSubgroup f K' f' =
        ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G B.β),
          LinearMap.trace ℂ V (ξ (Quotient.out c : GlobalTheory.LKCx.grp G B.β).1) *
            centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
              (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c) := by
  first | (exact @GlobalTheory.HeckeTrace.dform_trace_eq) | (exact GlobalTheory.HeckeTrace.dform_trace_eq) | (intros; apply GlobalTheory.HeckeTrace.dform_trace_eq <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DefVanish

section Generic

variable {Γ H : Type} [Group Γ] [Group H]

theorem finite_coset_preimage (ι : Γ →* H) (hι : Function.Injective ι) (K : Subgroup H) (x : H) (c : H ⧸ K)
    (hstab : Finite (GlobalTheory.LKLoc.locPart ι.range K x)) :
    {w : Γ | (QuotientGroup.mk (x⁻¹ * ι w * x) : H ⧸ K) = c}.Finite := by
  by_cases hne : ∃ w₀ : Γ, (QuotientGroup.mk (x⁻¹ * ι w₀ * x) : H ⧸ K) = c
  · obtain ⟨w₀, hw₀⟩ := hne
    have hfin : ((GlobalTheory.LKLoc.locPart ι.range K x : Subgroup H) : Set H).Finite := Set.toFinite _
    have hpre : (ι ⁻¹' (GlobalTheory.LKLoc.locPart ι.range K x : Set H)).Finite := hfin.preimage hι.injOn
    refine (hpre.image (fun u => w₀ * u)).subset ?_
    intro w hw
    refine ⟨w₀⁻¹ * w, ?_, by simp⟩
    have h1 : (QuotientGroup.mk (x⁻¹ * ι w * x) : H ⧸ K) = QuotientGroup.mk (x⁻¹ * ι w₀ * x) := by
      rw [hw, hw₀]
    rw [QuotientGroup.eq] at h1
    simp only [Set.mem_preimage, SetLike.mem_coe, GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, MonoidHom.mem_range]
    refine ⟨⟨w₀⁻¹ * w, rfl⟩, ?_⟩
    rw [GlobalTheory.LKCountPoint.mem_map_conj]
    have e : x⁻¹ * ι (w₀⁻¹ * w) * x = (x⁻¹ * ι w₀ * x)⁻¹ * (x⁻¹ * ι w * x) := by
      simp only [map_mul, map_inv]; group
    rw [e]
    have h2 := K.inv_mem h1
    rwa [_root_.mul_inv_rev, inv_inv] at h2
  · push_neg at hne
    convert Set.finite_empty
    ext w; simp [hne w]

theorem finite_supp_cent (ι : Γ →* H) (hι : Function.Injective ι) (K : Subgroup H) (F₀ : H → ℂ) (y : Γ)
    (hbi : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F₀ (k * g * k') = F₀ g)
    (hcls : Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H)))
    (hstab : ∀ x, Finite (GlobalTheory.LKLoc.locPart ι.range K x))
    (hsupp : (Function.support (fun c : H ⧸ K => F₀ c.out)).Finite) :
    {q : DoubleCoset.Quotient (((Subgroup.centralizer {y}).map ι : Subgroup H) : Set H) (K : Set H) |
      F₀ ((Quotient.out q)⁻¹ * ι y * Quotient.out q) ≠ 0}.Finite := by
  set D := DoubleCoset.Quotient (ι.range : Set H) (K : Set H)

  set W : Set Γ := ⋃ d : D, ⋃ c ∈ Function.support (fun c : H ⧸ K => F₀ c.out),
    {w : Γ | (QuotientGroup.mk ((Quotient.out d)⁻¹ * ι w * Quotient.out d) : H ⧸ K) = c}
  have hW : W.Finite :=
    Set.finite_iUnion fun d => hsupp.biUnion fun c _ => finite_coset_preimage ι hι K _ c (hstab _)
  let cj : Γ → Γ := fun w => if h : ∃ γ : Γ, γ⁻¹ * y * γ = w then h.choose else 1
  let g : Γ × D → DoubleCoset.Quotient (((Subgroup.centralizer {y}).map ι : Subgroup H) : Set H) (K : Set H) :=
    fun wd => DoubleCoset.mk _ K (ι (cj wd.1) * Quotient.out wd.2)
  refine ((hW.prod (Set.finite_univ (α := D))).image g).subset ?_
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  set x := Quotient.out q
  obtain ⟨h, k, hh, hk, hd⟩ := DoubleCoset.mk_out_eq_mul ι.range K x
  obtain ⟨γ₀, rfl⟩ := hh
  set d : D := DoubleCoset.mk ι.range K x

  have hx : x = ι γ₀⁻¹ * Quotient.out d * k⁻¹ := by
    rw [hd, map_inv]; group
  set w := γ₀ * y * γ₀⁻¹
  have hconj : x⁻¹ * ι y * x = k * ((Quotient.out d)⁻¹ * ι w * Quotient.out d) * k⁻¹ := by
    rw [hx]; simp only [w, map_mul, map_inv]; group
  have hF : F₀ ((Quotient.out d)⁻¹ * ι w * Quotient.out d) ≠ 0 := by
    rw [hconj, hbi k hk _ (K.inv_mem hk)] at hq; exact hq
  have hwW : w ∈ W := by
    simp only [W, Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨d, QuotientGroup.mk ((Quotient.out d)⁻¹ * ι w * Quotient.out d), ?_, rfl⟩
    simp only [Function.mem_support]
    obtain ⟨k', hk'⟩ := QuotientGroup.mk_out_eq_mul K ((Quotient.out d)⁻¹ * ι w * Quotient.out d)
    rw [hk']
    have := hbi 1 K.one_mem k' k'.2 ((Quotient.out d)⁻¹ * ι w * Quotient.out d)
    rw [one_mul] at this
    rw [this]; exact hF
  refine ⟨(w, d), ⟨hwW, Set.mem_univ _⟩, ?_⟩
  have hex : ∃ γ : Γ, γ⁻¹ * y * γ = w := ⟨γ₀⁻¹, by simp [w]⟩
  have hcj : cj w = hex.choose := dif_pos hex
  have hcs := hex.choose_spec
  set γw := hex.choose

  have hz : γ₀⁻¹ * γw⁻¹ ∈ Subgroup.centralizer {y} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : y * γw = γw * w := by rw [← hcs]; group
    have e2 : w = γ₀ * y * γ₀⁻¹ := rfl
    calc γ₀⁻¹ * γw⁻¹ * y = γ₀⁻¹ * (γw⁻¹ * (y * γw)) * γw⁻¹ := by group
      _ = γ₀⁻¹ * w * γw⁻¹ := by rw [e]; group
      _ = y * (γ₀⁻¹ * γw⁻¹) := by rw [e2]; group
  show DoubleCoset.mk _ K (ι (cj w) * Quotient.out d) = q
  rw [← DoubleCoset.out_eq' _ K q]
  rw [DoubleCoset.eq]
  refine ⟨ι (γ₀⁻¹ * γw⁻¹), ⟨_, hz, rfl⟩, k⁻¹, K.inv_mem hk, ?_⟩
  show x = _
  rw [hx, hcj]; simp only [map_mul, map_inv]; group

end Generic

end GlobalTheory.DefVanish

namespace GlobalTheory.DefVanish

variable {p : ℕ} [Fact p.Prime]

theorem toAfF_injective (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) : Function.Injective (GlobalTheory.LKCx.toAfF G β x t hx) := by
  haveI := GlobalTheory.LKMid.finiteAdeleRingAway_nontrivial p
  intro a b h
  have h0 := congrArg Subtype.val h
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [GlobalTheory.LKCx.toAfF, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
    Prod.map_fst, Prod.map_snd, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj,
    mul_right_inj] at h1 h2
  have e1 : (a : G.Cˣ × ℚˣ).1 = (b : G.Cˣ × ℚˣ).1 := by
    apply Units.ext
    have := congrArg Units.val h1
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (AfP p)).injective this
  have e2 : (a : G.Cˣ × ℚˣ).2 = (b : G.Cˣ × ℚˣ).2 := by
    apply Units.ext
    have := congrArg Units.val h2
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact (algebraMap ℚ (AfP p)).injective this
  exact Subtype.ext (Prod.ext e1 e2)

theorem emb_injective (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) : Function.Injective B.emb := fun a b h =>
  toAfF_injective G B.β _ _ _ (congrArg Prod.fst h)

end GlobalTheory.DefVanish

open scoped Pointwise

namespace GlobalTheory.DefVanish
theorem conjAct_smul_eq_map' {H : Type} [Group H] (g : H) (S : Subgroup H) :
    (ConjAct.toConjAct g • S) = S.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl
end GlobalTheory.DefVanish

open GlobalTheory.DefVanish in

theorem GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ (B : GlobalTheory.LKDef.DForm G) (y : GlobalTheory.LKCx.grp G B.β),
      orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.emb y) (fun h => f h.1 * f' h.2) = 0 →
      centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
        (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' y = 0 := by
  intro p _ G ha L f hf hfb K' f' hf' hf'b B y horb
  have hι : Function.Injective B.emb := emb_injective G B
  have hemb : (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec).prod
      (GlobalTheory.LKCx.toP1 G B.β) = B.emb := rfl
  set K : Subgroup (G.GAf × Gr G 1) := L.K.toSubgroup.prod K' with hKdef
  set F₀ : G.GAf × Gr G 1 → ℂ := fun h => f h.1 * f' h.2 with hF₀
  set Γ' : Subgroup (G.GAf × Gr G 1) := (Subgroup.centralizer {y}).map B.emb with hΓ'
  set T : Subgroup (G.GAf × Gr G 1) := GlobalTheory.BCT.twCent (MonoidHom.id _) (B.emb y) with hT
  have hK'c : ∀ g : Gr G 1, (K'.map (MulAut.conj g).toMonoidHom).Commensurable K' := by
    intro g
    have h1 : (K'.map (MulAut.conj g).toMonoidHom).Commensurable
        ((KHT p G.m G.n 1 G.Fw).map (MulAut.conj g).toMonoidHom) := by
      rw [← conjAct_smul_eq_map', ← conjAct_smul_eq_map']
      exact (Subgroup.Commensurable.commensurable_conj _).1 hf'.1
    exact (h1.trans ((GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius p G 1 one_pos).1 g)).trans hf'.1.symm
  have hK : ∀ x : G.GAf × Gr G 1, (K.map (MulAut.conj x).toMonoidHom).Commensurable K :=
    GlobalTheory.LKCountComm.commensurable_prod _ _ (GlobalTheory.T.compactOpenLevel_conj_commensurable p G L) hK'c
  have hbi : ∀ k ∈ K, ∀ k' ∈ K, ∀ g, F₀ (k * g * k') = F₀ g := by
    intro k hk k' hk' g
    obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
    obtain ⟨hk1', hk2'⟩ := Subgroup.mem_prod.1 hk'
    simp only [hF₀, Prod.fst_mul, Prod.snd_mul]
    rw [hfb _ hk1 _ hk1', hf'b _ hk2 _ hk2']
  have hrange : Γ' ≤ B.emb.range := by
    rintro _ ⟨c, -, rfl⟩; exact ⟨c, rfl⟩
  have hΓT : Γ' ≤ T := by
    rintro _ ⟨c, hc, rfl⟩
    show B.emb c * B.emb y = B.emb y * (MonoidHom.id _) (B.emb c)
    rw [MonoidHom.id_apply, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hc]
  have hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F₀ ((t * x * k)⁻¹ * B.emb y * (t * x * k)) = F₀ (x⁻¹ * B.emb y * x) := by
    intro t ht x k hk
    have ht' : t * B.emb y = B.emb y * t := ht
    have e : (t * x * k)⁻¹ * B.emb y * (t * x * k) = k⁻¹ * (x⁻¹ * B.emb y * x) * k := by
      have e0 : t⁻¹ * B.emb y * t = B.emb y := by rw [mul_assoc, ← ht', inv_mul_cancel_left]
      calc (t * x * k)⁻¹ * B.emb y * (t * x * k) = k⁻¹ * (x⁻¹ * (t⁻¹ * B.emb y * t) * x) * k := by group
        _ = _ := by rw [e0]
    rw [e, hbi _ (K.inv_mem hk) _ hk]
  have hstab := GlobalTheory.T.definiteForm_stabilizer_finite_away_from_p p G ha L K' hf'.1 B
  have hfin : ∀ x : G.GAf × Gr G 1, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1)).Finite := by
    intro x
    haveI := hstab x
    exact (Set.toFinite ((GlobalTheory.LKLoc.locPart B.emb.range K x : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))).subset
      (SetLike.coe_subset_coe.2 (inf_le_inf_right _ hrange))
  have hsupp := finite_supp_cent B.emb hι K F₀ y hbi (GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level p G ha L K' hf'.1 B) hstab
    (GlobalTheory.T.heckeTestProduct_support_finite_leftCosets p G L f hf hfb K' f' hf' hf'b)
  have hcore := (GlobalTheory.LKCountComm.core_count_of_commensurable Γ' T K (fun x => F₀ (x⁻¹ * B.emb y * x)) hΓT hK
    hF hfin hsupp).1
  have horb' : (∑ᶠ q : DoubleCoset.Quotient (T : Set (G.GAf × Gr G 1)) (K : Set (G.GAf × Gr G 1)),
      ((vol (T ⊓ K) (T ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℚ) : ℂ)⁻¹ *
        F₀ ((Quotient.out q)⁻¹ * B.emb y * Quotient.out q)) = 0 := horb
  rw [horb', mul_zero] at hcore
  have hcard : ∀ x : G.GAf × Gr G 1, Nat.card (GlobalTheory.LKCount.stab (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose
      B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec) (GlobalTheory.LKCx.toP1 G B.β) L.K.toSubgroup K' x ⊓
      Subgroup.centralizer {y} : Subgroup (GlobalTheory.LKCx.grp G B.β)) =
      Nat.card (Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup (G.GAf × Gr G 1)) := by
    intro x
    rw [GlobalTheory.LKCountPoint.stab_eq]
    change Nat.card (((K.map (MulAut.conj x).toMonoidHom).comap B.emb ⊓ Subgroup.centralizer {y} :
      Subgroup (GlobalTheory.LKCx.grp G B.β))) = _
    refine Nat.card_congr ((Subgroup.equivMapOfInjective _ _ hι).toEquiv.trans (Equiv.setCongr ?_))
    congr 1
    rw [Subgroup.map_inf_eq _ _ _ hι, Subgroup.map_comap_eq, inf_comm B.emb.range, inf_assoc,
      inf_eq_right.2 hrange, inf_comm]
  rw [← hcore]
  unfold centSum
  refine finsum_congr fun q => ?_
  rw [hcard]
  congr 1
  · simp only [term, hF₀, hemb, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, mul_one, MonoidHom.id_apply]
    rfl
end
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 →
    ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
    ∀ (B : GlobalTheory.LKDef.DForm G) (y : GlobalTheory.LKCx.grp G B.β),
      orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.emb y) (fun h => f h.1 * f' h.2) = 0 →
      centSum (GlobalTheory.LKCx.toAfF G B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec)
        (GlobalTheory.LKCx.toP1 G B.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' y = 0 := by
  first | (exact @GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK) | (exact GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK) | (intros; apply GlobalTheory.LKDef.DForm.centSum_eq_zero_of_orbK <;> assumption)
end

section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bi_invariant_test_function_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 := by
  first | (exact @GlobalTheory.LKDef.Regroup.regroup) | (exact GlobalTheory.LKDef.Regroup.regroup) | (intros; apply GlobalTheory.LKDef.Regroup.regroup <;> assumption)
end

section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem trace_definite_forms_identity : TraceDefinitePairsEqAutomorphicTrace := by
  intro p _ G ha V _ _ _ ξ wt hξ L f hf hfb K' f' hf' hf'b hvan
  rw [GlobalTheory.T.bi_invariant_test_function_sum p G ha wt L f hf hfb K' f' hf' hf'b]
  unfold dTrace
  refine finsum_congr (fun q => ?_)
  rw [GlobalTheory.T.heckeTrace_definiteForm_eq_sum_conjClasses p G ha V ξ L f hf hfb K' f' hf' hf'b (Quot.out q)]
  refine finsum_congr (fun c => ?_)
  split_ifs with h
  · rw [hξ (Quot.out q) (Quotient.out c) h.1 h.2.1]
  · rw [GlobalTheory.T.centSum_eq_zero_of_orbitalIntegral_eq_zero p G ha L f hf hfb K' f' hf' hf'b (Quot.out q) (Quotient.out c)
      (hvan (Quot.out q) _ _ _ (Quotient.out c) h), mul_zero]

end GlobalTheory.LKDef
end
end
