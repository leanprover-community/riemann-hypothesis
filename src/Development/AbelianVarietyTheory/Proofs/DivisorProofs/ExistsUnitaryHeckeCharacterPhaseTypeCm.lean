import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationTranslation
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitRealOfCongrOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdArgRealUnitEqOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetCharEqOneOfHasWt

section
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem weil_unit_phase_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (q : ℕ), q.Prime → 2 < q → ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} → ∏ w : InfinitePlace F, ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  intro F E _ _ _ _ _ _ σ h emb q hq hq2 ht u hu
  have hr := GlobalTheory.T.unit_real_of_sub_one_mem_span_prime E q hq ht u hu
  have hs := GlobalTheory.T.prod_arg_real_unit_eq_one' E q hq hq2 u hu hr
  obtain ⟨hF, hE, h2, -⟩ := h
  let f : InfinitePlace F → InfinitePlace E := fun w => InfinitePlace.mk (emb w).1
  have hcomap : ∀ w, (f w).comap (algebraMap F E) = w := by
    intro w
    simp only [f]
    rw [InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
  have hinj : Function.Injective f := fun a b hab => by
    rw [← hcomap a, ← hcomap b, hab]
  have hcard : Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace E) := by
    have a1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have a2 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have b1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
    have b2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    have c1 := IsTotallyReal.nrComplexPlaces_eq_zero F
    have c2 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have d := Module.finrank_mul_finrank ℚ F E
    rw [h2] at d
    omega
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩
  have hfac : ∀ w, (emb w).1 ((u : 𝓞 E) : E) = (f w).embedding ((u : 𝓞 E) : E) := by
    intro w
    rcases InfinitePlace.embedding_mk_eq (emb w).1 with h' | h'
    · simp only [f]; rw [h']
    · simp only [f]; rw [h', ComplexEmbedding.conjugate_coe_eq, hr]
  rw [← hs]
  rw [← Fintype.prod_bijective f hbij (fun w => ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun v => (v.embedding ((u : 𝓞 E) : E) / ((‖v.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ))) (fun w => by rw [hfac w])]

end GlobalTheory
end

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (q : ℕ), q.Prime → 2 < q → ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} → ∏ w : InfinitePlace F, ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  atlas_forward_decl GlobalTheory.weil_unit_phase_prod
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.OpenCongrIdele

theorem exists_open_congr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (q : ℕ), q ≠ 0 → ∃ U : Subgroup (AF F ⊗[F] E)ˣ, IsOpen (U : Set (AF F ⊗[F] E)ˣ) ∧ (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → z ∈ U) ∧ ∀ k : Eˣ, Units.map (incAF F E).toMonoidHom k ∈ U → ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k ∧ (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
  intro F E _ _ _ _ _ _ q hq
  obtain ⟨Θ, hc, hΘ⟩ := GlobalTheory.CharTransport.exists_toAdele F E
  set 𝔪 : Ideal (𝓞 E) := Ideal.span {((q : ℕ) : 𝓞 E)} with h𝔪
  have hm : 𝔪 ≠ ⊥ := by
    rw [h𝔪, Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hq
  let V : Subgroup (Neutral.B1.Ideles E) := GlobalTheory.Mem.Chr.unitIdl E ⊓ GlobalTheory.RayChar.congrIdl 𝔪
  let φ : (AF F ⊗[F] E)ˣ →* Neutral.B1.Ideles E := Units.map Θ.toMonoidHom
  refine ⟨V.comap φ, ?_, fun z hz => ?_, fun k hk => ?_⟩
  · exact (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.RayChar.isOpen_congrIdl hm)).preimage
      (Continuous.units_map _ hc)
  · have hfin : (Θ (z : AF F ⊗[F] E)).2 = 1 := by
      let a : AF F := pairA F 0 1
      have ha : evI F a = 0 := by
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _
      have h0 : a • ((z : AF F ⊗[F] E) - 1) = 0 := hz a ha
      have h1 : Θ (a • ((z : AF F ⊗[F] E) - 1)) =
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * Θ ((z : AF F ⊗[F] E) - 1) := by
        rw [Algebra.smul_def, map_mul]
        congr 1
        change Θ (a ⊗ₜ[F] (1 : E)) = _
        rw [hΘ, map_one, mul_one]
      have h2 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a).2 = 1 := map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E)
      have h3 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * Θ ((z : AF F ⊗[F] E) - 1)).2 = 0 := by
        rw [← h1, h0, map_zero]; rfl
      have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a).2 * (Θ ((z : AF F ⊗[F] E) - 1)).2 = 0 := h3
      rw [h2, one_mul, map_sub, map_one] at h4
      exact sub_eq_zero.1 h4
    have hv : ∀ v : HeightOneSpectrum (𝓞 E), GlobalTheory.RayChar.cmp (φ z) v = 1 := fun v => by
      show (Θ (z : AF F ⊗[F] E)).2 v = 1
      rw [hfin]; rfl
    refine ⟨fun v => ?_, (GlobalTheory.RayChar.mem_congrIdl hm).2 fun v _ => ?_⟩
    · show Valued.v (GlobalTheory.RayChar.cmp (φ z) v) = 1
      rw [hv v, map_one]
    · rw [hv v, sub_self, map_zero]; exact zero_le'
  · have he : φ (Units.map (incAF F E).toMonoidHom k) = Neutral.B1.diagUnits E k := Units.ext (by
      change Θ ((1 : AF F) ⊗ₜ[F] (k : E)) = _
      rw [hΘ, map_one, one_mul]; rfl)
    have hk' : Neutral.B1.diagUnits E k ∈ V := by rw [← he]; exact hk
    obtain ⟨u, hu⟩ := GlobalTheory.DefU.NonTriv.exists_unit k hk'.1
    refine ⟨u, hu, (GlobalTheory.RayChar.mem_iff_at hm _).2 fun v hv => ?_⟩
    rw [GlobalTheory.RayChar.at'_sub_one]
    have h2 := (GlobalTheory.RayChar.mem_congrIdl hm).1 hk'.2 v hv
    rw [GlobalTheory.RayChar.cmp_diag, ← hu] at h2
    exact h2

end GlobalTheory.OpenCongrIdele
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (q : ℕ), q ≠ 0 → ∃ U : Subgroup (AF F ⊗[F] E)ˣ, IsOpen (U : Set (AF F ⊗[F] E)ˣ) ∧ (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → z ∈ U) ∧ ∀ k : Eˣ, Units.map (incAF F E).toMonoidHom k ∈ U → ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k ∧ (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
  atlas_forward_decl GlobalTheory.OpenCongrIdele.exists_open_congr
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.WeilTypeChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isCMField_of_cmExt {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : IsCMField E := by
  haveI := h.1; haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  exact IsCMField.ofCMExtension F E

def phase : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    ring

theorem phase_val (z : ℂˣ) : ((phase z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem continuous_phase : Continuous phase := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm) fun z => by simp
  · have : (fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((phase z⁻¹ : ℂˣ) : ℂ) :=
      funext fun z => by rw [map_inv]
    show Continuous fun z : ℂˣ => (((phase z)⁻¹ : ℂˣ) : ℂ)
    rw [this]
    show Continuous fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ) / ((‖((z⁻¹ : ℂˣ) : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_coe_inv.div (Complex.continuous_ofReal.comp Units.continuous_coe_inv.norm) fun z => by simp

theorem norm_phase (z : ℂˣ) : ‖((phase z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phase_val, norm_div, Complex.norm_real, norm_norm, div_self (by simp)]

def chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : (AF F ⊗[F] E)ˣ →* ℂˣ :=
  ∏ w, phase.comp (Units.map (piInf (emb w)).toMonoidHom)

theorem chiInf_apply (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ((chiInf emb z : ℂˣ) : ℂ) = ∏ w, (piInf (emb w) z / ((‖piInf (emb w) z‖ : ℝ) : ℂ)) := by
  rw [chiInf, MonoidHom.finset_prod_apply, Units.coe_prod]
  rfl

theorem continuous_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Continuous (chiInf emb) := by
  have e : ⇑(chiInf emb) = fun z => ∏ w, phase (Units.map (piInf (emb w)).toMonoidHom z) :=
    funext fun z => by rw [chiInf, MonoidHom.finset_prod_apply]; rfl
  rw [e]
  exact continuous_finset_prod _ fun w _ =>
    continuous_phase.comp (Continuous.units_map _ (GlobalTheory.ContMapReal.continuous_piInf (emb w)))

theorem norm_chiInf (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (z : (AF F ⊗[F] E)ˣ) :
    ‖((chiInf emb z : ℂˣ) : ℂ)‖ = 1 := by
  rw [chiInf, MonoidHom.finset_prod_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun w _ => norm_phase _

theorem exists_weil_char : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ξ ∧ HasExp B.emb ξ (fun _ => 1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsCMField E := isCMField_of_cmExt hB.cm
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (max 3 (Nat.card (Units.torsion E) + 1))
  have hq2 : 2 < q := by omega
  have htq : Nat.card (Units.torsion E) < q := by omega
  have ht : ¬ q ∣ Nat.card (Units.torsion E) := fun h => absurd (Nat.le_of_dvd Nat.card_pos h) (by omega)
  obtain ⟨U, hU, hUinf, hUk⟩ := GlobalTheory.T.exists_open_idele_subgroup_congruence_mod_q F E q hq.ne_zero
  obtain ⟨χ, hχc, hχ1, hχU, hχk⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (AF F ⊗[F] E)ˣ Eˣ U hU
    (Units.map (incAF F E).toMonoidHom) 1 (chiInf B.emb) (continuous_chiInf B.emb) (norm_chiInf B.emb)
    (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu, hu1⟩ := hUk k hk
      refine Units.ext ?_
      rw [chiInf_apply, MonoidHom.one_apply, Units.val_one]
      have e : ∀ w, piInf (B.emb w) ((Units.map (incAF F E).toMonoidHom k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
          (B.emb w).1 ((u : 𝓞 E) : E) := fun w => by
        rw [hu]
        exact GlobalTheory.ThK.EvAt0.ZPartArc.piInf_inclR' (B.emb w) (k : E)
      simp only [e]
      exact (GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one F E σ hB.cm B.emb q hq hq2 ht u hu1).symm)
  refine ⟨GlobalTheory.unitaryCharToCircle χ hχ1, ⟨?_, fun k => ?_⟩, fun z hz => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp hχc) _
  · apply Circle.ext
    show ((χ (Units.map (incAF F E).toMonoidHom k) : ℂˣ) : ℂ) = 1
    rw [hχk]; rfl
  · show ((χ z : ℂˣ) : ℂ) = _
    rw [hχU z (hUinf z hz), chiInf_apply]
    simp

end GlobalTheory.WeilTypeChar
end
end
