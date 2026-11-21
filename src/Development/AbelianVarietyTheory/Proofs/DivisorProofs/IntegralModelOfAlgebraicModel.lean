import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldLatticeBaseCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDifferentExponentDenominator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorProofsFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneOverLIdeleCharacterValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageCorrespondence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodNormIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetAbelianGalois

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.CMTypeThroughField

theorem comp_bar {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] (j : K →+* ℂ)
    (ψ : E →+* K) : j.comp (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar ψ) = ComplexEmbedding.conjugate (j.comp ψ) := by
  ext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, RingHom.coe_comp, Function.comp_apply]
  exact IsCMField.complexEmbedding_complexConj E (j.comp ψ) x

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K]
    (ψ : E →+* K) : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar ψ) = ψ := by
  ext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar]

theorem isCMTypeIn_bar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (K : Type) [Field K] (j : K →+* ℂ) (I : Type)
    (φ : I → E →+* ℂ) (φK : I → E →+* K), (∀ i, j.comp (φK i) = φ i) → IsCMType φ →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  intro E _ _ _ K _ j I φ φK hφ hcm σ
  have hinj : Function.Injective (fun ψ : E →+* K => j.comp ψ) := by
    intro a b h
    ext x
    exact j.injective (DFunLike.congr_fun h x)
  have key : ∀ i, (σ = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i) ∨ σ = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) ↔
      (j.comp σ = φ i ∨ j.comp σ = ComplexEmbedding.conjugate (φ i)) := by
    intro i
    rw [bar_bar, or_comm]
    constructor
    · rintro (h | h)
      · exact Or.inl (by rw [h, hφ])
      · exact Or.inr (by rw [h, comp_bar, hφ])
    · rintro (h | h)
      · exact Or.inl (hinj (by simp only; rw [h, hφ]))
      · exact Or.inr (hinj (by simp only; rw [h, comp_bar, hφ]))
  obtain ⟨i, hi, hu⟩ := hcm (j.comp σ)
  exact ⟨i, (key i).2 hi, fun i' hi' => hu i' ((key i').1 hi')⟩

end GlobalTheory.CMTypeThroughField
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_conjugate_in_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (K : Type) [Field K] (j : K →+* ℂ) (I : Type)
    (φ : I → E →+* ℂ) (φK : I → E →+* K), (∀ i, j.comp (φK i) = φ i) → IsCMType φ →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMTypeIn (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  atlas_forward_decl GlobalTheory.CMTypeThroughField.isCMTypeIn_bar
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

noncomputable section

namespace GlobalTheory.CNumAtPrime

theorem cNum_eq_c_vp : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (𝔣 : Ideal (OF E)) (l : ℕ), l.Prime →
    ∃ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal ∧ ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp 𝔣 l P : ℚ) : ℝ) = c_vp 𝔣 l := by
  intro E _ _ _ 𝔣 l hl
  classical
  have hlu : ¬ IsUnit (l : 𝓞 E) := by
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 E))
    rw [show (l : 𝓞 E) = algebraMap ℤ (𝓞 E) (l : ℤ) by simp, Algebra.norm_algebraMap] at h2
    have hn : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
    rw [isUnit_pow_iff hn, Int.isUnit_iff] at h2
    have := hl.one_lt
    omega
  obtain ⟨M, hM, hlM⟩ := Ideal.exists_le_maximal _ ((Ideal.span_singleton_ne_top hlu))
  have hlP : (l : 𝓞 E) ∈ M := hlM (Ideal.mem_span_singleton_self _)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    exact Nat.cast_ne_zero.2 hl.ne_zero ((Submodule.mem_bot _).1 hlP)
  let P : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hM0⟩
  refine ⟨P, hlP, ?_⟩
  have hiff : (∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal) ↔
      (∃ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal ∧ v.asIdeal ∣ 𝔣) :=
    ⟨fun ⟨v, a, b⟩ => ⟨v, b, a⟩, fun ⟨v, a, b⟩ => ⟨v, b, a⟩⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp c_vp
  by_cases h : ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal
  · rw [if_pos h, if_pos (hiff.1 h)]
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.condExp 𝔣 l = a0 𝔣 l := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.condExp a0
      congr 1
    rw [hc]
    push_cast
    rfl
  · rw [if_neg h, if_neg (mt hiff.2 h)]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.diffExp_vp GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp
    rw [GlobalTheory.DifferentElement.mult_ratio E l hl P.asIdeal P.isPrime hlP,
      show padicValInt l (discr E) = padicValNat l (discr E).natAbs from rfl, Nat.factorization_def _ hl]
    push_cast
    rfl

end GlobalTheory.CNumAtPrime
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_above_valuation_eq : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (𝔣 : Ideal (OF E)) (l : ℕ), l.Prime →
    ∃ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal ∧ ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp 𝔣 l P : ℚ) : ℝ) = c_vp 𝔣 l := by
  atlas_forward_decl GlobalTheory.CNumAtPrime.cNum_eq_c_vp
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel.HalfLower

section Lin

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

omit [NumberField E] [IsCMField E] in

theorem inK_injective [Module.Free O H] : Function.Injective (inK (O := O) K H) := by
  have h := (Module.Flat.rTensor_preserves_injective_linearMap (M := H) (Algebra.linearMap O K)
    (IsFractionRing.injective O K)).comp (TensorProduct.lid O H).symm.injective
  intro x y hxy
  apply h
  simpa [inK] using hxy

theorem bar_bar (σ : E →+* K) : bar (bar σ) = σ := by
  ext x; simp [bar]

omit [IsDomain O] [IsFractionRing O K] in

theorem baseChange_inK (B : LinearMap.BilinForm O H) (x y : H) :
    B.baseChange K (inK K H x) (inK K H y) = algebraMap O K (B x y) := by
  simp [inK, Algebra.smul_def]

omit [IsCMField E] [IsDomain O] [IsFractionRing O K] in

theorem form_act (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) {σ : E →+* K} {f : H}
    (hf : f ∈ eigLat ρ σ) (a : orderC c) (x : H) : algebraMap O K (B x (ρ a f)) = σ a * algebraMap O K (B x f) := by
  have h : inK K H f ∈ eigK ρ σ := hf
  have h1 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 h a)
  have h2 : (ρ a).baseChange K (inK K H f) = inK K H (ρ a f) := by simp [inK]
  rw [← baseChange_inK, ← baseChange_inK, ← h2, h1, map_smul, smul_eq_mul]

theorem lower_eq [Module.Free O H] (ρ : orderC c →+* Module.End O H) (B : LinearMap.BilinForm O H) {D : O} (hD : D ≠ 0)
    {τ : E →+* K} {e f : H} (he : eigLat ρ τ = O ∙ e) (hf : f ∈ eigLat ρ (bar τ))
    (hsup : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ)
    (horth : ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0)
    {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (hN : IsLower ρ τ e f N) (hM : IsScaledRestr D N M) (x : H) :
    B e f • M x = (D * B x f) • f := by
  have key : ∀ h ∈ ⨆ σ : E →+* K, eigLat ρ σ, B e f • M h = (D * B h f) • f := by
    intro h hh
    induction hh using Submodule.iSup_induction' with
    | mem σ h hh =>
      by_cases hσ : σ = τ
      · subst hσ
        rw [he] at hh
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hh
        have hMe : M e = D • f := inK_injective (K := K) (by rw [hM, hN.1, map_smul, algebraMap_smul])
        simp only [map_smul, hMe, LinearMap.smul_apply, smul_eq_mul, smul_smul]
        congr 1; ring
      · have h1 : M h = 0 := inK_injective (K := K) (by rw [hM, hN.2 σ hσ _ hh, smul_zero, map_zero])
        have h2 : B h f = 0 := IsFractionRing.injective O K (by
          rw [← baseChange_inK, map_zero]
          exact horth σ (bar τ) (fun h' ↦ hσ (by rw [← bar_bar σ, ← h', bar_bar])) _ hh _ hf)
        simp [h1, h2]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, LinearMap.add_apply, smul_add, mul_add, add_smul, hx, hy]
  have h := key _ (hsup x)
  apply smul_right_injective H hD
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h ⊢
  rw [smul_comm D, h, smul_smul]

theorem lower_eq_of_scale [CharZero O] [Module.Free O H] (ρ : orderC c →+* Module.End O H) (B B' : LinearMap.BilinForm O H)
    {D : O} (hD : D ≠ 0)
    {τ : E →+* K} {e f : H} (he : eigLat ρ τ = O ∙ e) (hf : f ∈ eigLat ρ (bar τ))
    (hsup : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat ρ σ)
    (horth : ∀ σ σ' : E →+* K, σ' ≠ bar σ → ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', B.baseChange K x y = 0)
    {N : Module.End K (K ⊗[O] H)} {M : Module.End O H} (hN : IsLower ρ τ e f N) (hM : IsScaledRestr D N M)
    {n : ℕ} (hn : n ≠ 0) (a : orderC c) (hB : ∀ x y, (n : O) * B' x y = 2 * B x (ρ a y)) (h0 : B' e f ≠ 0) (x : H) :
    B' e f • M x = (D * B' x f) • f := by
  have hn' : (n : O) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : B e (ρ a f) * B x f = B x (ρ a f) * B e f := IsFractionRing.injective O K (by
    rw [map_mul, map_mul, form_act ρ B hf, form_act ρ B hf]; ring)
  have h2 : B' e f * B x f = B' x f * B e f :=
    mul_left_cancel₀ hn' (by linear_combination B x f * hB e f - B e f * hB x f + 2 * h1)
  have hβ : B e f ≠ 0 := fun hβ ↦ h0 (mul_left_cancel₀ hn' (by
    have : B e (ρ a f) = 0 := IsFractionRing.injective O K (by rw [form_act ρ B hf, hβ]; simp)
    rw [hB, this]; simp))
  apply smul_right_injective H hβ
  simp only
  rw [smul_comm, lower_eq ρ B hD he hf hsup horth hN hM, smul_smul, smul_smul]
  congr 1
  linear_combination D * h2

end Lin

theorem exists_polForm_baseChange {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem corr_lower (hDR : GlobalTheory.Published.AbelianDeRham) {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
    {𝔠 : FracId (FR E)} {R : Subring ℂ} {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {X₀ : Obj (FR E) 𝔠 (Sp R)} {X : Obj (FR E) 𝔠 (Sp ℂ)} {p : X.A.left ⟶ X₀.A.left} (cm : OAct (orderC c) X₀.A)
    (hrm : ∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a)
    {n : ℕ} (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) {c₀ c₁ : 𝔠.elt} {ψ₀ ψR : LinearMap.BilinForm R (HdR X₀.A)} (hc₀ : (c₀ : FR E) ≠ 0)
    (hψ₀ : IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀)) (hψR : IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₁) ψR)
    {D : R} (hD : D ≠ 0) {τ : E →+* K} {e f : Fin n → R}
    (he : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) τ = R ∙ e)
    (hf : f ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar τ))
    (hsup : ∀ h : Fin n → R, D • h ∈ ⨆ σ : E →+* K, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ)
    (horth : ∀ σ σ' : E →+* K, σ' ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ →
      ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ,
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ',
      LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) x y = 0)
    {N : Module.End K (K ⊗[R] (Fin n → R))} {M : Module.End R (Fin n → R)}
    (hN : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) τ e f N)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D N M)
    (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p)
    {ψ : LinearMap.BilinForm ℂ (HdR X.A)} (hψ : ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ x' y' = algebraMap R ℂ (ψR x y))
    {ev yv : HdR X.A} (hev : m.Corr (eH.symm e) ev) (hyv : m.Corr (eH.symm f) yv) (h0 : ψ ev yv ≠ 0)
    (x₀ : HdR X₀.A) (x : HdR X.A) (hx : m.Corr x₀ x) :
    m.Corr (eH.symm.conjRingEquiv M x₀) ((((D : ℂ) / ψ ev yv) • (ψ.flip yv).smulRight yv) x) := by
  obtain ⟨k, t, hk, ht⟩ := GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hDR (FR E) 𝔠 R X₀ c₁ c₀ hc₀ ψR _ hψR hψ₀
  have hact : act (dp0 R) (𝟙 _) X₀.rm t = act (dp0 R) (𝟙 _) cm (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t) := by
    haveI := X₀.rm.hom t
    haveI := cm.hom (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t)
    rw [act_apply, act_apply]
    exact push_congr _ _ (hrm t).symm
  have hγ := hψ _ _ _ _ hev hyv
  have h1 := lower_eq_of_scale (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
    (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap) (ψR.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap) hD he hf hsup horth
    hN hM hk (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c t) (fun x y ↦ by
      have := ht (eH.symm x) (eH.symm y)
      rw [hact] at this
      simpa using this) (fun h ↦ h0 (by
      have h' : ψR (eH.symm e) (eH.symm f) = 0 := h
      rw [hγ, h', map_zero])) (eH x₀)
  have h2 : ψR (eH.symm e) (eH.symm f) • eH.symm (M (eH x₀)) = (D * ψR x₀ (eH.symm f)) • eH.symm f := by
    have := congrArg eH.symm h1
    simpa using this
  intro z
  have h3 := congrArg (algebraMap R ℂ) (LinearMap.congr_fun h2 z)
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul] at h3
  have h4 : eH.symm.conjRingEquiv M x₀ = eH.symm (M (eH x₀)) := rfl
  rw [h4]
  simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.flip_apply, smul_eq_mul]
  have h5 : ψ.flip yv x = algebraMap R ℂ (ψR x₀ (eH.symm f)) := hψ _ _ _ _ hx hyv
  rw [hyv z, h5, div_mul_eq_mul_div, div_eq_iff h0, hγ]
  have h6 : algebraMap R ℂ D = (D : ℂ) := rfl
  rw [h6] at h3
  linear_combination -h3

theorem neg_le_val_inv {R : Subring ℂ} [IsDiscreteValuationRing R] (l : ℕ) (x : R) (q : ℚ) (hx : x ≠ 0)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) x) ≤ (q : WithTop ℚ)) :
    ((-q : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l ((algebraMap R (FractionRing R) x)⁻¹) := by
  have hx' : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hx
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp at h ⊢
  rw [if_neg hx'] at h
  rw [if_neg (inv_ne_zero hx')]
  have ho : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R ((algebraMap R (FractionRing R) x)⁻¹) = - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (algebraMap R (FractionRing R) x) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw
    rw [map_inv₀, WithZero.log_inv, neg_neg]
  rw [ho]
  have h' := WithTop.coe_le_coe.1 h
  refine WithTop.coe_le_coe.2 ?_
  push_cast
  rw [neg_div]
  exact neg_le_neg h'

end GlobalTheory.LatModel.HalfLower
end
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AdmTransport

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations (inK IsScaledRestr)

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

theorem conj_apply {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) (x : M₂) : e.conjRingEquiv f x = e (f (e.symm x)) := rfl

theorem conj_symm_conj {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) : e.symm.conjRingEquiv (e.conjRingEquiv f) = f := by
  ext x; simp [conj_apply]

theorem inK_injective [IsFractionRing R K] (n : ℕ) : Function.Injective (inK (O := R) K (Fin n → R)) := by
  intro x y hxy
  have h := congrArg (TensorProduct.piScalarRight R K K (Fin n)) hxy
  funext i
  have hi := congrFun h i
  simp [inK] at hi
  apply IsFractionRing.injective R K
  simpa [Algebra.smul_def] using hi

variable {H : Type} [AddCommGroup H] [Module R H]

theorem baseChange_inK (T : Module.End R H) (h : H) : T.baseChange K (inK K H h) = inK K H (T h) := by
  simp [inK, LinearMap.baseChange_tmul]

theorem commute_of_scaledRestr (hinj : Function.Injective (inK (O := R) K H)) {D : R} {N : Module.End K (K ⊗[R] H)}
    {M : Module.End R H} (hM : IsScaledRestr D N M) {T : Module.End R H} (hT : Commute N (T.baseChange K)) :
    Commute M T := by
  refine LinearMap.ext fun h ↦ hinj ?_
  have e := LinearMap.congr_fun hT.eq (inK K H h)
  simp only [Module.End.mul_apply] at e ⊢
  rw [hM, ← baseChange_inK, e, ← LinearMap.map_smul, ← hM, baseChange_inK]

theorem mul_eq_zero_of_scaledRestr (hinj : Function.Injective (inK (O := R) K H)) {D : R}
    {N N' : Module.End K (K ⊗[R] H)} {M M' : Module.End R H} (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M')
    (h0 : N * N' = 0) : M * M' = 0 := by
  refine LinearMap.ext fun h ↦ hinj ?_
  have e := LinearMap.congr_fun h0 (inK K H h)
  simp only [Module.End.mul_apply, LinearMap.zero_apply] at e ⊢
  rw [hM, hM', LinearMap.map_smul, e, smul_zero, smul_zero, map_zero]

theorem bilin_inK (B : LinearMap.BilinForm R H) (u v : H) :
    B.baseChange K (inK K H u) (inK K H v) = algebraMap R K (B u v) := by
  simp [inK, Algebra.algebraMap_eq_smul_one]

theorem skew_of_scaledRestr [IsFractionRing R K] {D : R} {N : Module.End K (K ⊗[R] H)} {M : Module.End R H}
    (hM : IsScaledRestr D N M) (B : LinearMap.BilinForm R H)
    (hs : ∀ x y, B.baseChange K (N x) y + B.baseChange K x (N y) = 0) (u v : H) : B (M u) v + B u (M v) = 0 := by
  apply IsFractionRing.injective R K
  rw [map_add, map_zero, ← bilin_inK, ← bilin_inK, hM, hM, LinearMap.map_smul₂, LinearMap.map_smul, ← smul_add, hs, smul_zero]

theorem orth_of_scaledRestr [IsFractionRing R K] {D : R} {N N' : Module.End K (K ⊗[R] H)} {M M' : Module.End R H}
    (hM : IsScaledRestr D N M) (hM' : IsScaledRestr D N' M') (B : LinearMap.BilinForm R H)
    (hs : ∀ x y, B.baseChange K (N x) (N' y) = 0) (u v : H) : B (M u) (M' v) = 0 := by
  apply IsFractionRing.injective R K
  rw [map_zero, ← bilin_inK, hM, hM', LinearMap.map_smul₂, LinearMap.map_smul, hs, smul_zero, smul_zero]

end GlobalTheory.AdmTransport

namespace GlobalTheory.AdmTransport

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations (inK IsScaledRestr ofF)

theorem admissible_transport_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (cm : OAct (orderC c) X₀.A),
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)),
    (∀ (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X₀.A)), IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c) ψ →
      ∃ (n : ℕ) (t : 𝓞 (FR E)), n ≠ 0 ∧ ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X₀.rm t y)) →
    ∀ (I : Type) [Fintype I] (D : R) (N : I → Module.End K (K ⊗[R] (Fin n → R))) (M : I → Module.End R (Fin n → R)),
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D (N i) (M i)) →
    (∀ i (a : OF E), Commute (N i) (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a)).baseChange K)) →
    (∀ i j, N i * N j = 0) →
    (∀ i x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) y + LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) x (N i y) = 0) →
    (∀ i j x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) (N j y) = 0) → admitted X₀ (fun i ↦ eH.symm.conjRingEquiv (M i)) := by
  intro E _ _ _ c 𝔠 R _ _ _ K _ _ _ X₀ cm hcm n eH ψ₀ hpol I _ D N M hM hN hNN hskew horth
  have hinj := inK_injective (R := R) (K := K) n

  have hact : ∀ a : OF E, act (dp0 R) (𝟙 _) cm (ofF c a) = act (dp0 R) (𝟙 _) X₀.rm a := by
    intro a
    haveI := cm.hom (ofF c a)
    haveI := X₀.rm.hom a
    rw [act_apply, act_apply]
    exact push_congr _ _ (hcm a)

  have hcomm : ∀ i (a : OF E), Commute (eH.symm.conjRingEquiv (M i)) (act (dp0 R) (𝟙 _) X₀.rm a) := by
    intro i a
    have h1 := commute_of_scaledRestr hinj (hM i) (hN i a)
    have h2 := h1.map eH.symm.conjRingEquiv
    rw [← hact]
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, conj_symm_conj] using h2
  set B : LinearMap.BilinForm R (Fin n → R) := ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap with hB
  have hBψ : ∀ x y, ψ₀ x y = B (eH x) (eH y) := by intro x y; simp [hB]
  have hs₀ : ∀ i x y, ψ₀ (eH.symm.conjRingEquiv (M i) x) y + ψ₀ x (eH.symm.conjRingEquiv (M i) y) = 0 := by
    intro i x y
    rw [hBψ, hBψ x]
    simpa [conj_apply] using skew_of_scaledRestr (hM i) B (hskew i) (eH x) (eH y)
  have ho₀ : ∀ i j x y, ψ₀ (eH.symm.conjRingEquiv (M i) x) (eH.symm.conjRingEquiv (M j) y) = 0 := by
    intro i j x y
    rw [hBψ]
    simpa [conj_apply] using orth_of_scaledRestr (hM i) (hM j) B (horth i j) (eH x) (eH y)
  refine ⟨hcomm, fun i j ↦ ?_, fun c' ψ hψ ↦ ?_⟩
  · rw [← map_mul, mul_eq_zero_of_scaledRestr hinj (hM i) (hM j) (hNN i j), map_zero]
  · obtain ⟨m, t, hm, ht⟩ := hpol c' ψ hψ
    have hm' : (m : R) ≠ 0 := Nat.cast_ne_zero.2 hm
    have hT : ∀ i y, act (dp0 R) (𝟙 _) X₀.rm t (eH.symm.conjRingEquiv (M i) y) =
        eH.symm.conjRingEquiv (M i) (act (dp0 R) (𝟙 _) X₀.rm t y) := by
      intro i y
      have := LinearMap.congr_fun (hcomm i t).eq y
      simp only [Module.End.mul_apply] at this
      exact this.symm
    refine ⟨fun i x y ↦ ?_, fun i j x y ↦ ?_⟩
    · apply mul_left_cancel₀ hm'
      rw [mul_add, ht, ht, hT, mul_zero]
      exact hs₀ i x _
    · apply mul_left_cancel₀ hm'
      rw [ht, hT, mul_zero]
      exact ho₀ i j x _

end GlobalTheory.AdmTransport
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_multiplication_de_rham_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (cm : OAct (orderC c) X₀.A),
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)),
    (∀ (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X₀.A)), IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c) ψ →
      ∃ (n : ℕ) (t : 𝓞 (FR E)), n ≠ 0 ∧ ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X₀.rm t y)) →
    ∀ (I : Type) [Fintype I] (D : R) (N : I → Module.End K (K ⊗[R] (Fin n → R))) (M : I → Module.End R (Fin n → R)),
    (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsScaledRestr D (N i) (M i)) →
    (∀ i (a : OF E), Commute (N i) (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a)).baseChange K)) →
    (∀ i j, N i * N j = 0) →
    (∀ i x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) y + LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) x (N i y) = 0) →
    (∀ i j x y, LinearMap.BilinForm.baseChange K (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) (N i x) (N j y) = 0) → admitted X₀ (fun i ↦ eH.symm.conjRingEquiv (M i)) := by
  atlas_forward_decl GlobalTheory.AdmTransport.admissible_transport_equiv
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMVecBC

def diagL {g : ℕ} (d : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun w j := d j * w j
  map_add' w w' := by funext j; simp [mul_add]
  map_smul' r w := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem diagL_apply {g : ℕ} (d w : Fin g → ℂ) (j : Fin g) : diagL d w j = d j * w j := rfl

section Rep

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def lcH (P : u.Λ →+ HdR A) : (u.Λ →₀ ℂ) →ₗ[ℂ] HdR A := Finsupp.linearCombination ℂ (fun x ↦ P x)

def lcW : (u.Λ →₀ ℂ) →ₗ[ℂ] (Fin g → ℂ) := Finsupp.linearCombination ℂ (fun x : u.Λ ↦ (x : Fin g → ℂ))

def Good (h : HdR A) (W : Fin g → ℂ) : Prop := ∃ v, IsLieImage h v ∧ u.IsDiff W v

variable {u}

theorem good_comb (hA : IsAbelianScheme A) {n : ℕ} (cf : Fin n → ℂ) {h : Fin n → HdR A}
    {W : Fin n → Fin g → ℂ} (H : ∀ k, Good u (h k) (W k)) :
    Good u (∑ k, cf k • h k) (∑ k, cf k • W k) := by
  choose v hv using H
  exact ⟨FlagTan.lieComb cf v, FlagTan.isLieImage_lieComb cf fun k ↦ (hv k).1,
    isDiff_sum_smul_of_isLieComb A hA L g n u v W cf _ (fun k ↦ (hv k).1.1) (fun k ↦ (hv k).2)
      (FlagTan.isLieComb_lieComb cf v)⟩

theorem good_zero (hA : IsAbelianScheme A) : Good u 0 0 := by
  simpa using good_comb (u := u) hA (n := 0) Fin.elim0 (h := Fin.elim0) (W := Fin.elim0) fun k ↦ k.elim0

theorem good_add (hA : IsAbelianScheme A) {h h' : HdR A} {W W' : Fin g → ℂ} (H : Good u h W)
    (H' : Good u h' W') : Good u (h + h') (W + W') := by
  have := good_comb (u := u) hA ![1, 1] (h := ![h, h']) (W := ![W, W']) fun k ↦ by
    fin_cases k
    · exact H
    · exact H'
  simpa [Fin.sum_univ_two] using this

theorem good_smul (hA : IsAbelianScheme A) {h : HdR A} {W : Fin g → ℂ} (H : Good u h W) (r : ℂ) :
    Good u (r • h) (r • W) := by
  have := good_comb (u := u) hA ![r] (h := ![h]) (W := ![W]) fun k ↦ by
    fin_cases k
    exact H
  simpa using this

variable (u)

theorem rep_good (hA : IsAbelianScheme A) (P : u.Λ →+ HdR A)
    (hP : ∀ x : u.Λ, ∃ v, IsLieImage (P x) v ∧ u.IsDiff x v) (f : u.Λ →₀ ℂ) :
    Good u (lcH u P f) (lcW u f) := by
  refine Finsupp.induction_linear f ?_ (fun f f' hf hf' ↦ ?_) (fun x r ↦ ?_)
  · simpa using good_zero (u := u) hA
  · simpa [map_add] using good_add hA hf hf'
  · simpa [lcH, lcW] using good_smul hA (hP x) r

theorem rep_push (P : u.Λ →+ HdR A) (α : A ⟶ A) [IsMonHom α] (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ w, u.ex (M w) = u.ex w ≫ α)
    (hpush : ∀ x x' : u.Λ, (x' : Fin g → ℂ) = M x → push (dp0 ℂ) (𝟙 _) α (P x) = P x')
    (f : u.Λ →₀ ℂ) : ∃ f', lcH u P f' = push (dp0 ℂ) (𝟙 _) α (lcH u P f) ∧ lcW u f' = M (lcW u f) := by
  have hΛ : ∀ x : u.Λ, M x ∈ u.Λ := fun x ↦ (u.ker _).1 (by rw [hM, (u.ker _).2 x.2, one_comp])
  let mu : u.Λ → u.Λ := fun x ↦ ⟨M x, hΛ x⟩
  refine ⟨Finsupp.mapDomain mu f, ?_, ?_⟩
  · simp only [lcH, Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
    congr 2
    funext x
    exact (hpush x (mu x) rfl).symm
  · simp only [lcW, Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
    rfl

end Rep

theorem coe_functional {R : Subring ℂ} {n : ℕ} (ℓ : (Fin n → R) →ₗ[R] R) (z : ℂ) (v w : Fin n → R)
    (h : ∀ k, ((v k : R) : ℂ) = z * (w k : ℂ)) : ((ℓ v : R) : ℂ) = z * (ℓ w : ℂ) := by
  classical
  rw [LinearMap.pi_apply_eq_sum_univ ℓ v, LinearMap.pi_apply_eq_sum_univ ℓ w]
  simp only [smul_eq_mul, AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_assoc _ _ _

end GlobalTheory.CMVecBC

namespace GlobalTheory.CMVecBC

open GlobalTheory.CMVecBC in

theorem isCMVec_of_mem_eigLat : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.PeriodComparison → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (y : (Af E)ˣ) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X)
    (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A), c ≠ ⊥ → X.IsPullBy X₀ (spMap R.subtype) p →
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
      ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i)) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC →
    ∀ (i : I) (g : Fin n → R), g ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (φK i) →
    ∃ (yv : HdR X.A) (w : ℂ), U.IsCMVec i yv w ∧ m.Corr (eH.symm g) yv ∧
      ((e i (hL.toLie X₀.rm (eH.symm g)) : R) : ℂ) = a i * w := by
  intro hdR hPC E _ _ _ I _ φ c y 𝔠 R _ X₀ X U p cm hc hpull hcmF hcmC j hj φK hφK e a hPG hL n eH m hm i g hg
  classical
  set g0 := Module.finrank ℚ (FR E) with hg0
  obtain ⟨ε, hPC⟩ := hPC
  obtain ⟨P, hspan, -, hlie, hpush, -⟩ :=
    hPC X.A g0 X.ab X.dim (X.diag U.c) (LB.isLB_pull (X.isLB U.c) _) U.u
  obtain ⟨yv, hyv⟩ := hm.exists (eH.symm g)
  set ρ := eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm) with hρ
  have hcoord : ∀ (b : orderC c) k, (((ρ b g) k : R) : ℂ) = φ i b * (g k : ℂ) := by
    intro b k
    have hg' : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK (FractionRing R) (Fin n → R) g ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (φK i) :=
      Submodule.mem_comap.1 hg
    have h1 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hg' b)
    have h2 := congrArg (LinearMap.liftBaseChange (FractionRing R)
      ((Algebra.linearMap R (FractionRing R)) ∘ₗ LinearMap.proj k)) h1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK, TensorProduct.mk_apply, LinearMap.baseChange_tmul, LinearMap.map_smul,
      LinearMap.liftBaseChange_tmul, one_smul, smul_eq_mul, LinearMap.comp_apply, Algebra.linearMap_apply,
      LinearMap.proj_apply] at h2
    have h3 := congrArg j h2
    have h4 : j (φK i b) = φ i b := by rw [← RingHom.comp_apply, hφK]
    simp only [map_mul, map_one, one_mul, hj, h4] at h3
    simpa using h3
  have hmodel : ∀ (b : orderC c) (α : X.A ⟶ X.A) [IsMonHom α], α.left ≫ p = p ≫ (cm.act b).left →
      push (dp0 ℂ) (𝟙 _) α yv = φ i b • yv := by
    intro b α _ hα
    haveI := cm.hom b
    have h1 : m.Corr (push (dp0 R) (𝟙 _) (cm.act b) (eH.symm g)) (push (dp0 ℂ) (𝟙 _) α yv) :=
      GrpMor.Corr.push m (cm.act b) α hα.symm hyv
    refine (hm.unique h1 fun c' ↦ ?_)
    have he : push (dp0 R) (𝟙 _) (cm.act b) (eH.symm g) = eH.symm (ρ b g) := by
      rw [← act_apply]
      simp [ρ, LinearEquiv.conjRingEquiv, LinearEquiv.conj_apply]
    rw [LinearMap.smul_apply, hyv c', smul_eq_mul, he]
    exact (coe_functional ((LinearMap.applyₗ c') ∘ₗ eH.symm.toLinearMap) _ _ _ (hcoord b)).symm
  have hΛ : ∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α],
      (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∀ x : U.u.Λ, (fun j ↦ φ (U.e j) b * (x : Fin g0 → ℂ) j) ∈ U.u.Λ := fun b α _ hα x ↦
    (U.u.ker _).1 (by rw [hα, (U.u.ker _).2 x.2, one_comp])
  have hCM1 : ∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α],
      (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      push (dp0 ℂ) (𝟙 _) α yv = φ i b • yv := by
    intro b α _ hα
    obtain ⟨N, hN, hNb⟩ := GlobalTheory.CMExtend.exists_natMul_mem_orderC hc b
    obtain ⟨α', _, hα'p, hα'⟩ := hcmC ⟨_, hNb⟩
    have e1 := hmodel ⟨_, hNb⟩ α' hα'p
    have e2 : push (dp0 ℂ) (𝟙 _) α' = (N : ℂ) • push (dp0 ℂ) (𝟙 _) α := by
      refine LinearMap.ext_on_range hspan fun x ↦ ?_
      rw [hpush α' (diagL fun j ↦ φ (U.e j) ((N : E) * b)) hα' x (N • ⟨_, hΛ b α hα x⟩) ?_,
        LinearMap.smul_apply, hpush α (diagL fun j ↦ φ (U.e j) b) hα x ⟨_, hΛ b α hα x⟩ rfl, map_nsmul,
        Nat.cast_smul_eq_nsmul]
      funext k
      have hvec : φ (U.e k) ((N : E) * b) * (x : Fin g0 → ℂ) k = (N : ℂ) * (φ (U.e k) b * (x : Fin g0 → ℂ) k) := by
        simp only [map_mul, map_natCast]; ring
      rw [diagL_apply, hvec]
      clear * - hvec
      simp
    rw [e2, LinearMap.smul_apply] at e1
    have e3 : φ i ((N : E) * b) = (N : ℂ) * φ i b := by simp
    refine smul_right_injective _ (Nat.cast_ne_zero.2 hN : (N : ℂ) ≠ 0) ?_
    simp only
    rw [e1]
    change φ i ((N : E) * b) • yv = _
    rw [e3, mul_smul]
  have hinj : Function.Injective φ := by
    intro i1 i2 h12
    by_contra hne
    have hk : U.e.symm i1 ≠ U.e.symm i2 := fun h ↦ hne (U.e.symm.injective h)
    let S : Submodule ℝ (Fin g0 → ℂ) := LinearMap.ker
      (((LinearMap.proj (R := ℂ) (φ := fun _ : Fin g0 ↦ ℂ) (U.e.symm i1)) - LinearMap.proj (R := ℂ) (φ := fun _ : Fin g0 ↦ ℂ) (U.e.symm i2)).restrictScalars ℝ)
    have hΛS : (U.u.Λ : Set (Fin g0 → ℂ)) ⊆ S := by
      intro w hw
      obtain ⟨x, -, rfl⟩ := (U.lat w).1 hw
      simp [S, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, h12]
    have hle : Submodule.span ℝ (U.u.Λ : Set (Fin g0 → ℂ)) ≤ S := Submodule.span_le.2 hΛS
    rw [U.u.full] at hle
    have h1 := hle (Submodule.mem_top (x := Pi.single (U.e.symm i1) 1))
    simp [S, Pi.single_apply, hk.symm] at h1
  have hsep : ∀ k : Fin g0, k ≠ U.e.symm i → ∃ b : orderC c, φ (U.e k) b ≠ φ i b := by
    intro k hk
    have hne : φ (U.e k) ≠ φ i := fun h ↦ hk (U.e.eq_symm_apply.2 (hinj h))
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.1 hne
    obtain ⟨N, hN, hNx⟩ := GlobalTheory.CMExtend.exists_natMul_mem_orderC hc x
    refine ⟨⟨_, hNx⟩, ?_⟩
    simp only [map_mul, map_natCast]
    exact fun h ↦ hx (mul_left_cancel₀ (Nat.cast_ne_zero.2 hN) h)
  have hrep0 : ∃ f, lcH U.u P f = yv := by
    have h0 : yv ∈ Submodule.span ℂ (Set.range fun x ↦ P x) := by
      rw [show (fun x ↦ P x) = ⇑P from rfl, hspan]; exact Submodule.mem_top
    rw [← Finsupp.range_linearCombination] at h0
    exact h0
  have hstep : ∀ s : Finset (Fin g0), ∃ f, lcH U.u P f = yv ∧ ∀ k ∈ s, k ≠ U.e.symm i → lcW U.u f k = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨f, hf⟩ := hrep0
      exact ⟨f, hf, by simp⟩
    | insert k s hks ih =>
      obtain ⟨f, hf, hz⟩ := ih
      by_cases hk : k = U.e.symm i
      · refine ⟨f, hf, fun k' hk' hne ↦ ?_⟩
        rcases Finset.mem_insert.1 hk' with rfl | h
        · exact absurd hk hne
        · exact hz k' h hne
      obtain ⟨b, hb⟩ := hsep k hk
      obtain ⟨α, _, hαp, hα⟩ := hcmC b
      obtain ⟨f', hf'1, hf'2⟩ :=
        rep_push U.u P α (diagL fun j ↦ φ (U.e j) b) hα (hpush α _ hα) f
      have hne : φ i b - φ (U.e k) b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
      refine ⟨(φ i b - φ (U.e k) b)⁻¹ • (f' - φ (U.e k) b • f), ?_, fun k' hk' hne' ↦ ?_⟩
      · rw [map_smul, map_sub, map_smul, hf'1, hf, hmodel b α hαp, ← sub_smul, smul_smul,
          inv_mul_cancel₀ hne, one_smul]
      · rw [map_smul, map_sub, map_smul, hf'2]
        simp only [Pi.smul_apply, Pi.sub_apply, diagL_apply, smul_eq_mul]
        rcases Finset.mem_insert.1 hk' with rfl | h
        · ring
        · rw [hz k' h hne']; ring
  obtain ⟨f, hf, hz⟩ := hstep Finset.univ
  obtain ⟨v, hv, hdv⟩ := rep_good U.u X.ab P hlie f
  have hW : lcW U.u f = Pi.single (U.e.symm i) (lcW U.u f (U.e.symm i)) := by
    funext k
    by_cases hk : k = U.e.symm i
    · subst hk; simp
    · rw [hz k (Finset.mem_univ _) hk]; simp [Pi.single_apply, hk]
  rw [hf] at hv
  rw [hW] at hdv
  refine ⟨yv, lcW U.u f (U.e.symm i), ⟨fun b α _ hα ↦ hCM1 b α hα, v, hv, hdv⟩, hyv, ?_⟩
  have hcorr := GlobalTheory.RealMult.Obj.lieCorr_of_isLieImage hdR R.subtype hpull m hyv
    ((hL.toLie_eq_iff X₀.rm).1 rfl) (v' := GlobalTheory.Serre.Lie.mk X.rm v hv.1) hv
  have := hPG i _ _ _ hcorr hdv
  rw [this, Pi.single_eq_same]

end GlobalTheory.CMVecBC
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_abelian_variety_good_reduction_model : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.PeriodComparison → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (y : (Af E)ˣ) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X)
    (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC c) X₀.A), c ≠ ⊥ → X.IsPullBy X₀ (spMap R.subtype) p →
    (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = X₀.rm.act a) →
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
      ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i)) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC →
    ∀ (i : I) (g : Fin n → R), g ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (φK i) →
    ∃ (yv : HdR X.A) (w : ℂ), U.IsCMVec i yv w ∧ m.Corr (eH.symm g) yv ∧
      ((e i (hL.toLie X₀.rm (eH.symm g)) : R) : ℂ) = a i * w := by
  atlas_forward_decl GlobalTheory.CMVecBC.isCMVec_of_mem_eigLat
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodDet

theorem multilinear_ext_of {K M N : Type} [CommSemiring K] [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    {J : Type} [Fintype J] [DecidableEq J] (S : Set M)
    (hS : ∀ l₁ l₂ : M →ₗ[K] N, (∀ x ∈ S, l₁ x = l₂ x) → l₁ = l₂)
    (f g : MultilinearMap K (fun _ : J ↦ M) N) (h : ∀ v, (∀ i, v i ∈ S) → f v = g v) : f = g := by
  have key : ∀ s : Finset J, ∀ v : J → M, (∀ i ∉ s, v i ∈ S) → f v = g v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro v hv; exact h v (fun i ↦ hv i (by simp))
    | insert i s hi ih =>
      intro v hv
      have hl := hS (f.toLinearMap v i) (g.toLinearMap v i) (fun x hx ↦ by
        simp only [MultilinearMap.toLinearMap_apply]
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst hji; simpa using hx
        · rw [Function.update_of_ne hji]; exact hv j (by simp [hji, hj]))
      have h2 := LinearMap.congr_fun hl (v i)
      simpa [MultilinearMap.toLinearMap_apply, Function.update_eq_self] using h2
  ext v
  exact key Finset.univ v (by simp)

open GlobalTheory.RealMult.Obj in

theorem exists_detGen_isDet : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (L : Set E) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
    (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap R.subtype) p →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i)) →
    ∀ (δ₀ : X₀.DetGen) (u₀ : R), u₀ ≠ 0 →
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 →
    ∃ δ : X.DetGen, Obj.DetCorr R.subtype p δ₀.1 δ.1 ∧ U.IsDet δ.1 ((∏ i, a i) / (u₀ : ℂ)) := by
  intro _hAb E _ _ _ I _ φ L 𝔠 R _ X₀ X U p hp e a ha δ₀ u₀ hu₀ heq
  classical
  letI : Algebra R ℂ := R.subtype.toAlgebra
  obtain ⟨δ, hδ, -⟩ := Obj.IsPullBy.existsUnique_detGen R.subtype hp δ₀
  obtain ⟨eL, heL, -⟩ := Obj.exists_lieEquiv (R := R) (R' := ℂ) (φ := p) hp
  obtain ⟨h1, h2⟩ := UnifTangent.tangent_bijection U.u X.dim
  have hb : ∀ k : Fin (Module.finrank ℚ (FR E)), ∃ t : X.Lie, U.u.IsDiff (Pi.single k 1) t.hom := fun k ↦ by
    obtain ⟨t, ⟨ht, hd⟩, -⟩ := h2 (Pi.single k 1)
    exact ⟨Serre.Lie.mk X.rm t ht, hd⟩
  choose b hb using hb
  let T : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] X.Lie := Fintype.linearCombination ℂ b
  have hT : ∀ w, U.u.IsDiff w (T w).hom := fun w ↦ by
    have hc : IsLieComb w (fun k ↦ (b k).hom) (T w).hom := by
      rw [Serre.Lie.isLieComb_iff]
      simp [T, Fintype.linearCombination_apply]
    have := UnifDifferential.isDiff_of_isLieComb X.A (X.diag U.c) _ _ U.u (fun k ↦ Pi.single k 1) (fun k ↦ (b k).hom) w
      (T w).hom (fun k ↦ (b k).isTangent) hb hc
    convert this using 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hTu : ∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : X.Lie), U.u.IsDiff w v.hom → v = T w := fun w v hw ↦
    Serre.Lie.ext ((h2 w).unique ⟨v.isTangent, hw⟩ ⟨(T w).isTangent, hT w⟩)
  have hTinj : Function.Injective T := fun w w' h ↦
    (h1 (T w).hom (T w).isTangent).unique (hT w) (h ▸ hT w')
  have hTsurj : Function.Surjective T := fun v ↦ by
    obtain ⟨w, hw, -⟩ := h1 v.hom v.isTangent
    exact ⟨w, (hTu w v hw).symm⟩
  let Te := LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩
  have hS : ∀ l₁ l₂ : X.Lie →ₗ[ℂ] ℂ, (∀ x ∈ Set.range (fun y : X₀.Lie ↦ eL (1 ⊗ₜ y)), l₁ x = l₂ x) → l₁ = l₂ := by
    intro l₁ l₂ h
    have hc : l₁ ∘ₗ eL.toLinearMap = l₂ ∘ₗ eL.toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro x y
      have hx : x ⊗ₜ[R] y = x • ((1 : ℂ) ⊗ₜ[R] y) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hx, map_smul]
      rw [h _ ⟨y, rfl⟩]
    refine LinearMap.ext fun x ↦ ?_
    simpa using LinearMap.congr_fun hc (eL.symm x)
  let eh : I → X.Lie →ₗ[ℂ] ℂ := fun i ↦
    (LinearMap.liftBaseChange ℂ ((Algebra.linearMap R ℂ) ∘ₗ e i)) ∘ₗ eL.symm.toLinearMap
  have heh : ∀ i y, eh i (eL (1 ⊗ₜ y)) = ((e i y : R) : ℂ) := by
    intro i y
    simp [eh, LinearMap.liftBaseChange_tmul]
    rfl

  have hper : ∀ i, eh i = (a i • LinearMap.proj (U.e.symm i)) ∘ₗ Te.symm.toLinearMap := by
    intro i
    apply hS
    rintro _ ⟨y, rfl⟩
    have hW : U.u.IsDiff (Te.symm (eL (1 ⊗ₜ y))) (eL (1 ⊗ₜ y)).hom := by
      have h3 := hT (Te.symm (eL (1 ⊗ₜ y)))
      have h4 : T (Te.symm (eL (1 ⊗ₜ y))) = eL (1 ⊗ₜ y) := Te.apply_symm_apply _
      rwa [h4] at h3
    rw [heh]
    have h5 := ha i y (eL (1 ⊗ₜ y)) _ ((heL _ _).2 rfl) hW
    rw [h5]
    simp
  let D : X.DetOmega := Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ eh (U.e k))
  have hD : ((u₀ : ℂ) • δ.1 : X.DetOmega) = D := by
    apply AlternatingMap.coe_multilinearMap_injective
    apply PeriodDet.multilinear_ext_of _ hS
    intro v hv
    choose y hy using hv
    obtain rfl : v = fun j ↦ eL (1 ⊗ₜ y j) := funext fun j ↦ (hy j).symm
    have hc := hδ y (fun j ↦ eL (1 ⊗ₜ y j)) (fun j ↦ (heL _ _).2 rfl)
    have hq : (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) y =
        (u₀ • δ₀.1) y := DFunLike.congr_fun heq y
    have hD1 : D (fun j ↦ eL (1 ⊗ₜ y j)) =
        R.subtype ((Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) y) := by
      change Matrix.det (fun j ↦ (LinearMap.pi fun k ↦ eh (U.e k)) (eL (1 ⊗ₜ y j))) =
        R.subtype (Matrix.det (fun j ↦ (LinearMap.pi fun k ↦ e (U.e k)) (y j)))
      refine Eq.trans ?_ (RingHom.map_det R.subtype _).symm
      congr 1
      ext j k
      exact heh _ _
    simp only [AlternatingMap.coe_multilinearMap, AlternatingMap.smul_apply, smul_eq_mul]
    rw [hc, hD1, hq]
    simp
  refine ⟨δ, hδ, fun v W hW ↦ ?_⟩
  have hv : ∀ j, Te.symm (v j) = W j := fun j ↦ by
    rw [hTu (W j) (v j) (hW j)]
    exact Te.symm_apply_apply (W j)
  have hu : (u₀ : ℂ) ≠ 0 := fun h ↦ hu₀ (Subtype.ext h)
  have hDv : D v = (∏ i, a i) * W.det := by
    change Matrix.det (fun j ↦ (LinearMap.pi fun k ↦ eh (U.e k)) (v j)) = _
    have hM : (fun j ↦ (LinearMap.pi fun k ↦ eh (U.e k)) (v j)) = Matrix.of fun j k ↦ a (U.e k) * W j k := by
      funext j k
      rw [Matrix.of_apply, LinearMap.pi_apply, hper]
      simp [hv]
    rw [hM, Matrix.det_mul_row, Equiv.prod_comp U.e a]
  have h6 := DFunLike.congr_fun hD v
  rw [AlternatingMap.smul_apply, hDv, smul_eq_mul] at h6
  field_simp
  linear_combination h6

end GlobalTheory.PeriodDet
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_of_good_reduction_model : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (L : Set E) (𝔠 : FracId (FR E)) (R : Subring ℂ) [IsDiscreteValuationRing R]
    (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
    (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap R.subtype) p →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i)) →
    ∀ (δ₀ : X₀.DetGen) (u₀ : R), u₀ ≠ 0 →
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 →
    ∃ δ : X.DetGen, Obj.DetCorr R.subtype p δ₀.1 δ.1 ∧ U.IsDet δ.1 ((∏ i, a i) / (u₀ : ℂ)) := by
  atlas_forward_decl GlobalTheory.PeriodDet.exists_detGen_isDet
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DeRham

theorem hdR_free_of_dvr (H : GlobalTheory.Published.AbelianDeRham) (F : Type) [Field F] [NumberField F]
    (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Obj F 𝔠 (Sp R)) : ∃ n : ℕ, Nonempty (HdR X.A ≃ₗ[R] (Fin n → R)) := by
  letI := X.grp
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim H.1 X.ab X.dim
  haveI := hfin
  haveI := hproj
  haveI : Module.Free R (primDR X.A) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free R (HdR X.A) := inferInstanceAs (Module.Free R (Module.Dual R (primDR X.A)))
  haveI : Module.Finite R (HdR X.A) := inferInstanceAs (Module.Finite R (Module.Dual R (primDR X.A)))
  let b := Module.Free.chooseBasis R (HdR X.A)
  exact ⟨Fintype.card (Module.Free.ChooseBasisIndex R (HdR X.A)),
    ⟨b.equivFun.trans (LinearEquiv.funCongrLeft R R (Fintype.equivFin _).symm)⟩⟩

end GlobalTheory.DeRham
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

set_option maxHeartbeats 1000000 in

theorem modelInt_of_latModel : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
      GlobalTheory.LatModel.HasLatModel φ (condQ 𝔣 Q) y l lam (a0 𝔣 l) Ω →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsLocalRing R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
      (N : I → Module.End R (HdR X₀.A)) (T : CxPt 𝔠 φ (lattice (condQ 𝔣 Q) y)) (a b : I → ℂ),
      (∀ x ∈ R, Sz l lam 0 x) ∧ (∀ q : ℚ, 0 ≤ padicValRat l q → (q : ℂ) ∈ R) ∧ admitted X₀ N ∧ T.IsOver R.subtype X₀ δ₀ N ∧
      (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ T.A i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
        Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ ∧
        Sz l lam (c_vp 𝔣 l) (b i / (a i * T.A i))) ∧
      Sz l lam (Fintype.card I * c_vp 𝔣 l) (T.C / ∏ i, a i) := by
  intro hPC hDR hDC hPM h31 E _ _ _ _ I _ d φ hd 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ hM
  obtain ⟨𝔠, R, hR, X₀, X, U, p, cm, hp, hrm, hcmC, hgen⟩ := hM
  haveI : IsDiscreteValuationRing R := hR.1
  obtain ⟨j, hj, hch, hlm, hcard, hlift, hbr⟩ := GlobalTheory.T.place_ring_fraction_embedding E l lam R hR
  haveI : CharZero R := hch
  choose φK hφK using fun i ↦ hlift (φ i)
  have hCM := GlobalTheory.T.cm_type_conjugate_in_field E (FractionRing R) j I φ φK hφK hd.2.2.2.2.2.2.1
  choose e a ha hSz hPG huniq using hgen
  have hgens : ∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
      ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i :=
    fun i ↦ ⟨ha i, hPG i, huniq i⟩
  have hL : LieExact X₀.A := (hDR.2.1 R X₀.A _ X₀.ab X₀.dim).1
  obtain ⟨n, ⟨eH⟩⟩ := GlobalTheory.DeRham.hdR_free_of_dvr hDR (FR E) 𝔠 R X₀
  obtain ⟨c₀, ψ₀, hc₀, hgen0, hpol, hCML, hr⟩ := GlobalTheory.T.divisorProofs_fact hPC hDR hDC hPM E I d φ hd 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR
    X₀ X U p cm hp hrm hcmC j hj φK hφK e a hgens hL n eH
  obtain ⟨P, hlP, hPc⟩ := GlobalTheory.T.exists_prime_above_valuation_eq E 𝔣 l Fact.out
  obtain ⟨⟨D, hDv, hDc⟩, hDQ⟩ := h31.1 E 𝔣 h𝔣 l Fact.out R (FractionRing R) hlm hcard
  have hD0 : D ≠ 0 := by
    intro h
    have h' := hDv P hlP
    rw [h, map_zero] at h'
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp] at h'
  obtain ⟨hEig, hrest⟩ := h31.2.1 E 𝔣 h𝔣 l Fact.out Q hQ hQl R (FractionRing R) hlm hcard D hD0 hDc I
    (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) hCM (Fin n → R) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) hCML
  have hg : ∀ σ : E →+* FractionRing R, ∃ g : Fin n → R,
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ = Submodule.span R {g} := fun σ ↦ by
    obtain ⟨g, -, h⟩ := (hEig.2.1 σ).2.1
    exact ⟨g, h⟩
  choose gen hgen' using hg
  have hIG : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
      (fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) (fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)))) :=
    fun i ↦ ⟨hgen' _, hgen' _⟩
  obtain ⟨hbd, hLow, -, -⟩ := hrest _ _ hIG
  choose N hN using fun i ↦ (hLow.1 i).exists
  obtain ⟨hMex, hcomm, hprod, hskew, horth, -⟩ := hLow.2 N hN
  choose M hM using fun i ↦ (hMex i).exists
  obtain ⟨δ₀, u₀, hu₀, hu₀v⟩ := GlobalTheory.T.one_over_l_idele_character_value hDR E I d φ hd 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hp hrm hcmC j hj φK hφK
    e a hgens D hD0 ((hDQ Q hQ hQl D).2 hDc)
  have hAdm := GlobalTheory.T.complex_multiplication_de_rham_form E (condQ 𝔣 Q) 𝔠 R (FractionRing R) X₀ cm hrm n eH ψ₀
    (fun c ψ hψ ↦ by
      obtain ⟨k, t, hk, h⟩ := GlobalTheory.RealMult.PolScale.exists_nat_mul_polForm_eq hDR (FR E) 𝔠 R X₀ c c₀ hc₀ ψ ((2 : R) • ψ₀) hψ hpol
      refine ⟨k, 2 * t, hk, fun x y ↦ ?_⟩
      rw [h, two_mul t, map_add]
      simp [two_smul]) I D N M hM hcomm hprod hskew horth
  let e' : I → Fin n → R := fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))
  let f' : I → Fin n → R := fun i ↦ gen (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)))
  let cv : ℚ := GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp 𝔣 l P
  have hDv' : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) = (cv : WithTop ℚ) := hDv P hlP
  have hcv : (cv : ℝ) = c_vp 𝔣 l := hPc
  obtain ⟨m, hm⟩ : ∃ m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p, m.IsBC :=
    ⟨GlobalTheory.Published.AbelianDeRham.bcMor hp.grp, (hDR.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hp.grp).1⟩
  obtain ⟨ψR, hψR⟩ := GlobalTheory.PureLift.exists_isPolForm hDR.1 X₀.ab X₀.dim (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB (X₀.isLB U.c) _)
  obtain ⟨ψ, hψ, hψbc⟩ := HalfLower.exists_polForm_baseChange (algebraMap R ℂ) hp m U.c hψR
  have hf'' : ∀ i, f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm))
      (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i))) := fun i ↦ by
    rw [(hIG i).2]
    exact Submodule.mem_span_singleton_self _
  have hf' : ∀ i, f' i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (φK i) := fun i ↦ by
    have h := hf'' i
    rwa [HalfLower.bar_bar] at h
  choose yv w hcm hyv hw using fun i ↦ GlobalTheory.T.cm_abelian_variety_good_reduction_model hDR hPC E I φ (condQ 𝔣 Q) y 𝔠 R X₀ X U p cm
    (mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ ↦ q.ne_bot)) hp hrm hcmC j hj φK hφK e a hPG hL n eH m hm i (f' i) (hf' i)
  choose ev hev using fun i ↦ hm.exists (eH.symm (e' i))
  have hDC0 : (D : ℂ) ≠ 0 := by exact_mod_cast hD0
  have hpol' : IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) := by
    rwa [two_smul, ← two_smul R ψ₀]
  have hsz := GlobalTheory.T.cm_auxiliary_set_abelian_galois hPC hDR hDC hPM E I d φ hd 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hp hrm hcmC j hj φK hφK e a hgens
    hL n eH c₀ ψ₀ hc₀ hgen0 hpol' hCML hr D cv hDv' hcv e' f' hIG hbd m hm ψ hψ yv ev w hcm hyv hev hw
  have hne : ∀ i, ψ (ev i) (yv i) ≠ 0 := fun i h ↦ (hsz i).1 (by rw [h]; simp)
  have hlow := fun i ↦ HalfLower.corr_lower hDR cm hrm eH hc₀ hpol hψR hD0 (hIG i).1 (hf'' i) hEig.2.2.1.2 hEig.2.2.2.2
    (hN i) (hM i) m hψbc (hev i) (hyv i) (hne i)
  have hnsm : (Fintype.card I • (cv : WithTop ℚ)) = (((Fintype.card I : ℚ) * cv : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_nsmul, nsmul_eq_mul]
  have hu0 : u₀ ≠ 0 := by
    rintro rfl
    rw [hDv', hnsm, map_zero] at hu₀v
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (0 : FractionRing R) = ⊤ := by simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp]
    rw [h0] at hu₀v
    exact WithTop.not_top_le_coe _ hu₀v
  obtain ⟨δ, hδ, hdet⟩ := GlobalTheory.T.periods_of_good_reduction_model hDR E I φ _ 𝔠 R X₀ X U p hp e a hPG δ₀ u₀ hu0 hu₀
  have hSz' : ∀ (x : R) (q : ℚ), x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) x) ≤ (q : WithTop ℚ) →
      Sz l lam (q : ℝ) ((x : ℂ))⁻¹ := fun x q hx h ↦ by
    have := hbr _ q (HalfLower.neg_le_val_inv l x q hx h)
    rwa [map_inv₀, hj] at this
  have hpa : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ ha i
  let T : CxPt 𝔠 φ (lattice (condQ 𝔣 Q) y) :=
    { X := X, U := U, δ := δ, C := (∏ i, a i) / (u₀ : ℂ), det := hdet, ψ := ψ, pol := hψ, y := yv, w := w,
      s := fun i ↦ (D : ℂ) / ψ (ev i) (yv i), cm := hcm }
  have hA : ∀ i, T.A i = (Real.pi : ℂ) * (U.h i : ℂ) * ((D : ℂ) / ψ (ev i) (yv i)) * w i ^ 2 := fun i ↦ rfl
  refine ⟨𝔠, R, inferInstance, X₀, δ₀, _, T, a, fun i ↦ a i * T.A i / (D : ℂ), hR.2.1, hR.2.2.1, hAdm,
    ⟨p, m, hp, hδ, fun i x₀ x hx ↦ hlow i x₀ x hx⟩, fun i ↦ ?_, ?_⟩
  · have hA0 : T.A i ≠ 0 := by rw [hA]; exact (hsz i).1
    refine ⟨ha i, div_ne_zero (mul_ne_zero (ha i) hA0) hDC0, hA0, hSz i, (hsz i).2, ?_⟩
    have hai := ha i
    have e1 : a i * T.A i / (D : ℂ) / (a i * T.A i) = ((D : R) : ℂ)⁻¹ := by
      field_simp
    show Sz l lam (c_vp 𝔣 l) (a i * T.A i / (D : ℂ) / (a i * T.A i))
    rw [e1, ← hcv]
    exact hSz' D cv hD0 (le_of_eq hDv')
  · have e1 : T.C / ∏ i, a i = ((u₀ : R) : ℂ)⁻¹ := by
      show (∏ i, a i) / (u₀ : ℂ) / ∏ i, a i = _
      field_simp
    rw [e1]
    have h2 := hSz' u₀ ((Fintype.card I : ℚ) * cv) hu0 (by rw [hDv', hnsm] at hu₀v; exact hu₀v)
    convert h2 using 2
    push_cast
    rw [hcv]

end GlobalTheory.LatModel
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_field_lattice_prime_condition : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
      GlobalTheory.LatModel.HasLatModel φ (condQ 𝔣 Q) y l lam (a0 𝔣 l) Ω →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsLocalRing R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (δ₀ : X₀.DetGen)
      (N : I → Module.End R (HdR X₀.A)) (T : CxPt 𝔠 φ (lattice (condQ 𝔣 Q) y)) (a b : I → ℂ),
      (∀ x ∈ R, Sz l lam 0 x) ∧ (∀ q : ℚ, 0 ≤ padicValRat l q → (q : ℂ) ∈ R) ∧ admitted X₀ N ∧ T.IsOver R.subtype X₀ δ₀ N ∧
      (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ T.A i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
        Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹ ∧
        Sz l lam (c_vp 𝔣 l) (b i / (a i * T.A i))) ∧
      Sz l lam (Fintype.card I * c_vp 𝔣 l) (T.C / ∏ i, a i) := by
  atlas_forward_decl GlobalTheory.LatModel.modelInt_of_latModel
end

section
section
set_option autoImplicit false

open GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatModel

theorem modelInt : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham →
    GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement → ModelAlg → ModelInt := by
  intro hPC hST hDR hDC hPM h31 _
  intro E _ _ _ _ I _ d φ _ hd _ _ _ 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy _ lam Ω hΩ
  exact GlobalTheory.T.cm_field_lattice_prime_condition hPC hDR hDC hPM h31 E I d φ hd 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ
    (GlobalTheory.T.cm_field_lattice_base_condition hPC hST hDR hDC hPM E I d φ hd 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ)

end GlobalTheory.LatModel
end

open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_of_algebraic_model : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement → ModelAlg → ModelInt := by
  atlas_forward_decl GlobalTheory.LatModel.modelInt
end
