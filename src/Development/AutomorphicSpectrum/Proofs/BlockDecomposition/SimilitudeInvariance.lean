import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalHHermScal
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFibreMeasureLocal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatrixEulerProduct

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SimilExists

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def frame (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) : Matrix (Fin 2) (Fin 2) E :=
  !![x 0, -(σ (x 0) * J 0 1 + σ (x 1) * J 1 1); x 1, σ (x 0) * J 0 0 + σ (x 1) * J 1 0]

theorem frame_det (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) :
    (frame σ J x).det = hE σ J x x := by
  simp [frame, Matrix.det_fin_two, hE, hform, Fin.sum_univ_two]
  ring

theorem frame_gram {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {J : Matrix (Fin 2) (Fin 2) E}
    (hJ : IsHermND σ J) (x : Fin 2 → E) :
    cT (σ : E →+* E) (frame σ J x) * J * frame σ J x =
      hE σ J x x • Matrix.diagonal ![1, J.det] := by
  have h00 : σ (J 0 0) = J 0 0 := hJ.1 0 0
  have h11 : σ (J 1 1) = J 1 1 := hJ.1 1 1
  have h01 : σ (J 1 0) = J 0 1 := hJ.1 0 1
  have h10 : σ (J 0 1) = J 1 0 := hJ.1 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, cT, Matrix.mul_apply, Fin.sum_univ_two, hE, hform, Matrix.det_fin_two, hσ, h00, h11,
      h01, h10] <;> ring

theorem exists_similitude_of_vectors {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) {x x' : Fin 2 → E} {b b' : E}
    (hx : hE σ J x x = b) (hx' : hE σ J x' x' = b') (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J *
      (γ : Matrix (Fin 2) (Fin 2) E) = (b' / b) • J := by
  set P := frame σ J x with hP
  set P' := frame σ J x' with hP'
  have hdet : P.det = b := by rw [hP, frame_det, hx]
  have hdet' : P'.det = b' := by rw [hP', frame_det, hx']
  have hu : IsUnit P.det := by rw [hdet]; exact hb.isUnit
  have hinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hc : cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P = 1 := by
    rw [← cT_mul, hinv, cT_one]
  have hg : cT (σ : E →+* E) P * J * P = b • Matrix.diagonal ![1, J.det] := by
    rw [hP, frame_gram hσ hJ, hx]
  have hg' : cT (σ : E →+* E) P' * J * P' = b' • Matrix.diagonal ![1, J.det] := by
    rw [hP', frame_gram hσ hJ, hx']
  have hJ' : J = b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
    calc J = (cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P) * J * (P * P⁻¹) := by
          rw [hc, hinv, Matrix.one_mul, Matrix.mul_one]
      _ = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P * J * P) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  have hdetG : (P' * P⁻¹).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hdet', hdet]
    simpa using ⟨hb', hb⟩
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (P' * P⁻¹) hdetG, ?_⟩
  change cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹) = (b' / b) • J
  calc cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹)
      = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P' * J * P') * P⁻¹ := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = b' • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
        rw [hg', Matrix.mul_smul, Matrix.smul_mul]
    _ = (b' / b) • (b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹)) := by
        rw [smul_smul, div_mul_cancel₀ _ hb]
    _ = (b' / b) • J := by rw [← hJ']

theorem exists_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  intro F E _ _ _ _ _ σ hcm J hJ β β' hβ hβ' ⟨X, hX⟩ ⟨X', hX'⟩
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2]
    simp
  have hx : hE σ J (X 0) (X 0) = algebraMap F E β := congrFun (congrFun hX 0) 0
  have hx' : hE σ J (X' 0) (X' 0) = algebraMap F E β' := congrFun (congrFun hX' 0) 0
  have hb : algebraMap F E β ≠ 0 := by simpa using hβ
  have hb' : algebraMap F E β' ≠ 0 := by simpa using hβ'
  rw [map_div₀]
  exact exists_similitude_of_vectors hσ hJ hx hx' hb hb'

end GlobalTheory.CompanionTheory.SimilExists

end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_between_nonempty_spheres : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SimilExists.exists_similitude
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThetaIndep

theorem thetaMeas_gram_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕₂ n T
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hrat := (GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ n 0 T).2
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n {X | gramE σ J X = T}
  have hl' := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ' 𝓕' hμ' h𝓕₂ n {X | gramE σ J X = T}
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  have : μ'.IsHaarMeasure := hμ'
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
  have h𝓕₁ : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 := (GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕₁ hfin).1
  have hsm : μ' = Measure.haarScalarFactor μ' μ • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hc0 : Measure.haarScalarFactor μ' μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne'
  set c : ℝ≥0 := Measure.haarScalarFactor μ' μ with hc
  have hac : μ ≪ μ' := by
    rw [hsm]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have h𝓕₃ : IsFundamentalDomain Γ 𝓕' μ' := h𝓕₂
  have h𝓕₄ : IsFundamentalDomain Γ 𝓕' μ := h𝓕₃.mono hac
  have hmass : μ 𝓕 = μ 𝓕' := h𝓕₁.measure_eq h𝓕₄
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [hl _ hΦ, hl' _ hΦ]
  set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : {X | gramE σ J X = T},
    Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
  have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
    choose t ht using fun X : {X | gramE σ J X = T} => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := n) γ⁻¹ X.1
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hT : ∀ X, gramE σ J (t X) = T := fun X =>
      Matrix.map_injective hinj (by simp only [← hrat, ← ht', ag]; rw [hrat, X.2])
    have hti : Function.Injective fun X => (⟨t X, hT X⟩ : {X | gramE σ J X = T}) := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact Subtype.ext (hri h1)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
  have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
    (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
  have hint : ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g in 𝓕', f g ∂μ := h𝓕₁.setLIntegral_eq h𝓕₄ f hinv
  have hcE0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [hint, hsm, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, ← hmass]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hcE0) (Or.inl hcT)]
  calc _ = ((c : ℝ≥0∞)⁻¹ * c) * ((μ 𝓕)⁻¹ * ∫⁻ g in 𝓕', f g ∂μ) := by rw [ENNReal.inv_mul_cancel hcE0 hcT, one_mul]
    _ = _ := by ring

end GlobalTheory.CompanionTheory.SW.ThetaIndep

end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_independent_choices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | exact GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SimTheta

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mem_UJ_smul_iff (s : A →+* A) (J : Matrix n n A) (c d : A) (hdc : d * c = 1) (u : GL n A) :
    u ∈ UJ s (c • J) ↔ u ∈ UJ s J := by
  have hscale : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) =
      c • (cT s (u : Matrix n n A) * J * (u : Matrix n n A)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · intro h
    have h' : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J := h
    rw [hscale] at h'
    change cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J
    have h2 := congrArg (fun B : Matrix n n A => d • B) h'
    simpa only [smul_smul, hdc, one_smul] using h2
  · intro h
    have h' : cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J := h
    change cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J
    rw [hscale, h']

theorem conj_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G * u * G⁻¹ ∈ UJ s J := by
  refine GlobalTheory.CompanionTheory.SW.HIsom.conj_mem_UJ s J G u ?_
  rw [hG]
  exact (mem_UJ_smul_iff s J c d hdc u).2 hu

theorem conj_inv_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G⁻¹ * u * G ∈ UJ s J := by
  have h := GlobalTheory.CompanionTheory.SW.HIsom.conj_inv_mem_UJ s J G u hu
  rw [hG] at h
  exact (mem_UJ_smul_iff s J c d hdc _).1 h

end Generic

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem JR_smul (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (c : E)
    (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (c • J) = inclR (F := F) R c • JR (F := F) R J := by
  ext i j
  simp [JR, Matrix.map_apply]

theorem gramE_smul (σ : E →ₐ[F] E) {M n : ℕ} (c : E) (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramE σ (c • J) X = c • gramE σ J X := by
  ext a b
  simp only [gramE, hE, hform, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def gramEquiv (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E) (c : E)
    (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    (T : Matrix (Fin n) (Fin n) E) :
    {X : Fin n → Fin M → E | gramE σ J X = T} ≃ {X : Fin n → Fin M → E | gramE σ J X = c • T} where
  toFun X := ⟨SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E) X.1, by
    have := X.2
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [SWIsom.gramE_ratAct, hg, gramE_smul, this]⟩
  invFun Y := ⟨SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1, by
    have hY := Y.2
    simp only [Set.mem_setOf_eq] at hY ⊢
    have h1 : gramE σ J (SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E)
        (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1)) =
        c • gramE σ J (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1) := by
      rw [SWIsom.gramE_ratAct, hg, gramE_smul]
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one, hY] at h1
    exact (smul_right_injective _ hc h1).symm⟩
  left_inv X := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ X.1) = X.1
    rw [SWIsom.ratAct_mul, Units.inv_mul, SWIsom.ratAct_one]
  right_inv Y := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ Y.1) = Y.1
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one]

end Alg

theorem unitaryConj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E)
    (l : F) (hl : l ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) =
      (algebraMap F E l) • J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    ∃ e : HA R σ J ≃ₜ* HA R σ J,
      (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J u * (bc (inclR R) g)⁻¹) ∧
      ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J u ∈ HFin R σ J := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens F E R
  set G : GL (Fin M) (R ⊗[F] E) := bc (inclR R) g with hG
  have hdcE : algebraMap F E l⁻¹ * algebraMap F E l = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hl, map_one]
  have hdcR : inclR (F := F) R (algebraMap F E l⁻¹) * inclR (F := F) R (algebraMap F E l) = 1 := by
    rw [← map_mul, hdcE, map_one]
  have hGR : cT (sigR R σ) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = inclR (F := F) R (algebraMap F E l) • JR R J := by
    rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj R σ J g, hg, JR_smul]
  have h₁ : ∀ u ∈ HR R σ J, G * u * G⁻¹ ∈ HR R σ J := fun u hu =>
    conj_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  have h₂ : ∀ u ∈ HR R σ J, G⁻¹ * u * G ∈ HR R σ J := fun u hu =>
    conj_inv_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  refine ⟨GlobalTheory.CompanionTheory.SW.HIsom.conjHomeo _ _ G h₁ h₂, fun u => rfl, fun u => ?_⟩
  change G * HA.mat R σ J u * G⁻¹ ∈ HFin R σ J ↔ _
  constructor
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g⁻¹ * w * g, conj_inv_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = G * HA.mat R σ J u * G⁻¹ := hwu
    simp only [map_mul, map_inv, this, ← hG]
    group
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g * w * g⁻¹, conj_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = HA.mat R σ J u := hwu
    simp only [map_mul, map_inv, this, ← hG]

section Theta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem theta_map (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (g : GL (Fin M) E) (c : E) (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    [LocallyCompactSpace (AF F)] [SecondCountableTopology (AF F)] [T2Space (AF F)]
    (He : HA (AF F) σ J ≃ᵐ HA (AF F) σ J)
    (hmat : ∀ u, HA.mat (AF F) σ J (He u) =
      bc (inclR (AF F)) g * HA.mat (AF F) σ J u * (bc (inclR (AF F)) g)⁻¹)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (T : Matrix (Fin n) (Fin n) E) :
    (thetaMeas σ J (μ.map He.symm) (He ⁻¹' 𝓕) {X | gramE σ J X = T}).map
        (actTup (AF F) (bc (inclR (AF F)) g)) =
      thetaMeas σ J μ 𝓕 {X | gramE σ J X = c • T} := by
  obtain ⟨tg, -, -, -, bs, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M
  set G : GL (Fin M) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
  have hmG := SWIsom.measurable_actTup (n := n) σ hCM (AF F) G
  have hmf : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ Y := fun Y =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have hmass : (μ.map He.symm) (He ⁻¹' 𝓕) = μ 𝓕 := by
    rw [He.symm.map_apply]
    congr 1
    ext x
    simp
  have hrest : ((μ.map He.symm).restrict (He ⁻¹' 𝓕)).map He = μ.restrict 𝓕 := by
    rw [← He.restrict_map, Measure.map_map He.measurable He.symm.measurable]
    simp
  unfold thetaMeas
  rw [Measure.map_smul, hmass]
  congr 1
  rw [Measure.map_sum hmG.aemeasurable, ← SWIsom.sum_reindex (gramEquiv σ J g c hc hg T)]
  congr 1
  funext X
  rw [Measure.map_map hmG (hmf _)]
  have hcomp : (actTup (AF F) G ∘ fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) =
      (fun h => actW (AF F) σ J h⁻¹
        (ratTup (AF F) ((gramEquiv σ J g c hc hg T X : _) : Fin n → Fin M → E))) ∘ He := by
    funext h
    have := SWIsom.act_conj (AF F) σ G He hmat h (ratTup (AF F) (X : Fin n → Fin M → E))
    simp only [Function.comp]
    rw [this, ← SWIsom.ratTup_ratAct]
    rfl
  rw [hcomp, ← Measure.map_map (hmf _) He.measurable, hrest]

end Theta

theorem theta_simil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (γ : GL (Fin M) E) (l : F), l ≠ 0 → cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J → ∃ (μ' : Measure (HA (AF F) σ J)) (𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ' ∧ IsFDH F E σ M J μ' 𝓕' ∧ ∀ (n : ℕ) (T T' : Matrix (Fin n) (Fin n) E), T' = (algebraMap F E l) • T → (thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T}).map (actTup (AF F) (bc (inclR (AF F)) γ)) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T'} := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ 𝓕 hμ h𝓕 γ l hl hγ
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := unitaryConj F E σ hCM M J γ l hl hγ (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M J (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M J (μ.map He.symm) (He ⁻¹' 𝓕) :=
    SWIsom.isFD_pull σ e.toMulEquiv hrat hq h𝓕
  have hc : algebraMap F E l ≠ 0 := by
    simpa using hl
  refine ⟨_, _, hμ', h𝓕', ?_⟩
  intro n T T' hT'
  subst hT'
  exact theta_map σ hCM J hJ γ _ hc hγ He hmat μ 𝓕 T

end GlobalTheory.CompanionTheory.SW.SimTheta
end
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (γ : GL (Fin M) E) (l : F), l ≠ 0 → cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J → ∃ (μ' : Measure (HA (AF F) σ J)) (𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ' ∧ IsFDH F E σ M J μ' 𝓕' ∧ ∀ (n : ℕ) (T T' : Matrix (Fin n) (Fin n) E), T' = (algebraMap F E l) • T → (thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T}).map (actTup (AF F) (bc (inclR (AF F)) γ)) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T'} := by
  first | exact @GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil | exact GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil | (intros; apply GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fibre_measure_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : GL (Fin M) (R ⊗[F] E)) (l : R), IsUnit l → cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (algebraMap R (R ⊗[F] E) l) • JR R J → ∀ a c : ℝ≥0, μ.map (actTup R g) = a • μ → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l) = c • ν → ∀ S, (m S).map (actTup R g) = (a / c) • m (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude | exact GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude | (intros; apply GlobalTheory.CompanionTheory.SW.FibSim.fib_similitude <;> assumption)
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

theorem map_eq_sqrt_smul {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] (c : ℝ≥0)
    (h : ν.map (e ∘ e) = c • ν) : ν.map e = NNReal.sqrt c • ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul, hb, smul_smul]
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbc : b * b = c := by
    have h3 : ((b * b : ℝ≥0) • ν) K = (c • ν) K := by rw [← h2, h]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  rw [hb, ← hbc, NNReal.sqrt_mul_self]

theorem scalH_scalH {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (a b : R) (S : HermR R σ n) :
    scalH R σ a (scalH R σ b S) = scalH R σ (a * b) S := by
  apply Subtype.ext
  simp only [scalH_coe, smul_smul, map_mul]

theorem scalH_one {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : scalH R σ 1 S = S := by
  apply Subtype.ext
  simp only [scalH_coe, map_one, one_smul]

def scalEquiv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (n : ℕ) (l : F) (hl : l ≠ 0) : HermR R σ n ≃ₜ+ HermR R σ n :=
  have hc : ∀ a : R, Continuous (scalH R σ (n := n) a) := fun a => by
    obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
    haveI := iTR
    exact Continuous.subtype_mk ((continuous_const_smul _).comp continuous_subtype_val) _
  have hm : algebraMap F R l * algebraMap F R l⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hl, map_one]
  { toFun := scalH R σ (algebraMap F R l)
    invFun := scalH R σ (algebraMap F R l⁻¹)
    left_inv := fun S => by rw [scalH_scalH, mul_comm, hm, scalH_one]
    right_inv := fun S => by rw [scalH_scalH, hm, scalH_one]
    map_add' := fun S T => by
      apply Subtype.ext
      simp [scalH_coe]
    continuous_toFun := hc _
    continuous_invFun := hc _ }

def oneByOne {F E : Type} [Field F] [Field E] [Algebra F E] (l : F) : Matrix (Fin 1) (Fin 1) E :=
  Matrix.of fun _ _ => algebraMap F E l

theorem action_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (l : F) (S : HermR R σ 1) :
    ((scalH R σ (algebraMap F R l) (scalH R σ (algebraMap F R l) S) : HermR R σ 1) :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R) := by
  have h1 : inclR R (algebraMap F E l) = algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l
  have h2 : sigR R σ (algebraMap R (R ⊗[F] E) (algebraMap F R l)) =
      algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  ext i j
  simp only [scalH_coe, cT, oneByOne, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul, h1, h2]
  have hi : i = default := Subsingleton.elim _ _
  have hj : j = default := Subsingleton.elim _ _
  subst hi hj
  ring

theorem local_scal {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (l : F) (hl : l ≠ 0) (c : ℝ≥0)
    (ν : Measure (HermR R σ 1)) (hν : ν.IsAddHaarMeasure)
    (h : ∀ τ : HermR R σ 1 → HermR R σ 1, (∀ S, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) → ν.map τ = c • ν) :
    ν.map (scalH R σ (algebraMap F R l)) = NNReal.sqrt c • ν := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := iTR
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R 1
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact map_eq_sqrt_smul (scalEquiv σ hcm R 1 l hl) ν c (h _ (action_eq R σ l))

theorem scal_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  intro F E _ _ _ _ _ σ hcm l hl
  have hdet : (oneByOne l : Matrix (Fin 1) (Fin 1) E).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    exact (map_ne_zero (algebraMap F E)).2 hl
  obtain ⟨ci, c, hu, hi, hv⟩ := GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm 1 (oneByOne l) hdet
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  refine ⟨NNReal.sqrt ci, fun v => NNReal.sqrt (c v), (PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ci ci c c hu hu).2.2.2.2.2.1, ?_, ?_⟩
  · intro ν hν
    exact local_scal σ hcm (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1) l hl ci ν hν (hi ν hν)
  · intro v ν hν
    exact local_scal σ hcm (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) l hl (c v) ν hν (hv v ν hν)

end GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

end
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_scaling_hermitian_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

theorem JR_sim {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (γ : GL (Fin M) E) (l : F)
    (hγ : cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J) :
    cT (sigR R σ) ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) (algebraMap F R l)) • JR R J := by
  rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj, hγ]
  ext i j
  change inclR R (algebraMap F E l * J i j) = algebraMap R (R ⊗[F] E) (algebraMap F R l) * inclR R (J i j)
  rw [map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l

theorem simil : PositivityTheory.Rg.Mass.Simil := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ _ hli hlam hμ h𝓕 hmi hm β β' hβ hβ' hs hs' c hc
  have hl0 : β' / β ≠ 0 := div_ne_zero hβ' hβ
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.similitude_between_nonempty_spheres F E σ hcm J hJ β β' hβ hβ' hs hs'
  obtain ⟨μ', 𝓕', hμ', h𝓕', hth⟩ := GlobalTheory.T.theta_measure_similitude F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 γ (β' / β) hl0 hγ
  have hT : (fun _ _ => algebraMap F E β' : Matrix (Fin 1) (Fin 1) E) =
      (algebraMap F E (β' / β)) • (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) := by
    funext a b'
    change algebraMap F E β' = algebraMap F E (β' / β) * algebraMap F E β
    rw [← map_mul, div_mul_cancel₀ _ hβ]
  have hth1 := hth 1 _ _ hT
  have hind := GlobalTheory.T.theta_measure_independent_choices F E σ hcm 2 J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕' 1 (fun _ _ => algebraMap F E β)
  change (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)).map _ = thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β') at hth1
  change thetaMeas σ J μ 𝓕 (PositivityTheory.Rg.Mass.sph σ J β) = thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β) at hind
  obtain ⟨ai, a, hau, hai, hav⟩ := GlobalTheory.T.haar_modulus_gl_action_product_formula F E σ hcm 1 2 γ
  obtain ⟨ci, cv, hcu, hci, hcv⟩ := GlobalTheory.T.similitude_scaling_hermitian_measure F E σ hcm (β' / β) hl0
  obtain ⟨-, -, -, -, hq, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ai ci a cv hau hcu
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := SWIsom.haar_of_loc σ hcm (Ainf F) hLi b li hli.1 1 2
  have hWv := fun v => SWIsom.haar_of_loc σ hcm (Fv F v) (hLv v) b (lam v) (hlam v).1 1 2
  have hJR : ∀ (R : Type) [CommRing R] [Algebra F R],
      cT (sigR R σ) ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) * JR R J *
        ((bc (inclR R) γ : GL (Fin 2) (R ⊗[F] E)) : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)) =
        (algebraMap R (R ⊗[F] E) (algebraMap F R (β' / β))) • JR R J := fun R _ _ => JR_sim R σ J γ _ hγ
  have hunit : ∀ (R : Type) [CommRing R] [Algebra F R] [Nontrivial R], IsUnit (algebraMap F R (β' / β)) :=
    fun R _ _ _ => (IsUnit.mk0 _ hl0).map _
  have sInf := GlobalTheory.T.gram_fibre_measure_local F E σ hcm 2 J hJ (Ainf F) hLi 1 _ _ mi hWi.1 hWi.2 hmi _ _ (hunit _) (hJR _) ai ci
    (hai _ hWi.1) (hci _ hWi.2)
  have sV := fun v => GlobalTheory.T.gram_fibre_measure_local F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v) _ _ (hunit _)
    (hJR _) (a v) (cv v) (hav v _ (hWv v).1) (hcv v _ (hWv v).2)
  have hS : ∀ (R : Type) [CommRing R] [Algebra F R], scalH R σ (algebraMap F R (β' / β))
      (hermScal R σ (algebraMap F R β)) = hermScal R σ (algebraMap F R β') := fun R _ _ => by
    rw [scalH_hermScal, ← map_mul, div_mul_cancel₀ _ hβ]
  have hproj : ∀ X : Fin 1 → Fin 2 → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) γ) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) γ) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) γ) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact SWIsom.map_actTup (fstA F) γ X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) γ) X) =
          actTup (Af F) (bc (inclR (Af F)) γ) (projFin X) := by
        funext a i
        exact SWIsom.map_actTup (sndA F) γ X a i
      rw [h1]
      funext a i
      exact SWIsom.map_actTup (evalV F v) γ (projFin X) a i
  have hfin : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β')) (latV b v) < ⊤ := by
    intro v
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermScal (Fv F v) σ (algebraMap F _ β'))).1
    exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v).1.measure_lt_top
  have key := euler_move_c F E σ hcm d b 1 2 (thetaMeas σ J μ' 𝓕' (PositivityTheory.Rg.Mass.sph σ J β)) (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β')))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β)))
    (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    (actTup (AF F) (bc (inclR (AF F)) γ))
    (actTup (Ainf F) (bc (inclR (Ainf F)) γ)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) γ))
    (SWIsom.measurable_actTup σ hcm (AF F) _) (SWIsom.measurable_of_loc σ hcm (Ainf F) hLi _)
    (fun v => SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hcm d b 1 2).2.1 γ) (ai / ci) (fun v => a v / cv v) hq
    (by rw [sInf, hS]) (fun v => by rw [sV v, hS]) hfin c
  unfold PositivityTheory.Rg.Mass.EP at hc ⊢
  rw [hind] at hc
  rw [← hth1]
  exact key hc

end GlobalTheory.CompanionTheory.SW.MassSimil

end
end
