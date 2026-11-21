import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexSpanAtRealPlaceAutPointLatticeProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubquotientCoveringRadiusRealPlaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPointStatement

section
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.NilLift

theorem exists_projector {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ P : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤)
    (hsat : ∀ c : O, c ≠ 0 → ∀ v ∈ Λ, c • v ∈ P → v ∈ P) :
    ∃ g : V →ₗ[K] V, (∀ z ∈ Λ, g z ∈ P) ∧ ∀ z ∈ Λ, z ∈ P → g z = z := by
  have hu : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) x) := fun s => by
    have := isLocalizedModule_id (nonZeroDivisors O) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := hu
      surj := fun y => by
        have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
        obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
        rw [Submodule.span_eq] at hs
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := P.comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c (nonZeroDivisors.coe_ne_zero c) v v.2 h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  let g : V →ₗ[K] V := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hu)
  have hg : ∀ y : Λ, g y = π y := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hu y
  refine ⟨g, fun z hz => ?_, fun z hz hP => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact hπ _
  · rw [hg ⟨z, hz⟩, hπ' ⟨z, hz⟩ hP]

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

local notation "𝒽" => Formalism.UG.hform (starRingEnd E) J

theorem form_eq (x y : Fin n → E) : 𝒽 x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply,
    starRingEnd_apply]

theorem form_star (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (x y : Fin n → E) :
    star (𝒽 x y) = 𝒽 y x := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => congrFun (congrFun hJ j) i
  simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_adj (hJ : J.det ≠ 0) (Ψ : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    𝒽 x ((J⁻¹ * Ψᴴ * J) *ᵥ y) = 𝒽 (Ψ *ᵥ x) y := by
  rw [form_eq, form_eq, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), Matrix.one_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem eq_zero_of_form (hJ : J.det ≠ 0) (y : Fin n → E) (h : ∀ x, 𝒽 x y = 0) : y = 0 := by
  have h1 : J *ᵥ y = 0 := by
    funext i
    have := h (Pi.single i 1)
    rw [form_eq] at this
    simpa [Pi.star_single] using this
  exact Matrix.eq_zero_of_mulVec_eq_zero hJ h1

theorem form_span_left (S : Set (Fin n → E)) (y : Fin n → E) (h : ∀ s ∈ S, 𝒽 s y = 0)
    (w : Fin n → E) (hw : w ∈ Submodule.span E S) : 𝒽 w y = 0 := by
  simp only [form_eq] at h ⊢
  induction hw using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => simp
  | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]

theorem inNil_sub_adj (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (hdet : J.det ≠ 0)
    (W : Submodule E (Fin n → E)) (hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd E) J W)
    (Ψ : Matrix (Fin n) (Fin n) E) (h1 : ∀ u, Ψ *ᵥ u ∈ W) (h2 : ∀ u ∈ W, Ψ *ᵥ u = 0) :
    InNil (starRingEnd E) J W (Ψ - J⁻¹ * Ψᴴ * J) ∧
      ∀ u ∈ perpSet (starRingEnd E) J W, (J⁻¹ * Ψᴴ * J) *ᵥ u = 0 := by
  have hA : ∀ u ∈ perpSet (starRingEnd E) J W, (J⁻¹ * Ψᴴ * J) *ᵥ u = 0 := fun u hu =>
    eq_zero_of_form J hdet _ fun v => by rw [form_adj J hdet]; exact hu _ (h1 v)
  have hsr : ∀ a b c : Fin n → E, 𝒽 a (b - c) = 𝒽 a b - 𝒽 a c := fun a b c => by
    simp only [form_eq, Matrix.mulVec_sub, dotProduct_sub]
  have hsl : ∀ a b c : Fin n → E, 𝒽 (b - c) a = 𝒽 b a - 𝒽 c a := fun a b c => by
    simp only [form_eq, star_sub, sub_dotProduct]
  refine ⟨⟨fun u u' => ?_, fun u w hw => ?_, fun u hu => ?_, fun u hu => ?_⟩, hA⟩
  · rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hsr, hsl, form_adj J hdet,
      ← form_star J hJ u' ((J⁻¹ * Ψᴴ * J) *ᵥ u), form_adj J hdet, form_star J hJ]
    ring
  · rw [Matrix.sub_mulVec, hsr, form_adj J hdet, h2 w hw, hW _ (h1 u) w hw, form_eq]
    simp
  · rw [Matrix.sub_mulVec, hA u hu, sub_zero]
    exact h1 u
  · rw [Matrix.sub_mulVec, hA u (hW u hu), sub_zero]
    exact h2 u hu

end Form

theorem mem_perpIn_iff (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => by simp [form_eq]⟩
  | add y z _ _ hy hz =>
    exact ⟨add_mem hy.1 hz.1, fun s hs => by
      rw [form_eq, Matrix.mulVec_add, dotProduct_add, ← form_eq, ← form_eq, hy.2 s hs, hz.2 s hs, add_zero]⟩
  | smul c y _ hy =>
    exact ⟨Submodule.smul_mem _ _ hy.1, fun s hs => by
      rw [form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq, hy.2 s hs, smul_zero]⟩

theorem exists_nilInt_lift : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  intro I x R hR Φ hΦ0 hΦ
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨g, hg, hg'⟩ := exists_projector (lamX I x) (perpIn I x R) hfg hspan (fun c hc v hv h => by
    refine (mem_perpIn_iff I x R v).2 ⟨hv, fun s hs => ?_⟩
    have h1 := ((mem_perpIn_iff I x R _).1 h).2 s hs
    rw [form_eq, Matrix.mulVec_smul, dotProduct_smul, ← form_eq] at h1
    exact (smul_eq_zero.1 h1).resolve_left hc)
  set W := Submodule.span I.E (R : Set (Fin I.n → I.E)) with hWdef
  let Ψ : Matrix (Fin I.n) (Fin I.n) I.E := Φ * LinearMap.toMatrix' g
  have hΨ : ∀ u, Ψ *ᵥ u = Φ *ᵥ g u := fun u => by
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  have hPΛ : ∀ y ∈ perpIn I x R, y ∈ lamX I x := fun y hy => ((mem_perpIn_iff I x R y).1 hy).1
  have hΨP : ∀ y ∈ perpIn I x R, Ψ *ᵥ y = Φ *ᵥ y := fun y hy => by rw [hΨ, hg' y (hPΛ y hy) hy]
  have hΨΛ : ∀ y ∈ lamX I x, Ψ *ᵥ y ∈ R := fun y hy => by rw [hΨ]; exact hΦ _ (hg y hy)
  have hP : ∀ y ∈ perpIn I x R, y ∈ perpSet (starRingEnd I.E) I.J W := fun y hy =>
    form_span_left I.J _ y ((mem_perpIn_iff I x R y).1 hy).2
  have hW : ∀ w ∈ W, w ∈ perpSet (starRingEnd I.E) I.J W := fun w hw w' hw' => by
    rw [← form_star I.J I.J_herm, form_span_left I.J _ w' (fun s hs => ?_) w hw, star_zero]
    rw [← form_star I.J I.J_herm, hP s (hR hs) w' hw', star_zero]
  have h1 : ∀ u, Ψ *ᵥ u ∈ W := fun u => by
    have : Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) ≤ W.comap (Matrix.mulVecLin Ψ) :=
      Submodule.span_le.2 fun y hy => Submodule.subset_span (hΨΛ y hy)
    exact this (hspan ▸ Submodule.mem_top)
  have h2 : ∀ u ∈ W, Ψ *ᵥ u = 0 := fun u hu => by
    have : W ≤ LinearMap.ker (Matrix.mulVecLin Ψ) :=
      Submodule.span_le.2 fun y hy => (hΨP y (hR hy)).trans (hΦ0 y hy)
    exact this hu
  obtain ⟨hN, hA⟩ := inNil_sub_adj I.J I.J_herm I.J_det W hW Ψ h1 h2
  refine ⟨_, ⟨hN, fun u hu => ?_⟩, fun y hy => ?_⟩
  · rw [Matrix.sub_mulVec]
    refine sub_mem (hPΛ _ (hR (hΨΛ u hu))) ((hdual _).2 fun z hz => ?_)
    rw [form_adj I.J I.J_det]
    exact (hdual u).1 hu _ (hPΛ _ (hR (hΨΛ z hz)))
  · rw [Matrix.sub_mulVec, hA y (hP y hy), sub_zero, hΨP y hy]

end GlobalTheory.NilLift
end
end

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  atlas_forward_decl GlobalTheory.NilLift.exists_nilInt_lift
end

section
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.NilLift

variable {n : ℕ}

theorem hs_eq_trace (M : Matrix (Fin n) (Fin n) ℂ) : hs M = (trace (Mᴴ * M)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem hs_nonneg' (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs M := by
  simp only [Formalism.REAL.hs]
  positivity

theorem exists_proj (W : Submodule ℂ (Fin n → ℂ)) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, Pᴴ = P ∧ (∀ u, P *ᵥ u ∈ W) ∧ ∀ u ∈ W, P *ᵥ u = u := by
  classical
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
    W.comap (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  let T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := K.starProjection
  have hT : ∀ u, (Matrix.toEuclideanLin.symm T) *ᵥ u = WithLp.ofLp (T (WithLp.toLp 2 u)) := by
    intro u
    have h := congrArg (fun f : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) =>
      WithLp.ofLp (f (WithLp.toLp 2 u))) (LinearEquiv.apply_symm_apply Matrix.toEuclideanLin T)
    exact h
  refine ⟨Matrix.toEuclideanLin.symm T, ?_, ?_, ?_⟩
  · have hH : (Matrix.toEuclideanLin.symm T).IsHermitian := by
      rw [← Matrix.isSymmetric_toEuclideanLin_iff, LinearEquiv.apply_symm_apply]
      exact K.starProjection_isSymmetric
    exact hH
  · intro u
    rw [hT]
    have hm : T (WithLp.toLp 2 u) ∈ K := K.starProjection_apply_mem _
    exact hm
  · intro u hu
    rw [hT]
    have hm : WithLp.toLp 2 u ∈ K := hu
    have h2 : T (WithLp.toLp 2 u) = WithLp.toLp 2 u := K.starProjection_eq_self_iff.mpr hm
    rw [h2]

theorem hs_mul_le (D Q : Matrix (Fin n) (Fin n) ℂ) (h1 : Qᴴ = Q) (h2 : Q * Q = Q) :
    hs (D * (1 - Q)) ≤ hs D := by
  have hR : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, h2, sub_self, sub_zero]
  have hDQ : hs (D * Q) = (trace (D * Q * Dᴴ)).re := by
    rw [hs_eq_trace, Matrix.trace_mul_comm, Matrix.conjTranspose_mul, h1, mul_assoc,
      ← mul_assoc Q Q, h2, ← mul_assoc]
  have hDR : hs (D * (1 - Q)) = (trace (D * Dᴴ)).re - (trace (D * Q * Dᴴ)).re := by
    rw [hs_eq_trace, Matrix.trace_mul_comm, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, h1, mul_assoc, ← mul_assoc (1 - Q) (1 - Q), hR, ← mul_assoc,
      mul_sub, mul_one, sub_mul, Matrix.trace_sub, Complex.sub_re]
  have hD : hs D = (trace (D * Dᴴ)).re := by rw [hs_eq_trace, Matrix.trace_mul_comm]
  have h0 := hs_nonneg' (D * Q)
  linarith

theorem core (J P D : Matrix (Fin n) (Fin n) ℂ) (j1 : J * J = 1) (j2 : Jᴴ = J) (p1 : Pᴴ = P)
    (p2 : P * P = P) (p3 : P * J * P = 0) (d1 : D * P = 0)
    (d2 : P * (D * (1 - J * P * J)) = D * (1 - J * P * J)) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, Aᴴ * J + J * A = 0 ∧ P * J * A = 0 ∧
      (∀ u, (P * J) *ᵥ u = 0 → A *ᵥ u = D *ᵥ u) ∧ hs A ≤ 2 * hs D := by
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, J * (J * X) = X := fun X => by
    rw [← mul_assoc, j1, one_mul]
  have hPP : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (P * X) = P * X := fun X => by
    rw [← mul_assoc, p2]
  have hPJP : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (J * (P * X)) = 0 := fun X => by
    rw [← mul_assoc, ← mul_assoc, p3, zero_mul]
  have hPDh : P * Dᴴ = 0 := by
    have h := congrArg conjTranspose d1
    rwa [conjTranspose_mul, p1, conjTranspose_zero] at h
  obtain ⟨B, hB⟩ : ∃ B, B = D * (1 - J * P * J) := ⟨_, rfl⟩
  rw [← hB] at d2
  have hBJP : B * (J * P) = 0 := by
    rw [hB]
    simp only [mul_assoc, sub_mul, mul_sub, one_mul, mul_one, hJJ, p2, hPP, sub_self, mul_zero]
  have hBJB : B * (J * B) = 0 := by
    calc B * (J * B) = B * (J * (P * B)) := by rw [d2]
      _ = B * (J * P) * B := by simp only [mul_assoc]
      _ = 0 := by rw [hBJP, zero_mul]
  have hBhP : Bᴴ * P = Bᴴ := by
    have h := congrArg conjTranspose d2
    rwa [conjTranspose_mul, p1] at h
  have hPBh : P * Bᴴ = 0 := by
    rw [hB]
    simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, j2, p1, mul_sub, sub_mul,
      one_mul, mul_one, mul_assoc, hPJP, hPDh, sub_zero, sub_self]
  have hPBhX : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (Bᴴ * X) = 0 := fun X => by
    rw [← mul_assoc, hPBh, zero_mul]
  have hPJB : P * (J * B) = 0 := by
    calc P * (J * B) = P * (J * (P * B)) := by rw [d2]
      _ = 0 := hPJP B
  have hBhJBh : ∀ X : Matrix (Fin n) (Fin n) ℂ, Bᴴ * (J * (Bᴴ * X)) = 0 := by
    intro X
    have h := congrArg conjTranspose hBJB
    rw [conjTranspose_mul, conjTranspose_mul, j2, conjTranspose_zero] at h
    rw [← mul_assoc, ← mul_assoc, h, zero_mul]
  refine ⟨B - J * Bᴴ * J, ?_, ?_, ?_, ?_⟩
  · simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, j2, sub_mul,
      mul_sub, mul_assoc, j1, hJJ, mul_one]
    abel
  · simp only [mul_sub, mul_assoc, hJJ, hPJB, hPBhX, sub_self]
  · intro u hu
    have e1 : J * Bᴴ * J = J * Bᴴ * (P * J) := by
      conv_lhs => rw [← hBhP]
      simp only [mul_assoc]
    have e2 : B = D - D * J * (P * J) := by
      rw [hB, mul_sub, mul_one]
      simp only [mul_assoc]
    have hA : B - J * Bᴴ * J = D - (D * J + J * Bᴴ) * (P * J) := by
      rw [e1, add_mul, ← sub_sub, ← e2]
    rw [hA, sub_mulVec, ← mulVec_mulVec, hu, mulVec_zero, sub_zero]
  · have hK1 : (J * P * J)ᴴ = J * P * J := by
      simp only [conjTranspose_mul, j2, p1, mul_assoc]
    have hK2 : J * P * J * (J * P * J) = J * P * J := by
      simp only [mul_assoc, hJJ, hPP]
    have hsB : hs B ≤ hs D := by
      rw [hB]
      exact hs_mul_le D (J * P * J) hK1 hK2
    have hM : (B - J * Bᴴ * J)ᴴ * (B - J * Bᴴ * J) = Bᴴ * B + J * (B * (Bᴴ * J)) := by
      simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, j2, sub_mul,
        mul_sub, mul_assoc, hJJ, hBJB, hBhJBh, mul_zero, sub_zero, zero_sub, sub_neg_eq_add]
    have t1 : trace (J * (B * (Bᴴ * J))) = trace (Bᴴ * B) := by
      rw [Matrix.trace_mul_comm, mul_assoc, mul_assoc, j1, mul_one, Matrix.trace_mul_comm]
    have hsA : hs (B - J * Bᴴ * J) = 2 * hs B := by
      rw [hs_eq_trace, hs_eq_trace, hM, Matrix.trace_add, t1, Complex.add_re]
      ring
    rw [hsA]
    linarith

theorem hform_eq (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) H x y = star x ⬝ᵥ (H *ᵥ y) := by
  unfold Formalism.UG.hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, mul_assoc]

theorem hform_mulVec (H X Y : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) H (X *ᵥ x) (Y *ᵥ y) = star x ⬝ᵥ ((Xᴴ * H * Y) *ᵥ y) := by
  rw [hform_eq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem ext_mulVec' {X Y : Matrix (Fin n) (Fin n) ℂ} (h : ∀ u, X *ᵥ u = Y *ᵥ u) : X = Y := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using h1

private theorem jm_sq_lemma (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem jm_herm_lemma_2 (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem exists_lift : ∀ (n : ℕ) (ε : Fin n → Bool) (H G D : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)), IsUnit G.det → Gᴴ * H * G = Jm ε → (∀ u ∈ W, u ∈ perpSet (starRingEnd ℂ) H W) → (∀ u ∈ W, D *ᵥ u = 0) → (∀ u ∈ perpSet (starRingEnd ℂ) H W, D *ᵥ u ∈ W) → ∃ A : Matrix (Fin n) (Fin n) ℂ, InNil (starRingEnd ℂ) H W A ∧ (∀ u ∈ perpSet (starRingEnd ℂ) H W, A *ᵥ u = D *ᵥ u) ∧ hs (G⁻¹ * A * G) ≤ 2 * hs (G⁻¹ * D * G) := by
  intro n ε H G D W hG hJ hiso hDW hDperp
  classical
  have j1 : Jm ε * Jm ε = 1 := jm_sq_lemma ε
  have j2 : (Jm ε)ᴴ = Jm ε := jm_herm_lemma_2 ε
  have hGi : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have hiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
  have hiGX : ∀ X : Matrix (Fin n) (Fin n) ℂ, G⁻¹ * (G * X) = X := fun X => by
    rw [← mul_assoc, hiG, one_mul]
  have hGu : ∀ u : Fin n → ℂ, G *ᵥ (G⁻¹ *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, hGi, one_mulVec]
  have hJJ : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← mul_assoc, j1, one_mul]
  obtain ⟨P, p1, hPW, hPfix⟩ := exists_proj (W.comap (Matrix.toLin' G))
  have hPW' : ∀ u, G *ᵥ (P *ᵥ u) ∈ W := fun u => by
    have h := hPW u
    rwa [Submodule.mem_comap, Matrix.toLin'_apply] at h
  have hPfix' : ∀ v, G *ᵥ v ∈ W → P *ᵥ v = v := fun v hv =>
    hPfix v (by rwa [Submodule.mem_comap, Matrix.toLin'_apply])
  have p2 : P * P = P := ext_mulVec' fun u => by
    rw [← mulVec_mulVec]
    exact hPfix' _ (hPW' u)
  have hPP : ∀ X : Matrix (Fin n) (Fin n) ℂ, P * (P * X) = P * X := fun X => by
    rw [← mul_assoc, p2]
  have hf : ∀ a b : Fin n → ℂ,
      Formalism.UG.hform (starRingEnd ℂ) H (G *ᵥ a) (G *ᵥ b) = star a ⬝ᵥ (Jm ε *ᵥ b) := fun a b => by
    rw [hform_mulVec, hJ]
  have hPs : ∀ a z : Fin n → ℂ, star (P *ᵥ a) ⬝ᵥ z = star a ⬝ᵥ (P *ᵥ z) := fun a z => by
    rw [star_mulVec, ← dotProduct_mulVec, p1]
  have hperp : ∀ v, G *ᵥ v ∈ perpSet (starRingEnd ℂ) H W ↔ (P * Jm ε) *ᵥ v = 0 := by
    intro v
    simp only [perpSet, Set.mem_setOf_eq]
    constructor
    · intro h
      apply dotProduct_star_self_eq_zero.mp
      rw [← mulVec_mulVec, ← hPs, ← hf]
      exact h _ (hPW' _)
    · intro h w hw
      rw [← hGu w, hf, ← hPfix' (G⁻¹ *ᵥ w) (by rw [hGu]; exact hw), hPs, mulVec_mulVec, h,
        dotProduct_zero]
  have p3 : P * Jm ε * P = 0 := ext_mulVec' fun u => by
    rw [zero_mulVec, ← mulVec_mulVec]
    exact (hperp _).mp (hiso _ (hPW' u))
  have hDv : ∀ v, (G⁻¹ * D * G) *ᵥ v = G⁻¹ *ᵥ (D *ᵥ (G *ᵥ v)) := fun v => by
    simp only [← mulVec_mulVec]
  have d1 : G⁻¹ * D * G * P = 0 := ext_mulVec' fun u => by
    rw [zero_mulVec, ← mulVec_mulVec, hDv, hDW _ (hPW' u), mulVec_zero]
  have d2 : P * (G⁻¹ * D * G * (1 - Jm ε * P * Jm ε)) = G⁻¹ * D * G * (1 - Jm ε * P * Jm ε) :=
    ext_mulVec' fun u => by
      have hz : (P * Jm ε) *ᵥ ((1 - Jm ε * P * Jm ε) *ᵥ u) = 0 := by
        rw [mulVec_mulVec, mul_sub, mul_one]
        simp only [mul_assoc, hJJ, hPP, sub_self, zero_mulVec]
      have hm : G *ᵥ ((G⁻¹ * D * G) *ᵥ ((1 - Jm ε * P * Jm ε) *ᵥ u)) ∈ W := by
        rw [hDv, hGu]
        exact hDperp _ ((hperp _).mpr hz)
      rw [← mulVec_mulVec _ P, ← mulVec_mulVec _ (G⁻¹ * D * G)]
      exact hPfix' _ hm
  obtain ⟨A', hA1, hA2, hA3, hA4⟩ := core (Jm ε) P (G⁻¹ * D * G) j1 j2 p1 p2 p3 d1 d2
  have hAv : ∀ v, (G * A' * G⁻¹) *ᵥ (G *ᵥ v) = G *ᵥ (A' *ᵥ v) := fun v => by
    simp only [mulVec_mulVec, mul_assoc, hiG, mul_one]
  have hagree : ∀ u ∈ perpSet (starRingEnd ℂ) H W, (G * A' * G⁻¹) *ᵥ u = D *ᵥ u := by
    intro u hu
    obtain ⟨v, rfl⟩ : ∃ v, u = G *ᵥ v := ⟨G⁻¹ *ᵥ u, (hGu u).symm⟩
    rw [hAv, hA3 v ((hperp v).mp hu), hDv, hGu]
  refine ⟨G * A' * G⁻¹, ?_, hagree, ?_⟩
  · unfold InNil IsSkew
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u u'
      obtain ⟨v, rfl⟩ : ∃ v, u = G *ᵥ v := ⟨G⁻¹ *ᵥ u, (hGu u).symm⟩
      obtain ⟨v', rfl⟩ : ∃ v', u' = G *ᵥ v' := ⟨G⁻¹ *ᵥ u', (hGu u').symm⟩
      rw [hAv, hAv, hf, hf, star_mulVec, ← dotProduct_mulVec, ← dotProduct_add, mulVec_mulVec,
        mulVec_mulVec, ← add_mulVec, hA1, zero_mulVec, dotProduct_zero]
    · intro u
      obtain ⟨v, rfl⟩ : ∃ v, u = G *ᵥ v := ⟨G⁻¹ *ᵥ u, (hGu u).symm⟩
      rw [hAv, hperp, mulVec_mulVec, hA2, zero_mulVec]
    · intro u hu
      rw [hagree u hu]
      exact hDperp u hu
    · intro u hu
      rw [hagree u (hiso u hu)]
      exact hDW u hu
  · have hc : G⁻¹ * (G * A' * G⁻¹) * G = A' := by
      simp only [mul_assoc, hiG, mul_one, hiGX]
    rw [hc]
    exact hA4

end GlobalTheory.NilLift
end
end

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stabilizerNilradical_lift_of_isotropic : ∀ (n : ℕ) (ε : Fin n → Bool) (H G D : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)), IsUnit G.det → Gᴴ * H * G = Jm ε → (∀ u ∈ W, u ∈ perpSet (starRingEnd ℂ) H W) → (∀ u ∈ W, D *ᵥ u = 0) → (∀ u ∈ perpSet (starRingEnd ℂ) H W, D *ᵥ u ∈ W) → ∃ A : Matrix (Fin n) (Fin n) ℂ, InNil (starRingEnd ℂ) H W A ∧ (∀ u ∈ perpSet (starRingEnd ℂ) H W, A *ᵥ u = D *ᵥ u) ∧ hs (G⁻¹ * A * G) ≤ 2 * hs (G⁻¹ * D * G) := by
  atlas_forward_decl GlobalTheory.NilLift.exists_lift
end

section
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.Count.FirstLayer

theorem inNil_sub {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (W : Submodule A (Fin n → A)) (Y Y' : Matrix (Fin n) (Fin n) A)
    (h : InNil s J W Y) (h' : InNil s J W Y') : InNil s J W (Y - Y') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  have l1 : ∀ a b c : Fin n → A, Formalism.UG.hform s J (a - b) c = Formalism.UG.hform s J a c - Formalism.UG.hform s J b c := by
    intro a b c
    simp [Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]
  have l2 : ∀ a b c : Fin n → A, Formalism.UG.hform s J c (a - b) = Formalism.UG.hform s J c a - Formalism.UG.hform s J c b := by
    intro a b c
    simp [Formalism.UG.hform, mul_sub, Finset.sum_sub_distrib]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u u'
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, l1, l2]
    have a := h1 u u'
    have b := g1 u u'
    linear_combination a - b
  · intro u w hw
    rw [Matrix.sub_mulVec, l2, h2 u w hw, g2 u w hw, sub_zero]
  · intro u hu
    rw [Matrix.sub_mulVec]
    exact W.sub_mem (h3 u hu) (g3 u hu)
  · intro u hu
    rw [Matrix.sub_mulVec, h4 u hu, g4 u hu, sub_zero]

theorem map_mulVec_emb (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) I.E)
    (y : Fin I.n → I.E) :
    M.map (I.φ v) *ᵥ (fun i => I.φ v (y i)) = fun i => I.φ v ((M *ᵥ y) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem mem_spanAt (I : AutInst) (v : InfinitePlace I.F) (R : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (y : Fin I.n → I.E) (hy : y ∈ R) : (fun i => I.φ v (y i)) ∈ spanAt I R v :=
  Submodule.subset_span ⟨y, hy, rfl⟩

theorem mulVec_mem_of_span (I : AutInst) (v : InfinitePlace I.F) (A : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (M : Matrix (Fin I.n) (Fin I.n) ℂ) (W : Submodule ℂ (Fin I.n → ℂ))
    (h : ∀ y ∈ A, M *ᵥ (fun i => I.φ v (y i)) ∈ W) : ∀ u ∈ spanAt I A v, M *ᵥ u ∈ W := by
  have : spanAt I A v ≤ W.comap (Matrix.mulVecLin M) := by
    unfold spanAt
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  intro u hu
  exact this hu

theorem frame_inv (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) ℂ) :
    uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * M * I.P v * uMat (x.1 v) =
      (I.P v * uMat (x.1 v))⁻¹ * M * (I.P v * uMat (x.1 v)) := by
  rw [Matrix.mul_inv_rev]
  have : uMat (x.1 v)⁻¹ = (uMat (x.1 v))⁻¹ := by
    simp only [uMat, Subgroup.coe_inv, Matrix.coe_units_inv]
  rw [this]
  simp only [Matrix.mul_assoc]

theorem frame_det (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    IsUnit (I.P v * uMat (x.1 v)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact (I.P_unit v).mul (Units.isUnit _)

theorem frame_spec (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    (I.P v * uMat (x.1 v))ᴴ * I.J.map (I.φ v) * (I.P v * uMat (x.1 v)) = Jm (I.ε v) := by
  have h : (uMat (x.1 v))ᴴ * Jm (I.ε v) * uMat (x.1 v) = Jm (I.ε v) := (x.1 v).2
  rw [← h, ← I.P_spec v, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem arith (n f k j rd lo hi rho : ℝ) (hf : 0 < f) (hrd : 0 ≤ rd) (hkj : k + j = n) (hlo : 0 < lo)
    (hhi : 0 < hi) (hr : hi ≤ rho * lo) :
    Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) ≤
      (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) := by
  have h1 : (k - j) * j ≤ n ^ 2 / 8 := by
    rw [← hkj]; nlinarith [sq_nonneg (k - 3 * j)]
  have h2 : hi / lo ≤ rho := by rwa [div_le_iff₀ hlo]
  have h3 : 0 < hi / lo := div_pos hhi hlo
  have hs : 0 < Real.sqrt (2 * f) := Real.sqrt_pos.2 (by linarith)
  have e : Real.sqrt 2 * Real.sqrt f = Real.sqrt (2 * f) := (Real.sqrt_mul (by norm_num) f).symm
  have e2 : Real.sqrt (2 * f) * Real.sqrt (2 * f) = 2 * f := Real.mul_self_sqrt (by linarith)
  have e3 : (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) =
      n ^ 2 / 8 * rho * (Real.sqrt (2 * f) * rd / 2) := by
    rw [div_eq_iff hs.ne']
    linear_combination (-(n ^ 2 / 8 * rho * rd / 2)) * e2
  have e4 : Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) =
      (k - j) * j * (hi / lo) * (Real.sqrt (2 * f) * rd / 2) := by
    rw [← e]; field_simp
  rw [e3, e4]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc (k - j) * j * (hi / lo) ≤ n ^ 2 / 8 * (hi / lo) := mul_le_mul_of_nonneg_right h1 h3.le
    _ ≤ n ^ 2 / 8 * rho := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem main : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → 0 < lo → hi ≤ rho * lo → ∀ Y ∈ nilReal I R, ∃ Y₀ ∈ nilInt I x R, ∃ Z ∈ cenReal I R, normAt I x (Y - diagEmb I Y₀ - Z) ≤ ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * rho / Real.sqrt (2 * I.f) := by
  intro I x R lo hi rho hsat hiso hhi hlarge hlow hlo hr Y hY
  have hpl : perpIn I x R ≤ lamX I x := by
    unfold perpIn
    rw [Submodule.span_le]
    exact fun y hy => hy.1
  have hfg : (lamX I x).FG := (GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x).2.1
  have hsat' : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) R := by
    refine ⟨hiso, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hiso hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩ hz
      exact hsat.2.2 _ ⟨y, hpl hy, rfl⟩ hz
  obtain ⟨-, -, hperp, hnil, -⟩ := GlobalTheory.T.complexSpanAtRealPlace_autPointLattice_properties I x R
  have hP : ∀ v u, u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ↔
      u ∈ spanAt I (perpIn I x R) v := by
    intro v u
    rw [← hperp v]; rfl
  have hmono : ∀ v, spanAt I R v ≤ spanAt I (perpIn I x R) v := fun v =>
    Submodule.span_mono (Set.image_mono hiso)
  obtain ⟨Φ, hΦ0, hΦ1, D, hD, hDn⟩ := GlobalTheory.T.subquotient_covering_radius_real_places I x (perpIn I x R) R R lo hi (hfg.of_le hpl) hsat'
    (hfg.of_le hsat.1) hlo hhi (fun N h1 h2 => hlow N h1 (h2.trans hpl)) hlarge Y
    (fun v y hy => (hY v).2.2.2 _ (mem_spanAt I v R y hy))
    (fun v y hy => (hY v).2.2.1 _ ((hP v _).2 (mem_spanAt I v _ y hy)))
  obtain ⟨Y₀, hY₀, hY₀Φ⟩ := GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal I x R hiso Φ hΦ0 hΦ1
  have hA : ∀ v, ∃ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) A ∧
      (∀ u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v), A *ᵥ u = D v *ᵥ u) ∧
      hs ((I.P v * uMat (x.1 v))⁻¹ * A * (I.P v * uMat (x.1 v))) ≤
        2 * hs ((I.P v * uMat (x.1 v))⁻¹ * D v * (I.P v * uMat (x.1 v))) := by
    intro v
    refine GlobalTheory.T.exists_stabilizerNilradical_lift_of_isotropic I.n (I.ε v) _ _ (D v) _ (frame_det I x v) (frame_spec I x v)
      (fun u hu => (hP v u).2 (hmono v hu)) ?_ ?_
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
        refine mulVec_mem_of_span I v R _ ⊥ ?_ u hu
        intro y hy
        rw [map_mulVec_emb, hΦ0 y hy, Submodule.mem_bot]
        funext i; simp
      rw [hD v u (hmono v hu), Matrix.sub_mulVec, (hY v).2.2.2 u hu, (Submodule.mem_bot ℂ).1 h0, sub_zero]
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ spanAt I R v := by
        refine mulVec_mem_of_span I v _ _ _ ?_ u ((hP v u).1 hu)
        intro y hy
        rw [map_mulVec_emb]
        exact mem_spanAt I v R _ (hΦ1 y hy)
      rw [hD v u ((hP v u).1 hu), Matrix.sub_mulVec]
      exact Submodule.sub_mem _ ((hY v).2.2.1 u hu) h0
  choose A hA1 hA2 hA3 using hA
  refine ⟨Y₀, hY₀, Y - diagEmb I Y₀ - A, ?_, ?_⟩
  · intro v
    refine ⟨inNil_sub _ _ _ _ _ (inNil_sub _ _ _ _ _ (hY v) (hnil Y₀ hY₀.1 v)) (hA1 v), ?_⟩
    intro u hu
    have h0 : (Y₀.map (I.φ v) - Φ.map (I.φ v)) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
      refine mulVec_mem_of_span I v _ _ ⊥ ?_ u ((hP v u).1 hu)
      intro y hy
      rw [Matrix.sub_mulVec, map_mulVec_emb, map_mulVec_emb, hY₀Φ y hy, sub_self]
      exact Submodule.zero_mem _
    rw [Submodule.mem_bot, Matrix.sub_mulVec, sub_eq_zero] at h0
    show (Y v - Y₀.map (I.φ v) - A v) *ᵥ u = 0
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hA2 v u hu, hD v u ((hP v u).1 hu), Matrix.sub_mulVec, h0,
      sub_self]
  · rw [sub_sub_cancel]
    have hAD : normAt I x A ≤ Real.sqrt 2 * normAt I x D := by
      unfold normAt
      rw [← Real.sqrt_mul (by norm_num), Finset.mul_sum]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro v _
      rw [frame_inv, frame_inv]
      exact hA3 v
    have hrk : rkK (perpIn I x R) + rkK R = I.n :=
      ((GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x).2.2.2 R R hsat hsat le_rfl).2.1
    have hf : (0 : ℝ) < I.f := by
      have : 0 < I.f := Module.finrank_pos
      exact_mod_cast this
    have hrd : 0 ≤ I.rd := Real.rpow_nonneg (abs_nonneg _) _
    refine hAD.trans ((mul_le_mul_of_nonneg_left hDn (Real.sqrt_nonneg _)).trans ?_)
    exact arith _ _ _ _ _ _ _ _ hf hrd (by exact_mod_cast hrk) hlo hhi hr

end GlobalTheory.Count.FirstLayer
end
end

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_first_layer_covering_radius_le : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → 0 < lo → hi ≤ rho * lo → ∀ Y ∈ nilReal I R, ∃ Y₀ ∈ nilInt I x R, ∃ Z ∈ cenReal I R, normAt I x (Y - diagEmb I Y₀ - Z) ≤ ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * rho / Real.sqrt (2 * I.f) := by
  atlas_forward_decl GlobalTheory.Count.FirstLayer.main
end
