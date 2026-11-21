import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralScalarEqWhittakerScalar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasseNormGroupProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSupportProperty
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRepresentativesForAdmissibleData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNormOneUnitsTrivialValuation
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionDiagonal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilActionUnitRotation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaGlobalCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFormulaModulusRational
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormEqualsComplexAbsSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIntegralUnitShift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnitTranslateValuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaZeroTermUnipotentInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierCoefficientHasSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationVectorHomomorphism
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousTwistedLocalThetaInTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoefficientMeasurableBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLocalThetaBoundedIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaValueIndicator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComponentRationalIdele
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormAtInertPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldCoefficientNormOneTwist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionDiagonal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionEquationGlobal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilActionDiagonal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaZeroTermNormInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductCharacterNormOneTrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharactersTrivialOfNonzeroAverage

section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2 lc)
open scoped NumberField.AdeleRing ValuativeRel
open Ad3.K.GL2LocalData

noncomputable section

namespace GlobalTheory.CompanionTheory.TwistZero

open GlobalTheory.CompanionTheory.SplitRep GlobalTheory.CompanionTheory.SplitPi

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem integral_scale_snd (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ u, G (u.1, s * u.2) ∂muS χ = (((modulus s : ℝ)⁻¹ : ℝ) : ℂ) * ∫ u, G u ∂muS χ := by
  have he1 : MeasurableEmbedding (fun x : F => s * x) := (Homeomorph.mulLeft₀ s hs).measurableEmbedding
  have hid : MeasurableEmbedding (id : F → F) := MeasurableEmbedding.id
  have he := hid.prodMap he1
  have hmap : Measure.map (Prod.map (id : F → F) (fun x : F => s * x)) (muS χ) =
      (modulus s)⁻¹ • muS χ := by
    rw [← Measure.map_prod_map _ _ measurable_id he1.measurable,
      map_mul_left_eq_smul _ hs, Measure.map_id, Measure.prod_smul_right]
  have h := he.integral_map (μ := muS χ) G
  rw [hmap, integral_smul_nnreal_measure] at h
  simp only [Prod.map, id] at h
  rw [← h, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring_nf

theorem integral_norm_one (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ y, G (y * (s, s⁻¹)) ∂muS χ = ∫ y, G y ∂muS χ := by
  have h1 := integral_scale_fst χ hs (fun y : F × F => G (y.1, s⁻¹ * y.2))
  have h2 := integral_scale_snd χ (inv_ne_zero hs) G
  have e : ∀ y : F × F, y * ((s, s⁻¹) : F × F) = (s * y.1, s⁻¹ * y.2) := fun y => by
    ext <;> simp [mul_comm]
  simp only [e]
  rw [h1, h2, ← mul_assoc]
  have hM : ((modulus s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hs
  rw [modulus_inv]
  push_cast
  field_simp

theorem rWS_zero_point (χ : AddChar F Circle) {m : Matrix (Fin 2) (Fin 2) F} (hm : m.det = 1) {s : F}
    (hs : s ≠ 0) (Ψ : F × F → ℂ) :
    rWS χ m (fun y => Ψ (y * (s, s⁻¹))) 0 = rWS χ m Ψ 0 := by
  by_cases hc : m 1 0 = 0
  · rw [rWS_zero χ hm hc, rWS_zero χ hm hc]
    simp
  · rw [rWS_ne χ hc, rWS_ne χ hc]
    congr 1
    have h := integral_norm_one χ hs (fun u : F × F =>
      (χ ((m 0 0 * ((0 : F × F).1 * (0 : F × F).2) + m 1 1 * (u.1 * u.2) -
        (u.1 * (0 : F × F).2 + u.2 * (0 : F × F).1)) / m 1 0) : ℂ) * Ψ u)
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have e : (u * ((s, s⁻¹) : F × F)).1 * (u * ((s, s⁻¹) : F × F)).2 = u.1 * u.2 := by
      simp only [Prod.fst_mul, Prod.snd_mul]
      field_simp
    simp only [e, Prod.fst_zero, Prod.snd_zero, mul_zero, zero_mul, add_zero]

theorem det_normal (g : GL (Fin 2) F) :
    (!![g.val 0 0 / (g.val).det, g.val 0 1; g.val 1 0 / (g.val).det, g.val 1 1] :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have hd : (g.val).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact this.ne_zero
  rw [Matrix.det_fin_two_of]
  rw [show g.val 0 0 / (g.val).det * g.val 1 1 - g.val 0 1 * (g.val 1 0 / (g.val).det) =
    (g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0) / (g.val).det by ring, ← Matrix.det_fin_two]
  exact div_self hd

theorem piS_zero (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) (u : Fˣ) (Φ : F × F → ℂ) :
    piS χ c₁ g (fun x => Φ (x * ((u : F), ((u⁻¹ : Fˣ) : F)))) 0 = piS χ c₁ g Φ 0 := by
  unfold piS
  congr 1
  have h := rWS_zero_point χ (det_normal g) u.ne_zero (fun y => Φ (y * ((g.val).det, 1)))
  simp only [rWS, rWm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  rw [Units.val_inv_eq_inv_val]
  rw [← h]
  congr 1
  funext y
  rw [mul_right_comm]

end Local

open GroundTheory.Global.AdicLiesOver in
theorem degreeOneEmbedding_zero {K : Type} [Field K] [NumberField K] (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : dg1 v w (0 : K) = 0 := by
  have hinj : Function.Injective (algebraMap (Qv v) (Kv K w)) := (algebraMap (Qv v) (Kv K w)).injective
  have h := Function.leftInverse_invFun hinj 0
  simpa [dg1] using h

end GlobalTheory.CompanionTheory.TwistZero

namespace GlobalTheory.CompanionTheory.TwistZero

theorem val_tw_zero : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl) (D : LM c v)
    (u : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)), (D.tw u).val g 0 = D.val g 0 := by
  intro K _ _ c v D u g
  cases D with
  | sp w₁ w₂ Φ =>
    simp only [LM.tw, LM.val, degreeOneEmbedding_zero]
    exact piS_zero _ _ g u Φ
  | ns w σ η Φ => rfl

end GlobalTheory.CompanionTheory.TwistZero
end
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.OrbitSums

theorem summable_fst_of_norm {Q K : Type} [Finite K] (G : Q → ℂ)
    (hn : Summable (fun q => ‖G q‖)) : Summable (fun p : Q × K => G p.1) := by
  have := Fintype.ofFinite K
  have hn' : Summable (fun _ : K => ‖(1 : ℂ)‖) := (hasSum_fintype _).summable
  simpa using summable_mul_of_summable_norm (f := G) (g := fun _ : K => (1:ℂ)) hn hn'

theorem hasSum_fst_prod {Q K : Type} [Finite K] (G : Q → ℂ) (s : ℂ) (h2 : HasSum G s) :
    HasSum (fun p : Q × K => G p.1) ((Nat.card K : ℂ) * s) := by
  have := Fintype.ofFinite K
  have hs : Summable (fun p : Q × K => G p.1) := summable_fst_of_norm G h2.summable.norm
  have hf : ∀ q, HasSum (fun k : K => G (q, k).1) ((Nat.card K : ℂ) * G q) := fun q => by
    have := hasSum_fintype (fun _ : K => G q)
    simpa [Nat.card_eq_fintype_card] using this
  have h5 := hs.hasSum.prod_fiberwise hf
  have h6 : HasSum (fun q => (Nat.card K : ℂ) * G q) ((Nat.card K : ℂ) * s) := h2.mul_left _
  rw [h6.unique h5]
  exact hs.hasSum

theorem hasSum_comp_mk {H : Type} [CommGroup H] (K : Subgroup H) [Finite K] (G : H ⧸ K → ℂ)
    (s : ℂ) (h2 : HasSum G s) :
    HasSum (fun h : H => G (QuotientGroup.mk h)) ((Nat.card K : ℂ) * s) := by
  have h5 := ((Subgroup.groupEquivQuotientProdSubgroup (s := K)).hasSum_iff
      (f := fun p : (H ⧸ K) × K => G p.1)).2 (hasSum_fst_prod G s h2)
  have hfst : ∀ h : H, ((Subgroup.groupEquivQuotientProdSubgroup (s := K)) h).1
      = QuotientGroup.mk h := fun h => rfl
  simpa only [Function.comp_def, hfst] using h5

theorem orbit_sum_unfold {H A : Type} [CommGroup H] [AddCommGroup A] (T : AddSubgroup A)
    (φ : H → A) (hT : ∀ h, φ h ∈ T) (hφ : ∀ a b, φ (a * b) = φ a + φ b) (R : Finset A)
    (hR : ∀ r ∈ R, r ∈ T) (hu : ∀ m ∈ T, ∃! r, r ∈ R ∧ ∃ h, m = r + φ h)
    (hK : Finite {h : H // φ h = 0}) (F : A → ℂ) (s : ℂ)
    (hs : HasSum (fun m : T => F m) s) :
    HasSum (fun h : H => ∑ r ∈ R, F (r + φ h)) ((Nat.card {h : H // φ h = 0} : ℂ) * s) := by
  classical
  let φ' : H →* Multiplicative A := MonoidHom.mk' (fun h => Multiplicative.ofAdd (φ h))
    (fun a b => by simp [hφ])
  let K : Subgroup H := φ'.ker
  have memK : ∀ h, h ∈ K ↔ φ h = 0 := fun h => by
    simp [K, φ', MonoidHom.mem_ker]
  let bar : (H ⧸ K) → A := fun q => Multiplicative.toAdd (QuotientGroup.kerLift φ' q)
  have bar_inj : Function.Injective bar := fun a b hab =>
    QuotientGroup.kerLift_injective φ' (Multiplicative.toAdd.injective hab)
  have barT : ∀ q, bar q ∈ T := fun q => by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    exact hT h
  let ψ : (H ⧸ K) × R → T := fun p => ⟨(p.2 : A) + bar p.1, T.add_mem (hR _ p.2.2) (barT _)⟩
  have ψbij : Function.Bijective ψ := by
    constructor
    · rintro ⟨q, r, hr⟩ ⟨q', r', hr'⟩ h
      have h' : r + bar q = r' + bar q' := congrArg Subtype.val h
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q'
      have hm : r + φ g ∈ T := T.add_mem (hR _ hr) (hT g)
      have hrr : r = r' := (hu _ hm).unique ⟨hr, g, rfl⟩ ⟨hr', g', h'⟩
      subst hrr
      have : bar (QuotientGroup.mk g) = bar (QuotientGroup.mk g') := add_left_cancel h'
      rw [bar_inj this]
    · rintro ⟨m, hm⟩
      obtain ⟨r, ⟨hr, h, rfl⟩, -⟩ := hu m hm
      exact ⟨(QuotientGroup.mk h, ⟨r, hr⟩), rfl⟩
  have h1 : HasSum (fun p : (H ⧸ K) × R => F ((p.2 : A) + bar p.1)) s :=
    ((Equiv.ofBijective ψ ψbij).hasSum_iff (f := fun m : T => F m)).2 hs
  have h2 : HasSum (fun q : H ⧸ K => ∑ r ∈ R, F (r + bar q)) s := by
    refine h1.prod_fiberwise (fun q => ?_)
    rw [← Finset.sum_coe_sort R (fun r => F (r + bar q))]
    exact hasSum_fintype (fun r : R => F ((r : A) + bar q))
  have hKf : Finite K := Finite.of_equiv _ (Equiv.subtypeEquivRight (fun h => (memK h).symm))
  have h5 := hasSum_comp_mk K _ s h2
  have hc : Nat.card K = Nat.card {h : H // φ h = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight memK)
  rw [hc] at h5
  exact h5

end GlobalTheory.CompanionTheory.OrbitSums
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_over_coset_representatives : ∀ {H A : Type} [CommGroup H] [AddCommGroup A] (T : AddSubgroup A) (φ : H → A), (∀ h, φ h ∈ T) →
  (∀ a b, φ (a * b) = φ a + φ b) → ∀ R : Finset A, (∀ r ∈ R, r ∈ T) →
  (∀ m ∈ T, ∃! r, r ∈ R ∧ ∃ h, m = r + φ h) → Finite {h : H // φ h = 0} →
  ∀ (F : A → ℂ) (s : ℂ), HasSum (fun m : T => F m) s →
    HasSum (fun h : H => ∑ r ∈ R, F (r + φ h)) ((Nat.card {h : H // φ h = 0} : ℂ) * s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.OrbitSums.orbit_sum_unfold
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_integral_unit_shift : ∀ (Sp : Pl → Prop) (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ), (∀ v ∈ Sv, Sp v) → (∀ v, Measurable (f v)) →
  (∀ v, ∃ C : ℝ, ∀ x, ‖f v x‖ ≤ C) → (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, f v (x * e) = f v x) →
  (∃ B : Finset Pl, ∀ v ∉ B, v ∉ Sv ∧ f v 1 = 1 ∧ (Sp v → ∀ k : ℤ, k ≠ 0 → f v (unifUnit (Qv v) ^ k) = 0)) →
  (∀ v, Sp v → ∃ N : ℕ, ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v, f v (unifUnit (Qv v) ^ k * u) = 0) →
  (Function.mulSupport (locF Sp f)).Finite ∧
    HasSum (fun m : {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → Sp v} => ∫ u, ∏ᶠ v, f v (tu Sv m.1 u v) ∂muU Sv) (∏ᶠ v, locF Sp f v) := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.ProdSum.hasSum_integral_finprod | exact GlobalTheory.CompanionTheory.FexTheta.ProdSum.hasSum_integral_finprod | (intros; apply GlobalTheory.CompanionTheory.FexTheta.ProdSum.hasSum_integral_finprod <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unit_translate_valuation : ∀ (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ), (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, f v (x * e) = f v x) →
  ∀ (k : ∀ v : Pl, (Qv v)ˣ) (m' : Pl →₀ ℤ), (∀ v, ord ((k v : (Qv v)ˣ) : Qv v) = m' v) → ∀ m : Pl →₀ ℤ,
    ∫ u, ∏ᶠ v, f v (tu Sv m u v * k v) ∂muU Sv = ∫ u, ∏ᶠ v, f v (tu Sv (m + m') u v) ∂muU Sv := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.torusAverage_shift | exact GlobalTheory.CompanionTheory.FexTheta.torusAverage_shift | (intros; apply GlobalTheory.CompanionTheory.FexTheta.torusAverage_shift <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.KUnit

theorem finite_nonunit_places (K : Type) [Field K] [NumberField K] (κ : Kˣ) :
    {w : PlK K | 1 < w.valuation K (κ : K) ∨ 1 < w.valuation K ((κ⁻¹ : Kˣ) : K)}.Finite := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 K) (κ : K)
  have h2 := HeightOneSpectrum.Support.finite (𝓞 K) ((κ⁻¹ : Kˣ) : K)
  exact (h1.union h2).subset fun w hw => hw

theorem subsingleton_below (K : Type) [Field K] [NumberField K] (w : PlK K) :
    {v : Pl | w.asIdeal.LiesOver v.asIdeal}.Subsingleton := by
  intro v hv v' hv'
  have h1 : v.asIdeal = w.asIdeal.under (𝓞 ℚ) := (hv : w.asIdeal.LiesOver v.asIdeal).over
  have h2 : v'.asIdeal = w.asIdeal.under (𝓞 ℚ) := (hv' : w.asIdeal.LiesOver v'.asIdeal).over
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

theorem mem_integer_of_val (K : Type) [Field K] [NumberField K] (w : PlK K) {k : K}
    (h : ¬ 1 < w.valuation K k) : algebraMap K (Kv K w) k ∈ 𝒪[Kv K w] := by
  have hmem : algebraMap K (Kv K w) k ∈ w.adicCompletionIntegers K := by
    have e : Valued.v (algebraMap K (w.adicCompletion K) k) = w.valuation K k :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact e.le.trans (not_lt.1 h)
  exact (mem_valuationInteger_iff w _).2 hmem

theorem unit_almost_everywhere : ∀ (K : Type) [Field K] [NumberField K] (κ : Kˣ), ∃ S : Finset Pl, ∀ v ∉ S, ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal →
  ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] ∧ (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] := by
  intro K _ _ κ
  have hfin : {v : Pl | ∃ w ∈ {w : PlK K | 1 < w.valuation K (κ : K) ∨
      1 < w.valuation K ((κ⁻¹ : Kˣ) : K)}, w.asIdeal.LiesOver v.asIdeal}.Finite := by
    have := (finite_nonunit_places K κ).biUnion
      (t := fun w => {v : Pl | w.asIdeal.LiesOver v.asIdeal})
      (fun w _ => (subsingleton_below K w).finite)
    refine this.subset ?_
    rintro v ⟨w, hw, hv⟩
    exact Set.mem_biUnion hw hv
  refine ⟨hfin.toFinset, fun v hv w hw => ?_⟩
  have hnot : ¬ (1 < w.valuation K (κ : K) ∨ 1 < w.valuation K ((κ⁻¹ : Kˣ) : K)) := by
    intro h
    exact hv (hfin.mem_toFinset.2 ⟨w, h, hw⟩)
  rw [not_or] at hnot
  constructor
  · exact mem_integer_of_val K w hnot.1
  · have : (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) = algebraMap K (Kv K w) ((κ⁻¹ : Kˣ) : K) := by
      simp [atW]
    rw [this]
    exact mem_integer_of_val K w hnot.2

end GlobalTheory.CompanionTheory.KUnit
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_unit_integral_almost_everywhere : ∀ (K : Type) [Field K] [NumberField K] (κ : Kˣ), ∃ S : Finset Pl, ∀ v ∉ S, ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal →
  ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] ∧ (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] := by
  atlas_forward_decl GlobalTheory.CompanionTheory.KUnit.unit_almost_everywhere
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexThetaMeas

theorem continuous_val_tw (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl)
    (L : LM c v) (hL : L.ok) (g : GL (Fin 2) (Qv v)) (ξ : K) :
    Continuous (fun τ : (Qv v)ˣ => (L.tw τ).val g ξ) := by
  cases L with
  | ns w σ η Φ => exact continuous_const
  | sp w₁ w₂ Φ =>
    obtain ⟨-, hlc, hcs⟩ := hL
    have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
    obtain ⟨hχc, hχ1, -⟩ :=
      (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
    have hf := (GlobalTheory.CompanionTheory.SplitPi.piS_mem hχc hχ1 (cAt c v w₁)
      (show Φ ∈ GL2LocalData.SBE (Qv v × Qv v) from ⟨hlc, hcs⟩) g).1
    have hτ : Continuous (fun τ : (Qv v)ˣ =>
        (dg1 v w₁ ξ, dg1 v w₂ ξ) * ((τ : Qv v), ((τ⁻¹ : (Qv v)ˣ) : Qv v))) :=
      continuous_const.mul (Units.continuous_val.prodMk (Units.continuous_val.comp continuous_inv))
    have e : (fun τ : (Qv v)ˣ => ((LM.sp w₁ w₂ Φ : LM c v).tw τ).val g ξ) = fun τ : (Qv v)ˣ =>
        GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g Φ
          ((dg1 v w₁ ξ, dg1 v w₂ ξ) * ((τ : Qv v), ((τ⁻¹ : (Qv v)ˣ) : Qv v))) := by
      funext τ
      exact GlobalTheory.CompanionTheory.SplitTorus.piS_torus (Qv v) _ hχc hχ1 (cAt c v w₁) g Φ τ _
    rw [e]
    exact hf.continuous.comp hτ

theorem continuous_fL (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (v : Pl)
    (L : LM c v) (hL : L.ok) (g : GL (Fin 2) (Qv v)) (ξ : K) : Continuous (fL L g ξ) :=
  (GlobalTheory.CompanionTheory.CtMeas.continuous_ct L).mul (continuous_val_tw K c v L hL g ξ)

theorem measurable_fL : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K), Measurable (fL L g ξ) := by
  intro K _ _ _ c v L hL g ξ
  exact (continuous_fL K c v L hL g ξ).measurable

end GlobalTheory.CompanionTheory.FexThetaMeas
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_local_theta_coefficient : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K), Measurable (fL L g ξ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexThetaMeas.measurable_fL
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexBound

theorem bounded : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K), ∃ C : ℝ, ∀ x, ‖fL L g ξ x‖ ≤ C := by
  intro K _ _ _ c v L hok g ξ
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    obtain ⟨_, hl, hc⟩ := hok
    have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
    have hχc := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
    have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
    have hf := (GlobalTheory.CompanionTheory.SplitPi.sPiRep (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) (cAt c v w₂)
      (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₁) (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₂) Φ ⟨hl, hc⟩ 1 g).2
    obtain ⟨B, hB⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
    refine ⟨B, fun x => ?_⟩
    unfold fL
    rw [norm_mul, GlobalTheory.CompanionTheory.CtMeas.norm_ct, one_mul]
    change ‖GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g (fun y => Φ (y * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))))
      (dg1 v w₁ ξ, dg1 v w₂ ξ)‖ ≤ B
    rw [GlobalTheory.T.split_weil_action_torus_equivariant (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) g Φ x]
    exact hB _
  | @ns w h σ η Φ =>
    refine ⟨‖(LM.ns w σ η Φ : LM c v).val g ξ‖, fun x => ?_⟩
    unfold fL
    rw [norm_mul, GlobalTheory.CompanionTheory.CtMeas.norm_ct, one_mul]
    exact le_rfl

end GlobalTheory.CompanionTheory.FexBound
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_local_theta_coefficient : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K), ∃ C : ℝ, ∀ x, ‖fL L g ξ x‖ ≤ C := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexBound.bounded
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta

theorem fL_mul_unit : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → (¬ L.IsSp ∨ (Unr c v ∧ L.std)) → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (x : (Qv v)ˣ),
    ∀ e ∈ unQ v, fL L g ξ (x * e) = fL L g ξ x := by
  intro K _ _ _ c v L _ hL g ξ x e he
  cases L with
  | ns w σ η Φ => rfl
  | sp w₁ w₂ Φ =>
    rcases hL with h | ⟨hU, hstd⟩
    · exact absurd trivial h
    have r₁ : IsUnramifiedChar (cAt c v w₁) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1
    have r₂ : IsUnramifiedChar (cAt c v w₂) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hU w₂).1
    have hval : ValuativeRel.valuation (Qv v) (e : Qv v) = 1 := by
      have ha : ValuativeRel.valuation (Qv v) (e : Qv v) ≤ 1 := he.1
      have hb : ValuativeRel.valuation (Qv v) ((e⁻¹ : (Qv v)ˣ) : Qv v) ≤ 1 := he.2
      have hm : ValuativeRel.valuation (Qv v) (e : Qv v) *
          ValuativeRel.valuation (Qv v) ((e⁻¹ : (Qv v)ˣ) : Qv v) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      refine le_antisymm ha ?_
      calc (1 : _) = ValuativeRel.valuation (Qv v) (e : Qv v) *
            ValuativeRel.valuation (Qv v) ((e⁻¹ : (Qv v)ˣ) : Qv v) := hm.symm
        _ ≤ ValuativeRel.valuation (Qv v) (e : Qv v) * 1 := mul_le_mul_right hb _
        _ = _ := mul_one _
    have hmem : e ∈ unitFiltrationUnits (Qv v) 0 := mem_unitFiltrationUnits_zero_iff.mpr hval
    have he₁ : cAt c v w₁ e = 1 := MonoidHom.mem_ker.1 (r₁ hmem)
    have he₂ : cAt c v w₂ e = 1 := MonoidHom.mem_ker.1 (r₂ hmem)
    have hct : (LM.sp w₁ w₂ Φ : LM c v).ct (x * e) = (LM.sp w₁ w₂ Φ : LM c v).ct x := by
      simp [LM.ct, map_mul, he₁, he₂]
    have htw : (LM.sp w₁ w₂ Φ : LM c v).tw (x * e) = (LM.sp w₁ w₂ Φ : LM c v).tw x := by
      have hΦ : Φ = Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1 := hstd
      simp only [LM.tw]
      congr 1
      funext y
      have hO : ∀ (a : Qv v) (u : (Qv v)ˣ), (u : Qv v) ∈ 𝒪[Qv v] → ((u⁻¹ : (Qv v)ˣ) : Qv v) ∈ 𝒪[Qv v] →
          (a * (u : Qv v) ∈ 𝒪[Qv v] ↔ a ∈ 𝒪[Qv v]) := by
        intro a u h1 h2
        refine ⟨fun h => ?_, fun h => mul_mem h h1⟩
        have h3 := mul_mem h h2
        rwa [mul_assoc, Units.mul_inv, mul_one] at h3
      have key : (y * (((x * e : (Qv v)ˣ) : Qv v), (((x * e)⁻¹ : (Qv v)ˣ) : Qv v))) ∈
            {z : Qv v × Qv v | z.1 ∈ 𝒪[Qv v] ∧ z.2 ∈ 𝒪[Qv v]} ↔
          (y * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))) ∈
            {z : Qv v × Qv v | z.1 ∈ 𝒪[Qv v] ∧ z.2 ∈ 𝒪[Qv v]} := by
        have e1' : y.1 * ((x * e : (Qv v)ˣ) : Qv v) = (y.1 * (x : Qv v)) * (e : Qv v) := by
          rw [Units.val_mul, mul_assoc]
        have e2' : y.2 * (((x * e)⁻¹ : (Qv v)ˣ) : Qv v) =
            (y.2 * ((x⁻¹ : (Qv v)ˣ) : Qv v)) * ((e⁻¹ : (Qv v)ˣ) : Qv v) := by
          rw [mul_inv, Units.val_mul, mul_assoc]
        have hinv : (((e⁻¹)⁻¹ : (Qv v)ˣ) : Qv v) ∈ 𝒪[Qv v] := by
          rw [inv_inv]; exact he.1
        simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul]
        rw [e1', e2', hO _ e he.1 he.2, hO _ e⁻¹ he.2 hinv]
      rw [hΦ]
      by_cases h : (y * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))) ∈
          {z : Qv v × Qv v | z.1 ∈ 𝒪[Qv v] ∧ z.2 ∈ 𝒪[Qv v]}
      · rw [Set.indicator_of_mem (key.2 h), Set.indicator_of_mem h]; rfl
      · rw [Set.indicator_of_notMem (fun h' => h (key.1 h')), Set.indicator_of_notMem h]
    simp only [fL, hct, htw]

end GlobalTheory.CompanionTheory.FexTheta
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_theta_coefficient_unit_invariant : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → (¬ L.IsSp ∨ (Unr c v ∧ L.std)) → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (x : (Qv v)ˣ),
    ∀ e ∈ unQ v, fL L g ξ (x * e) = fL L g ξ x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexTheta.fL_mul_unit
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.StdLocal

variable {K : Type} [Field K] [NumberField K]

theorem ct_one {c : HeckeCharacter K} {v : Pl} (L : LM c v) : L.ct 1 = 1 := by
  cases L <;> simp [LM.ct]

theorem tw_one {c : HeckeCharacter K} {v : Pl} (L : LM c v) : L.tw 1 = L := by
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    have e : (((1 : (Qv v)ˣ) : Qv v), (((1 : (Qv v)ˣ)⁻¹ : (Qv v)ˣ) : Qv v)) = 1 := by
      simp [Prod.ext_iff]
    have e' : (fun x : Qv v × Qv v =>
        Φ (x * (((1 : (Qv v)ˣ) : Qv v), (((1 : (Qv v)ˣ)⁻¹ : (Qv v)ˣ) : Qv v))))  = Φ := by
      funext x
      rw [e, mul_one]
    simp only [LM.tw, e']
  | @ns w h σ η Φ => rfl

theorem degreeOneEmbedding_integral_unit (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h1 : Module.finrank (Qv v) (Kv K w) = 1) (κ : Kˣ)
    (h : ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w])
    (h' : (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w]) :
    dg1 v w (κ : K) ≠ 0 ∧ dg1 v w (κ : K) ∈ 𝒪[Qv v] ∧ (dg1 v w (κ : K))⁻¹ ∈ 𝒪[Qv v] := by
  have hb := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.algebraMap_bijective v w h1
  have e : ∀ ξ : K, algebraMap (Qv v) (Kv K w) (dg1 v w ξ) = algebraMap K (Kv K w) ξ :=
    fun ξ => Function.rightInverse_invFun hb.2 _
  have hmul : dg1 v w (κ : K) * dg1 v w ((κ⁻¹ : Kˣ) : K) = 1 := by
    apply hb.1
    rw [map_mul, e, e, map_one, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one hmul, (GlobalTheory.CompanionTheory.StdSphVal.degreeOneEmbedding_mem_integers_iff v w h1 _).2 h, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hmul]
  refine (GlobalTheory.CompanionTheory.StdSphVal.degreeOneEmbedding_mem_integers_iff v w h1 _).2 ?_
  have e2 : atW w κ⁻¹ = (atW w κ)⁻¹ := map_inv _ _
  change ((atW w κ⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w]
  rw [e2]
  exact h'

theorem not_integral {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {a b : F} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (ha : a⁻¹ ∈ 𝒪[F]) (hb : b⁻¹ ∈ 𝒪[F]) {j : ℤ} (hj : j ≠ 0)
    (h1 : a * ((unifUnit F ^ j : Fˣ) : F) ∈ 𝒪[F])
    (h2 : b * (((unifUnit F ^ j)⁻¹ : Fˣ) : F) ∈ 𝒪[F]) : False := by
  have t0 : ((unifUnit F ^ j : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have p1 : ((unifUnit F ^ j : Fˣ) : F) ∈ 𝒪[F] := by
    have := mul_mem ha h1
    rwa [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at this
  have p2 : ((unifUnit F ^ j : Fˣ) : F)⁻¹ ∈ 𝒪[F] := by
    have := mul_mem hb h2
    rwa [← mul_assoc, inv_mul_cancel₀ hb0, one_mul, Units.val_inv_eq_inv_val] at this
  have := GlobalTheory.CompanionTheory.SphTheta.SplitPiK.ord_of_unit t0 p1 p2
  rw [ord_unifUnit_zpow] at this
  exact hj this

set_option maxHeartbeats 1000000 in

theorem fL_std : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → Unr c v → L.std → ∀ k ∈ integralGL (Qv v) 2, ∀ κ : Kˣ,
  (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] ∧
    (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w]) →
  fL L k (κ : K) 1 = 1 ∧ (L.IsSp → ∀ j : ℤ, j ≠ 0 → fL L k (κ : K) (unifUnit (Qv v) ^ j) = 0) := by
  intro K _ _ h2 c v L hok hU hstd k hk κ hκ
  refine ⟨?_, ?_⟩
  · have h := (GlobalTheory.CompanionTheory.StdSphVal.val_std K h2 c v L hok hstd hU k hk (κ : K)).1
      (fun w hw => (hκ w hw).1)
    simp only [fL, ct_one, tw_one, h, one_mul]
  · intro hsp j hj
    cases L with
    | @ns w i σ η Φ => exact hsp.elim
    | @sp w₁ w₂ i₁ i₂ Φ =>
      haveI := i₁
      haveI := i₂
      obtain ⟨hne, -, -⟩ := hok
      have hΦ : Φ = Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1 := hstd
      subst hΦ
      obtain ⟨-, d₁, d₂⟩ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_split h2 v w₁ w₂ hne
      have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
      obtain ⟨hχc, hχ1, hχ0⟩ :=
        (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
      have r₁ : IsUnramifiedChar (cAt c v w₁) :=
        GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1
      have hfix := GlobalTheory.CompanionTheory.SphTheta.SplitPiK.piks
        (GlobalTheory.CompanionTheory.SphTheta.SplitRWK.rwks GlobalTheory.CompanionTheory.SplitRep.sRep) (Qv v) _ hχc hχ1 hχ0 _ r₁ k hk
      obtain ⟨a0, -, a1⟩ := degreeOneEmbedding_integral_unit v w₁ d₁ κ (hκ w₁ i₁).1 (hκ w₁ i₁).2
      obtain ⟨b0, -, b1⟩ := degreeOneEmbedding_integral_unit v w₂ d₂ κ (hκ w₂ i₂).1 (hκ w₂ i₂).2
      have e := GlobalTheory.CompanionTheory.SplitTorus.piS_torus (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) k
        (Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1) (unifUnit (Qv v) ^ j)
        (dg1 v w₁ (κ : K), dg1 v w₂ (κ : K))
      have hnot : (dg1 v w₁ (κ : K), dg1 v w₂ (κ : K)) *
          (((unifUnit (Qv v) ^ j : (Qv v)ˣ) : Qv v), (((unifUnit (Qv v) ^ j)⁻¹ : (Qv v)ˣ) : Qv v)) ∉
          {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} :=
        fun h => not_integral a0 b0 a1 b1 hj h.1 h.2
      simp only [fL, LM.tw, LM.val]
      rw [e, hfix, Set.indicator_of_notMem hnot, mul_zero]

end GlobalTheory.CompanionTheory.FexTheta.StdLocal
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_local_coefficient_values : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → Unr c v → L.std → ∀ k ∈ integralGL (Qv v) 2, ∀ κ : Kˣ,
  (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] ∧
    (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w]) →
  fL L k (κ : K) 1 = 1 ∧ (L.IsSp → ∀ j : ℤ, j ≠ 0 → fL L k (κ : K) (unifUnit (Qv v) ^ j) = 0) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexTheta.StdLocal.fL_std
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexSupport

open ValuativeRel

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem ord_nonneg_of_mem {x : F} (hx : x ≠ 0) (h : x ∈ 𝒪[F]) : 0 ≤ ord x := by
  have h0 := mem_valBall_iff_le_ord (n := 0) hx
  rw [mem_valBall_zero_iff] at h0
  exact h0.mp h

theorem ord_eq_zero_of_mem {u : Fˣ} (h₁ : (u : F) ∈ 𝒪[F]) (h₂ : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F]) :
    ord (u : F) = 0 := by
  have a := ord_nonneg_of_mem u.ne_zero h₁
  have b := ord_nonneg_of_mem (u⁻¹ : Fˣ).ne_zero h₂
  rw [ord_units_inv] at b
  omega

theorem exists_ord_lower [CharZero F] {S : Set F} (hS : IsCompact S) :
    ∃ A : ℤ, ∀ x ∈ S, x ≠ 0 → -A ≤ ord x := by
  obtain ⟨N, hN, H⟩ := GlobalTheory.CompanionTheory.ThetaBound.exists_nat_mul_mem hS
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
  refine ⟨ord (N : F), fun x hx h0 => ?_⟩
  have := ord_nonneg_of_mem (mul_ne_zero hN' h0) (H x hx)
  rw [ord_mul hN' h0] at this
  omega

end Loc

end GlobalTheory.CompanionTheory.FexSupport

theorem GlobalTheory.CompanionTheory.FexSupport.fL_eq_zero : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ), ∃ N : ℕ, ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v,
    fL L g (κ : K) (unifUnit (Qv v) ^ k * u) = 0 := by
  intro K _ _ h2 c v L hok hsp g κ
  cases L with
  | ns w σ η Φ => exact hsp.elim
  | @sp w₁ w₂ h₁ h₂ Φ =>
    obtain ⟨hne, hl, hc⟩ := hok
    haveI : CharZero (Qv v) := charZero_of_injective_algebraMap (algebraMap ℚ (Qv v)).injective
    have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
    have hχc := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
    have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
    have hf := (GlobalTheory.CompanionTheory.SplitPi.sPiRep (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) (cAt c v w₂)
      (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₁) (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₂) Φ ⟨hl, hc⟩ 1 g).2
    set f := GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g Φ with hfdef
    have hC : IsCompact (tsupport f) := hf.2
    obtain ⟨A₁, hA₁⟩ := GlobalTheory.CompanionTheory.FexSupport.exists_ord_lower (hC.image continuous_fst)
    obtain ⟨A₂, hA₂⟩ := GlobalTheory.CompanionTheory.FexSupport.exists_ord_lower (hC.image continuous_snd)
    obtain ⟨e₁, e₂, -⟩ := GlobalTheory.T.split_place_embedding_properties K h2 v w₁ w₂ hne
    have hκ : algebraMap K (Kv K w₁) (κ : K) ≠ 0 := (map_ne_zero _).2 κ.ne_zero
    have hκ' : algebraMap K (Kv K w₂) (κ : K) ≠ 0 := (map_ne_zero _).2 κ.ne_zero
    have hξ₁ : dg1 v w₁ (κ : K) ≠ 0 := fun h => hκ (by rw [← e₁, h, map_zero])
    have hξ₂ : dg1 v w₂ (κ : K) ≠ 0 := fun h => hκ' (by rw [← e₂, h, map_zero])
    refine ⟨(|A₁ + ord (dg1 v w₁ (κ : K))| + |A₂ + ord (dg1 v w₂ (κ : K))|).toNat, fun k hk u hu => ?_⟩
    set x : (Qv v)ˣ := unifUnit (Qv v) ^ k * u with hx
    have hu0 : ord (u : Qv v) = 0 := GlobalTheory.CompanionTheory.FexSupport.ord_eq_zero_of_mem hu.1 hu.2
    have ox : ord (x : Qv v) = k := by
      rw [hx, ord_units_mul, ord_unifUnit_zpow, hu0, add_zero]
    have ox' : ord ((x⁻¹ : (Qv v)ˣ) : Qv v) = -k := by rw [ord_units_inv, ox]
    have hval : (LM.tw (LM.sp w₁ w₂ Φ) x).val g (κ : K) =
        f ((dg1 v w₁ (κ : K), dg1 v w₂ (κ : K)) * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))) :=
      GlobalTheory.T.split_weil_action_torus_equivariant (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) g Φ x _
    have hz : f ((dg1 v w₁ (κ : K), dg1 v w₂ (κ : K)) * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))) = 0 := by
      by_contra hnz
      have hs := subset_tsupport f hnz
      have a₁ : -A₁ ≤ ord (dg1 v w₁ (κ : K) * (x : Qv v)) := hA₁ _ ⟨_, hs, rfl⟩ (mul_ne_zero hξ₁ x.ne_zero)
      have a₂ : -A₂ ≤ ord (dg1 v w₂ (κ : K) * ((x⁻¹ : (Qv v)ˣ) : Qv v)) :=
        hA₂ _ ⟨_, hs, rfl⟩ (mul_ne_zero hξ₂ (x⁻¹ : (Qv v)ˣ).ne_zero)
      rw [ord_mul hξ₁ x.ne_zero, ox] at a₁
      rw [ord_mul hξ₂ (x⁻¹ : (Qv v)ˣ).ne_zero, ox'] at a₂
      have b₁ := le_abs_self (A₁ + ord (dg1 v w₁ (κ : K)))
      have b₂ := neg_abs_le (A₁ + ord (dg1 v w₁ (κ : K)))
      have b₃ := le_abs_self (A₂ + ord (dg1 v w₂ (κ : K)))
      have b₄ := neg_abs_le (A₂ + ord (dg1 v w₂ (κ : K)))
      have hk' := lt_of_le_of_lt (Int.self_le_toNat _) hk
      rcases abs_cases k with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    simp only [fL]
    rw [hval, hz, mul_zero]
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_coefficient_vanishes_at_large_order : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ), ∃ N : ℕ, ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v,
    fL L g (κ : K) (unifUnit (Qv v) ^ k * u) = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexSupport.fL_eq_zero
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexTheta.SplitNormOne

theorem fL_mul_norm_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (κ : Kˣ), κ ∈ K1 K → ∀ x : (Qv v)ˣ,
    fL L g (ξ * κ) x * cW L κ = fL L g ξ (x * k1 L κ) := by
  intro K _ _ h2 c v L hok hsp g ξ κ hκ x
  cases L with
  | ns w σ η Φ => exact hsp.elim
  | sp w₁ w₂ Φ =>
    obtain ⟨hne, -, -⟩ := hok
    obtain ⟨a1, a2, aN⟩ := GlobalTheory.T.split_place_embedding_properties K h2 v w₁ w₂ hne
    have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
    obtain ⟨hχc, hχ1, -⟩ :=
      (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
    have inj1 : Function.Injective (algebraMap (Qv v) (Kv K w₁)) :=
      (algebraMap (Qv v) (Kv K w₁)).injective
    have inj2 : Function.Injective (algebraMap (Qv v) (Kv K w₂)) :=
      (algebraMap (Qv v) (Kv K w₂)).injective
    have m1 : dg1 v w₁ (ξ * κ) = dg1 v w₁ ξ * dg1 v w₁ (κ : K) := by
      apply inj1; rw [map_mul, a1, a1, a1, map_mul]
    have m2 : dg1 v w₂ (ξ * κ) = dg1 v w₂ ξ * dg1 v w₂ (κ : K) := by
      apply inj2; rw [map_mul, a2, a2, a2, map_mul]
    have hN : Algebra.norm ℚ (κ : K) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hκ)
      simpa using this
    have hk : dg1 v w₁ (κ : K) * dg1 v w₂ (κ : K) = 1 := by
      rw [aN, hN]; simp
    have h0 : dg1 v w₁ (κ : K) ≠ 0 := left_ne_zero_of_mul_eq_one hk
    set u : (Qv v)ˣ := Units.mk0 _ h0 with hu
    have hk1 : k1 (LM.sp w₁ w₂ Φ : LM c v) κ = u := by
      have : e1 (LM.sp w₁ w₂ Φ : LM c v) (κ : K) = dg1 v w₁ (κ : K) := rfl
      unfold k1
      rw [dif_neg (by rw [this]; exact h0)]
      exact Units.ext rfl
    have hu1 : (u : Qv v) = dg1 v w₁ (κ : K) := rfl
    have hu2 : ((u⁻¹ : (Qv v)ˣ) : Qv v) = dg1 v w₂ (κ : K) := by
      apply Units.inv_eq_of_mul_eq_one_right
      exact hk
    have c1 : cK c w₁ κ = ((cAt c v w₁ u : ℂˣ) : ℂ) := by
      have : atW w₁ κ = Units.map (algebraMap (Qv v) (Kv K w₁)).toMonoidHom u := by
        apply Units.ext
        exact (a1 (κ : K)).symm
      simp only [cK, cAt, MonoidHom.comp_apply, this]
    have c2 : cK c w₂ κ = ((cAt c v w₂ u⁻¹ : ℂˣ) : ℂ) := by
      have : atW w₂ κ = Units.map (algebraMap (Qv v) (Kv K w₂)).toMonoidHom u⁻¹ := by
        apply Units.ext
        show algebraMap K (Kv K w₂) (κ : K) = algebraMap (Qv v) (Kv K w₂) ((u⁻¹ : (Qv v)ˣ) : Qv v)
        rw [hu2, a2]
      simp only [cK, cAt, MonoidHom.comp_apply, this]
    have tw : ∀ (y : (Qv v)ˣ) (ζ : K), ((LM.sp w₁ w₂ Φ : LM c v).tw y).val g ζ =
        GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g Φ
          ((dg1 v w₁ ζ, dg1 v w₂ ζ) * ((y : Qv v), ((y⁻¹ : (Qv v)ˣ) : Qv v))) := fun y ζ =>
      GlobalTheory.CompanionTheory.SplitTorus.piS_torus (Qv v) _ hχc hχ1 (cAt c v w₁) g Φ y _
    have pt : (dg1 v w₁ (ξ * κ), dg1 v w₂ (ξ * κ)) * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v)) =
        (dg1 v w₁ ξ, dg1 v w₂ ξ) * (((x * u : (Qv v)ˣ) : Qv v), (((x * u)⁻¹ : (Qv v)ˣ) : Qv v)) := by
      rw [m1, m2, mul_inv, Units.val_mul, Units.val_mul, hu1, hu2]
      ext <;> simp <;> ring
    rw [hk1]
    simp only [fL, tw, cW, pt, c1, c2]
    simp only [LM.ct, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
    ring

end GlobalTheory.CompanionTheory.FexTheta.SplitNormOne
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_coefficient_norm_one_twist : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (κ : Kˣ), κ ∈ K1 K → ∀ x : (Qv v)ˣ,
    fL L g (ξ * κ) x * cW L κ = fL L g ξ (x * k1 L κ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexTheta.SplitNormOne.fL_mul_norm_one
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexTheta.SplitW

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem wcS_eq_integral (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Φ : F × F → ℂ) (h : GL (Fin 2) F) :
    GL2LocalData.WcS χ c₁ c₂ Φ h = ∫ u : Fˣ, GL2LocalData.piS χ c₁ h Φ ((u : F), ((u⁻¹ : Fˣ) : F)) * ((c₁ u : ℂˣ) : ℂ) *
      (((c₂ u)⁻¹ : ℂˣ) : ℂ) ∂multHaar F := by
  unfold GL2LocalData.WcS GL2LocalData.piS
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [mul_assoc]

theorem wcS_diag [CharZero F] (χ : AddChar F Circle) (hχ : Continuous χ) (hχ1 : χ ≠ 1) (c₁ c₂ : Fˣ →* ℂˣ)
    (Φ : F × F → ℂ) (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) (g : GL (Fin 2) F) (ξ₁ ξ₂ : Fˣ) :
    GL2LocalData.WcS χ c₁ c₂ Φ (dg2 (ξ₁ * ξ₂) 1 * g) =
      ((c₁ ξ₁ : ℂˣ) : ℂ) * ((c₂ ξ₂ : ℂˣ) : ℂ) * mp (ξ₁ * ξ₂) (1 / 2) *
        ∫ x : Fˣ, ((c₁ x * (c₂ x)⁻¹ : ℂˣ) : ℂ) *
          GL2LocalData.piS χ c₁ g (fun y => Φ (y * ((x : F), ((x⁻¹ : Fˣ) : F)))) ((ξ₁ : F), (ξ₂ : F)) ∂multHaar F := by
  rw [wcS_eq_integral, ← integral_mul_left_eq_self _ ξ₂⁻¹, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e1 := GlobalTheory.T.split_weil_action_diagonal F χ hχ hχ1 c₁ Φ hl hc (ξ₁ * ξ₂) g
    (((ξ₂⁻¹ * x : Fˣ) : F), (((ξ₂⁻¹ * x)⁻¹ : Fˣ) : F))
  have e2 := GlobalTheory.T.split_weil_action_torus_equivariant F χ hχ hχ1 c₁ g Φ x ((ξ₁ : F), (ξ₂ : F))
  have hpt : (((ξ₁ * ξ₂ : Fˣ) : F) * ((ξ₂⁻¹ * x : Fˣ) : F), (((ξ₂⁻¹ * x)⁻¹ : Fˣ) : F)) =
      ((ξ₁ : F), (ξ₂ : F)) * ((x : F), ((x⁻¹ : Fˣ) : F)) := by
    have h2 : (ξ₂ : F) ≠ 0 := ξ₂.ne_zero
    have hx : (x : F) ≠ 0 := x.ne_zero
    refine Prod.ext ?_ ?_
    · simp only [Units.val_mul, Units.val_inv_eq_inv_val, Prod.fst_mul]
      field_simp
    · simp only [Units.val_mul, Units.val_inv_eq_inv_val, Prod.snd_mul, mul_inv, inv_inv]
  beta_reduce
  rw [e1, hpt, e2]
  have n1 : ((c₁ ξ₂ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have n2 : ((c₂ ξ₂ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have n3 : ((c₂ x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [map_mul, map_inv, mul_inv, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end Local

theorem split_alt : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
      L.W (dg2 (nv v κ) 1 * g) = cW L κ * mp (nv v κ) (1 / 2) * locI L g κ := by
  intro K _ _ h2 c v L hok hsp g κ
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
  have hψ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
  have hψ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
  cases L with
  | ns w σ η Φ => exact hsp.elim
  | @sp w₁ w₂ h₁ h₂ Φ =>
    obtain ⟨hne, hl, hc⟩ := hok
    obtain ⟨d1, d2, dn⟩ := GlobalTheory.T.split_place_embedding_properties K h2 v w₁ w₂ hne
    have hnv : ((nv v κ : (Qv v)ˣ) : Qv v) = dg1 v w₁ (κ : K) * dg1 v w₂ (κ : K) := by
      rw [dn]
      simpa [nv] using GlobalTheory.T.local_component_rational_idele v (Units.map (Algebra.norm ℚ : K →* ℚ) κ)
    have hn0 : dg1 v w₁ (κ : K) * dg1 v w₂ (κ : K) ≠ 0 := hnv ▸ (nv v κ).ne_zero
    let ξ₁ : (Qv v)ˣ := Units.mk0 _ (left_ne_zero_of_mul hn0)
    let ξ₂ : (Qv v)ˣ := Units.mk0 _ (right_ne_zero_of_mul hn0)
    have ha : nv v κ = ξ₁ * ξ₂ := Units.ext (by simpa [ξ₁, ξ₂] using hnv)
    have k1 : cAt c v w₁ ξ₁ = localChar c w₁ (atW w₁ κ) := by
      refine congrArg (localChar c w₁) (Units.ext ?_)
      simpa [ξ₁, atW] using d1 (κ : K)
    have k2 : cAt c v w₂ ξ₂ = localChar c w₂ (atW w₂ κ) := by
      refine congrArg (localChar c w₂) (Units.ext ?_)
      simpa [ξ₂, atW] using d2 (κ : K)
    show GL2LocalData.WcS (GP.psiF v)⁻¹ (cAt c v w₁) (cAt c v w₂) Φ (dg2 (nv v κ) 1 * g) =
      (cK c w₁ κ * cK c w₂ κ) * mp (nv v κ) (1 / 2) * ∫ x, fL (LM.sp w₁ w₂ Φ) g (κ : K) x ∂multHaar (Qv v)
    rw [ha, wcS_diag _ hψ hψ1 _ _ Φ hl hc g ξ₁ ξ₂, k1, k2]
    rfl

end GlobalTheory.CompanionTheory.FexTheta.SplitW
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_whittaker_diagonal_norm : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.W (dg2 (nv v κ) 1 * g) = cW L κ * mp (nv v κ) (1 / 2) * locI L g κ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexTheta.SplitW.split_alt
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section
namespace GlobalTheory.CompanionTheory.FexTheta

theorem whittaker_diagonal_norm_field : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ¬ L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.W (dg2 (nv v κ) 1 * g) = cW L κ * mp (nv v κ) (1 / 2) * locI L g κ := by
  intro K _ _ h2 c v m hok hsp g κ
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ => exact absurd trivial hsp
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨hu, hσ, hη, hΦ⟩ := hok
    have hN : ((nv v κ : (Qv v)ˣ) : Qv v) = Algebra.norm (Qv v) ((atW w κ : (Kv K w)ˣ) : Kv K w) := by
      have h1 := GlobalTheory.T.local_norm_at_inert_place K h2 v w hu (κ : K)
      have h3 := GlobalTheory.T.local_component_rational_idele v (Units.map (Algebra.norm ℚ : K →* ℚ) κ)
      show ((Ad3.R.lc v (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) : (Qv v)ˣ) : Qv v) = Algebra.norm (Qv v) (algebraMap K (Kv K w) (κ : K))
      rw [h3, h1]
      rfl
    have key := GlobalTheory.T.field_weil_action_diagonal (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη _ Φ hΦ (atW w κ) (nv v κ) hN g 1
    rw [one_mul] at key
    have hWc : ∀ h : GL (Fin 2) (Qv v), (LM.ns w σ η Φ : LM c v).W h =
        GL2LocalData.piE (Kv K w) (GP.psiF v)⁻¹ σ η (localChar c w) h Φ 1 := by
      intro h
      rfl
    rw [hWc, key]
    rfl

end GlobalTheory.CompanionTheory.FexTheta
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_whittaker_diagonal_norm : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ¬ L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.W (dg2 (nv v κ) 1 * g) = cW L κ * mp (nv v κ) (1 / 2) * locI L g κ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexTheta.whittaker_diagonal_norm_field
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver

open GlobalTheory.CompanionTheory.FexTheta

noncomputable section
namespace GlobalTheory.CompanionTheory.FexMain

theorem L_reps : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M → ∃ R : Finset (Pl →₀ ℤ), IsReps M R := GlobalTheory.T.exists_representatives_for_admissible_data

theorem L_stab : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M → Finite {κ : K1 K // vK M (κ : Kˣ) = 0} := GlobalTheory.T.finite_norm_one_units_trivial_valuation

theorem L_unfold : ∀ {H A : Type} [CommGroup H] [AddCommGroup A] (T : AddSubgroup A) (φ : H → A), (∀ h, φ h ∈ T) →
  (∀ a b, φ (a * b) = φ a + φ b) → ∀ R : Finset A, (∀ r ∈ R, r ∈ T) →
  (∀ m ∈ T, ∃! r, r ∈ R ∧ ∃ h, m = r + φ h) → Finite {h : H // φ h = 0} →
  ∀ (F : A → ℂ) (s : ℂ), HasSum (fun m : T => F m) s →
    HasSum (fun h : H => ∑ r ∈ R, F (r + φ h)) ((Nat.card {h : H // φ h = 0} : ℂ) * s) := GlobalTheory.T.hasSum_over_coset_representatives

theorem L_rsim : ∀ (n : ℤ) (t : ℝ) (z : ℂˣ) (a : ℝˣ), (a : ℝ) = ‖(z : ℂ)‖ ^ 2 → ∀ (g : GL (Fin 2) ℝ) (x : ℂ),
  piRc (chC n (Complex.I * t)) (dg2 a 1 * g) (PhiInf n) x =
    chC n (Complex.I * t) z * ((‖(z : ℂ)‖ : ℝ) : ℂ) * piRc (chC n (Complex.I * t)) g (PhiInf n) (x * z) := GlobalTheory.T.real_weil_action_diagonal

theorem L_riso : ∀ (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) (x u : ℂ), ‖u‖ = 1 →
  piRc (chC n (Complex.I * t)) g (PhiInf n) (x * u) = u ^ (-n) * piRc (chC n (Complex.I * t)) g (PhiInf n) x := GlobalTheory.T.real_weil_action_unit_rotation

theorem L_hecke : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, (∀ v, (M v).ok) → ∀ κ : Kˣ,
    (Function.mulSupport fun v : Pl => cW (M v) κ).Finite ∧
      (∏ᶠ v : Pl, cW (M v) κ) * chC n (Complex.I * t) (embU κ) = 1 := GlobalTheory.T.product_formula_global_character

theorem L_pf : ∀ α : ℚˣ, (Function.mulSupport fun v : Pl => mp (Ad3.R.lc v (pri α)) (1 / 2)).Finite ∧
  (∏ᶠ v : Pl, mp (Ad3.R.lc v (pri α)) (1 / 2)) * ((|(α : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 1 := GlobalTheory.T.product_formula_modulus_rational

theorem L_normemb : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ κ : Kˣ,
  (((Units.map (Algebra.norm ℚ : K →* ℚ) κ : ℚˣ) : ℚ) : ℝ) = ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 ∧
  ((RationalIdeles.realPart (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) : ℝˣ) : ℝ) = ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 := GlobalTheory.T.norm_equals_complex_abs_sq

theorem L_prodsum : ∀ (Sp : Pl → Prop) (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ), (∀ v ∈ Sv, Sp v) → (∀ v, Measurable (f v)) →
  (∀ v, ∃ C : ℝ, ∀ x, ‖f v x‖ ≤ C) → (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, f v (x * e) = f v x) →
  (∃ B : Finset Pl, ∀ v ∉ B, v ∉ Sv ∧ f v 1 = 1 ∧ (Sp v → ∀ k : ℤ, k ≠ 0 → f v (unifUnit (Qv v) ^ k) = 0)) →
  (∀ v, Sp v → ∃ N : ℕ, ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v, f v (unifUnit (Qv v) ^ k * u) = 0) →
  (Function.mulSupport (locF Sp f)).Finite ∧
    HasSum (fun m : {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → Sp v} => ∫ u, ∏ᶠ v, f v (tu Sv m.1 u v) ∂muU Sv) (∏ᶠ v, locF Sp f v) := GlobalTheory.T.product_integral_unit_shift

theorem L_shift : ∀ (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ), (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, f v (x * e) = f v x) →
  ∀ (k : ∀ v : Pl, (Qv v)ˣ) (m' : Pl →₀ ℤ), (∀ v, ord ((k v : (Qv v)ˣ) : Qv v) = m' v) → ∀ m : Pl →₀ ℤ,
    ∫ u, ∏ᶠ v, f v (tu Sv m u v * k v) ∂muU Sv = ∫ u, ∏ᶠ v, f v (tu Sv (m + m') u v) ∂muU Sv := GlobalTheory.T.integral_unit_translate_valuation

theorem L_thn : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ)
  (M : ∀ v : Pl, LM c v), AdmM M → ∀ (x : 𝔸[ℚ]) (g : G2), thT n t M (uni2 x * g) 0 = thT n t M g 0 := GlobalTheory.T.theta_zero_term_unipotent_invariant

theorem L_summ : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K)
  (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ), ∀ g ∈ Gp M,
    HasSum (fun ξ : K => aT n t M Sv g m ξ) (∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv) := GlobalTheory.T.theta_fourier_coefficient_hasSum

theorem L_vk : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
  ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
    (∀ (κ : Kˣ) (v : Pl), vK M κ v = ord ((k1 (M v) κ : (Qv v)ˣ) : Qv v)) ∧ (∀ κ : Kˣ, vK M κ ∈ Tm M) ∧
      ∀ a b : Kˣ, vK M (a * b) = vK M a + vK M b := GlobalTheory.T.valuation_vector_homomorphism

theorem L_th0diag : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → (∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1) → ∀ (κ : Kˣ) (g : G2),
    thT n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) 0 = thT n t M g 0 := GlobalTheory.T.theta_zero_term_norm_invariance
theorem L_liso : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (κ : Kˣ), κ ∈ K1 K → ∀ x : (Qv v)ˣ,
    fL L g (ξ * κ) x * cW L κ = fL L g ξ (x * k1 L κ) := by
  intro K _ _ h2 c v L hL g ξ κ hκ x
  by_cases hs : L.IsSp
  · exact GlobalTheory.T.split_coefficient_norm_one_twist K h2 c v L hL hs g ξ κ hκ x
  · exact GlobalTheory.T.field_coefficient_norm_one_twist K h2 c v L hL hs g ξ κ hκ x

theorem L_lsim : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.W (dg2 (nv v κ) 1 * g) = cW L κ * mp (nv v κ) (1 / 2) * locI L g κ := by
  intro K _ _ h2 c v L hL g κ
  by_cases hs : L.IsSp
  · exact GlobalTheory.T.split_whittaker_diagonal_norm K h2 c v L hL hs g κ
  · exact GlobalTheory.T.field_whittaker_diagonal_norm K h2 c v L hL hs g κ

theorem L_fam : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K)
  (M : ∀ v : Pl, LM c v), AdmM M → ∀ Sv : Finset Pl, GoodSv M Sv → ∀ (g : G2) (κ : Kˣ),
    (∀ v, Measurable (fL (M v) (finAt v g) (κ : K))) ∧
    (∀ v, ∃ C : ℝ, ∀ x, ‖fL (M v) (finAt v g) (κ : K) x‖ ≤ C) ∧
    (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, fL (M v) (finAt v g) (κ : K) (x * e) = fL (M v) (finAt v g) (κ : K) x) ∧
    (∃ B : Finset Pl, ∀ v ∉ B, v ∉ Sv ∧ fL (M v) (finAt v g) (κ : K) 1 = 1 ∧
      ((M v).IsSp → ∀ k : ℤ, k ≠ 0 → fL (M v) (finAt v g) (κ : K) (unifUnit (Qv v) ^ k) = 0)) ∧
    (∀ v, (M v).IsSp → ∃ N : ℕ, ∀ k : ℤ, (N : ℤ) < |k| → ∀ u ∈ unQ v,
      fL (M v) (finAt v g) (κ : K) (unifUnit (Qv v) ^ k * u) = 0) := by
  classical
  intro K _ _ h2 c M hM Sv hS g κ
  refine ⟨fun v => GlobalTheory.T.measurable_local_theta_coefficient K h2 c v (M v) (hM.1 v) _ _, fun v => GlobalTheory.T.bounded_local_theta_coefficient K h2 c v (M v) (hM.1 v) _ _,
    fun v hv x e he => GlobalTheory.T.local_theta_coefficient_unit_invariant K h2 c v (M v) (hM.1 v) ?_ _ _ x e he, ?_,
    fun v hs => GlobalTheory.T.split_coefficient_vanishes_at_large_order K h2 c v (M v) (hM.1 v) hs _ _⟩
  · by_cases hs : (M v).IsSp
    · exact Or.inr (hS.2 v hv hs)
    · exact Or.inl hs
  · obtain ⟨hok, S0, hS0⟩ := hM
    obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g
    obtain ⟨S2, hS2⟩ := GlobalTheory.T.global_unit_integral_almost_everywhere K κ
    refine ⟨S0 ∪ S1 ∪ S2 ∪ Sv, fun v hv => ?_⟩
    simp only [Finset.mem_union, not_or] at hv
    obtain ⟨⟨⟨h0, h1⟩, h2'⟩, h3⟩ := hv
    have := GlobalTheory.T.standard_local_coefficient_values K h2 c v (M v) (hok v) (hS0 v h0).1 (hS0 v h0).2 _ (hS1 v h1) κ (hS2 v h2')
    exact ⟨h3, this.1, this.2⟩

variable {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K}

theorem ct_base {v : Pl} (L : LM c v) : L.ct 1 = 1 := by
  cases L <;> simp [LM.ct]

theorem tu_off (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) (v : Pl) (h1 : v ∉ Sv) (h2 : m v = 0) :
    tu Sv m u v = 1 := by
  simp [tu, h1, h2]

theorem ctM_eq (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) :
    ctM M Sv m u = ∏ᶠ v, (M v).ct (tu Sv m u v) := by
  classical
  unfold ctM
  refine (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
  intro v hv
  by_contra hn
  apply hv
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn
  show (M v).ct (tu Sv m u v) = 1
  rw [tu_off Sv m u v hn.2 hn.1, ct_base]

theorem fact (h2 : Module.finrank ℚ K = 2) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (Sv : Finset Pl)
    (hS : GoodSv M Sv) (g : G2) (κ : Kˣ) (m : Pl →₀ ℤ) :
    aT n t M Sv g m (κ : K) = piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K (κ : K)) *
      ∫ u, ∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m u v) ∂muU Sv := by
  classical
  obtain ⟨-, -, -, ⟨B, hB⟩, -⟩ := L_fam K h2 c M hM Sv hS g κ
  unfold aT
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show ctM M Sv m u * thT n t (twM M Sv m u) g (κ : K) = _ * ∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m u v)
  have hct : (Function.mulSupport fun v => (M v).ct (tu Sv m u v)).Finite := by
    refine (m.support ∪ Sv).finite_toSet.subset fun v hv => ?_
    by_contra hn
    apply hv
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn
    show (M v).ct (tu Sv m u v) = 1
    rw [tu_off Sv m u v hn.2 hn.1, ct_base]
  have hval : (Function.mulSupport fun v => ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K)).Finite := by
    refine (B ∪ m.support ∪ Sv).finite_toSet.subset fun v hv => ?_
    by_contra hn
    apply hv
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn
    have h1 := (hB v hn.1.1).2.1
    show ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K) = 1
    rw [tu_off Sv m u v hn.2 hn.1.2]
    simpa [fL, ct_base] using h1
  have e : (∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m u v)) =
      (∏ᶠ v, (M v).ct (tu Sv m u v)) * ∏ᶠ v, ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K) :=
    finprod_mul_distrib hct hval
  rw [e, ← ctM_eq, thT]
  show _ * (_ * ∏ᶠ v, ((M v).tw (tu Sv m u v)).val (finAt v g) (κ : K)) = _
  ring

theorem chC_norm_one (n : ℤ) (s : ℂ) (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) : chC n s a = (a : ℂ) ^ n := by
  simp [chC, ha]

theorem norm_complex_embedding_norm_one (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) (κ : Kˣ) (hκ : κ ∈ K1 K) :
    ‖((embU κ : ℂˣ) : ℂ)‖ = 1 := by
  have h := (L_normemb K h2 hC κ).1
  have h1 : Units.map (Algebra.norm ℚ : K →* ℚ) κ = 1 := hκ
  rw [h1] at h
  have h3 : ‖((embU κ : ℂˣ) : ℂ)‖ ^ 2 = 1 := by simpa using h.symm
  have h4 := norm_nonneg ((embU κ : ℂˣ) : ℂ)
  nlinarith [sq_nonneg (‖((embU κ : ℂˣ) : ℂ)‖ - 1)]

theorem embC_mul (a b : Kˣ) : embC K ((a * b : Kˣ) : K) = embC K (a : K) * ((embU b : ℂˣ) : ℂ) := by
  simp [embC, embU]

theorem equiv (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) {DK : DatK K} {n : ℤ} {t : ℝ}
    {S : Finset (PlK K)} (hA : AdmK DK c n t S) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (Sv : Finset Pl)
    (hS : GoodSv M Sv) (g : G2) (ξ κ : Kˣ) (hκ : κ ∈ K1 K) (m : Pl →₀ ℤ) :
    aT n t M Sv g m ((ξ * κ : Kˣ) : K) = aT n t M Sv g (m + vK M κ) (ξ : K) := by
  classical
  obtain ⟨-, -, hinv, -, -⟩ := L_fam K h2 c M hM Sv hS g ξ
  obtain ⟨-, -, -, ⟨B, hB⟩, -⟩ := L_fam K h2 c M hM Sv hS g (ξ * κ)
  obtain ⟨hcf, hP⟩ := L_hecke K h2 hC DK c n t S hA M hM.1 κ
  have hnorm := norm_complex_embedding_norm_one h2 hC κ hκ
  have hu0 : ((embU κ : ℂˣ) : ℂ) ≠ 0 := (embU κ).ne_zero
  rw [chC_norm_one n _ _ hnorm] at hP
  rw [fact h2 n t M hM Sv hS g (ξ * κ) m, fact h2 n t M hM Sv hS g ξ (m + vK M κ)]
  rw [← L_shift Sv _ hinv (fun v => k1 (M v) κ) (vK M κ) (fun v => ((L_vk K h2 c M hM).1 κ v).symm) m]
  have hpt : ∀ u, ∏ᶠ v, fL (M v) (finAt v g) (ξ : K) (tu Sv m u v * k1 (M v) κ) =
      (∏ᶠ v, fL (M v) (finAt v g) ((ξ * κ : Kˣ) : K) (tu Sv m u v)) * ∏ᶠ v, cW (M v) κ := by
    intro u
    have hf : (Function.mulSupport fun v => fL (M v) (finAt v g) ((ξ * κ : Kˣ) : K) (tu Sv m u v)).Finite := by
      refine (B ∪ m.support ∪ Sv).finite_toSet.subset fun v hv => ?_
      by_contra hn
      apply hv
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, not_or, not_not] at hn
      show fL (M v) (finAt v g) ((ξ * κ : Kˣ) : K) (tu Sv m u v) = 1
      rw [tu_off Sv m u v hn.2 hn.1.2]
      exact (hB v hn.1.1).2.1
    rw [← finprod_mul_distrib hf hcf]
    refine finprod_congr fun v => ?_
    rw [Units.val_mul, L_liso K h2 c v (M v) (hM.1 v) (finAt v g) (ξ : K) κ hκ]
  simp only [hpt]
  rw [integral_mul_const, embC_mul, L_riso n t _ _ _ hnorm]
  have hz : ((embU κ : ℂˣ) : ℂ) ^ (-n) = ∏ᶠ v, cW (M v) κ := by
    rw [zpow_neg]
    exact (eq_inv_of_mul_eq_one_left hP).symm
  rw [hz]
  ring

open Classical in
theorem locI_eq' {v : Pl} (L : LM c v) (g : GL (Fin 2) (Qv v)) (ξ : K) :
    locI L g ξ = if L.IsSp then ∫ x, fL L g ξ x ∂multHaar (Qv v) else fL L g ξ 1 := by
  cases L with
  | sp w₁ w₂ Φ => simp [locI, LM.IsSp]
  | ns w σ η Φ => simp [locI, LM.IsSp, fL, LM.ct, LM.tw]

theorem locI_eq (M : ∀ v : Pl, LM c v) (g : G2) (ξ : K) (v : Pl) :
    locI (M v) (finAt v g) ξ = locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) ξ) v := by
  rw [locI_eq']
  rfl

theorem cpow_half_sq (r : ℝ) (hr : 0 ≤ r) : (((r ^ 2 : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = (r : ℂ) := by
  have h : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
  rw [← h, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hr]

theorem sumt (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) {DK : DatK K} {n : ℤ} {t : ℝ}
    {S : Finset (PlK K)} (hA : AdmK DK c n t S) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (Sv : Finset Pl)
    (hS : GoodSv M Sv) (g : G2) (κ : Kˣ) :
    HasSum (fun m : Tm M => aT n t M Sv g m (κ : K))
      (WM n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g)) := by
  classical
  obtain ⟨hm, hb, hinv, hfin, hsupp⟩ := L_fam K h2 c M hM Sv hS g κ
  obtain ⟨hmul, hsum⟩ := L_prodsum (fun v => (M v).IsSp) Sv (fun v => fL (M v) (finAt v g) (κ : K)) hS.1 hm hb hinv hfin hsupp
  obtain ⟨hcf, hP⟩ := L_hecke K h2 hC DK c n t S hA M hM.1 κ
  obtain ⟨hmp, hQ⟩ := L_pf (Units.map (Algebra.norm ℚ : K →* ℚ) κ)
  obtain ⟨hn1, hn2⟩ := L_normemb K h2 hC κ
  obtain ⟨hc1, hc2, hc3, -⟩ := GlobalTheory.T.adelic_realPart_properties
  set R := piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K (κ : K)) with hR
  set α := Units.map (Algebra.norm ℚ : K →* ℚ) κ with hα
  set z := embU κ with hz
  have hW : WM n t M (dg2 (pri α) 1 * g) = R * ∏ᶠ v, locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v := by
    have hloc : ∀ v, (M v).W (finAt v (dg2 (pri α) 1 * g)) =
        cW (M v) κ * mp (Ad3.R.lc v (pri α)) (1 / 2) * locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v := by
      intro v
      have h1 : finAt v (dg2 (pri α) 1 * g) = dg2 (nv v κ) 1 * finAt v g := by
        rw [GroundTheory.Automorphic.Reduction.finAt_mul, hc1]
        simp [nv, hα, Ad3.R.lc]
      rw [h1, L_lsim K h2 c v (M v) (hM.1 v), locI_eq]
      rfl
    have hre : WcR (chC n (Complex.I * t)) (PhiInf n) (GL2Classical.realPart (dg2 (pri α) 1 * g)) =
        chC n (Complex.I * t) z * ((‖(z : ℂ)‖ : ℝ) : ℂ) * R := by
      have h1 : GL2Classical.realPart (dg2 (pri α) 1 * g) = dg2 (RationalIdeles.realPart (pri α)) 1 * GL2Classical.realPart g := by
        rw [hc2, hc3, map_one]
      rw [h1]
      have h2' := L_rsim n t z (RationalIdeles.realPart (pri α)) hn2 (GL2Classical.realPart g) 1
      rw [one_mul] at h2'
      exact h2'
    unfold WM pw2
    rw [hre, finprod_congr hloc, finprod_mul_distrib ((hcf.union hmp).subset (Function.mulSupport_mul _ _)) hmul,
      finprod_mul_distrib hcf hmp]
    have hq : ((|(((α : ℚˣ) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) := by
      have : |(((α : ℚˣ) : ℚ) : ℝ)| = ‖(z : ℂ)‖ ^ 2 := by
        rw [hn1, abs_of_nonneg (by positivity)]
      rw [this]
      exact cpow_half_sq _ (norm_nonneg _)
    rw [hq] at hQ
    linear_combination (R * (∏ᶠ v, locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v) *
        (∏ᶠ v, mp (Ad3.R.lc v (pri α)) (1 / 2)) * ((‖(z : ℂ)‖ : ℝ) : ℂ)) * hP +
      (R * ∏ᶠ v, locF (fun v => (M v).IsSp) (fun v => fL (M v) (finAt v g) (κ : K)) v) * hQ
  rw [hW]
  let e : Tm M ≃ {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → (M v).IsSp} := Equiv.subtypeEquivRight fun _ => Iff.rfl
  have h3 := hsum.mul_left R
  have h4 := (e.hasSum_iff).2 h3
  have e2 : (fun m : Tm M => aT n t M Sv g m (κ : K)) =
      (fun m : {m : Pl →₀ ℤ // ∀ v, m v ≠ 0 → (M v).IsSp} => R * ∫ u, ∏ᶠ v, fL (M v) (finAt v g) (κ : K) (tu Sv m.1 u v) ∂muU Sv) ∘ e := by
    funext m
    exact fact h2 n t M hM Sv hS g κ m.1
  rw [e2]
  exact h4

theorem det_diagonal_one_mul (a : Jd) (g : G2) :
    Matrix.GeneralLinearGroup.det (dg2 a 1 * g) = a * Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  congr 1
  apply Units.ext
  simp [dg2, Matrix.det_fin_two]

theorem wvanish (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v)
    (hM : AdmM M) (g : G2) (hg : g ∈ Gp M) (α : ℚˣ) (hα : α ∉ NmK K) : WM n t M (dg2 (pri α) 1 * g) = 0 := by
  obtain ⟨D, -, hGp, hDN⟩ := GlobalTheory.CompanionTheory.HasseGp.gpd K h2 hC c M hM
  refine GlobalTheory.CompanionTheory.WSupport.wsup K h2 c n t M hM _ fun h => hα ?_
  rw [hGp] at h hg
  have h1 : pri α * Matrix.GeneralLinearGroup.det g ∈ D := by
    have : Matrix.GeneralLinearGroup.det (dg2 (pri α) 1 * g) ∈ D := h
    rwa [det_diagonal_one_mul] at this
  have h3 : pri α ∈ D := by
    have := D.mul_mem h1 (D.inv_mem hg)
    simpa using this
  exact (hDN α).1 h3

theorem expansion (h2 : Module.finrank ℚ K = 2) (hC : IsTotallyComplex K) {DK : DatK K} {n : ℤ} {t : ℝ}
    {S : Finset (PlK K)} (hA : AdmK DK c n t S) (M : ∀ v : Pl, LM c v) (hM : AdmM M) (R : Finset (Pl →₀ ℤ))
    (hR : IsReps M R) (Sv : Finset Pl) (hS : GoodSv M Sv) (g : G2) (hg : g ∈ Gp M) :
    HasSum (fun α : ℚˣ => (Nat.card {κ : K1 K // vK M (κ : Kˣ) = 0} : ℂ) * WM n t M (dg2 (pri α) 1 * g))
      (thA R Sv n t M g - th0 R Sv n t M g) := by
  classical
  set I : K → ℂ := fun ξ => ∑ m ∈ R, aT n t M Sv g m ξ with hI
  have hIs : HasSum I (thA R Sv n t M g) := hasSum_sum fun m _ => L_summ K h2 hC c n t M hM Sv m g hg
  have hI0 : I 0 = th0 R Sv n t M g := rfl
  have h1 := hIs.update 0 0
  have h1' : HasSum (Function.update I 0 0) (thA R Sv n t M g - th0 R Sv n t M g) := by
    have e0 : (0 : ℂ) - I 0 + thA R Sv n t M g = thA R Sv n t M g - th0 R Sv n t M g := by
      rw [hI0]; ring
    rwa [e0] at h1
  have hU : HasSum (fun κ : Kˣ => I (κ : K)) (thA R Sv n t M g - th0 R Sv n t M g) := by
    have hinj : Function.Injective ((↑) : Kˣ → K) := Units.val_injective
    have h2' := (hinj.hasSum_iff (f := Function.update I 0 0) (by
      intro x hx
      by_cases h0 : x = 0
      · simp [h0]
      · exact absurd ⟨Units.mk0 x h0, rfl⟩ hx)).2 h1'
    have e : (Function.update I 0 0 ∘ ((↑) : Kˣ → K)) = fun κ : Kˣ => I (κ : K) := by
      funext κ
      simp [Function.update_of_ne κ.ne_zero]
    rwa [e] at h2'
  have hF := hU.tsum_fiberwise (Units.map (Algebra.norm ℚ : K →* ℚ))
  have hst := L_stab K h2 hC c M hM
  obtain ⟨hvk1, hvkT, hvkA⟩ := L_vk K h2 c M hM
  have hfun : (fun α : ℚˣ => (Nat.card {κ : K1 K // vK M (κ : Kˣ) = 0} : ℂ) * WM n t M (dg2 (pri α) 1 * g)) =
      fun α : ℚˣ => ∑' b : (Units.map (Algebra.norm ℚ : K →* ℚ)) ⁻¹' {α}, I ((b : Kˣ) : K) := by
    funext α
    by_cases hα : α ∈ NmK K
    · obtain ⟨ξ₀, rfl⟩ := MonoidHom.mem_range.1 hα
      let e : K1 K ≃ ((Units.map (Algebra.norm ℚ : K →* ℚ)) ⁻¹' {Units.map (Algebra.norm ℚ : K →* ℚ) ξ₀}) :=
        { toFun := fun κ => ⟨ξ₀ * (κ : Kˣ), by
            have h3 : Units.map (Algebra.norm ℚ : K →* ℚ) (κ : Kˣ) = 1 := κ.2
            simp only [Set.mem_preimage, Set.mem_singleton_iff, map_mul, h3, mul_one]⟩
          invFun := fun b => ⟨ξ₀⁻¹ * (b : Kˣ), by
            have h3 : Units.map (Algebra.norm ℚ : K →* ℚ) (b : Kˣ) = Units.map (Algebra.norm ℚ : K →* ℚ) ξ₀ := b.2
            show Units.map (Algebra.norm ℚ : K →* ℚ) (ξ₀⁻¹ * (b : Kˣ)) = 1
            rw [map_mul, h3, map_inv, inv_mul_cancel]⟩
          left_inv := fun κ => Subtype.ext (by simp)
          right_inv := fun b => Subtype.ext (by simp) }
      have hsum := L_unfold (Tm M) (fun h : K1 K => vK M (h : Kˣ)) (fun h => hvkT _)
        (fun a b => hvkA _ _) R hR.1 (fun m hm => by
          obtain ⟨r, ⟨hr, κ, hκ, e1⟩, hu⟩ := hR.2 m hm
          exact ⟨r, ⟨hr, ⟨κ, hκ⟩, e1⟩, fun r' h' => by
            obtain ⟨hr', κ', e'⟩ := h'
            exact hu r' ⟨hr', κ'.1, κ'.2, e'⟩⟩) hst
        (fun m => aT n t M Sv g m (ξ₀ : K)) _ (sumt h2 hC hA M hM Sv hS g ξ₀)
      rw [← e.tsum_eq, ← hsum.tsum_eq]
      refine tsum_congr fun κ => ?_
      refine Finset.sum_congr rfl fun r _ => ?_
      exact (equiv h2 hC hA M hM Sv hS g ξ₀ κ κ.2 r).symm
    · have hemp : IsEmpty ((Units.map (Algebra.norm ℚ : K →* ℚ)) ⁻¹' {α}) :=
        ⟨fun b => hα (MonoidHom.mem_range.2 ⟨b.1, b.2⟩)⟩
      rw [wvanish h2 hC n t M hM g hg α hα, tsum_empty, mul_zero]
  rw [hfun]
  exact hF

theorem theta_twisted_data_value_at_zero (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) (g : G2) :
    thT n t (twM M Sv m u) g 0 = thT n t M g 0 := by
  simp only [thT]
  congr 1
  exact finprod_congr fun v => GlobalTheory.CompanionTheory.TwistZero.val_tw_zero K c v (M v) _ _

theorem thetaZero_periodLattice_eq (R : Finset (Pl →₀ ℤ)) (Sv : Finset Pl) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (g : G2) :
    th0 R Sv n t M g = (∑ m ∈ R, ∫ u, ctM M Sv m u ∂muU Sv) * thT n t M g 0 := by
  simp only [th0, theta_twisted_data_value_at_zero, Finset.sum_mul, integral_mul_const]

theorem L_ctone : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)), AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ R : Finset (Pl →₀ ℤ), IsReps M R → ∀ Sv : Finset Pl, GoodSv M Sv →
  ∀ g : G2, th0 R Sv n t M g ≠ 0 → ∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1 := by
  intro K _ _ h2 hC DK c n t S hA M hM R hR Sv hS g h
  rw [thetaZero_periodLattice_eq] at h
  have h1 := left_ne_zero_of_mul h
  have h3 := right_ne_zero_of_mul h
  exact GlobalTheory.T.local_characters_trivial_of_nonzero_average K h2 hC c M hM R hR Sv hS (GlobalTheory.T.product_character_norm_one_trivial K h2 hC DK c n t S hA M hM g h3) h1
theorem exists_goodSv (M : ∀ v : Pl, LM c v) (hM : AdmM M) : ∃ Sv, GoodSv M Sv := by
  classical
  obtain ⟨-, S0, hS0⟩ := hM
  refine ⟨S0.filter fun v => (M v).IsSp, fun v hv => (Finset.mem_filter.1 hv).2, fun v hv hs => ?_⟩
  exact hS0 v fun h => hv (Finset.mem_filter.2 ⟨h, hs⟩)

theorem centralScalar_eq_of_trivial_character (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v) (hct : ∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1) (z : Jd) :
    GlobalTheory.CompanionTheory.CenTheta.u0 n t M z = GlobalTheory.CompanionTheory.CenTheta.uW n t M z := by
  unfold GlobalTheory.CompanionTheory.CenTheta.u0 GlobalTheory.CompanionTheory.CenTheta.uW
  congr 1
  refine finprod_congr fun v => ?_
  have h := hct v (Ad3.R.lc v z)
  cases hm : M v with
  | sp w₁ w₂ Φ =>
    rw [hm] at h
    have h1 : ((cAt c v w₁ (Ad3.R.lc v z) : ℂˣ) : ℂ) = ((cAt c v w₂ (Ad3.R.lc v z) : ℂˣ) : ℂ) := by
      have h2 : ((cAt c v w₁ (Ad3.R.lc v z) * (cAt c v w₂ (Ad3.R.lc v z))⁻¹ : ℂˣ) : ℂ) = 1 := h
      have h3 : cAt c v w₁ (Ad3.R.lc v z) * (cAt c v w₂ (Ad3.R.lc v z))⁻¹ = 1 := Units.ext h2
      rw [mul_inv_eq_one.1 h3]
    simp only [GlobalTheory.CompanionTheory.CenTheta.om0, GlobalTheory.CompanionTheory.CenTheta.omW, Units.val_mul, h1]
  | ns w σ η Φ => rfl

theorem main : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.Th.FourierExpansionCentral K := by
  intro K _ _ h2 hC DK c n t S hA M hM
  obtain ⟨R, hR⟩ := L_reps K h2 hC c M hM
  obtain ⟨Sv, hS⟩ := exists_goodSv M hM
  obtain ⟨hvk1, hvkT, hvkA⟩ := L_vk K h2 c M hM
  have hst := L_stab K h2 hC c M hM
  refine ⟨R, Sv, (Nat.card {κ : K1 K // vK M (κ : Kˣ) = 0} : ℂ), ?_, fun g hg => ⟨?_, ?_, ?_⟩, fun z => ?_⟩
  · have h1 : vK M (1 : Kˣ) = 0 := by
      have := hvkA 1 1
      simpa using this
    haveI : Nonempty {κ : K1 K // vK M (κ : Kˣ) = 0} := ⟨⟨1, h1⟩⟩
    exact_mod_cast (Nat.card_pos).ne'
  · exact expansion h2 hC hA M hM R hR Sv hS g hg
  · intro x
    simp only [thetaZero_periodLattice_eq, L_thn K h2 c n t M hM x g]
  · intro κ
    by_cases h0 : th0 R Sv n t M g = 0 ∧
        th0 R Sv n t M (dg2 (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) 1 * g) = 0
    · rw [h0.1, h0.2]
    · have hct : ∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1 := by
        by_cases h1 : th0 R Sv n t M g = 0
        · exact L_ctone K h2 hC DK c n t S hA M hM R hR Sv hS _ fun h => h0 ⟨h1, h⟩
        · exact L_ctone K h2 hC DK c n t S hA M hM R hR Sv hS _ h1
      simp only [thetaZero_periodLattice_eq, L_th0diag K h2 hC DK c n t S hA M hM hct κ g]
  · refine ⟨GlobalTheory.CompanionTheory.CenTheta.uW n t M z, GlobalTheory.T.norm_global_central_scalar_eq_one K h2 c n t M hM z,
      fun g => GlobalTheory.T.global_whittaker_central_character K h2 c n t M hM z g, fun g _ => ?_⟩
    rw [GlobalTheory.CompanionTheory.CenTheta.theta_central_character h2 n t M hM R Sv z g]
    by_cases h0 : th0 R Sv n t M g = 0
    · rw [h0, mul_zero, mul_zero]
    · rw [centralScalar_eq_of_trivial_character n t M (L_ctone K h2 hC DK c n t S hA M hM R hR Sv hS g h0) z]

end GlobalTheory.CompanionTheory.FexMain
end
end
