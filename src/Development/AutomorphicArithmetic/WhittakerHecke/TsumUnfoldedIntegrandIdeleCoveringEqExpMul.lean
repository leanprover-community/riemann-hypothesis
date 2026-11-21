import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AutomorphicArithmetic.WhittakerHecke.RealIdeleMulAbsContinuousAndUnitAbsEqOne

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.whittaker_scalar_mul_eq_centralChar_sq_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (x : IdeleGroup ℚ) (g : GL (Fin 2) (A E)),
        Wo D φ (em E (Matrix.GeneralLinearGroup.scalar (Fin 2) x) * g) = ((ω.1 x : ℂˣ) : ℂ) ^ 2 * Wo D φ g := by
  intro E _ _ D ω φ hφ x g
  have h1 : em E (Matrix.GeneralLinearGroup.scalar (Fin 2) x) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E x) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change AdeleBaseChange.adeleMap ℚ E (Matrix.scalar (Fin 2) (x : A ℚ) i j) =
      Matrix.scalar (Fin 2) (AdeleBaseChange.adeleMap ℚ E (x : A ℚ)) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have h2 : ∀ (z : (A E)ˣ) (n : GL (Fin 2) (A E)),
      n * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = Matrix.GeneralLinearGroup.scalar (Fin 2) z * (n * g) := by
    intro z n
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Units.ext (Matrix.scalar_commute (z : A E) (fun _ => Commute.all _ _) n.val).symm.eq
  have h3 : ideleNorm ℚ E (ideleEmbedding ℚ E x) = x ^ 2 := by
    rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  unfold Wo
  rw [h1, ← integral_const_mul]
  congr 1
  funext u
  rw [h2, hφ.cen, h3, map_pow, Units.val_pow_eq_pow_val, mul_assoc]
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem vol_FS : adeleMeasure ℚ (fundamentalSet ℚ) = 1 := adeleMeasure_fundamentalSet ℚ

private instance finFS : IsFiniteMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) :=
  ⟨by rw [Measure.restrict_apply_univ, vol_FS]; exact ENNReal.one_lt_top⟩

private theorem int_cont {g : A ℚ → ℂ} (hg : Continuous g) : IntegrableOn g (fundamentalSet ℚ) (adeleMeasure ℚ) := by
  obtain ⟨C, hC, hs⟩ := Pp.exists_cpt (F := ℚ)
  exact (hg.continuousOn.integrableOn_compact hC).mono_set hs

private theorem cont_psi_mul (a : ℚ) : Continuous fun v : A ℚ => ψ (rt a * v) :=
  Pp.cont_ψ.comp (continuous_const.mul continuous_id)

private theorem psi_rt_mul_per (a k : ℚ) (v : A ℚ) : ψ (rt a * (rt k + v)) = ψ (rt a * v) := by
  rw [mul_add, Pp.ψ_add, ← map_mul, Pp.ψ_rt, one_mul]

private theorem int_psi (γ : ℚ) :
    ∫ v in fundamentalSet ℚ, ψ (rt γ * v) ∂(adeleMeasure ℚ) = if γ = 0 then 1 else 0 := by
  split_ifs with h
  · subst h
    simp [Pp.ψ_rt, ψ, Measure.real, vol_FS]
  · have hne : adelicChar ℚ ≠ 1 := adelicChar_ne_one
    obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hne (DFunLike.ext _ _ fun x => by
        rw [AddChar.one_apply]
        exact Circle.coe_injective (by simpa [ψ] using hc x))
    have h1 := Pp.int_add (h := fun v => ψ (rt γ * v)) (fun k x => psi_rt_mul_per γ k x) (rt γ⁻¹ * a)
    have e : ∀ b : A ℚ, ψ (rt γ * (b + rt γ⁻¹ * a)) = ψ a * ψ (rt γ * b) := by
      intro b
      rw [mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h, map_one, one_mul, Pp.ψ_add, mul_comm]
    simp only [e] at h1
    rw [integral_const_mul] at h1
    have h3 : (ψ a - 1) * ∫ v in fundamentalSet ℚ, ψ (rt γ * v) ∂(adeleMeasure ℚ) = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ha)

private theorem ker_psi (x : A ℚ) : (∀ a : ℚ, ψ (rt a * x) = 1) ↔ x ∈ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ := by
  constructor
  · intro h
    let χ : AddChar (A ℚ) Circle :=
      { toFun := fun y => adelicChar ℚ (x * y)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := fun a b => by rw [mul_add, AddChar.map_add_eq_mul] }
    have hχ : Continuous χ := (continuous_adelicChar (K := ℚ)).comp (continuous_const.mul continuous_id)
    have hk : ∀ k : ℚ, χ (algebraMap ℚ (A ℚ) k) = 1 := fun k => by
      have := h k
      refine Circle.coe_injective ?_
      change ψ (x * rt k) = _
      rw [mul_comm, this]; simp
    obtain ⟨ξ, hξ, -⟩ := existsUnique_eq_adelicChar_mul χ hχ hk
    refine ⟨ξ, ?_⟩
    have h0 : x - rt ξ = 0 := GlobalTheory.CompanionTheory.AdeleAnn.eq_zero_of_forall_adelicChar_mul fun z => by
      have := hξ z
      change adelicChar ℚ (x * z) = adelicChar ℚ (rt ξ * z) at this
      rw [sub_mul, AddChar.map_sub_eq_div, this, div_self']
    exact (sub_eq_zero.1 h0).symm
  · rintro ⟨k, rfl⟩ a
    change ψ (rt a * rt k) = 1
    rw [← map_mul, Pp.ψ_rt]

private theorem eq_zero_of_coeff (Φ : A ℚ → ℂ) (hc : Continuous Φ) (hp : ∀ (k : ℚ) x, Φ (rt k + x) = Φ x)
    (h0 : ∀ a : ℚ, ∫ v in fundamentalSet ℚ, ψ (rt a * v) * Φ v ∂(adeleMeasure ℚ) = 0) : Φ = 0 := by
  haveI := discreteTopology_principalSubgroup ℚ
  obtain ⟨C, hC, hs⟩ := Pp.exists_cpt (F := ℚ)
  have hcov : ∀ x : A ℚ, ∃ γ ∈ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ, γ + x ∈ C := by
    intro x
    obtain ⟨k, hk, -⟩ := existsUnique_sub_mem_fundamentalSet ℚ x
    refine ⟨rt (-k), ⟨-k, rfl⟩, hs ?_⟩
    have e : rt (-k) + x = x - algebraMap ℚ (A ℚ) k := by
      change algebraMap ℚ (A ℚ) (-k) + x = _
      rw [map_neg]
      abel
    rw [e]
    exact hk
  refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (A ℚ) (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) C hC hcov ℚ
    (fun a v => ψ (rt a * v)) cont_psi_mul ?_ ?_ ?_ (fun a x => Pp.norm_ψ _) ker_psi (adeleMeasure ℚ) (fundamentalSet ℚ)
    inferInstance (isAddFundamentalDomain_fundamentalSet ℚ) Φ hc ?_ h0
  · intro a x y
    rw [mul_add, Pp.ψ_add]
  · intro a b x
    simp only [map_add, add_mul, Pp.ψ_add]
  · intro x
    simp [ψ]
  · rintro _ ⟨k, rfl⟩ x
    exact hp k x

private theorem inv_of_summable (f : A ℚ → ℂ) (hc : Continuous f) (hp : ∀ (k : ℚ) x, f (rt k + x) = f x)
    (hs : Summable fun α : ℚ => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * f v ∂(adeleMeasure ℚ)) :
    HasSum (fun α : ℚ => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * f v ∂(adeleMeasure ℚ)) (f 0) := by
  set c : ℚ → ℂ := fun α => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * f v ∂(adeleMeasure ℚ) with hcdef
  have hsn : Summable fun α => ‖c α‖ := hs.norm
  let T : ℚ → A ℚ → ℂ := fun α v => c α * ψ (-(rt α * v))
  have hTc : ∀ α, Continuous (T α) := fun α =>
    continuous_const.mul (Pp.cont_ψ.comp (continuous_const.mul continuous_id).neg)
  have hTn : ∀ α v, ‖T α v‖ = ‖c α‖ := fun α v => by
    simp only [T, norm_mul, Pp.norm_ψ, mul_one]
  let G : A ℚ → ℂ := fun v => ∑' α, T α v
  have hGc : Continuous G := continuous_tsum hTc hsn fun α v => (hTn α v).le
  have hGp : ∀ (k : ℚ) x, G (rt k + x) = G x := by
    intro k x
    refine tsum_congr fun α => ?_
    simp only [T]
    congr 1
    rw [mul_add, neg_add, Pp.ψ_add, ← map_mul, ← map_neg, Pp.ψ_rt, one_mul]
  have hG0 : HasSum c (G 0) := by
    have h1 : Summable fun α => T α 0 := by
      refine Summable.of_norm ?_
      simpa only [hTn] using hsn
    have h2 : HasSum (fun α => T α 0) (G 0) := h1.hasSum
    have e : (fun α => T α 0) = c := by
      funext α
      simp [T, ψ]
    rwa [e] at h2
  have hcoef : ∀ β, ∫ v in fundamentalSet ℚ, ψ (rt β * v) * G v ∂(adeleMeasure ℚ) = c β := by
    intro β
    let Fn : ℚ → A ℚ → ℂ := fun α v => ψ (rt β * v) * T α v
    have hFc : ∀ α, Continuous (Fn α) := fun α => (cont_psi_mul β).mul (hTc α)
    have hFn : ∀ α v, ‖Fn α v‖ = ‖c α‖ := fun α v => by
      simp only [Fn, norm_mul, Pp.norm_ψ, one_mul, hTn]
    have hFi : ∀ α, Integrable (Fn α) ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) := fun α =>
      Integrable.of_bound (C := ‖c α‖) (hFc α).aestronglyMeasurable (ae_of_all _ fun v => (hFn α v).le)
    have hint : ∀ α, ∫ v, ‖Fn α v‖ ∂((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) = ‖c α‖ := fun α => by
      simp only [hFn]
      simp [Measure.real, vol_FS]
    have hsum := hasSum_integral_of_summable_integral_norm hFi (by simpa only [hint] using hsn)
    have e1 : ∀ v, ∑' α, Fn α v = ψ (rt β * v) * G v := fun v => tsum_mul_left
    simp only [e1] at hsum
    have e2 : ∀ α, ∫ v in fundamentalSet ℚ, Fn α v ∂(adeleMeasure ℚ) = if α = β then c β else 0 := by
      intro α
      have e3 : ∀ v, Fn α v = c α * ψ (rt (β - α) * v) := fun v => by
        have e4 : rt (β - α) * v = rt β * v + -(rt α * v) := by
          rw [show rt (β - α) = rt β - rt α from map_sub _ _ _]
          ring
        simp only [Fn, T]
        rw [e4, Pp.ψ_add]
        ring
      simp only [e3]
      rw [integral_const_mul, int_psi]
      by_cases h : α = β
      · subst h
        simp
      · rw [if_neg h, if_neg (sub_ne_zero.2 (Ne.symm h)), mul_zero]
    simp only [e2] at hsum
    exact hsum.unique (hasSum_ite_eq β (c β))
  have hz : (fun v => f v - G v) = 0 := by
    refine eq_zero_of_coeff _ (hc.sub hGc) (fun k x => by rw [hp, hGp]) fun a => ?_
    have hi1 : IntegrableOn (fun v => ψ (rt a * v) * f v) (fundamentalSet ℚ) (adeleMeasure ℚ) :=
      int_cont ((cont_psi_mul a).mul hc)
    have hi2 : IntegrableOn (fun v => ψ (rt a * v) * G v) (fundamentalSet ℚ) (adeleMeasure ℚ) :=
      int_cont ((cont_psi_mul a).mul hGc)
    simp only [mul_sub]
    rw [integral_sub hi1 hi2, hcoef, sub_self]
  have h0 := congrFun hz 0
  simp only [Pi.zero_apply, sub_eq_zero] at h0
  rw [h0]
  exact hG0

section Slice

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

private theorem cont_m : Continuous fun p : A ℚ × A ℚ => gl (nU (D.mkE p.1 p.2)) :=
  Pp.cont_n.comp (D.continuous_mkE' continuous_fst continuous_snd)

private theorem em_val (g : GL (Fin 2) (A ℚ)) (i j : Fin 2) :
    (UpperTheory.ConvolutionTheory.RankTwoDescent.em E g).val i j = am E (g.val i j) := rfl

private theorem em_nU (b : A ℚ) : UpperTheory.ConvolutionTheory.RankTwoDescent.em E (gl (nU b)) = gl (nU (am E b)) := by
  apply Units.ext
  ext i j
  rw [em_val]
  change am E ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) = (!![1, am E b; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j
  fin_cases i <;> fin_cases j <;> simp

private theorem em_aE (y : (A ℚ)ˣ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE y) = aE (Units.map (am (F := ℚ) E).toMonoidHom y) := by
  apply Units.ext
  ext i j
  rw [em_val]
  change am E ((!![(y : A ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) =
    (!![am E (y : A ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j
  fin_cases i <;> fin_cases j <;> simp

private noncomputable def Sl (φ : GL (Fin 2) (A E) → ℂ) (x : GL (Fin 2) (A E)) (v : A ℚ) : ℂ :=
  ∫ b in fundamentalSet ℚ, φ (gl (nU (D.mkE b v)) * x) ∂(adeleMeasure ℚ)

private theorem Fb_eq (φ : GL (Fin 2) (A E) → ℂ) (x : GL (Fin 2) (A E)) : Un.Fb φ x = Sl D φ x 0 := by
  simp only [Un.Fb, Sl, em_nU, D.mkE_base]

private theorem Sl_cont {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) (hb : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B)
    (x : GL (Fin 2) (A E)) : Continuous (Sl D φ x) := by
  obtain ⟨B, hB⟩ := hb
  refine continuous_of_dominated (bound := fun _ => B) (fun v => ?_)
    (fun v => ae_of_all _ fun b => hB _) (integrable_const _) (ae_of_all _ fun b => ?_)
  · exact (hc.comp (((cont_m D).comp (continuous_id.prodMk continuous_const)).mul continuous_const)).aestronglyMeasurable
  · exact hc.comp (((cont_m D).comp (continuous_const.prodMk continuous_id)).mul continuous_const)

private theorem Sl_per {φ : GL (Fin 2) (A E) → ℂ} (hL : Pp.Lf φ) (x : GL (Fin 2) (A E)) (k : ℚ) (v : A ℚ) :
    Sl D φ x (rt k + v) = Sl D φ x v := by
  simp only [Sl]
  congr 1
  funext b
  have e : D.mkE b (rt k + v) = rt (algebraMap ℚ E 0 + algebraMap ℚ E k * D.θ) + D.mkE b v := by
    rw [← D.mkE_rt, ← D.mkE_add, show (rt 0 : A ℚ) = 0 from map_zero _, zero_add]
  rw [e, hL.per]

private theorem fub (H : A ℚ → A ℚ → ℂ) (hH : Continuous fun p : A ℚ × A ℚ => H p.1 p.2) :
    ∫ u in FS2 ℚ, H (u 0) (u 1) ∂(adeleMeasurePi ℚ) =
      ∫ v in fundamentalSet ℚ, ∫ b in fundamentalSet ℚ, H b v ∂(adeleMeasure ℚ) ∂(adeleMeasure ℚ) := by
  set ν := (adeleMeasure ℚ).restrict (fundamentalSet ℚ) with hν
  have h1 : (adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ) = Measure.pi fun _ : Fin 2 => ν :=
    Measure.restrict_pi_pi _ _
  rw [h1]
  have mp := measurePreserving_piFinTwo (fun _ : Fin 2 => ν)
  have h2 := mp.integral_comp' (fun p : A ℚ × A ℚ => H p.1 p.2)
  have h3 : ∫ u, H (u 0) (u 1) ∂(Measure.pi fun _ : Fin 2 => ν) = ∫ p : A ℚ × A ℚ, H p.1 p.2 ∂(ν.prod ν) := h2
  rw [h3, integral_prod_symm]
  obtain ⟨C, hC, hs⟩ := Pp.exists_cpt (F := ℚ)
  rw [hν, Measure.prod_restrict]
  exact (hH.continuousOn.integrableOn_compact (hC.prod hC)).mono_set (Set.prod_mono hs hs)

private theorem coeff_eq {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) (x : GL (Fin 2) (A E)) (α : ℚ) :
    ∫ v in fundamentalSet ℚ, ψ (rt α * v) * Sl D φ x v ∂(adeleMeasure ℚ) =
      ∫ u in FS2 ℚ, φ (nE D u * x) * ψ (rt α * u 1) ∂(adeleMeasurePi ℚ) := by
  have h := fub (fun b v => φ (gl (nU (D.mkE b v)) * x) * ψ (rt α * v))
    ((hc.comp ((cont_m D).mul continuous_const)).mul
      ((cont_psi_mul α).comp continuous_snd))
  refine Eq.trans ?_ h.symm
  congr 1
  funext v
  rw [Sl, integral_mul_const, mul_comm]

private theorem aE_rat (α : ℚˣ) : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) := by
  have h1 : algebraMap ℚ E (α : ℚ) * algebraMap ℚ E ((α⁻¹ : ℚˣ) : ℚ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : algebraMap ℚ E ((α⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ E (α : ℚ) = 1 := by
    rw [mul_comm, h1]
  refine ⟨⟨!![algebraMap ℚ E α, 0; 0, 1], !![algebraMap ℚ E ((α⁻¹ : ℚˣ) : ℚ), 0; 0, 1], ?_, ?_⟩, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]
  · apply Units.ext
    ext i j
    rw [ratGL_apply, em_val]
    change rt ((!![algebraMap ℚ E α, 0; 0, 1] : Matrix (Fin 2) (Fin 2) E) i j) =
      am E ((!![((IdeleGroup.diagonal ℚ α : (A ℚ)ˣ) : A ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)
    rw [coe_diagonal]
    fin_cases i <;> fin_cases j <;> simp [am_rt]

end Slice

section Main

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

open GroundTheory.Automorphic.FourierWhittaker in
private theorem coeff_ne {φ : GL (Fin 2) (A E) → ℂ} (hL : Pp.Lf φ) (x : GL (Fin 2) (A E)) (α : ℚˣ) :
    Wo D φ (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x) =
      ∫ u in FS2 ℚ, φ (nE D u * x) * ψ (rt (α : ℚ) * u 1) ∂(adeleMeasurePi ℚ) := by
  let H : (Fin 2 → A ℚ) → ℂ := fun u => φ (nE D u * x) * ψ (rt (α : ℚ) * u 1)
  have hper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ y, H (ξ + y) = H y := by
    intro ξ hξ y
    obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
    have e1 : D.mkE (rt (η 0) + y 0) (rt (η 1) + y 1) =
        rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (y 0) (y 1) := by
      rw [D.mkE_add, D.mkE_rt]
    change φ (gl (nU (D.mkE (rt (η 0) + y 0) (rt (η 1) + y 1))) * x) * ψ (rt (α : ℚ) * (rt (η 1) + y 1)) =
      φ (gl (nU (D.mkE (y 0) (y 1))) * x) * ψ (rt (α : ℚ) * y 1)
    rw [e1, hL.per, psi_rt_mul_per]
  let M : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.scalar (Fin 2) α⁻¹
  have key := setIntegral_comp_matVec M hper
  have hmv : ∀ (u : Fin 2 → A ℚ) i, matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u i = rt ((α⁻¹ : ℚˣ) : ℚ) * u i := by
    intro u i
    rw [matVec_apply, Finset.sum_eq_single i]
    · simp [M, Matrix.GeneralLinearGroup.scalar]
    · intro j _ hj
      simp [M, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, Ne.symm hj]
    · simp
  obtain ⟨γ, hγ⟩ := aE_rat (E := E) α
  have hrα : rt (α : ℚ) * rt ((α⁻¹ : ℚˣ) : ℚ) = (1 : A ℚ) := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hpt : ∀ u : Fin 2 → A ℚ, φ (nE D u * (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x)) * ψ (u 1) =
      H (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u) := by
    intro u
    set t : (A E)ˣ := Units.map (am (F := ℚ) E).toMonoidHom (IdeleGroup.diagonal ℚ α) with ht
    have htv : (t : A E) = am E (rt (α : ℚ)) := by
      rw [ht, Units.coe_map, coe_diagonal]
      rfl
    set w : A E := D.mkE (u 0) (u 1) with hw
    have e1 : D.mkE (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 0) (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1) =
        am E (rt ((α⁻¹ : ℚˣ) : ℚ)) * w := by
      rw [hmv, hmv, hw, D.am_mul_mkE]
    have e2 : (t : A E) * (am E (rt ((α⁻¹ : ℚˣ) : ℚ)) * w) = w := by
      rw [htv, ← mul_assoc, ← map_mul, hrα, map_one, one_mul]
    have h3 := Pp.a_n t (am E (rt ((α⁻¹ : ℚˣ) : ℚ)) * w)
    rw [e2] at h3
    have e3 : nE D u * (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x) =
        ratGL E 2 γ * (nE D (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u) * x) := by
      rw [hγ, em_aE]
      change gl (nU w) * (aE t * x) = aE t * (gl (nU (D.mkE (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 0)
        (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1))) * x)
      rw [e1, ← mul_assoc, ← mul_assoc, h3]
    have e4 : rt (α : ℚ) * matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1 = u 1 := by
      rw [hmv, ← mul_assoc, hrα, one_mul]
    change _ = φ (nE D (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u) * x) *
      ψ (rt (α : ℚ) * matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1)
    rw [e3, hL.2, e4]
  simp only [Wo, hpt]
  exact key

end Main

theorem UpperTheory.hasSum_whittaker_diagTorus_rat_eq_unipotentConstantTerm :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ x : GL (Fin 2) (A E),
        Summable (fun α : ℚˣ => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x)) →
        HasSum (fun α : ℚˣ => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x)) (Un.Fb φ x) := by
  intro E _ _ D ω φ hA x hs
  have hL : Pp.Lf φ := ⟨hA.cont, hA.left⟩
  set c : ℚ → ℂ := fun α => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * Sl D φ x v ∂(adeleMeasure ℚ) with hcdef
  have hc0 : c 0 = 0 := by
    simp only [hcdef, coeff_eq D hA.cont x 0]
    have e : ∀ u : Fin 2 → A ℚ, φ (nE D u * x) * ψ (rt (0 : ℚ) * u 1) = φ (nE D u * x) := fun u => by
      rw [show (rt 0 : A ℚ) = 0 from map_zero _, zero_mul, ψ_zero, mul_one]
    simp only [e]
    exact hA.zero x
  have hcα : ∀ α : ℚˣ, c α = Wo D φ (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x) := fun α => by
    rw [coeff_ne D hL x α]
    exact coeff_eq D hA.cont x α
  have hinj : Function.Injective (Units.val : ℚˣ → ℚ) := Units.val_injective
  have hsupp : ∀ q ∉ Set.range (Units.val : ℚˣ → ℚ), c q = 0 := by
    intro q hq
    by_cases h : q = 0
    · rw [h, hc0]
    · exact absurd ⟨Units.mk0 q h, rfl⟩ hq
  have hfc : c ∘ (Units.val : ℚˣ → ℚ) = fun α : ℚˣ => Wo D φ (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x) :=
    funext hcα
  have hsum : Summable c := (hinj.summable_iff hsupp).1 (by rw [hfc]; exact hs)
  have hinv := inv_of_summable (Sl D φ x) (Sl_cont D hA.cont hA.bdd x) (Sl_per D hL x) hsum
  rw [Fb_eq D, ← hfc]
  exact (hinj.hasSum_iff hsupp).2 hinv
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem ab_mul' (a b : (A ℚ)ˣ) : ab (a * b) = ab a * ab b := by simp [ab, map_mul]

private theorem ab_pos' (a : (A ℚ)ˣ) : 0 < ab a := (IdeleGroup.ideleModule ℚ a).2

private theorem ab_inv' (a : (A ℚ)ˣ) : ab a⁻¹ = (ab a)⁻¹ := by simp [ab, map_inv]

private theorem ab_diag' (α : ℚˣ) : ab (IdeleGroup.diagonal ℚ α) = 1 := by
  simp [ab, IdeleGroup.ideleModule_diagonal]

private theorem cpow_exp (x : ℝ) (w : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ w = Complex.exp ((x : ℂ) * w) := by
  have h : ((Real.exp x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [Complex.cpow_def_of_ne_zero h, ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

private theorem modid (t r : ℝ) (hr : 0 < r) (s : ℂ) :
    Complex.exp (2 * s * t) * ((((Real.exp t * r⁻¹)⁻¹ ^ 2 : ℝ)) : ℂ) =
      ((Real.exp t * Real.exp t * (r⁻¹ * r⁻¹) : ℝ) : ℂ) ^ (s - 1) * (r : ℂ) ^ (2 * s) := by
  obtain ⟨L, rfl⟩ : ∃ L, r = Real.exp L := ⟨Real.log r, (Real.exp_log hr).symm⟩
  have h1 : (Real.exp t * (Real.exp L)⁻¹)⁻¹ ^ 2 = Real.exp (2 * L - 2 * t) := by
    rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h2 : Real.exp t * Real.exp t * ((Real.exp L)⁻¹ * (Real.exp L)⁻¹) = Real.exp (2 * t - 2 * L) := by
    rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h1, h2, cpow_exp, cpow_exp, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem cpow_ne {r : ℝ} (hr : 0 < r) (w : ℂ) : (r : ℂ) ^ w ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne')]
  exact Complex.exp_ne_zero _

private theorem cg1 {G : Type} [CommGroup G] (e u z : G) :
    e * e * u * (z * z)⁻¹ = (e * u * z⁻¹) * (e * u * z⁻¹) * u⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem cg2 {G : Type} [CommGroup G] (e u z : G) :
    e * ((e * u * z⁻¹)⁻¹ * u) = z := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem cg3 {G : Type} [CommGroup G] (a u : G) :
    a * a * u⁻¹ = u * (u * a⁻¹)⁻¹ * (u * a⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem cg4 {G : Type} [CommGroup G] (a b u : G) :
    (u * a⁻¹) * (b * (a * a * u⁻¹)) = b * a := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

private theorem gl_mD (a : (A ℚ)ˣ) : (gl (mD a)).val = !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl

private theorem mat_id (b a u : (A ℚ)ˣ) :
    aE b * gl (mD a) * dM u = Matrix.GeneralLinearGroup.scalar (Fin 2) (u * a⁻¹) * aE (b * (a * a * u⁻¹)) := by
  have h4 : ((u : A ℚ) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)) * ((b : A ℚ) * ((a : A ℚ) * (a : A ℚ) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ))) = (b : A ℚ) * (a : A ℚ) := by
    have := congrArg Units.val (cg4 a b u)
    simpa only [Units.val_mul] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aE, gl_mD, dM, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two, h4, mul_comm]

private theorem row_id (a u : (A ℚ)ˣ) (k : G1 ℚ) (j : Fin 2) :
    (gl (mD a) * dM u * gl k).val 1 j = ((a⁻¹ * u : (A ℚ)ˣ) : A ℚ) * row k j := by
  simp [gl_mD, dM, UpperTheory.ConvolutionTheory.R2.G.row, Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.tsum_unfoldedIntegrand_ideleCovering_eq_exp_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ) (t : ℝ) (u : IdeleGroup ℚ), u ∈ UU →
        ∀ p : IdeleGroup ℚ × G1 ℚ, (Summable fun α : ℚˣ => Un.Hh D χ φ Φ s (Un.cov t u α * (p.1 * p.1)⁻¹, p)) →
        Complex.exp (2 * s * t) * (((χ.1 u : ℂˣ) : ℂ) * Un.Tt φ Φ t u p) = ∑' α : ℚˣ, Un.Hh D χ φ Φ s (Un.cov t u α * (p.1 * p.1)⁻¹, p) := by
  intro E _ _ D ω χ φ hA hχω Φ s t u hu p hS
  obtain ⟨z, k⟩ := p
  obtain ⟨e, he⟩ : ∃ e : (A ℚ)ˣ, e = iy (Real.exp t) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (A ℚ)ˣ, a = e * u * z⁻¹ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (A ℚ)ˣ, c = u * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : (A ℚ)ˣ, y = a * a * u⁻¹ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : GL (Fin 2) (A E), x = em E (gl (mD a) * dM u * gl k) := ⟨_, rfl⟩
  obtain ⟨Φz, hΦz⟩ : ∃ w : ℂ, w = Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j := ⟨_, rfl⟩
  have haa : Un.aa t u z = a := by rw [ha, he]; rfl
  have hcov : ∀ α : ℚˣ, Un.cov t u α * (z * z)⁻¹ = IdeleGroup.diagonal ℚ α * y := fun α => by
    have h := cg1 e u z
    rw [← ha, ← hy] at h
    rw [← h, he]
    simp only [Un.cov, mul_assoc]
  have hrow : (fun j => (iy (Real.exp t) : A ℚ) * (gl (mD a) * dM u * gl k).val 1 j) =
      fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j := by
    funext j
    rw [row_id, ← he, ← mul_assoc, ← Units.val_mul, ha, cg2]
  have hTt : Un.Tt φ Φ t u (z, k) = (((ab a)⁻¹ ^ 2 : ℝ) : ℂ) * Un.Fb φ x * Φz := by
    show (((ab (Un.aa t u z))⁻¹ ^ 2 : ℝ) : ℂ) * Un.Fb φ (em E (gl (mD (Un.aa t u z)) * dM u * gl k)) *
      (Φ fun j => (iy (Real.exp t) : A ℚ) * (gl (mD (Un.aa t u z)) * dM u * gl k).val 1 j) = _
    rw [haa, hrow, ← hx, ← hΦz]
  obtain ⟨W, hWd⟩ : ∃ W : ℚˣ → ℂ, W = fun α => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α * y) * gl k)) := ⟨_, rfl⟩
  have hW : ∀ α : ℚˣ, Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x) = ((ω.1 c : ℂˣ) : ℂ) ^ 2 * W α := fun α => by
    have h : aE (IdeleGroup.diagonal ℚ α) * (gl (mD a) * dM u * gl k) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c * (aE (IdeleGroup.diagonal ℚ α * y) * gl k) := by
      calc _ = aE (IdeleGroup.diagonal ℚ α) * gl (mD a) * dM u * gl k := by simp only [mul_assoc]
        _ = _ := by rw [mat_id, mul_assoc, ← hc, ← hy]
    rw [hx, ← map_mul, h, map_mul, UpperTheory.whittaker_scalar_mul_eq_centralChar_sq_mul E D ω φ hA, hWd]
  obtain ⟨C, hC⟩ : ∃ C : ℂ, C = ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) * (Φz * ((ab z : ℝ) : ℂ) ^ (2 * s)) := ⟨_, rfl⟩
  have habd : ∀ α : ℚˣ, ab (IdeleGroup.diagonal ℚ α * y) = ab y := fun α => by
    rw [ab_mul', ab_diag', one_mul]
  have hχd : ∀ α : ℚˣ, χ.1 (IdeleGroup.diagonal ℚ α * y) = χ.1 y := fun α => by
    have h : χ.1 (IdeleGroup.diagonal ℚ α) = 1 := χ.2.2 α
    rw [map_mul, h, one_mul]
  have hH : ∀ α : ℚˣ, Un.Hh D χ φ Φ s (Un.cov t u α * (z * z)⁻¹, (z, k)) = W α * C := fun α => by
    rw [hcov α]
    show Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α * y) * gl k)) * ((χ.1 (IdeleGroup.diagonal ℚ α * y) : ℂˣ) : ℂ) *
      ((ab (IdeleGroup.diagonal ℚ α * y) : ℝ) : ℂ) ^ (s - 1) *
      ((Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)) = _
    rw [hχd, habd, ← hΦz, hC, hWd]
    ring
  have hS' : Summable fun α : ℚˣ => W α * C := by
    simpa only [hH] using hS
  simp only [hH]
  rw [hTt]
  by_cases h0 : Φz = 0
  · have hC0 : C = 0 := by rw [hC, h0]; ring
    simp [h0, hC0]
  have hCne : C ≠ 0 := by
    rw [hC]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (cpow_ne (ab_pos' y) _)) (mul_ne_zero h0 (cpow_ne (ab_pos' z) _))
  have hsW : Summable W := (summable_mul_right_iff hCne).1 hS'
  have hsum : Summable fun α : ℚˣ => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x) := by
    simp only [hW]
    exact hsW.mul_left _
  have hFb : Un.Fb φ x = ((ω.1 c : ℂˣ) : ℂ) ^ 2 * ∑' α, W α := by
    have h := (UpperTheory.hasSum_whittaker_diagTorus_rat_eq_unipotentConstantTerm E D ω φ hA x hsum).tsum_eq
    simp only [hW] at h
    rw [← h, tsum_mul_left]
  have hchar : ((χ.1 u : ℂˣ) : ℂ) * ((ω.1 c : ℂˣ) : ℂ) ^ 2 = ((χ.1 y : ℂˣ) : ℂ) := by
    have h2 : ω.1 c ^ 2 = (χ.1 c)⁻¹ * (χ.1 c)⁻¹ := by
      have h := hχω c
      rw [mul_pow] at h
      rw [← mul_inv, ← sq]
      exact eq_inv_of_mul_eq_one_right h
    have h3 : χ.1 y = χ.1 u * ω.1 c ^ 2 := by
      rw [hy, cg3, ← hc, map_mul, map_mul, map_inv, h2, mul_assoc]
    rw [h3]
    push_cast
    rfl
  have hiy : ab e = Real.exp t := by
    rw [he, (UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one).2.1 _ (Real.exp_ne_zero t), abs_of_pos (Real.exp_pos t)]
  have hau : ab u = 1 := (UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one).2.2.2 u hu
  have hab : ab a = Real.exp t * (ab z)⁻¹ := by
    rw [ha, ab_mul', ab_mul', hiy, hau, ab_inv', mul_one]
  have haby : ab y = Real.exp t * Real.exp t * ((ab z)⁻¹ * (ab z)⁻¹) := by
    rw [hy, ab_mul', ab_mul', ab_inv', hab, hau]
    ring
  have hmod := modid t (ab z) (ab_pos' z) s
  rw [← hab, ← haby] at hmod
  rw [tsum_mul_right, hFb, hC, ← hchar]
  linear_combination (((χ.1 u : ℂˣ) : ℂ) * ((ω.1 c : ℂˣ) : ℂ) ^ 2 * (∑' α, W α) * Φz) * hmod
end
