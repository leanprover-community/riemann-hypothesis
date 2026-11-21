import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharDotMulMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairRestrictionTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LagrUniqW

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ l l' : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) → l' ∈ (adeleClass F).adm (Fin n × Fin d) →
      (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ ∧ l' (M.co.rho B.ψ u Φ) = l' Φ) →
      (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        l (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l Φ ∧
        l' (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l' Φ) →
      (∃ Φ ∈ schA F (Fin n × Fin d), l' Φ ≠ 0) → ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), l Φ = c * l' Φ := by
  intro _hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ l l' hl hl' h0 h1 hne
  obtain ⟨L, hiso, hrank, hL⟩ :=
    GlobalTheory.T.skew_adapted_pair_restriction_theta F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁
  have hstd : IsStd B.ψ := hP.base.std
  have key : ∀ m : Fn F n d →ₗ[ℂ] ℂ,
      (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), m (M.co.rho B.ψ u Φ) = m Φ) →
      (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        m (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = m Φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F (Fin n × Fin d),
        m (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = m φ := by
    intro m hm0 hm1 t w hw φ hφ
    obtain ⟨u, hu, z, hz, heq⟩ := hL t w hw
    rw [heq, hm0 u hu _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ φ hφ), hm1 z hz φ hφ]
  exact GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hstd (Fin n × Fin d) L hiso hrank l hl l' hl'
    (key l (fun u hu Φ hΦ => (h0 u hu Φ hΦ).1) (fun z hz Φ hΦ => (h1 z hz Φ hΦ).1))
    (key l' (fun u hu Φ hΦ => (h0 u hu Φ hΦ).2) (fun z hz Φ hΦ => (h1 z hz Φ hΦ).2)) hne

end GlobalTheory.LagrUniqW
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_adapted_pair_restriction_eigen : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ l l' : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) → l' ∈ (adeleClass F).adm (Fin n × Fin d) →
      (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ ∧ l' (M.co.rho B.ψ u Φ) = l' Φ) →
      (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        l (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l Φ ∧
        l' (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l' Φ) →
      (∃ Φ ∈ schA F (Fin n × Fin d), l' Φ ≠ 0) → ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), l Φ = c * l' Φ := by
  atlas_forward_decl GlobalTheory.LagrUniqW.main
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvNeZero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pure_ne_zero {κ : Type} [Fintype κ] (g : SInf F κ) (hg : g ≠ 0) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    by_contra! h
    exact hg (SchwartzMap.ext h)
  have hfin : {v | ¬ φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1}.Finite := hstd
  set T := hfin.toFinset with hT
  have hy : ∀ v, ∃ y : κ → Fv F v, φ v y ≠ 0 := fun v => by
    by_contra! h
    exact h0 v (funext h)
  choose y hy using hy
  let xf : κ → Af F := fun i => ⟨fun v => if v ∈ T then y v i else 0, by
    filter_upwards [T.eventually_cofinite_notMem] with v hv
    simp only [if_neg hv]
    exact zero_mem _⟩
  let x : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), xf i)
  intro hz
  have hx := congrFun hz x
  have e1 : (fun i => evI F (x i)) = a := funext fun i => by simp [x, evI]
  have e2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ T then y v i else 0 := fun v => funext fun i => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, e1, e2] at hx
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_] at hx
  · rcases mul_eq_zero.1 hx with h | h
    · exact ha h
    · obtain ⟨v, hv, h⟩ := Finset.prod_eq_zero_iff.1 h
      simp only [hv, if_true] at h
      exact hy v h
  · intro v hv
    by_contra hvT
    apply hv
    have hφ : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      by_contra hc
      exact hvT (hfin.mem_toFinset.2 hc)
    have hvT' : v ∉ T := hvT
    simp only [hvT', if_false, hφ]
    rw [Set.indicator_of_mem (s := {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}) (a := fun _ => 0)
      (fun i => zero_mem _)]
    rfl

theorem exists_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ he
  obtain ⟨ei, ev, hei, hev, hpure⟩ := he.loc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra! h
    exact hei (ContinuousLinearMap.ext h)
  have hfam : GlobalTheory.BigNZ.Fam M M.vac := ⟨fun v => (hM.vac v).1, Filter.Eventually.of_forall fun _ => rfl⟩
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac, hfam.mem hM f, ?_⟩
  rw [hpure f M.vac hfam.1 hfam.2]
  have hv : (fun v => ev v (M.vac v)) = M₁.vac := funext fun v => (hev v).1
  rw [hv]
  exact pure_ne_zero (ei f) hf M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std

end GlobalTheory.ThK.EvNeZero
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  first | exact @GlobalTheory.ThK.EvNeZero.exists_ne_zero | exact GlobalTheory.ThK.EvNeZero.exists_ne_zero | (intros; apply GlobalTheory.ThK.EvNeZero.exists_ne_zero <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvZeroUniq

open scoped Classical

theorem proj_zero_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AF F) i).1) = 0 := by
    funext i
    exact map_zero _
  have h2 : (fun i => ((0 : κ → AF F) i).2) = 0 := rfl
  show pureA F f g 0 = _
  rw [pureA, h1, h2]
  simp [mul_comm]

theorem schr_mem_schA {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  have h2 := GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace ψ hψ w.2 _ (GlobalTheory.SchwartzTranslate.main F κ w.1 Φ hΦ)
  have : schr ψ w Φ = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) • (fun x => ψ (x ⬝ᵥ w.2) * Φ (x + w.1)) := by
    funext x
    simp only [schr, Pi.smul_apply, smul_eq_mul, AddChar.map_add_eq_mul]
    ring
  rw [this]
  exact Submodule.smul_mem _ _ h2

theorem apply_eq_rho {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (f : (κ → AF F) → ℂ)
    (x : κ → AF F) : f x = dc.rho ψ (dc.e.symm (x, 0)) f 0 := by
  simp [Darboux.rho, schr]

theorem rho_apply_zero {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (f : (κ → AF F) → ℂ)
    (z : W) (hz : (dc.e z).1 = 0) : dc.rho ψ z f 0 = f 0 := by
  simp [Darboux.rho, schr, hz]

theorem uniqB : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ l l' : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) → l' ∈ (adeleClass F).adm (Fin n × Fin d) →
      (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ ∧ l' (M.co.rho B.ψ u Φ) = l' Φ) →
      (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        l (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l Φ ∧
        l' (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = l' Φ) →
      (∃ Φ ∈ schA F (Fin n × Fin d), l' Φ ≠ 0) → ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), l Φ = c * l' Φ := GlobalTheory.T.skew_adapted_pair_restriction_eigen

theorem evNe : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := GlobalTheory.T.eigen_intertwiner_extension

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ S : Fn F n d →ₗ[ℂ] Fn F n d₁, (∀ Φ ∈ schA F (Fin n × Fin d), S Φ ∈ schA F (Fin n × Fin d₁)) →
        (∀ z : Matrix (Fin n) (Fin d₁) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (S Φ)) →
        (∀ u ∈ iso0 n H', ∀ Φ ∈ schA F (Fin n × Fin d), S (M.co.rho B.ψ u Φ) = S Φ) →
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁), l ∘ₗ S ∈ (adeleClass F).adm (Fin n × Fin d)) →
        ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), S Φ = c • e Φ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁ e he S _ hSheis hSinv hSadm
  have hstd : IsStd B.ψ := hP.base.std
  let δ : Fn F n d₁ →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hδ : δ ∈ (adeleClass F).adm (Fin n × Fin d₁) := proj_zero_mem_adm F _
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d) :=
    fun u Φ hΦ => schr_mem_schA _ hstd _ hΦ
  have hδe : ∀ (f : Fn F n d₁) x, f x = δ (M₁.co.rho B.ψ (M₁.co.e.symm (x, 0)) f) := fun f x => apply_eq_rho _ _ f x
  have hfix : ∀ z, (M₁.co.e z).1 = 0 → ∀ f : Fn F n d₁, δ (M₁.co.rho B.ψ z f) = δ f :=
    fun z hz f => rho_apply_zero _ _ f z hz
  obtain ⟨Φ₀, hΦ₀, hne⟩ := evNe F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he
  obtain ⟨x₀, hx₀⟩ : ∃ x, e Φ₀ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨c, hc⟩ := uniqB hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁
    (δ ∘ₗ S) (δ ∘ₗ e) (hSadm δ hδ) (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he δ hδ)
    (fun u hu Φ hΦ => ⟨by simp only [LinearMap.comp_apply]; rw [hSinv u hu Φ hΦ],
      by simp only [LinearMap.comp_apply]; rw [he.inv u hu Φ hΦ]⟩)
    (fun z hz Φ hΦ => ⟨by simp only [LinearMap.comp_apply]; rw [hSheis z Φ hΦ, hfix z hz],
      by simp only [LinearMap.comp_apply]; rw [he.Heisenberg₂ z Φ hΦ, hfix z hz]⟩)
    ⟨_, hρ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (x₀, 0) * (incM F H'.ι)ᵀ) Φ₀ hΦ₀, by
      simp only [LinearMap.comp_apply]
      rw [he.Heisenberg₂ _ Φ₀ hΦ₀, ← hδe]
      exact hx₀⟩
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  have h1 := hc _ (hρ (incM F (1 : Matrix (Fin n) (Fin n) E) * M₁.co.e.symm (x, 0) * (incM F H'.ι)ᵀ) Φ hΦ)
  simp only [LinearMap.comp_apply] at h1
  rw [hSheis _ Φ hΦ, he.Heisenberg₂ _ Φ hΦ, ← hδe, ← hδe] at h1
  simpa using h1

end GlobalTheory.EvZeroUniq
end
end
