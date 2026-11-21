import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KHeisComm

variable {F : Type} [Field F] [NumberField F]

theorem archimedean_isomorphism_split_trivial {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.ArchIsom.r0 F κ (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = 1 := by
  change GlobalTheory.ArchIsom.g0 F κ 0 = 1
  simp [GlobalTheory.ArchIsom.g0, Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts (F := F) κ)]

theorem tens_split {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ (GlobalTheory.ArchIsom.r0 F κ) (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = φ z := by
  have hz : (fun i => evI F (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0) i)) = z :=
    funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv κ _ i
  simp only [tens, hz, archimedean_isomorphism_split_trivial, mul_one]

open scoped Classical in

theorem proj_mem_adm {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end GlobalTheory.KHeisComm

open GlobalTheory.KHeisComm in
open scoped Classical in

theorem GlobalTheory.KHeisComm.actsD_heisLine_mat_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∀ f f₁ fk h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ → Acts (evI F) (om (k, 1)) f fk →
      Acts (evI F) (om (k, 1)) f₁ h → ActsD (evI F) (M.heisLine B.ψ (mat k * u)) fk h := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k _ u hu f f₁ fk h hD hA hA₁
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨D, hDD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hψ
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.HeisDeriv.exists_heisLine_deriv M B.ψ hψ (mat k * u)
  have hg0 := GlobalTheory.ArchIsom.standard_vector_mem_schwartz_bruhat (F := F) (Fin n × Fin d)

  have hf₁ : (D u f : SInf F (Fin n × Fin d)) = f₁ := by
    refine SchwartzMap.ext fun z => ?_
    set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
    have a1 : HasDerivAt (fun t => M.heisLine B.ψ u t (tens (evI F) (⇑f) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x)
        (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d)) x) 0 :=
      (hDD u hu f).1 _ hg0 _ (proj_mem_adm x)
    have a2 := hD _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f) x
    have e := a1.unique a2
    rw [← GlobalTheory.ArchIsom.tensor_at_standard_point, tens_split, tens_split] at e
    exact e
  suffices e : h = D₁ fk by rw [e]; exact hD₁ fk
  refine SchwartzMap.ext fun z => ?_
  set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
  have hl := hS.adm (k, 1) _ (proj_mem_adm x)
  have b1 := (hDD u hu f).1 _ hg0 _ hl
  have hmem : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)) ∈ schA F (Fin n × Fin d) :=
    fun g => (GlobalTheory.ArchIsom.restriction_at_standard_point _ g).2
  have hfun : (fun t : ℝ => ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (M.co.rho B.ψ (realAd F t • u) (pureA F (⇑f) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))))) =
      fun t => M.heisLine B.ψ (mat k * u) t (tens (evI F) (⇑fk) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x := by
    funext t
    rw [LinearMap.comp_apply, LinearMap.proj_apply, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hS.impl (k, 1) _ _ (hmem f),
      hA _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)]
    have hw : actAB (cA σ) ((k, 1) : UA σ X.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat k * u) := by
      simp only [actAB, mat, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
    rw [hw]
    rfl
  have hval : ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))) = h z := by
    rw [LinearMap.comp_apply, LinearMap.proj_apply, hf₁, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hA₁ _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f₁),
      tens_split]
  rw [hfun, hval] at b1
  have b2 := hD₁ fk _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ fk) x
  rw [tens_split] at b2
  exact b1.unique b2
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitary_moves_heisenbergDerivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∀ f f₁ fk h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ → Acts (evI F) (om (k, 1)) f fk →
      Acts (evI F) (om (k, 1)) f₁ h → ActsD (evI F) (M.heisLine B.ψ (mat k * u)) fk h := by
  atlas_forward_decl GlobalTheory.KHeisComm.actsD_heisLine_mat_mul
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Matrix

namespace GlobalTheory.FockVacStab

theorem mat_mul_mat_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (k : UA σ X.J) : mat k * mat k⁻¹ = 1 ∧ mat k⁻¹ * mat k = 1 := by
  constructor
  · show (k * k⁻¹).1.1 = 1
    simp
  · show (k⁻¹ * k).1.1 = 1
    simp

theorem isGauss_of_acts : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f₀ hG f₁ hact
  have hPA := GlobalTheory.T.polynomial_datum_action_of_pair hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := GlobalTheory.T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff _ using hD
  obtain ⟨Dk, _, hDk⟩ := hPA.2.1 k hk
  have hGP : ∀ g, M.IsGauss B.ψ B.emb g → g ∈ M.Pol B.ψ B.emb := fun g h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 g h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hAt : ∀ (a : Matrix (Fin n) (Fin n) (AE F E)) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u →
      At (evI F) (a * u) := fun a u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨hkk, hkk'⟩ := mat_mul_mat_inv k

  have hcomm : ∀ w, (mat k⁻¹).map (piInf (B.emb w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
    intro w
    set A := (mat k).map (piInf (B.emb w))
    set A' := (mat k⁻¹).map (piInf (B.emb w))
    have h1 : A * A' = 1 := by
      rw [← Matrix.map_mul, hkk]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have h2 : A' * A = 1 := by
      rw [← Matrix.map_mul, hkk']; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hc : A * X.θ w = X.θ w * A := hk.2 w
    calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [h1, Matrix.mul_one]
      _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
      _ = A' * (A * X.θ w) * A' := by rw [hc]
      _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
      _ = X.θ w * A' := by rw [h2, Matrix.one_mul]
  obtain ⟨ε, hε⟩ := hG
  refine ⟨ε, fun u u' hu hu' huu' f f' hf hf' => ?_⟩
  set v := mat k⁻¹ * u
  set v' := mat k⁻¹ * u'
  have hv : At (evI F) v := hAt _ u hu
  have hv' : At (evI F) v' := hAt _ u' hu'
  have hvv' : ∀ w, v'.map (piInf (B.emb w)) =
      (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * v.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    simp only [v, v', Matrix.map_mul, huu' w, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm w]
  have hkv : mat k * v = u := by simp only [v, ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hkv' : mat k * v' = u' := by simp only [v', ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hgg : Dfun v' f₀ = Complex.I • Dfun v f₀ :=
    hε v v' hv hv' hvv' _ _ ((hDiff v hv f₀ _).2 rfl) ((hDiff v' hv' f₀ _).2 rfl)
  have hf0 : f₀ ∈ M.Pol B.ψ B.emb := hGP f₀ ⟨ε, hε⟩

  have hmove : ∀ x, At (evI F) x → ActsD (evI F) (M.heisLine B.ψ (mat k * x)) f₁ (Dk (Dfun x f₀)) := by
    intro x hx
    exact GlobalTheory.T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k hk x hx f₀ (Dfun x f₀) f₁ (Dk (Dfun x f₀))
      ((hDiff x hx f₀ _).2 rfl) hact ((hDk _ (hclos x hx f₀ hf0) _).2 rfl)
  have e1 : f = Dk (Dfun v f₀) := by
    have a := (hDiff u hu f₁ f).1 hf
    have b := (hDiff u hu f₁ _).1 (hkv ▸ hmove v hv)
    rw [a, b]
  have e2 : f' = Dk (Dfun v' f₀) := by
    have a := (hDiff u' hu' f₁ f').1 hf'
    have b := (hDiff u' hu' f₁ _).1 (hkv' ▸ hmove v' hv')
    rw [a, b]
  rw [e2, e1, hgg, map_smul]

end GlobalTheory.FockVacStab
end
