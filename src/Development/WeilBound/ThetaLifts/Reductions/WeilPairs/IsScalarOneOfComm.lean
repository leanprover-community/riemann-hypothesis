import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutTraceA
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutReal
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareOfApproximation
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutProd
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutGen
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSubst
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealChartAdeleTensorAdmissibleCMBaseStatement

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem gauss_mul_integral (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hbij : Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x))
    (hF : Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume) (κ : ℂ)
    (hκ : ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, Fixes (opFF hc w) (latF F E nS nT Λ) f → IsVacF σ JS JT ξ₀ B.ψ ι s f → ∀ x,
      (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = κ * ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x)
    (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (ht : ∀ k, b * t k * a - t k ∈ Λ)
    (hu : ∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) :
    ∃ r : ℝ, 0 < r ∧ (∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k)) *
      ∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v = r * κ :=
  Trc.gauss_mul_integral_A C hG hR hO hs ha hb hbij hF κ hκ n t ht hu

end PositivityTheory.ThKW

end
end

section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW.AutEtaA

section Abstract

variable {E : Type} [Field E] [NumberField E]

theorem hom_fix (Fx : HeightOneSpectrum (𝓞 E) → Prop) {G : Type} [CommGroup G]
    (w : HeightOneSpectrum (𝓞 E) → G →* WithZero (Multiplicative ℤ)) (i : Eˣ →* G) (ψ : G →* Circle)
    (lam : ℕ →* ℂ) (hi : ∀ Q k, w Q (i k) = Q.valuation E (k : E))
    (h1 : ∀ y, (∀ Q, Fx Q → w Q y = 1) → ψ y = 1)
    (h3 : ∀ P, Fx P → ∃ z, w P z = WithZero.exp (-1 : ℤ) ∧ (∀ Q, Q ≠ P → w Q z = 1) ∧ (ψ z : ℂ) = -1)
    (h5 : ∀ P : HeightOneSpectrum (𝓞 E), (Fx P →
        lam (Ideal.absNorm P.asIdeal) = -(Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)) ∧
      (¬ Fx P → lam (Ideal.absNorm P.asIdeal) = (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)))
    (u : 𝓞 E) (k : Eˣ) (hk : (k : E) = u) :
    lam (Ideal.absNorm (Ideal.span {u})) = (ψ (i k) : ℂ) * (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ) := by
  let Gen : Ideal (𝓞 E) → G → Prop := fun B y =>
    ∀ Q : HeightOneSpectrum (𝓞 E), Fx Q → w Q y = WithZero.exp (-multiplicity Q.asIdeal B : ℤ)
  have gmul : ∀ {A B y z}, A ≠ ⊥ → B ≠ ⊥ → Gen A y → Gen B z → Gen (A * B) (y * z) := by
    intro A B y z hA hB hy hz Q hQ
    rw [map_mul, hy Q hQ, hz Q hQ, GlobalTheory.EtaProduct.mult_mul Q hA hB, ← WithZero.exp_add]
    push_cast
    rw [neg_add]
  have guniq : ∀ {B y z}, Gen B y → Gen B z → ψ y = ψ z := by
    intro B y z hy hz
    have := h1 (y * z⁻¹) fun Q hQ => by
      rw [map_mul, map_inv, hy Q hQ, hz Q hQ, mul_inv_cancel₀ WithZero.exp_ne_zero]
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have gspan : ∀ (u : 𝓞 E) (k : Eˣ), (k : E) = u → Gen (Ideal.span {u}) (i k) := by
    intro u k hk Q _
    have hu : u ≠ 0 := by
      rintro rfl
      exact k.ne_zero (by simpa using hk)
    rw [hi, hk, GlobalTheory.EtaProduct.val_int Q hu]
  have gone : Gen ⊤ 1 := fun Q _ => by
    rw [map_one, ← Ideal.one_eq_top, multiplicity_eq_zero.2 Q.prime.not_dvd_one]
    simp
  have gmov : ∀ P : HeightOneSpectrum (𝓞 E), ¬ Fx P → Gen P.asIdeal 1 := fun P hP Q hQ => by
    rw [map_one, GlobalTheory.EtaProduct.mult_ne (P := P) (Q := Q) (fun h => hP (h ▸ hQ))]
    simp
  have gfix : ∀ (P : HeightOneSpectrum (𝓞 E)) z, w P z = WithZero.exp (-1 : ℤ) → (∀ Q, Q ≠ P → w Q z = 1) →
      Gen P.asIdeal z := by
    intro P z a1 a3 Q _
    by_cases hQ : Q = P
    · rw [hQ, a1, multiplicity_self]; simp
    · rw [a3 Q hQ, GlobalTheory.EtaProduct.mult_ne hQ]; simp
  have gprime : ∀ P : HeightOneSpectrum (𝓞 E), ∃ z, Gen P.asIdeal z := by
    intro P
    by_cases hP : Fx P
    · obtain ⟨z, a1, a3, -⟩ := h3 P hP
      exact ⟨z, gfix P z a1 a3⟩
    · exact ⟨1, gmov P hP⟩
  have gex : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∃ z, Gen B z := by
    intro B
    induction B using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ B hB => intro _; rw [Ideal.isUnit_iff.1 hB]; exact ⟨1, gone⟩
    | h₃ C P hC hP ih =>
      intro _
      obtain ⟨a, a1⟩ := gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
      obtain ⟨b, b1⟩ := ih hC
      exact ⟨a * b, gmul hP.ne_zero hC a1 b1⟩
  have vprime : ∀ (P : HeightOneSpectrum (𝓞 E)) y, Gen P.asIdeal y →
      lam (Ideal.absNorm P.asIdeal) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) := by
    intro P y hy
    by_cases hP : Fx P
    · obtain ⟨z, a1, a3, a4⟩ := h3 P hP
      rw [guniq hy (gfix P z a1 a3), a4, (h5 P).1 hP, neg_one_mul]
    · rw [guniq hy (gmov P hP), map_one, (h5 P).2 hP]
      simp
  have main : ∀ B : Ideal (𝓞 E), B ≠ ⊥ → ∀ y, Gen B y →
      lam (Ideal.absNorm B) = (ψ y : ℂ) * (Real.sqrt (Ideal.absNorm B) : ℂ) := by
    intro B
    induction B using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ B hB =>
      intro _ y hy
      rw [Ideal.isUnit_iff.1 hB] at hy ⊢
      rw [guniq hy gone, Ideal.absNorm_top, map_one, map_one]
      simp
    | h₃ C P hC hP ih =>
      intro _ y hy
      obtain ⟨a, a1⟩ := gprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
      obtain ⟨b, b1⟩ := gex C hC
      have v1 := vprime ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩ a a1
      rw [guniq hy (gmul hP.ne_zero hC a1 b1), map_mul, map_mul, map_mul, v1, ih hC b b1, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, Circle.coe_mul]
      ring
  refine main _ ?_ _ (gspan u k hk)
  rw [Ne, Ideal.span_singleton_eq_bot]
  rintro rfl
  exact k.ne_zero (by simpa using hk)

end Abstract

section Half

open GlobalTheory.SplitDetCharF

theorem exists_half_abstract' {F T T' : Type} [Field F] [NumberField F] [CommRing T] [CommRing T']
    (j : AF F →+* T) (c : T →+* T) (p : T →+* T') (δ : T) (d : 𝓞 F) (hd0 : (d : F) ≠ 0) (hinj : Function.Injective j)
    (hcj : ∀ a, c (j a) = j a) (hcδ : c δ = -δ) (hδ2 : δ * δ = j (algebraMap F (AF F) (d : F)))
    (hdec : ∀ z, ∃ a b, z = j a + j b * δ) (hinf : ∀ α, p (j (pairA F 0 α)) = 0) :
    ∃ (ε : T) (ι : Af F), ε * ε = ε ∧ ε * c ε = 0 ∧ p ε = 0 ∧ ε + c ε = j (pairA F 0 ι) ∧
      (∀ v, (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) (d : F))) ∨
        (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) (d : F)))) ∧
      ∀ e, (e * e = e ∧ e * c e = 0 ∧ ∃ v η, IsPlaceIdemF F v η ∧ e + c e = j η) →
        (ε * e = e ∧ ε * c e = 0) ∨ (ε * e = 0 ∧ ε * c e = c e) := by
  obtain ⟨s, ι, hsι⟩ := exists_sqrt_adele F d
  have hsq : ∀ v, (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) (d : F))) ∨
      (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) (d : F))) := fun v =>
    (hsι v).imp (fun h => ⟨h.1, ⟨_, h.2.symm⟩⟩) (fun h => ⟨h.1, fun ⟨r, hr⟩ => h.2.2 r hr.symm⟩)
  obtain ⟨h, hh⟩ : ∃ h : AF F, h * (2 * algebraMap F (AF F) (d : F)) = 1 := by
    have hd : (2 * (d : F)) ≠ 0 := mul_ne_zero two_ne_zero hd0
    have := congrArg (algebraMap F (AF F)) (inv_mul_cancel₀ hd)
    rw [map_mul, map_mul, map_ofNat, map_one] at this
    exact ⟨_, this⟩
  have hH : j h * (2 * j (algebraMap F (AF F) (d : F))) = 1 := by
    have := congrArg j hh
    rwa [map_mul, map_mul, map_ofNat, map_one] at this
  have hII : j (pairA _ 0 ι) * j (pairA _ 0 ι) = j (pairA _ 0 ι) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext' _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h <;> simp [h.1]
  have hIS : j (pairA _ 0 ι) * j (pairA _ 0 s) = j (pairA _ 0 s) := by
    rw [← map_mul, pair_mul]
    congr 2
    refine af_ext' _ fun w => ?_
    rw [map_mul]
    rcases hsι w with h | h
    · simp [h.1]
    · simp [h.2.1]
  have hSS : j (pairA _ 0 s) * j (pairA _ 0 s) = j (pairA _ 0 ι) * j (algebraMap F (AF F) (d : F)) := by
    rw [← map_mul, ← map_mul, pair_mul, pair_mul']
    congr 2
    refine af_ext' _ fun w => ?_
    rw [map_mul, map_mul, evalV_snd_algebraMap]
    rcases hsι w with h | h
    · rw [h.1, h.2, one_mul]
    · rw [h.1, h.2.1, zero_mul, zero_mul]
  obtain ⟨ε, hε⟩ : ∃ ε : T, ε = j h * (j (pairA _ 0 ι) * j (algebraMap F (AF F) (d : F)) - j (pairA _ 0 s) * δ) :=
    ⟨_, rfl⟩
  have hcε : c ε = j h * (j (pairA _ 0 ι) * j (algebraMap F (AF F) (d : F)) + j (pairA _ 0 s) * δ) := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hcj, hcj, hcj, hcj, hcδ]; ring
  have hinfε : p ε = 0 := by
    rw [hε, map_mul, map_sub, map_mul, map_mul, hinf, hinf]; simp
  generalize hI : j (pairA _ 0 ι) = I at hII hIS hSS hε hcε
  generalize hS : j (pairA _ 0 s) = S at hIS hSS hε hcε
  generalize hD : j (algebraMap F (AF F) (d : F)) = D at hH hSS hε hcε hδ2
  generalize hHH : j h = H at hH hε hcε
  have h2 : ε * c ε = 0 := by
    rw [hcε, hε]
    linear_combination H * H * D * D * hII - H * H * δ * δ * hSS - H * H * I * D * hδ2
  have h3 : ε + c ε = I := by
    rw [hcε, hε]
    linear_combination I * hH
  have h4 : I * ε = ε := by
    rw [hε]
    linear_combination H * D * hII - H * δ * hIS
  have h1 : ε * ε = ε := by
    linear_combination ε * h3 - h2 + h4
  refine ⟨ε, ι, h1, h2, hinfε, h3.trans hI.symm, hsq, ?_⟩
  rintro e ⟨he1, he2, v, η, ⟨α, rfl, hα1, hα0⟩, he3⟩
  obtain ⟨a, b, hab⟩ := hdec e
  have hce : c e = j a - j b * δ := by
    rw [hab, map_add, map_mul, hcj, hcj, hcδ]; ring
  have he4 : c e * c e = c e := by rw [← map_mul, he1]
  obtain ⟨B, hB⟩ : ∃ B : AF F, B = 2 * algebraMap F (AF F) (d : F) * b := ⟨_, rfl⟩
  have hjB : j B = δ * (e - c e) := by
    rw [hB, map_mul, map_mul, map_ofNat, hD, hce]
    linear_combination -δ * hab - 2 * j b * hδ2
  have hB1 : pairA _ 0 α * B = B := hinj (by
    rw [map_mul, ← he3, hjB]
    linear_combination δ * he1 - δ * he4)
  have hB2 : B * B = pairA _ 0 α * algebraMap F (AF F) (d : F) := hinj (by
    rw [map_mul, map_mul, hD, ← he3, hjB]
    linear_combination δ * δ * he1 + δ * δ * he4 - 2 * δ * δ * he2 + (e + c e) * hδ2)
  have hB3 : evalV _ v (sndA _ B) * evalV _ v (sndA _ B) = algebraMap F (Fv F v) (d : F) := by
    rw [← map_mul, ← map_mul, hB2, map_mul, map_mul, evalV_snd_algebraMap]
    change evalV _ v α * _ = _
    rw [hα1, one_mul]
  rcases hsι v with ⟨hι, hs⟩ | ⟨-, -, hn⟩
  swap
  · exact absurd hB3 (hn _)
  have hNI : (e + c e) * I = e + c e := by
    rw [he3, ← hI, ← map_mul, pair_mul, place_ext _ hα0 (y := 1) (by rw [hι, map_one]), mul_one]
  rcases mul_self_eq_mul_self_iff.1 (hB3.trans hs.symm) with hp | hp
  · right
    have : j B = (e + c e) * S := by
      rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', place_ext _ hα0 hp]
    have h5 : c e = (e + c e) * ε := by
      rw [hε]
      linear_combination -H * D * hNI - H * δ * this + H * δ * hjB + H * (e - c e) * hδ2 - c e * hH
    constructor
    · linear_combination -e * h5 + (1 - ε) * he2 - ε * he1
    · linear_combination -(c e) * h5 + (1 - ε) * he4 - ε * he2
  · left
    have : j B = -((e + c e) * S) := by
      rw [he3, ← hS, ← map_mul, ← hB1, pair_mul, pair_mul', ← map_neg, pair_neg, ← mul_neg,
        place_ext _ hα0 (y := -s) (by rw [hp, map_neg])]
    have h5 : e = (e + c e) * ε := by
      rw [hε]
      linear_combination -H * D * hNI + H * δ * this - H * δ * hjB - H * (e - c e) * hδ2 - e * hH
    constructor
    · linear_combination -e * h5 + (1 - ε) * he1 - ε * he2
    · linear_combination -(c e) * h5 + (1 - ε) * he2 - ε * he4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_half {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : 𝓞 F) (ε : AEF F E) (ι : Af F), (d : F) ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E (d : F) ∧
      (∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ) ∧
      ε * ε = ε ∧ ε * cAF σ ε = 0 ∧ infPartF F E ε = 0 ∧ ε + cAF σ ε = algebraMap (AF F) (AEF F E) (pairA F 0 ι) ∧
      (∀ v, (evalV F v ι = 1 ∧ IsSquare (algebraMap F (Fv F v) (d : F))) ∨
        (evalV F v ι = 0 ∧ ¬ IsSquare (algebraMap F (Fv F v) (d : F)))) ∧
      ∀ e, IsSplitIdemF σ e → (ε * e = e ∧ ε * cAF σ e = 0) ∨ (ε * e = 0 ∧ ε * cAF σ e = cAF σ e) := by
  obtain ⟨θ, d, hd0, hσθ, hθθ, hdec⟩ := exists_int_basis h
  have hs : ∀ (a : AF F) (x : E), cAF σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := fun _ _ => rfl
  obtain ⟨ε, ι, h1, h2, h3, h5, h6, h4⟩ := exists_half_abstract' (algebraMap (AF F) (AEF F E)) (cAF σ) (infPartF F E)
    ((1 : AF F) ⊗ₜ[F] θ) d hd0 tensor_inj
    (fun a => by
      rw [Algebra.TensorProduct.algebraMap_apply, hs, map_one])
    (by rw [hs, hσθ, TensorProduct.tmul_neg])
    (by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hθθ, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one (A := AF F),
        TensorProduct.smul_tmul']
      congr 1
      exact (algebraMap_smul (AF F) (d : F) (1 : AF F)).symm)
    (tensor_decomp θ hdec)
    (fun α => by
      show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (algebraMap (AF F) (AEF F E) (pairA F 0 α)) = 0
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, Algebra.algebraMap_self,
        RingHom.id_apply, show fstA F (pairA F 0 α) = 0 from rfl, TensorProduct.zero_tmul])
  exact ⟨θ, d, ε, ι, hd0, hσθ, hθθ, hdec, h1, h2, h3, h5, h6, fun e he => h4 e he⟩

end Half

end PositivityTheory.ThKW.AutEtaA

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.LiftF Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.AutEtaA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Ev

variable (F E) in

def ev (Q : HeightOneSpectrum (𝓞 E)) : AEF F E →+* Q.adicCompletion E :=
  ((evalV E Q).toRingHom.comp (GlobalTheory.LFun.finAdEquiv F E).toRingHom).comp (finPartF F E)

theorem ev_tmul (Q : HeightOneSpectrum (𝓞 E)) (a : AF F) (x : E) :
    ev F E Q (a ⊗ₜ[F] x) = complMap rfl ((sndA F a) (Q.under (𝓞 F))) * algebraMap E _ x := rfl

theorem ev_inc (Q : HeightOneSpectrum (𝓞 E)) (x : E) : ev F E Q (incAF F E x) = algebraMap E _ x := by
  have : incAF F E x = (1 : AF F) ⊗ₜ[F] x := rfl
  rw [this, ev_tmul, map_one]
  erw [map_one, one_mul]

theorem ev_alg (Q : HeightOneSpectrum (𝓞 E)) (a : AF F) :
    ev F E Q (algebraMap (AF F) (AEF F E) a) = complMap rfl ((sndA F a) (Q.under (𝓞 F))) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, ev_tmul, map_one, mul_one]

variable (F E) in

def wv (Q : HeightOneSpectrum (𝓞 E)) : (AEF F E)ˣ →* WithZero (Multiplicative ℤ) :=
  ((Valued.v (R := Q.adicCompletion E)).toMonoidWithZeroHom.toMonoidHom.comp (ev F E Q).toMonoidHom).comp
    (Units.coeHom _)

theorem wv_apply (Q : HeightOneSpectrum (𝓞 E)) (y : (AEF F E)ˣ) : wv F E Q y = Valued.v (ev F E Q y) := rfl

theorem wv_inc (Q : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    wv F E Q (Units.map (incAF F E).toMonoidHom k) = Q.valuation E (k : E) := by
  rw [wv_apply]
  change Valued.v (ev F E Q (incAF F E (k : E))) = _
  rw [ev_inc]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q (k : E)

theorem int_iff (y : AEF F E) : finPartF F E y ∈ intAEF F E ↔ ∀ Q, Valued.v (ev F E Q y) ≤ 1 :=
  GlobalTheory.LFun.mem_int_iff (finPartF F E y)

end Ev

section Fix

variable {σ : E →ₐ[F] E}

variable (σ) in

def Fx (Q : HeightOneSpectrum (𝓞 E)) : Prop := ∀ r ∈ Q.asIdeal, sgOF σ r ∈ Q.asIdeal

theorem sgOF_sgOF (h : IsCMExt F E σ) (x : 𝓞 E) : sgOF σ (sgOF σ x) = x :=
  RingOfIntegers.ext (GlobalTheory.SplitDetCharF.sig_invol h (x : E))

theorem sgOF_alg (a : 𝓞 F) : sgOF σ (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a :=
  RingOfIntegers.ext (σ.commutes (a : F))

theorem isSplit_of_not_fx (h : IsCMExt F E σ) {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Fx σ Q) :
    Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (Q.under (𝓞 F)) := by
  have hne : Q.asIdeal.comap (sgOF σ) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    intro hb
    have : sgOF σ x ∈ Q.asIdeal.comap (sgOF σ) := by
      show sgOF σ (sgOF σ x) ∈ Q.asIdeal
      rw [sgOF_sgOF h]; exact hx
    rw [hb, Ideal.mem_bot] at this
    exact hx0 (by rw [← sgOF_sgOF h x, this, map_zero])
  let Q' : HeightOneSpectrum (𝓞 E) := ⟨Q.asIdeal.comap (sgOF σ), Ideal.comap_isPrime _ _, hne⟩
  refine GlobalTheory.LFun.isSplit_iff.2 ⟨Q', Q, fun e => hQ fun r hr => ?_, ?_, rfl⟩
  · have : r ∈ Q'.asIdeal := by rw [e]; exact hr
    exact this
  · refine HeightOneSpectrum.ext ?_
    show (Q.asIdeal.comap (sgOF σ)).comap (algebraMap (𝓞 F) (𝓞 E)) = Q.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    rw [Ideal.comap_comap]
    congr 1
    exact RingHom.ext sgOF_alg

theorem isQuad (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ) :
    GlobalTheory.QNorm.IsQuad (d : F) θ
      (AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h)) (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h))) := by
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm, map_eq_zero] at hθθ
    exact hd0 hθθ
  refine ⟨fun ⟨r, hr⟩ => ?_, by rw [pow_two, hθθ], hσθ, fun x => ?_⟩
  · have h1 : θ * θ = algebraMap F E r * algebraMap F E r := by rw [hθθ, hr, map_mul]
    rcases mul_self_eq_mul_self_iff.1 h1 with h2 | h2
    · have := hσθ
      rw [h2, AlgHom.commutes] at this
      have h4 : (2 : E) * algebraMap F E r = 0 := by linear_combination this
      rcases mul_eq_zero.1 h4 with h3 | h3
      · exact two_ne_zero h3
      · exact hθ0 (h2.trans h3)
    · have := hσθ
      rw [h2, map_neg, AlgHom.commutes, neg_neg] at this
      have h4 : (2 : E) * algebraMap F E r = 0 := by linear_combination -this
      rcases mul_eq_zero.1 h4 with h3 | h3
      · exact two_ne_zero h3
      · exact hθ0 (by rw [h2, h3, neg_zero])
  · obtain ⟨u, w, e⟩ := hdec x
    exact ⟨u, w, by rw [e, Algebra.smul_def, Algebra.smul_def, mul_one]⟩

theorem not_sq_of_fx (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : Fx σ Q) : ¬ IsSquare (algebraMap F (Fv F (Q.under (𝓞 F))) (d : F)) := by
  let σe : E ≃ₐ[F] E :=
    AlgEquiv.ofAlgHom σ σ (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h)) (AlgHom.ext (GlobalTheory.SplitDetCharF.sig_invol h))
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (σe : E ≃+* E)
  have hs : ∀ x, ((s x : 𝓞 E) : E) = σe x := fun _ => rfl
  have hsg : ∀ x, s x = sgOF σ x := fun _ => rfl
  refine GlobalTheory.FixedPrimeNorm.not_isSquare_of_fixed (isQuad h hd0 hσθ hθθ hdec) s hs Q (le_antisymm ?_ ?_)
  · refine Ideal.map_le_iff_le_comap.2 fun r hr => ?_
    show s r ∈ Q.asIdeal
    rw [hsg]; exact hQ r hr
  · intro x hx
    have : x = s (sgOF σ x) := by rw [hsg, sgOF_sgOF h]
    rw [this]
    exact Ideal.mem_map_of_mem _ (hQ x hx)

theorem sq_of_split (h : IsCMExt F E σ) {θ : E} {d : 𝓞 F} (hd0 : (d : F) ≠ 0) (hσθ : σ θ = -θ)
    (hθθ : θ * θ = algebraMap F E (d : F)) (hdec : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    IsSquare (algebraMap F (Fv F v) (d : F)) :=
  _root_.UpperTheory.Reformulated.B.SquareOfApproximation.main h hd0 hσθ hθθ hdec hv

end Fix

end PositivityTheory.ThKW.AutEtaA

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
open Formalism.IndefR.LiftF Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.AutEtaA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Idem

variable (F E) in

def rI : AEF F E := algebraMap (AF F) (AEF F E) (pairA F 1 0)

theorem rI_idem : rI F E * rI F E = rI F E := by
  rw [rI, ← map_mul]
  congr 1
  exact Prod.ext (mul_one _) (mul_zero _)

theorem rI_mul_fin (ι : Af F) : rI F E * algebraMap (AF F) (AEF F E) (pairA F 0 ι) = 0 := by
  rw [rI, ← map_mul, show pairA F 1 0 * pairA F 0 ι = 0 from Prod.ext (mul_zero _) (zero_mul _), map_zero]

theorem infPart_rI : infPartF F E (rI F E) = 1 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 1 0 ⊗ₜ 1) = 1
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 1 0) = 1 from rfl, AlgHom.id_apply]
  rfl

theorem infPart_fin (ι : Af F) : infPartF F E (algebraMap (AF F) (AEF F E) (pairA F 0 ι)) = 0 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 0 ι ⊗ₜ 1) = 0
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 0 ι) = 0 from rfl, TensorProduct.zero_tmul]

theorem ev_rI (Q : HeightOneSpectrum (𝓞 E)) : ev F E Q (rI F E) = 0 := by
  rw [rI, ev_alg]
  exact map_zero _

theorem ev_fin (Q : HeightOneSpectrum (𝓞 E)) (ι : Af F) :
    ev F E Q (algebraMap (AF F) (AEF F E) (pairA F 0 ι)) = complMap rfl (evalV F (Q.under (𝓞 F)) ι) := by
  rw [ev_alg]
  rfl

theorem piInf_inc {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (incAF F E x) = τ.1 x := by
  change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [show compInf F E w ((1 : AF F) ⊗ₜ[F] x) = evInf F w 1 ⊗ₜ[F] x from rfl, infEmb_tmul, map_one, map_one, one_mul]

theorem piInf_rI {w : InfinitePlace F} (τ : EmbOver E w) : piInf τ (rI F E) = 1 := by
  have h1 : piInf τ (rI F E + algebraMap (AF F) (AEF F E) (pairA F 0 1)) = 1 := by
    rw [rI, ← map_add, show pairA F 1 0 + pairA F 0 1 = 1 from Prod.ext (add_zero _) (zero_add _), map_one, map_one]
  have h2 : piInf τ (algebraMap (AF F) (AEF F E) (pairA F 0 1)) = 0 := by
    change infEmb τ (compInf F E w (pairA F 0 1 ⊗ₜ[F] (1 : E))) = _
    rw [show compInf F E w (pairA F 0 1 ⊗ₜ[F] (1 : E)) = evInf F w (pairA F 0 1) ⊗ₜ[F] (1 : E) from rfl,
      show evInf F w (pairA F 0 1) = 0 from map_zero (GlobalTheory.AutFunCompare.evW w), TensorProduct.zero_tmul, map_zero]
  rw [map_add, h2, add_zero] at h1
  exact h1

end Idem

section Main

theorem eta_real {B : Base F E} {η : (AEF F E)ˣ →* Circle} (h3 : HasExp B.emb η (fun _ => 1)) (t : (AEF F E)ˣ) :
    (η (GlobalTheory.InertTrivial.proj (rI F E) rI_idem t) : ℂ) =
      ∏ w, piInf (B.emb w) (t : AEF F E) / (‖piInf (B.emb w) (t : AEF F E)‖ : ℂ) := by
  have hAt : At (evI F) (((GlobalTheory.InertTrivial.proj (rI F E) rI_idem t : (AEF F E)ˣ) : AEF F E) - 1) := by
    intro u hu
    have hu1 : u.1 = 0 := (RingEquiv.map_eq_zero_iff (InfiniteAdeleRing.ringEquiv_mixedSpace F)).1 hu
    have h0 : algebraMap (AF F) (AEF F E) u * rI F E = 0 := by
      rw [rI, ← map_mul, show u * pairA F 1 0 = 0 from Prod.ext (show u.1 * 1 = 0 by rw [hu1, zero_mul])
        (show u.2 * 0 = 0 from mul_zero _), map_zero]
    rw [GlobalTheory.InertTrivial.proj_val, Algebra.smul_def]
    linear_combination ((t : AEF F E) - 1) * h0
  rw [h3 _ hAt]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hpi : piInf (B.emb w) ((GlobalTheory.InertTrivial.proj (rI F E) rI_idem t : (AEF F E)ˣ) : AEF F E) =
      piInf (B.emb w) (t : AEF F E) := by
    rw [GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub, map_one, piInf_rI]
    ring
  rw [zpow_one, hpi]

set_option maxHeartbeats 1000000 in
theorem exists_half_character_eta_product {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {η : (AEF F E)ˣ →* Circle}
    (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1) (h3 : HasExp B.emb η (fun _ => 1)) (h4 : UnramInert σ η)
    {lam : ℕ →* ℂ} (hlam : GoodNorm (sgOF σ) lam)
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) :
    ∃ ε, IsHalfF σ ε ∧ ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ v, tauB B v x = r := by
  have hcm := hB.cm
  have : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  have := hB.unram
  obtain ⟨θ, d, ε, ι, hd0, hσθ, hθθ, hdec, e1, e2, e3, e4, e5, e6⟩ := exists_half hcm
  refine ⟨ε, ⟨e1, e2, e3, e6⟩, ?_⟩
  set J := algebraMap (AF F) (AEF F E) (pairA F 0 ι) with hJdef
  have hc2 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, e1]
  have hJ : J * J = J := by rw [← e4]; linear_combination e1 + hc2 + 2 * e2
  have hrJ : rI F E * J = 0 := rI_mul_fin ι
  have hf : (1 - rI F E - J) * (1 - rI F E - J) = 1 - rI F E - J := by
    linear_combination hJ + rI_idem (F := F) (E := E) + 2 * hrJ
  have evJ : ∀ Q : HeightOneSpectrum (𝓞 E), (Fx σ Q → ev F E Q J = 0) ∧ (¬ Fx σ Q → ev F E Q J = 1) := by
    intro Q
    rw [hJdef, ev_fin]
    rcases e5 (Q.under (𝓞 F)) with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · exact ⟨fun hQ => absurd h6 (not_sq_of_fx hcm hd0 hσθ hθθ hdec hQ), fun _ => by rw [h5, map_one]⟩
    · exact ⟨fun _ => by rw [h5, map_zero],
        fun hQ => absurd (sq_of_split hcm hd0 hσθ hθθ hdec (isSplit_of_not_fx hcm hQ)) h6⟩
  have hker : ∀ y : (AEF F E)ˣ, (∀ Q, Fx σ Q → wv F E Q y = 1) → (η.comp (GlobalTheory.InertTrivial.proj _ hf)) y = 1 := by
    intro y hy
    have hint : ∀ z : (AEF F E)ˣ, (∀ Q, Fx σ Q → wv F E Q z = 1) →
        finPartF F E (GlobalTheory.InertTrivial.proj _ hf z : AEF F E) ∈ intAEF F E := by
      intro z hz
      refine (int_iff _).2 fun Q => ?_
      have hevf : ev F E Q (1 - rI F E - J) = 1 - ev F E Q J := by rw [map_sub, map_sub, map_one, ev_rI, sub_zero]
      rw [GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub (ev F E Q) 1, map_one, hevf]
      by_cases hQ : Fx σ Q
      · rw [(evJ Q).1 hQ]
        simp only [sub_zero, one_mul, sub_self, add_zero]
        exact le_of_eq (hz Q hQ)
      · rw [(evJ Q).2 hQ]
        simp
    have hinf : infPartF F E (1 - rI F E - J) = 0 := by
      rw [map_sub, map_sub, map_one, infPart_rI, hJdef, infPart_fin]
      ring
    refine h4 _ ?_ ?_ (hint y hy) ?_
    · rw [GlobalTheory.InertTrivial.proj_val, map_add, map_mul, map_sub (infPartF F E) 1 (1 - rI F E - J), hinf, map_one]
      ring
    · intro e he
      have hcc : ∀ z, cAF σ (cAF σ z) = z := GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hcm)
      have heJ : e * J = e := by
        rw [← e4]
        rcases e6 e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
        · have : e * cAF σ ε = 0 := by
            have := congrArg (cAF σ) a2
            rwa [map_mul, hcc, map_zero, mul_comm] at this
          linear_combination a1 + this
        · have : e * cAF σ ε = e := by
            have := congrArg (cAF σ) a2
            rwa [map_mul, hcc, mul_comm] at this
          linear_combination a1 + this
      obtain ⟨he1, he2, v, ε', ⟨α, hα, -, -⟩, he3⟩ := he
      have her : e * rI F E = 0 := by
        have h0 : e = e * algebraMap (AF F) (AEF F E) ε' := by rw [← he3]; linear_combination -he1 - he2
        rw [h0, mul_assoc, mul_comm (algebraMap _ _ ε'), hα, rI_mul_fin, mul_zero]
      rw [GlobalTheory.InertTrivial.proj_val]
      linear_combination (1 - (y : AEF F E)) * her + (1 - (y : AEF F E)) * heJ
    · rw [← map_inv]
      exact hint _ fun Q hQ => by rw [map_inv, hy Q hQ, inv_one]
  have hgen : ∀ P, Fx σ P → ∃ z, wv F E P z = WithZero.exp (-1 : ℤ) ∧ (∀ Q, Q ≠ P → wv F E Q z = 1) ∧
      ((η.comp (GlobalTheory.InertTrivial.proj _ hf)) z : ℂ) = -1 := by
    intro P hP
    have hns : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (P.under (𝓞 F)) := fun hs =>
      not_sq_of_fx hcm hd0 hσθ hθθ hdec hP (sq_of_split hcm hd0 hσθ hθθ hdec hs)
    have hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (P.under (𝓞 F)) :=
      GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
    let π : (Fv F (P.under (𝓞 F)))ˣ := Formalism.L2.Host.atFin (P.under (𝓞 F)) (Formalism.L2.Host.unif (P.under (𝓞 F)))
    let a : (AF F)ˣ := Neutral.B1.localIdele F (P.under (𝓞 F)) π
    have ha1 : (a : AF F).2 (P.under (𝓞 F)) = π := Neutral.B1.localIdele_snd_self F (P.under (𝓞 F)) π
    have ha2 : ∀ u, u ≠ P.under (𝓞 F) → (a : AF F).2 u = 1 := fun u hu' => Pi.mulSingle_eq_of_ne hu' _
    have hι : evalV F (P.under (𝓞 F)) ι = 0 := by
      rcases e5 (P.under (𝓞 F)) with ⟨-, h6⟩ | ⟨h5, -⟩
      · exact absurd h6 (not_sq_of_fx hcm hd0 hσθ hθθ hdec hP)
      · exact h5
    refine ⟨idFF F E a, ?_, fun Q hQ => ?_, ?_⟩
    · rw [wv_apply]
      change Valued.v (ev F E P (algebraMap (AF F) (AEF F E) (a : AF F))) = _
      rw [ev_alg]
      change Valued.v (complMap rfl ((a : AF F).2 (P.under (𝓞 F)))) = _
      rw [ha1, valued_complMap rfl π.ne_zero, GlobalTheory.LFun.isUnram_iff.1 hu P rfl, pow_one]
      exact Formalism.L2.Host.unif_spec (P.under (𝓞 F))
    · have hQv : Q.under (𝓞 F) ≠ P.under (𝓞 F) := fun h => hQ (GlobalTheory.LFun.eq_of_not_isSplit hns h rfl)
      rw [wv_apply]
      change Valued.v (ev F E Q (algebraMap (AF F) (AEF F E) (a : AF F))) = _
      rw [ev_alg]
      change Valued.v (complMap rfl ((a : AF F).2 (Q.under (𝓞 F)))) = _
      rw [ha2 _ hQv, map_one, map_one]
    · have hsnd : (0 + ι) * ((a : AF F).2 - 1) = 0 := by
        refine GlobalTheory.SplitDetCharF.af_ext' F fun u => ?_
        rw [map_mul, map_sub, map_one, map_add, map_zero, zero_add]
        by_cases hu' : u = P.under (𝓞 F)
        · rw [hu', hι, zero_mul]
        · rw [show evalV F u (a : AF F).2 = 1 from ha2 u hu', sub_self, mul_zero]
      have hprod : (pairA F 1 0 + pairA F 0 ι) * ((a : AF F) - 1) = 0 :=
        Prod.ext (show (1 + 0) * ((a : AF F).1 - 1) = 0 by
          rw [show (a : AF F).1 = 1 from rfl]; ring) hsnd
      have hz : (rI F E + J) * (algebraMap (AF F) (AEF F E) (a : AF F) - 1) = 0 := by
        rw [rI, hJdef, ← map_add, ← map_one (algebraMap (AF F) (AEF F E)), ← map_sub, ← map_mul, hprod, map_zero]
      have hpz : GlobalTheory.InertTrivial.proj _ hf (idFF F E a) = idFF F E a := by
        refine Units.ext ?_
        rw [GlobalTheory.InertTrivial.proj_val]
        change (1 - rI F E - J) * algebraMap (AF F) (AEF F E) (a : AF F) + (1 - (1 - rI F E - J)) =
          algebraMap (AF F) (AEF F E) (a : AF F)
        linear_combination -hz
      show ((η (GlobalTheory.InertTrivial.proj _ hf (idFF F E a)) : Circle) : ℂ) = -1
      rw [hpz]
      obtain ⟨⟨η₀, h0⟩, hres⟩ := h2
      rw [hres η₀ h0 a, pow_one, GlobalTheory.EtaSignReal.eq_signToCircle η₀ h0, MonoidHom.comp_apply,
        GlobalTheory.LFun.normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.2
          (GlobalTheory.LFun.not_mem_normGroup_of_inert hcm.2.2.1 hns hu (Formalism.L2.Host.unif_spec (P.under (𝓞 F))))]
      change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = -1
      rw [if_neg (by decide)]
      simp
  have hlamP : ∀ P : HeightOneSpectrum (𝓞 E),
      (Fx σ P → lam (Ideal.absNorm P.asIdeal) = -(Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)) ∧
      (¬ Fx σ P → lam (Ideal.absNorm P.asIdeal) = (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ)) := fun P =>
    ⟨fun hP => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      exact ((hlam.2 P.asIdeal P.isMaximal (Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot)).2 hP).1,
    fun hP => hsq _ (fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) fun q hq hi hd =>
      hP (hi P.asIdeal P.isMaximal (GlobalTheory.EtaProduct.mem_of_dvd_absNorm P hq hd))⟩
  have lam_int : ∀ (u : 𝓞 E) (k : Eˣ), (k : E) = u → lam (Ideal.absNorm (Ideal.span {u})) =
      ((η.comp (GlobalTheory.InertTrivial.proj _ hf)) (Units.map (incAF F E).toMonoidHom k) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {u})) : ℂ) :=
    fun u k hk => hom_fix (Fx σ) (wv F E) (Units.map (incAF F E).toMonoidHom) (η.comp (GlobalTheory.InertTrivial.proj _ hf)) lam
      (fun Q k => wv_inc Q k) hker hgen hlamP u k hk
  have product : ∀ k : Eˣ, (η (GlobalTheory.InertTrivial.proj J hJ (Units.map (incAF F E).toMonoidHom k)) : ℂ) *
      ((η.comp (GlobalTheory.InertTrivial.proj _ hf)) (Units.map (incAF F E).toMonoidHom k) : ℂ) *
      ∏ w, tauB B w k / (‖tauB B w k‖ : ℂ) = 1 := by
    intro k
    have e0 := congrArg η (GlobalTheory.EtaProduct.proj_three (rI_idem (F := F) (E := E)) hJ hrJ hf
      (Units.map (incAF F E).toMonoidHom k))
    rw [h1.2 k, η.map_mul, η.map_mul] at e0
    have e1' := congrArg (fun z : Circle => (z : ℂ)) e0
    simp only [Circle.coe_mul, Circle.coe_one] at e1'
    have er := eta_real h3 (Units.map (incAF F E).toMonoidHom k)
    have hk' : ((Units.map (incAF F E).toMonoidHom k : (AEF F E)ˣ) : AEF F E) = incAF F E (k : E) := rfl
    rw [hk'] at er
    simp only [piInf_inc] at er
    rw [show ∏ w, tauB B w k / (‖tauB B w k‖ : ℂ) =
      (η (GlobalTheory.InertTrivial.proj (rI F E) rI_idem (Units.map (incAF F E).toMonoidHom k)) : ℂ) from er.symm]
    exact e1'.symm
  intro x k hx hk y hy
  obtain ⟨u, z, hz, e⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hzE : (z : E) ≠ 0 := by simpa using hz0
  have e' : x * (z : E) = u := by rw [← e]; exact div_mul_cancel₀ _ hzE
  have huE : (u : E) ≠ 0 := e' ▸ mul_ne_zero hx hzE
  have hN : ∀ a : 𝓞 E, ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℚ) = |Algebra.norm ℚ (a : E)| := fun a => by
    rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]
  have hk' : k * Ideal.absNorm (Ideal.span {z}) = Ideal.absNorm (Ideal.span {u}) := by
    have : ((k * Ideal.absNorm (Ideal.span {z}) : ℕ) : ℚ) = (Ideal.absNorm (Ideal.span {u}) : ℕ) := by
      rw [Nat.cast_mul, hN, hN, hk, ← e', map_mul, abs_mul]
    exact_mod_cast this
  have nz : Ideal.absNorm (Ideal.span {z}) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using hz0
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx (by simpa using hk.symm)
  have l1 := lam_int u (Units.mk0 _ huE) rfl
  have l2 := lam_int z (Units.mk0 _ hzE) rfl
  have eu : Units.mk0 _ huE = Units.mk0 x hx * Units.mk0 _ hzE := Units.ext e'.symm
  rw [← hk', map_mul, l2, eu, map_mul, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul,
    Circle.coe_mul] at l1
  have l3 : lam k = ((η.comp (GlobalTheory.InertTrivial.proj _ hf)) (Units.map (incAF F E).toMonoidHom (Units.mk0 x hx)) : ℂ) *
      (Real.sqrt k : ℂ) := by
    refine mul_right_cancel₀ (l2 ▸ hlam.1 _ nz) (l1.trans ?_)
    ring
  have p := product (Units.mk0 x hx)
  have ey : GlobalTheory.InertTrivial.proj J hJ (Units.map (incAF F E).toMonoidHom (Units.mk0 x hx)) = y :=
    Units.ext (by rw [GlobalTheory.InertTrivial.proj_val, hy, e4]; rfl)
  rw [ey, Units.val_mk0, Finset.prod_div_distrib, ← Complex.ofReal_prod] at p
  have hp : 0 < ∏ w, ‖tauB B w x‖ := Finset.prod_pos fun w _ => norm_pos_iff.2 ((map_ne_zero _).2 hx)
  refine ⟨Real.sqrt k * ∏ w, ‖tauB B w x‖, mul_pos (Real.sqrt_pos.2 (by positivity)) hp, ?_⟩
  have hp' : ((∏ w, ‖tauB B w x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [← mul_div_assoc, div_eq_one_iff_eq hp'] at p
  rw [l3, Complex.ofReal_mul, ← p]
  ring

end Main

end PositivityTheory.ThKW.AutEtaA

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem eta_prod (hB : B.IsGood σ) {η : (AEF F E)ˣ →* Circle} (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1)
    (h3 : HasExp B.emb η (fun _ => 1)) (h4 : UnramInert σ η) (hlam : GoodNorm (sgOF σ) lam)
    (hsq : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) :
    ∃ ε, IsHalfF σ ε ∧ ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ v, tauB B v x = r :=
  AutEtaA.exists_half_character_eta_product hB h1 h2 h3 h4 hlam hsq

end PositivityTheory.ThKW

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

variable (σ JS JT) in

def substF (p : GAF σ JS × GAF σ JT) : Module.End ℂ (WOF F E nS nT → ℂ) :=
  LinearMap.funLeft ℂ ℂ (actOF σ JS JT p.1⁻¹ p.2⁻¹)

theorem substF_apply (p : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ) :
    substF σ JS JT p f = fun x => f (actOF σ JS JT p.1⁻¹ p.2⁻¹ x) := rfl

theorem substF_mul (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ) :
    substF σ JS JT (p * q) f = substF σ JS JT p (substF σ JS JT q f) := by
  funext x
  show f (actOF σ JS JT (p.1 * q.1)⁻¹ (p.2 * q.2)⁻¹ x) = f (actOF σ JS JT q.1⁻¹ q.2⁻¹ (actOF σ JS JT p.1⁻¹ p.2⁻¹ x))
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, actOF_mul]

theorem substF_one (f : WOF F E nS nT → ℂ) : substF σ JS JT 1 f = f := by
  funext x
  show f (actOF σ JS JT 1⁻¹ 1⁻¹ x) = f x
  rw [inv_one, inv_one, GlobalTheory.FinLatF.actOF_one]

variable (ξ₀ B of oi) in

def IsScalarF (p : GAF σ JS × GAF σ JT) (c : ℂ) : Prop :=
  ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi p f) = c • substF σ JS JT p f

theorem exists_partsF (p : GAF σ JS × GAF σ JT) : ∃ a k : GAF σ JS × GAF σ JT, a.1 ∈ GinfCF σ JS ∧ a.2 ∈ GinfCF σ JT ∧
    k.1 ∈ GfCF σ JS ∧ k.2 ∈ GfCF σ JT ∧ p = a * k ∧ p = k * a := by
  obtain ⟨a, ha, k, hk, e1, e1'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nS JS p.1
  obtain ⟨b, hb, l, hl, e2, e2'⟩ := GlobalTheory.T.unitaryAdelicPoint_eq_real_mul_finite_both_orders F E σ nT JT p.2
  exact ⟨(a, b), (k, l), ha, hb, hk, hl, Prod.ext e1 e2, Prod.ext e1' e2'⟩

theorem exists_isScalarF (C : Ctx σ B JS JT ξ₀ θ ι) {χS χT : (AEF F E)ˣ →* Circle}
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ χS χT of) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    {p : GAF σ JS × GAF σ JT} (h1 : p.1 ∈ GQF σ JS) (h2 : p.2 ∈ GQF σ JT) : ∃ c : ℂ, ‖c‖ = 1 ∧ IsScalarF B ξ₀ of oi p c := by
  have R := fun f h => rat_subst C (inv_mem h1) (inv_mem h2) (f := f) h
  have R' := fun f h => rat_subst C h1 h2 (f := f) h
  obtain ⟨a, k, a1, a2, k1, k2, e1, e2⟩ := exists_partsF p
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi p f = oi a f := fun f h => by
    rw [e1, map_mul, Module.End.mul_apply, hi.triv k.1 k1 k.2 k2 f h]
  have hof : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p f = of k f := fun f h => by
    rw [e2, map_mul, Module.End.mul_apply, hf.triv a.1 a1 a.2 a2 f h]
  have hth := GlobalTheory.T.theta_function_heisenberg_invariant F E σ B C.good nS nT JS JT ξ₀
  obtain ⟨c, hc, h⟩ := schur_norm C (of p * oi p * substF σ JS JT p⁻¹)
    (fun f h => hf.pres _ _ (hi.pres _ _ (R f h).1))
    (fun u f h => by
      have t1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT p⁻¹ f) := (R f h).1
      have t2 : substF σ JS JT p⁻¹ (heisOF σ JS JT ξ₀ B.ψ u f) =
        heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT p.1⁻¹ p.2⁻¹ u) (substF σ JS JT p⁻¹ f) := (R f h).2.1 u
      simp only [Module.End.mul_apply]
      rw [t2, hoi _ (hth _ _ t1), hi.Heisenberg₂ a.1 a1 a.2 a2 _ _ t1, hof _ (hth _ _ (hi.pres _ _ t1)),
        hf.Heisenberg₂ k.1 k1 k.2 k2 _ _ (hi.pres _ _ t1), ← actOF_mul, ← actOF_mul, ← hof _ (hi.pres _ _ t1), ← hoi _ t1,
        show k.1 * a.1 = p.1 from congrArg Prod.fst e2.symm, show k.2 * a.2 = p.2 from congrArg Prod.snd e2.symm,
        mul_inv_cancel, mul_inv_cancel, GlobalTheory.FinLatF.actOF_one])
    (fun μ 𝓕 hμ h𝓕 f h => by
      have t1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT p⁻¹ f) := (R f h).1
      simp only [Module.End.mul_apply]
      rw [hf.unit μ 𝓕 hμ h𝓕 _ _ (hi.pres _ _ t1), hi.unit μ 𝓕 hμ h𝓕 _ _ t1]
      exact (R f h).2.2 μ 𝓕 hμ h𝓕)
  refine ⟨c, hc, fun f hf' => ?_⟩
  have := h (substF σ JS JT p f) (R' f hf').1
  simp only [Module.End.mul_apply] at this
  rwa [← substF_mul, inv_mul_cancel, substF_one] at this

theorem IsScalarF.mul (C : Ctx σ B JS JT ξ₀ θ ι) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f)) {p q : GAF σ JS × GAF σ JT} {c c' : ℂ}
    (h : IsScalarF B ξ₀ of oi p c) (h' : IsScalarF B ξ₀ of oi q c') (h1 : q.1 ∈ GQF σ JS) (h2 : q.2 ∈ GQF σ JT) :
    IsScalarF B ξ₀ of oi (p * q) (c * c') := fun f hf => by
  have t : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT q f) := (rat_subst C h1 h2 hf).1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcomm q p _ (hi.pres _ _ hf), h' f hf, map_smul,
    map_smul, h _ t, smul_smul, mul_comm c', substF_mul]

theorem comm_inv {G M : Type} [Group G] [Monoid M] (m : G →* M) {x : M} {p : G} (h : x * m p = m p * x) :
    x * m p⁻¹ = m p⁻¹ * x := by
  calc x * m p⁻¹ = m p⁻¹ * (m p * x) * m p⁻¹ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    _ = m p⁻¹ * x := by rw [← h, mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem IsRatF.det_ne {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {g : GAF σ J} {a} (h : IsRatF σ J g a) :
    a.det ≠ 0 := fun h0 => by
  have := congrArg Matrix.det h.unitary
  rw [Matrix.det_mul, h0, mul_zero] at this
  exact hJ.2 this.symm

def cutRat (x : AEF F E) (h : x * x = x) : Eˣ →* (AEF F E)ˣ :=
  (Units.map (GlobalTheory.SplitDetCharF.cut x h)).comp (Units.map (incAF F E).toMonoidHom)

theorem cutRat_val (x : AEF F E) (h : x * x = x) (u : Eˣ) : (cutRat x h u : AEF F E) = (1 - x) + x * incAF F E u := rfl

theorem cAF_incAF' (x : E) : cAF σ (incAF F E x) = incAF F E (σ x) := GlobalTheory.HeisLineF.cAF_incAF σ x

theorem half_add (hB : B.IsGood σ) (hε : IsHalfF σ ε) : (ε + cAF σ ε) * (ε + cAF σ ε) = ε + cAF σ ε := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  linear_combination hε.idem + h3 + 2 * hε.orth

theorem eta_cut (hB : B.IsGood σ) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) (u : Eˣ) :
    η (cutRat _ (half_add hB hε) u) * η (cutRat ε hε.idem (Units.map (σ : E →* E) u)) = η (cutRat ε hε.idem u) := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  have e1 : cutRat _ (half_add hB hε) u = cutRat ε hε.idem u * cutRat _ h3 u := Units.ext (by
    rw [Units.val_mul, cutRat_val, cutRat_val, cutRat_val]
    linear_combination (-(incAF F E u - 1) ^ 2) * hε.orth)
  have e2 := GlobalTheory.SplitDetCharF.char_norm hB.cm h2 (cutRat _ h3 u) (cutRat ε hε.idem (Units.map (σ : E →* E) u)) (by
    rw [cutRat_val, cutRat_val, map_add, map_sub, map_mul, map_one,
      GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm), cAF_incAF']
    rfl)
  rw [e1, map_mul, mul_assoc, e2, mul_one]

theorem cutDet_rat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {g : GAF σ J} {a} (h : IsRatF σ J g a)
    (x : AEF F E) (hx : x * x = x) : GlobalTheory.SplitDetCharF.cutDet σ J x hx g = cutRat x hx (Units.mk0 _ (h.det_ne hJ)) :=
  Units.ext (by
    rw [GlobalTheory.SplitDetCharF.cutDet_val, cutRat_val, show mtF σ J g = _ from h, Units.val_mk0, RingHom.map_det]
    rfl)

structure Parts (C : Ctx σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (lam : ℕ →* ℂ)
    (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)) (η : (AEF F E)ˣ →* Circle) (ε : AEF F E)
    (of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  res : ResEtaF η 1
  half : IsHalfF σ ε
  prod : ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ v, tauB B v x = r
  hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of
  hof : ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε half.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ)
  hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi
  vac : ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → (HMF JS JT ξ₀ (tauB B) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f

theorem real_data (C : Ctx σ B JS JT ξ₀ θ ι) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s)
    (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume ∧
      GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h)) ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v) * ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det =
        r * (-s).det * ((∏ v, tauB B v (b ⊗ₖ aᵀ).det) * GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h))) := by
  obtain ⟨q1, q2⟩ := det_mMF C ha hb
  have hH := GlobalTheory.T.hermitianFormRealCoordinateMatrix_hermitian_det_ne_zero F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ
  have hU := GlobalTheory.T.realCoordinateAction_unitary_preserves_hermitianForm F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι C.chart (g⁻¹, h⁻¹)
  have c1 : s * mMF σ JS JT θ (g⁻¹, h⁻¹) = mMF σ JS JT θ (g⁻¹, h⁻¹) * s := by
    have := comm_inv (mMF σ JS JT θ) hcm
    rwa [Prod.inv_mk] at this
  have c2 : mMF σ JS JT θ (g⁻¹, h⁻¹) * mMF σ JS JT θ (g, h) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]
  have c3 : (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det ≠ 0 := by
    rw [q2]
    exact Finset.prod_ne_zero_iff.2 fun v _ => (map_ne_zero _).2 hd
  rw [← q1, ← q2]
  exact integral_gaussV hH.1 hs.sq hs.pos hU c1 c2 c3

theorem zF_rat (C : Ctx σ B JS JT ξ₀ θ ι) (hε : ε * ε = ε) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) :
    zF σ JS JT η ε hε (g, h) * η (cutRat ε hε (Units.mk0 _ hΔ)) = 1 := by
  have da := ha.det_ne C.hS
  have db := hb.det_ne C.hT
  have e1 := cutDet_rat C.hT hb ε hε
  rw [map_inv, inv_eq_iff_eq_inv] at e1
  have e2 := cutDet_rat C.hS ha ε hε
  have u0 : Units.mk0 _ hΔ = Units.mk0 _ db ^ nS * Units.mk0 _ da ^ nT := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0,
      Matrix.det_kronecker, Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin])
  unfold zF
  rw [u0, e1, e2]
  simp only [MonoidHom.pow_apply, map_mul, map_pow, map_inv]
  generalize η (cutRat ε hε (Units.mk0 _ da)) = x
  generalize η (cutRat ε hε (Units.mk0 _ db)) = y
  rw [mul_comm (y ^ nS), mul_mul_mul_comm, inv_mul_cancel, inv_mul_cancel, one_mul]

theorem phase_rat (C : Ctx σ B JS JT ξ₀ θ ι) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) {Δ d N : E} (hΔ : Δ ≠ 0) (hd : d ≠ 0)
    (hN : N ≠ 0) {m : ℕ} (d1 : Δ * σ Δ = 1) (d2 : Δ * σ d = (-1) ^ m * d) {z : Circle}
    (v0 : z * η (cutRat ε hε.idem (Units.mk0 _ hΔ)) = 1) :
    (z : ℂ) * η (cutRat _ (half_add C.good hε) (Units.mk0 _ hN * Units.mk0 _ hΔ)) =
      η (cutRat ε hε.idem ((-1) ^ m)) * η (cutRat _ (half_add C.good hε) (Units.mk0 _ hN * Units.mk0 _ hd)) := by
  rw [← Circle.coe_mul, ← Circle.coe_mul]
  have u1 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hΔ) = 1 := Units.ext d1
  have u2 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hd) = (-1) ^ m * Units.mk0 _ hd :=
    Units.ext (by simpa using d2)
  exact congrArg _ (GlobalTheory.RatAut.phase_identity (η.comp (cutRat ε hε.idem)) (η.comp (cutRat _ (half_add C.good hε)))
    (Units.map (σ : E →* E)) (eta_cut C.good h2 hε) v0 u1 u2)

theorem Parts.prod' {C : Ctx σ B JS JT ξ₀ θ ι} (P : Parts C hc lam Om η ε of oi) {N x : E} (hN : N ≠ 0) (hx : x ≠ 0)
    {c n : ℕ} (h : ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ (N * x)|) : ∃ r : ℝ, 0 < r ∧
      (η (cutRat _ (half_add C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx)) : ℂ) * (lam c * lam n) *
        ((∏ v, tauB B v N) * ∏ v, tauB B v x) = r := by
  obtain ⟨r, p, e⟩ := P.prod _ _ (mul_ne_zero hN hx) h (cutRat _ (half_add C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx))
    (by rw [cutRat_val, add_comm, Units.val_mul, Units.val_mk0, Units.val_mk0])
  refine ⟨r, p, ?_⟩
  rw [← e, map_mul lam, ← Finset.prod_mul_distrib]
  simp only [map_mul]

theorem Parts.kappa {C : Ctx σ B JS JT ξ₀ θ ι} (P : Parts C hc lam Om η ε of oi)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT}
    (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s) {c : ℂ} (hc0 : c ≠ 0) (H : IsScalarF B ξ₀ of oi (g, h) c)
    (f : thetaSubF σ JS JT ξ₀ B.ψ) (f1 : Fixes (opFF hc w) (latF F E nS nT Λ) f) (f2 : IsVacF σ JS JT ξ₀ B.ψ ι s f)
    (x : WOF F E nS nT) :
    (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = (c⁻¹ * GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h)) *
      zF σ JS JT η ε P.half.idem (g, h) *
      (lam (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)))))⁻¹) *
      ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x := by
  have e1 := congrFun (H f f.2) x
  rw [P.vac s hs.sq hs.pos (g, h) hcm f f.2 f2, map_smul, P.hof, hO.vac _ f f1, normOp, Submodule.coe_smul] at e1
  simp only [Pi.smul_apply, smul_eq_mul, substF_apply] at e1
  rw [← one_mul (f.1 _), ← inv_mul_cancel₀ hc0, mul_assoc, ← e1]
  ring

theorem scalar_const (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (P : Parts C hc lam Om η ε of oi) (hs : CartF σ JS JT ξ₀ B θ s) :
    ∃ e s₀ : ℂ, s₀ ≠ 0 ∧ ∀ g h a b, IsRatF σ JS g a → IsRatF σ JT h⁻¹ b →
      s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s → (b ⊗ₖ aᵀ - 1).det ≠ 0 →
      ∀ c : ℂ, c ≠ 0 → IsScalarF B ξ₀ of oi (g, h) c → ∃ r : ℝ, 0 < r ∧ c * e = r * s₀ := by
  refine ⟨(-s).det, η (cutRat ε P.half.idem ((-1) ^ Fintype.card (Fin nT × Fin nS))), Circle.coe_ne_zero _,
    fun g h a b ha hb hcm hd c hc0 H => ?_⟩
  obtain ⟨d1, d2⟩ := det_kron C ha hb
  have hΔ := left_ne_zero_of_mul_eq_one d1
  obtain ⟨hbij, n, t, c₀, N, M, hn, hc₀, hN, t1, t2, g1, g2, i1, i2⟩ := finite_data C hG hR hO ha hb hΔ hd
  obtain ⟨hI, hδ0, r₂, p₂, h2⟩ := real_data C hs ha hb hcm hd
  obtain ⟨r₁, p₁, h1⟩ := gauss_mul_integral C hG hR hO hs ha hb hbij hI _ (P.kappa hO hs hcm hc0 H) n t t1 t2
  rw [g1] at h1
  have hN' : (N : E) ^ M ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  obtain ⟨r₃, p₃, h3⟩ := P.prod' hN' hd i1
  obtain ⟨r₄, p₄, h4⟩ := P.prod' hN' hΔ i2
  exact GlobalTheory.RatAut.final_algebra p₁ p₂ p₃ p₄ hn hc0 hδ0 (Circle.coe_ne_zero _) h1 h2 h3 h4 g2
    (phase_rat C P.res P.half hΔ hd hN' d1 d2 (zF_rat C P.half.idem ha hb hΔ))

set_option maxHeartbeats 1000000 in

theorem isScalar_one_of_comm (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (P : Parts C hc lam Om η ε of oi) (hs : CartF σ JS JT ξ₀ B θ s)
    {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GQF σ JS) (hh : h ∈ GQF σ JT)
    (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s) : IsScalarF B ξ₀ of oi (g, h) 1 := by
  obtain ⟨a, ha⟩ := exists_isRatF hg
  obtain ⟨b, hb⟩ := exists_isRatF (inv_mem hh)
  obtain ⟨e, s₀, hs₀, H⟩ := scalar_const C hG hR hO P hs
  obtain ⟨t, ht, ht'⟩ := (infinite_norm_one C).exists_notMem_finite
    ((GlobalTheory.RatAut.finite_det_smul_sub_one (b ⊗ₖ aᵀ)).union (GlobalTheory.RatAut.finite_det_smul_sub_one
      ((1 : Matrix (Fin nT) (Fin nT) E) ⊗ₖ (1 : Matrix (Fin nS) (Fin nS) E)ᵀ)))
  rw [Set.mem_union, not_or] at ht'
  obtain ⟨k, rk⟩ := exists_of_unitary (σ := σ) C.hT (a := t • 1) (by
    have e : ((t • (1 : Matrix (Fin nT) (Fin nT) E)).map σ)ᵀ = σ t • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
    rw [e, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, show t * σ t = 1 from ht, one_smul])
  have hk := rk.mem
  have hcomm := fin_inf_comm C hO (fun p => ⟨_, P.hof p⟩) P.hi
  have ck : s * mMF σ JS JT θ (1, k⁻¹) = mMF σ JS JT θ (1, k⁻¹) * s := by
    have := comm_inv (mMF σ JS JT θ) (hs.cen k t rk)
    rwa [Prod.inv_mk, inv_one] at this
  obtain ⟨c, hc1, sc⟩ := exists_isScalarF (p := (g, h)) C P.hf P.hi hg hh
  obtain ⟨c', hc', sc'⟩ := exists_isScalarF (p := (1, k⁻¹)) C P.hf P.hi (one_mem _) (inv_mem hk)
  have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (hc1 ▸ one_ne_zero)
  have hc0' : c' ≠ 0 := norm_ne_zero_iff.1 (hc' ▸ one_ne_zero)
  obtain ⟨r', p', e'⟩ := H 1 k⁻¹ 1 (t • 1) (isRatF_one JS) (by rwa [inv_inv]) ck
    (by rw [Matrix.smul_kronecker]; exact ht'.2) c' hc0' sc'
  obtain ⟨r, p, e''⟩ := H (g * 1) (h * k⁻¹) a (t • b) (by rwa [mul_one])
    (by
      have := rk.mul hb
      rwa [Matrix.smul_mul, Matrix.one_mul, ← inv_inv k, ← _root_.mul_inv_rev] at this)
    (by rw [← Prod.mk_mul_mk, map_mul, ← mul_assoc, hcm, mul_assoc, ck, mul_assoc])
    (by rw [Matrix.smul_kronecker]; exact ht'.1) (c * c') (mul_ne_zero hc0 hc0')
    (sc.mul C P.hi hcomm sc' (one_mem _) (inv_mem hk))
  have q' : (r' : ℂ) ≠ 0 := by exact_mod_cast p'.ne'
  have e1 : c = ((r / r' : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff q']
    refine mul_right_cancel₀ hs₀ ?_
    rw [← e'', mul_assoc, ← e', mul_assoc]
  have e2 : r / r' = 1 := by
    rw [e1, Complex.norm_real, Real.norm_of_nonneg (div_pos p p').le] at hc1
    exact hc1
  rwa [e1, e2, Complex.ofReal_one] at sc

theorem datumEta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)), IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
      ∀ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η → ResEtaF η 1 → HasExp B.emb η (fun _ => 1) → UnramInert σ η →
        ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hξ Λ hG hR hc w lam Om hO η h1 h2 h3 h4
  obtain ⟨θ, hθ⟩ := (GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB).2.1
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_realChart_adeleTensor_admissibleCMBase F E σ B hB θ hθ
  have C : Ctx σ B JS JT ξ₀ θ ι := ⟨hB, hS, hT, h0, hξ, hθ, hι⟩
  obtain ⟨ε, hε, hprod⟩ := eta_prod hB h1 h2 h3 h4 hO.good hO.sqrt
  obtain ⟨of, hf, hof⟩ := exists_fin C hO h1 h2 hε
  obtain ⟨oi, hi, hvac⟩ := exists_inf C
  have P : Parts C hc lam Om η ε of oi := ⟨h2, hε, hprod, hf, hof, hi, hvac⟩
  have hcomm := fin_inf_comm C hO (fun p => ⟨_, hof p⟩) hi
  refine datum_of_aut C hG hO h1 h2 hf (fun p => ⟨_, hof p⟩) hi fun γ hγ γ' hγ' f hf' => ?_
  have := rat_gen C (fun p => IsScalarF B ξ₀ of oi p 1)
    (fun p q _ _ q1 q2 a b => mul_one (1 : ℂ) ▸ a.mul C hi hcomm b q1 q2)
    (fun p s p1 p2 hs hcm => isScalar_one_of_comm C hG hR hO P hs p1 p2 hcm) (γ, γ') hγ hγ' f hf'
  rw [this, one_smul]
  show f (actOF σ JS JT γ⁻¹ γ'⁻¹ 0) = f 0
  rw [actOF, Matrix.mul_zero, Matrix.zero_mul]

end PositivityTheory.ThKW

end
end
