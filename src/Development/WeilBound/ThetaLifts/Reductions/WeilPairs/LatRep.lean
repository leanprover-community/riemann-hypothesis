import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat
import Development.WeilBound.ThetaLifts.TowerModels.PlaneCodiff
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsMore
import Mathlib

section
noncomputable section

open scoped TensorProduct Matrix Topology nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_trace_one (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) : ∃ b : 𝓞 E, Algebra.trace F E (b : E) = 1 := by
  classical
  haveI : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have htop : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra hn
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hn
    exact (not_dvd_differentIdeal_iff (A := 𝓞 F) (P := P)).2 inferInstance (Ideal.dvd_iff_le.2 hle)
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have e := coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)
    rw [htop, FractionalIdeal.coeIdeal_top] at e
    exact inv_eq_one.mp e.symm
  let J : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  by_cases hJ : J = ⊤
  · have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := h1
    refine ⟨b, ?_⟩
    have := Algebra.algebraMap_intTrace (K := F) (L := E) (A := 𝓞 F) b
    rw [hb, map_one] at this
    exact this.symm
  · exfalso
    obtain ⟨p, hp, hJp⟩ := Ideal.exists_le_maximal J hJ
    have hp0 : p ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)
    obtain ⟨t, ht, ht1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hp0 hp.ne_top
    have hmem : algebraMap F E t ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (by simp)]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      have hb : Algebra.intTrace (𝓞 F) (𝓞 E) b ∈ p := hJp ⟨b, rfl⟩
      have hp0' : (p : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
        rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
      have h2 : t * algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) b) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        have := FractionalIdeal.mul_mem_mul ht ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hb, rfl⟩)
        rwa [inv_mul_cancel₀ hp0'] at this
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h2
      refine ⟨c, ?_⟩
      rw [hc, Algebra.traceForm_apply, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul,
        Algebra.algebraMap_intTrace (L := E)]
    rw [hd] at hmem
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
    have hint : IsIntegral ℤ t := by
      rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, ← hc]
      exact RingOfIntegers.isIntegral_coe c
    exact ht1 ((FractionalIdeal.mem_one_iff _).2 ⟨⟨t, hint⟩, rfl⟩)

theorem exists_w (h : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) : ∃ w : 𝓞 E, w + sgOF σ w = 1 := by
  obtain ⟨b, hb⟩ := exists_trace_one hu
  refine ⟨b, RingOfIntegers.ext ?_⟩
  show (b : E) + σ b = 1
  rw [← PositivityTheory.ThKG.Tow.Pln.trace_cm h, hb, map_one]

theorem sg_comm (h : IsCMExt F E σ) (g : E ≃ₐ[ℚ] E) (x : E) : g (σ x) = σ (g x) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  have h1 := h.2.2.2 (τ.comp (g : E →+* E)) x
  have h2 := h.2.2.2 τ (g x)
  simp only [RingHom.comp_apply, RingHom.coe_coe] at h1
  rw [h2]
  exact h1

theorem sg_sg (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sg_ne (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  have := h.2.1
  by_contra hn
  push Not at hn
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hn y] at this
  simpa using this.symm

theorem inertQ_of_fix (h : IsCMExt F E σ) [IsGalois ℚ E] {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 E) ∈ P) (hfix : ∀ r ∈ P, sgOF σ r ∈ P) : InertQF σ q := by
  intro Q hQ hqQ r hr
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have key : ∀ P : Ideal (𝓞 E), P.IsPrime → (q : 𝓞 E) ∈ P → P.LiesOver (Ideal.span {(q : ℤ)}) :=
    fun P hP h => ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
      simpa using h)⟩
  haveI := key P hP.isPrime hqP
  haveI := key Q hQ.isPrime hqQ
  obtain ⟨g, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(q : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hr ⊢
  have e : g⁻¹ • sgOF σ r = sgOF σ (g⁻¹ • r) := RingOfIntegers.ext (sg_comm h g⁻¹ r)
  rw [e]
  exact hfix _ hr

theorem exists_move (h : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) {P : Ideal (𝓞 E)}
    (hP : P.IsMaximal) : ∃ r, sgOF σ r - r ∉ P := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have hσ := sg_sg h
  have : (P.under (𝓞 F)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) (P.under (𝓞 F)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 F)) P (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcard
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => by
    obtain ⟨x, hx⟩ := sg_ne h
    exact hx (congrArg (fun t : E ≃ₐ[F] E => t x) hs)
  by_contra hn
  push Not at hn
  have hs : s ∈ P.inertia (E ≃ₐ[F] E) := AddSubgroup.mem_inertia.2 fun x => hn x
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact hs1 hs

theorem exists_goodNorm (h : IsCMExt F E σ) [IsGalois ℚ E] (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) :
    ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam ∧
      ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  classical
  obtain ⟨lam, h0, h1, h2⟩ := GlobalTheory.FinWeil.exists_lam (InertQF σ)
    fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E)
  refine ⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩
  obtain ⟨q, hq, hqP, hf, hc⟩ := GlobalTheory.FinWeil.exists_card_eq_pow P hP
  have hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  refine ⟨?_, fun hfix => ⟨?_, exists_move h hu hP⟩⟩
  · rw [hc]
    by_cases hI : InertQF σ q
    · rw [h1 q hq hf hI, neg_sq, hsq]
    · rw [h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI
        ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]
  · rw [hc]
    exact h1 q hq hf (inertQ_of_fix h hP hq hqP hfix)

end PositivityTheory.ThKW.LatB

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {nS nT : ℕ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

variable (F) in

def inrA : Af F →ₗ[F] AF F where
  toFun a := pairA F 0 a
  map_add' _ _ := Prod.ext (add_zero 0).symm rfl
  map_smul' c _ := Prod.ext (smul_zero c).symm rfl

variable (F E) in

def liftF : Af F ⊗[F] E →ₗ[F] AEF F E := TensorProduct.map (inrA F) LinearMap.id

theorem liftF_tmul (a : Af F) (t : E) : liftF F E (a ⊗ₜ[F] t) = pairA F 0 a ⊗ₜ[F] t := rfl

variable (E) in

abbrev hatO : AddSubgroup (Af F ⊗[F] E) := GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E))

theorem fin_mul_eq (y : AEF F E) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) * y = liftF F E (finPartF F E y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero]
  | tmul a t =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      show finPartF F E (a ⊗ₜ[F] t) = sndA F a ⊗ₜ[F] t from rfl, liftF_tmul]
    congr 1
    exact Prod.ext (zero_mul _) (one_mul _)
  | add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]

theorem liftF_smul_mem {z : Af F ⊗[F] E} (hz : z ∈ hatO (F := F) E) {u : WOF F E nS nT}
    (hu : u ∈ latOF F E nS nT Λ) : liftF F E z • u ∈ latOF F E nS nT Λ := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := hz
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨α, hα, γ, hγ, rfl⟩ := hu
      refine AddSubgroup.subset_closure ⟨a * α, fun v => GlobalTheory.AdLat.adele_mul_integral F (ha v) (hα v),
        b • γ, Λ.smul_mem b hγ, ?_⟩
      ext i j
      simp only [liftF_tmul, Matrix.smul_apply, smul_eq_mul, ratWF, Matrix.map_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      show (pairA F 0 a ⊗ₜ[F] (b : E)) * ((pairA F 0 α ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] γ i j)) =
        (pairA F 0 (a * α) ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] ((b • γ) i j))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul, one_mul, Matrix.smul_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  | zero => rw [map_zero, zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, neg_smul]; exact neg_mem hx

theorem idem_smul_mem {e : AEF F E} (he : e * e = e) (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e)
    {u : WOF F E nS nT} (hu : u ∈ latOF F E nS nT Λ) : e • u ∈ latOF F E nS nT Λ := by
  have h1 : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, he])
  rw [← hf, fin_mul_eq]
  exact liftF_smul_mem h1 hu

theorem fin_of_place {e : AEF F E} {α : Af F} (h : algebraMap (AF F) (AEF F E) (pairA F 0 α) * e = e) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e := by
  rw [← h, ← mul_assoc, ← map_mul]
  congr 2
  exact Prod.ext (zero_mul _) (one_mul _)

theorem split_parts {e : AEF F E} (he : IsSplitIdemF σ e) :
    (algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) ∧
      (algebraMap (AF F) (AEF F E) (pairA F 0 1) * cAF σ e = cAF σ e) ∧ cAF σ e * cAF σ e = cAF σ e := by
  obtain ⟨hee, hec, v, ε, ⟨α, rfl, -⟩, hs⟩ := he
  have hce : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, hee]
  refine ⟨fin_of_place (α := α) ?_, fin_of_place (α := α) ?_, hce⟩
  · rw [← hs, add_mul, hee, mul_comm, hec, add_zero]
  · rw [← hs, add_mul, hec, hce, zero_add]

end PositivityTheory.ThKW.LatB

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {nS nT : ℕ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

theorem fin_smul_self (u : XFF F E nS nT) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) • (u : WOF F E nS nT) = u := by
  have h0 : pairA F 1 0 • (u : WOF F E nS nT) = 0 := GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (XFF.fin u)
  have h := PositivityTheory.ThKW.LatA.dec (u : WOF F E nS nT)
  rw [h0, zero_add] at h
  rw [algebraMap_smul]
  exact h.symm

theorem int_smul_mem {a : AEF F E} (ha : finPartF F E a ∈ hatO (F := F) E) {u : XFF F E nS nT}
    (hu : u ∈ (latF F E nS nT Λ).toAddSubgroup) : a • u ∈ (latF F E nS nT Λ).toAddSubgroup := by
  show ((a • u : XFF F E nS nT) : WOF F E nS nT) ∈ latOF F E nS nT Λ
  rw [XFF.coe_asmul, ← fin_smul_self u, smul_smul, mul_comm, fin_mul_eq]
  exact liftF_smul_mem ha hu

theorem int_smul_mem_map {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (p : GAF σ JS × GAF σ JT) {a : AEF F E} (ha : finPartF F E a ∈ hatO (F := F) E) {u : XFF F E nS nT}
    (hu : u ∈ ((latF F E nS nT Λ).map (rhoFF σ JS JT p)).toAddSubgroup) :
    a • u ∈ ((latF F E nS nT Λ).map (rhoFF σ JS JT p)).toAddSubgroup := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine ⟨a • y, int_smul_mem ha hy, XFF.ext ?_⟩
  rw [coe_rhoFF, XFF.coe_asmul, XFF.coe_asmul, coe_rhoFF, actOF_smul]

theorem mul_e_zero {a e : AEF F E} (ha : finPartF F E a = 0)
    (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) : a * e = 0 := by
  rw [← hf, ← mul_assoc, mul_comm a, fin_mul_eq, ha, map_zero, zero_mul]

theorem finPart_cAF_zero {a : AEF F E} (ha : finPartF F E a = 0) : finPartF F E (cAF σ a) = 0 := by
  have hr : infPartF F E (algebraMap (AF F) (AEF F E) (pairA F 1 0)) = 1 := rfl
  have hf : finPartF F E (algebraMap (AF F) (AEF F E) (pairA F 1 0)) = 0 := TensorProduct.zero_tmul _ _
  have e : a = algebraMap (AF F) (AEF F E) (pairA F 1 0) * a := by
    rw [← sub_eq_zero]
    refine GlobalTheory.SplitDetCharF.adele_tensor_ext _ ?_ ?_
    · rw [map_sub, map_mul, hr, one_mul, sub_self]
    · rw [map_sub, map_mul, hf, ha, zero_mul, sub_self]
  rw [e, map_mul, GlobalTheory.HeisThetaF.cAF_algebraMap, map_mul, hf, zero_mul]

theorem approx {k : ℕ} (hk : 0 < k) {z : Af F ⊗[F] E} (hz : z ∈ hatO (F := F) E) :
    ∃ (r : 𝓞 E) (s : AEF F E), finPartF F E s ∈ hatO (F := F) E ∧ finPartF F E (cAF σ s) ∈ hatO (F := F) E ∧
      z = finPartF F E (incAF F E (r : E) + k • s) := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, ⟨t, rfl⟩, rfl⟩ := hw
    obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F k hk).2 α hα
    refine ⟨algebraMap (𝓞 F) (𝓞 E) x * t, pairA F 0 β ⊗ₜ[F] (t : E),
      AddSubgroup.subset_closure ⟨β, hβ, _, ⟨t, rfl⟩, rfl⟩,
      AddSubgroup.subset_closure ⟨β, hβ, _, ⟨sgOF σ t, rfl⟩, rfl⟩, ?_⟩
    rw [hx, map_add, map_nsmul]
    exact GlobalTheory.SplitIndex.tmul_split β (x : F) k (t : E)
  | zero => exact ⟨0, 0, by rw [map_zero]; exact zero_mem _,
      by rw [map_zero, map_zero]; exact zero_mem _, by simp⟩
  | add x x' _ _ h h' =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    obtain ⟨r', s', h1', h2', rfl⟩ := h'
    refine ⟨r + r', s + s', by rw [map_add]; exact add_mem h1 h1',
      by rw [map_add, map_add]; exact add_mem h2 h2', ?_⟩
    rw [← map_add]
    congr 1
    push_cast
    rw [map_add, smul_add]
    abel
  | neg x _ h =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    refine ⟨-r, -s, by rw [map_neg]; exact neg_mem h1,
      by rw [map_neg, map_neg]; exact neg_mem h2, ?_⟩
    rw [← map_neg]
    congr 1
    push_cast
    rw [map_neg, smul_neg, neg_add]

theorem split_mem (h : IsCMExt F E σ) {e : AEF F E} (hee : e * e = e)
    (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) (hec : e * cAF σ e = 0) {q : ℕ} (hq : q.Prime)
    (hin : InertQF σ q) {x : XFF F E nS nT} (hx : q • x ∈ (latF F E nS nT Λ).toAddSubgroup) :
    e • x ∈ (latF F E nS nT Λ).toAddSubgroup := by
  have heI : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, hee])
  obtain ⟨r, s, hs, hs', hz⟩ := approx (σ := σ) hq.pos heI
  have h0 : finPartF F E (e - (incAF F E (r : E) + q • s)) = 0 := by rw [map_sub, ← hz, sub_self]
  have h0' := finPart_cAF_zero (σ := σ) h0
  rw [map_sub, map_add, map_nsmul, GlobalTheory.HeisLineF.cAF_incAF, ← coe_sgOF] at h0'
  refine GlobalTheory.SplitIndex.core_split ((incAF F E).comp (algebraMap (𝓞 E) E)) _
    (fun a => finPartF F E a ∈ hatO (F := F) E) (fun a ha u hu => int_smul_mem ha hu)
    (fun r => AddSubgroup.subset_closure ⟨1, fun v => GlobalTheory.AdLat.adele_one_integral F v, _, ⟨r, rfl⟩, rfl⟩)
    q x hx e (cAF σ e) s (cAF σ s) heI hs hs' hee hec r (sgOF σ r) (mul_e_zero h0 hf) (mul_e_zero h0' hf) ?_
  intro P hP hqP hr
  have := hin P hP hqP _ hr
  rwa [show sgOF σ (sgOF σ r) = r from RingOfIntegers.ext (sg_sg h _)] at this

theorem mtF_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a b : GAF σ J) : mtF σ J (a * b) = mtF σ J a * mtF σ J b := by
  simp only [mtF, map_mul, Units.val_mul]

theorem mtF_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mtF σ J 1 = 1 := by
  simp only [mtF, map_one, Units.val_one]

theorem supp_smul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  ext i j
  have := hg i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
  linear_combination -this

theorem supp_smul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  calc (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = ((1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E))) * mtF σ J g⁻¹ := by
        rw [Matrix.smul_mul, Matrix.one_mul]
    _ = ((1 - (e + cAF σ e)) • mtF σ J g) * mtF σ J g⁻¹ := by rw [supp_smul hg]
    _ = _ := by rw [Matrix.smul_mul, ← mtF_mul, mul_inv_cancel, mtF_one]

theorem act_supp {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {e : AEF F E}
    {g : GAF σ JS} {k : GAF σ JT} (hg : SuppAtF σ e JS g) (hk : SuppAtF σ e JT k) (y : WOF F E nS nT) :
    (1 - (e + cAF σ e)) • actOF σ JS JT g k y = (1 - (e + cAF σ e)) • y := by
  unfold actOF
  calc (1 - (e + cAF σ e)) • (mtF σ JT k * y * mtF σ JS g⁻¹)
      = ((1 - (e + cAF σ e)) • mtF σ JT k) * y * mtF σ JS g⁻¹ := by rw [Matrix.smul_mul, Matrix.smul_mul]
    _ = ((1 - (e + cAF σ e)) • (1 : Matrix (Fin nT) (Fin nT) (AEF F E))) * y * mtF σ JS g⁻¹ := by rw [supp_smul hk]
    _ = y * ((1 - (e + cAF σ e)) • mtF σ JS g⁻¹) := by
        rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
    _ = y * ((1 - (e + cAF σ e)) • (1 : Matrix (Fin nS) (Fin nS) (AEF F E))) := by rw [supp_smul_inv hg]
    _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one]

theorem idx_main (h : IsCMExt F E σ) {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) :
    ∀ e, IsSplitIdemF σ e → ∀ g k, SuppAtF σ e JS g → SuppAtF σ e JT k → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, k))) := by
  intro e he g k hg hk q hq hin
  obtain ⟨hf, hfc, hcc⟩ := split_parts he
  have hc2 : cAF σ (cAF σ e) = e := GlobalTheory.HeisLineF.cAF_cAF σ (sg_sg h) e
  have hec : e * cAF σ e = 0 := he.2.1
  have heI : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, he.1])
  have hcI : finPartF F E (cAF σ e) ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, hcc])
  have hcI' : finPartF F E (1 - (e + cAF σ e)) ∈ hatO (F := F) E := by
    rw [map_sub, map_add, map_one]
    exact sub_mem (GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩) (add_mem heI hcI)
  refine GlobalTheory.SplitIndex.not_dvd_of_saturated _ _ (hfin (g, k)) hq fun x hx hqx => ?_
  refine GlobalTheory.SplitIndex.mem_of_parts _ e (cAF σ e) x (split_mem h he.1 hf hec hq hin hqx)
    (split_mem h hcc hfc (by rw [hc2, mul_comm, hec]) hq hin hqx) ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have e1 : (1 - (e + cAF σ e)) • rhoFF σ JS JT (g, k) y = (1 - (e + cAF σ e)) • y :=
    XFF.ext (by rw [XFF.coe_asmul, XFF.coe_asmul, coe_rhoFF]; exact act_supp hg hk _)
  rw [e1]
  exact int_smul_mem hcI' hy

end PositivityTheory.ThKW.LatB

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_integral_trace_one (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ w : 𝓞 E, w + sgOF σ w = 1 :=
  LatB.exists_w hB.cm hB.unram

theorem exists_good_norm_character (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) : ∃ lam : ℕ →* ℂ, GoodNorm (sgOF σ) lam ∧
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQF σ q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  haveI := hB.galois
  exact LatB.exists_goodNorm hB.cm hB.unram

theorem lattice_stable_under_idempotents (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ := by
  intro e he a ha
  obtain ⟨hf, hfc, hcc⟩ := LatB.split_parts he
  exact ⟨LatB.idem_smul_mem he.1 hf ha, LatB.idem_smul_mem hcc hfc ha⟩

theorem lattice_index_prime_to_inert (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E))
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) :
    ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) :=
  LatB.idx_main hB.cm hfin

end PositivityTheory.ThKW

end
end

section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

namespace LatC

theorem symplOHF_two (x y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x (2 • y) = symplOF σ JS JT ξ₀ x y := by
  rw [two_nsmul, GlobalTheory.HeisLineF.symplOHF_add_right, symplOHF_add_self]

theorem phase_two (hA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)) (w : 𝓞 E) {u : XFF F E nS nT}
    (hu : u ∈ latF F E nS nT Λ) : phaseF σ JS JT ξ₀ ψ w (2 • u) = 1 := by
  have h : ψ (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u) = 1 :=
    (hA _).1 ((latF F E nS nT Λ).smul_mem w (nsmul_mem hu 2)) u hu
  have h2 := AddChar.map_add_eq_mul ψ (-symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
    (symplOF σ JS JT ξ₀ (intAF F w • ((2 • u : XFF F E nS nT) : WOF F E nS nT)) u)
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at h2
  rw [phaseF, h2, ← symplOHF_two]
  rfl

theorem smooth_theta (hg : GoodLat Λ) {hc : HeisClosedF σ JS JT ξ₀ ψ} {w : 𝓞 E}
    (H : IsHeis (sgOF σ) w (gamFF σ JS JT ξ₀ ψ) (opFF hc w)) (hA : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ))
    (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) :
    ∃ B : Submodule (𝓞 E) (XFF F E nS nT), idx (latF F E nS nT Λ) B ≠ 0 ∧
      ∀ a ∈ latF F E nS nT Λ, (∀ t ∈ B, gamFF σ JS JT ξ₀ ψ a t = 1) → opFF hc w a f = f := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨U, hU, hf⟩ := IsThetaFunOF.level f.2
  obtain ⟨N, hN, hNU⟩ := lat_lev hg U hU
  have hN2 : 0 < 2 * N := by omega
  have hdiv : ∀ x : XFF F E nS nT, (2 * N) • (incAF F E ((2 * N : ℕ) : E)⁻¹ • x) = x := nsmul_inv_smul hN2
  refine ⟨(latF F E nS nT Λ).comap ((2 * N) • LinearMap.id), idx_ne_zero hg _
    (DistribSMul.toAddMonoidHom _ (incAF F E ((2 * N : ℕ) : E)⁻¹)) (continuous_const_smul (incAF F E ((2 * N : ℕ) : E)⁻¹))
    (fun l hl => fin_smul _ (lat_fin hl)) (fun b hb => ⟨(2 * N) • (b : WOF F E nS nT), hb, ?_⟩), fun a _ ha => ?_⟩
  · show incAF F E ((2 * N : ℕ) : E)⁻¹ • ((2 * N) • (b : WOF F E nS nT)) = b
    rw [smul_comm, nsmul_inv_smul hN2]
  obtain ⟨a', rfl⟩ : ∃ a', a = (2 * N) • a' := ⟨_, (hdiv a).symm⟩
  have ha' : a' ∈ latF F E nS nT Λ := (hA a').2 fun t ht => by
    rw [← hdiv t, H.nsmul_right, ← H.nsmul_left]
    refine ha _ ?_
    show (2 * N) • (incAF F E ((2 * N : ℕ) : E)⁻¹ • t) ∈ latF F E nS nT Λ
    rw [hdiv]
    exact ht
  apply Subtype.ext
  rw [coe_opFF, hf _ (by rw [XFF.coe_nsmul, mul_comm, mul_smul]; exact hNU _ (nsmul_mem ha' 2)) (XFF.fin _),
    mul_smul, phase_two hA w (nsmul_mem ha' N), one_smul]

end LatC

theorem latRep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ hc : HeisClosedF σ JS JT ξ₀ B.ψ, ∃ (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ Λ hg hsd hc
  have hσ := LatA.sig_sig hB
  obtain ⟨w, hw⟩ := exists_integral_trace_one σ B hB
  obtain ⟨lam, hlam, hsq⟩ := exists_good_norm_character σ B hB
  have H := isHeis_opFF hσ hS hT hξ hc hw
  have hA := LatC.lat_sd hσ hB.std hg hsd
  have hspan := GlobalTheory.T.span_heisenberg_translates_of_lattice_vacua_eq_top H _ hA (LatC.smooth_theta hg H hA)
  have hidx : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0 := fun p => by
    refine LatC.idx_ne_zero hg _ (AddMonoidHom.mk' (actOF σ JS JT p.1 p.2) (actOF_add _ _))
      (LatC.continuous_act_right p.1 p.2) (fun l hl => actOF_mem_finSubF _ _ (lat_fin hl)) ?_
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  obtain ⟨Om, h1, h2⟩ := GlobalTheory.T.exists_weil_representation_of_lattice_vacua H lam hlam _ hA hspan (rhoFF σ JS JT) (LatA.gamFF_rhoFF hS) hidx
  refine ⟨w, lam, Om, hw, hA, hspan, hidx, h1, fun p => (h2 p).1, fun p => (h2 p).2, hlam, hsq, fun x => ?_,
    LatC.near hg, LatC.near' hg, lattice_stable_under_idempotents σ B hB Λ, lattice_index_prime_to_inert σ B hB JS JT Λ hidx⟩
  obtain ⟨M, hM, hx⟩ := lat_den hg (x : WOF F E nS nT) x.fin
  refine ⟨2 * M, by omega, fun l hl => ?_⟩
  have h3 : gamFF σ JS JT ξ₀ B.ψ x (M • l) = 1 := by
    rw [H.nsmul_right, ← H.nsmul_left]
    exact H.iso hA hx hl
  rw [mul_smul, LatC.symplOHF_two]
  exact h3

end PositivityTheory.ThKW

end
end
