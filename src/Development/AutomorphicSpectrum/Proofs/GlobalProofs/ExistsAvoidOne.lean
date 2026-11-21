import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Formalism.LocalToGlobal.GlobalTheory.GL2.TotallyComplexOfNoReal
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomainStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuationBis
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifference
import ReciprocityTheory.Chebotarev.EulerSum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.LargePrimeDivisors

section
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable {F : Type} [Field F] [NumberField F]

theorem finite_realEmbeddings : Finite (F →+* ℝ) := by
  infer_instance

theorem rayRel_of_signs (𝔣 I J R : Ideal (𝓞 F)) (a a' b b' : 𝓞 F) (ha0 : a ≠ 0) (ha0' : a' ≠ 0) (hb0 : b ≠ 0) (hb0' : b' ≠ 0)
    (hb1 : b - 1 ∈ 𝔣) (hb1' : b' - 1 ∈ 𝔣) (haq : Ideal.span {a} ⊔ 𝔣 = ⊤) (haa : a - a' ∈ 𝔣)
    (hs : ∀ σ : F →+* ℝ, 0 < σ ((a * b : 𝓞 F) : F) ↔ 0 < σ ((a' * b' : 𝓞 F) : F))
    (e1 : Ideal.span {a} * I = Ideal.span {b} * R) (e2 : Ideal.span {a'} * J = Ideal.span {b'} * R) :
    RayRel F 𝔣 I J := by
  obtain ⟨c, hc0, hc⟩ : ∃ c : 𝓞 F, c ≠ 0 ∧ c * a - 1 ∈ 𝔣 := by
    have h1 : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ 𝔣 := by rw [haq]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    by_cases h : c = 0
    · subst h
      have hz1 : (1 : 𝓞 F) ∈ 𝔣 := by rw [← hyz]; simpa using hz
      exact ⟨1, one_ne_zero, by simpa using 𝔣.mul_mem_left (1 * a - 1) hz1⟩
    · refine ⟨c, h, ?_⟩
      have : c * a - 1 = -z := by rw [← hyz]; ring
      rw [this]; exact 𝔣.neg_mem hz
  have qb : Ideal.Quotient.mk 𝔣 b = 1 := by
    rw [← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hb1
  have qb' : Ideal.Quotient.mk 𝔣 b' = 1 := by
    rw [← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hb1'
  have qa : Ideal.Quotient.mk 𝔣 a' = Ideal.Quotient.mk 𝔣 a := (Ideal.Quotient.eq.2 haa).symm
  have qc : Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔣)]; exact Ideal.Quotient.eq.2 hc
  have same : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → (0 < x ↔ 0 < y) → 0 < x * y := by
    intro x y hx hy hxy
    rcases lt_or_gt_of_ne hx with h | h
    · have hy' : y < 0 := lt_of_le_of_ne (not_lt.1 (fun h' => absurd (hxy.2 h') (not_lt.2 h.le))) hy
      exact mul_pos_of_neg_of_neg h hy'
    · exact mul_pos h (hxy.1 h)
  have coe0 : ∀ x : 𝓞 F, x ≠ 0 → ∀ σ : F →+* ℝ, σ (x : F) ≠ 0 := by
    intro x hx σ
    exact (map_ne_zero σ).2 (by exact_mod_cast hx)
  refine ⟨(a * b' * c) ^ 2, a' * b * a * b' * c ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero ha0 hb0') hc0)
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ha0' hb0) ha0) hb0') (pow_ne_zero 2 hc0)
  · apply Ideal.Quotient.eq.1
    simp only [map_pow, map_mul, map_one, qb']
    linear_combination (Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc
  · apply Ideal.Quotient.eq.1
    simp only [map_pow, map_mul, map_one, qb, qb', qa]
    linear_combination (Ideal.Quotient.mk 𝔣 c * Ideal.Quotient.mk 𝔣 a + 1) * qc
  · intro σ
    constructor
    · have hx := coe0 _ (mul_ne_zero (mul_ne_zero ha0 hb0') hc0) σ
      have : σ (((a * b' * c) ^ 2 : 𝓞 F) : F) = (σ ((a * b' * c : 𝓞 F) : F)) ^ 2 := by
        push_cast; simp only [map_pow]
      rw [this]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
    · have h1 := coe0 _ (mul_ne_zero ha0 hb0) σ
      have h2 := coe0 _ (mul_ne_zero ha0' hb0') σ
      have h3 := coe0 _ hc0 σ
      have : σ ((a' * b * a * b' * c ^ 2 : 𝓞 F) : F) =
          σ ((a * b : 𝓞 F) : F) * σ ((a' * b' : 𝓞 F) : F) * (σ (c : F)) ^ 2 := by
        push_cast; simp only [map_mul, map_pow]; ring
      rw [this]
      exact mul_pos (same _ _ h1 h2 (hs σ)) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h3)))
  · calc Ideal.span {(a * b' * c) ^ 2} * I
        = Ideal.span {a * b' ^ 2 * c ^ 2} * (Ideal.span {a} * I) := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton]; congr 2; ring_nf
      _ = Ideal.span {a * b' ^ 2 * c ^ 2} * (Ideal.span {b} * R) := by rw [e1]
      _ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {b'} * R) := by
          rw [← mul_assoc, ← mul_assoc, Ideal.span_singleton_mul_span_singleton,
            Ideal.span_singleton_mul_span_singleton]; congr 3; ring
      _ = Ideal.span {a * b * b' * c ^ 2} * (Ideal.span {a'} * J) := by rw [e2]
      _ = Ideal.span {a' * b * a * b' * c ^ 2} * J := by
          rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton]; congr 3; ring

theorem finRay (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) :
    ∃ S : Finset (Ideal (𝓞 F)), (∀ a ∈ S, CoprimeTo F 𝔣 a) ∧ (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) ∧
      ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a := by
  classical
  haveI : Finite (F →+* ℝ) := finite_realEmbeddings
  haveI : Finite (𝓞 F ⧸ 𝔣) :=
    (Ideal.absNorm_ne_zero_iff 𝔣).1 (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have key : ∀ A : Ideal (𝓞 F), A ≠ ⊥ → ∃ B : Ideal (𝓞 F), B ≠ ⊥ ∧ B ⊔ 𝔣 = ⊤ ∧
      ∃ r : 𝓞 F, r ≠ 0 ∧ A * B = Ideal.span {r} := by
    intro A hA
    have hA' : A ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
    have h𝔣' : 𝔣 ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    have hM0 : M ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot]
      exact Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
    have hAg : A * (𝔣 * M) ≠ 0 := mul_ne_zero hA' (mul_ne_zero h𝔣' hM0)
    obtain ⟨r, hr⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : A * (𝔣 * M) ≤ A) hAg
    obtain ⟨B, hB⟩ : A ∣ Ideal.span {r} :=
      Ideal.dvd_iff_le.2 ((le_sup_right : Ideal.span {r} ≤ A * (𝔣 * M) ⊔ Ideal.span {r}).trans hr.le)
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq] at hr
      have h1 : 𝔣 * M = ⊤ := by
        apply mul_left_cancel₀ hA'
        rw [hr, Ideal.mul_top]
      have h2 : 𝔣 * M ≤ M := Ideal.mul_le_inf.trans inf_le_right
      rw [h1] at h2
      exact hM.ne_top (top_le_iff.1 h2)
    refine ⟨B, ?_, ?_, r, hr0, hB.symm⟩
    · rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hB
      exact hr0 hB
    · have h1 : A * (𝔣 * M ⊔ B) = A * ⊤ := by
        rw [Ideal.mul_sup, ← hB, hr, Ideal.mul_top]
      have h2 : 𝔣 * M ⊔ B = ⊤ := mul_left_cancel₀ hA' h1
      rw [eq_top_iff, ← h2]
      exact sup_le ((Ideal.mul_le_inf.trans inf_le_left).trans le_sup_right) le_sup_left
  have rep : ∀ c : ClassGroup (𝓞 F), ∃ P : Ideal (𝓞 F), ∃ hP : P ∈ nonZeroDivisors (Ideal (𝓞 F)),
      P ⊔ 𝔣 = ⊤ ∧ ClassGroup.mk0 ⟨P, hP⟩ = c := by
    intro c
    obtain ⟨⟨A, hA⟩, hAc⟩ := ClassGroup.mk0_surjective c⁻¹
    have hA0 : A ≠ ⊥ := by
      have := nonZeroDivisors.ne_zero hA
      rwa [Ne, Ideal.zero_eq_bot] at this
    obtain ⟨B, hB0, hBf, r, hr0, hAB⟩ := key A hA0
    have hBm : B ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.zero_eq_bot])
    refine ⟨B, hBm, hBf, ?_⟩
    have hABm : A * B ∈ nonZeroDivisors (Ideal (𝓞 F)) := Submonoid.mul_mem _ hA hBm
    have h1 : ClassGroup.mk0 ⟨A * B, hABm⟩ = 1 := (ClassGroup.mk0_eq_one_iff hABm).2 ⟨⟨r, hAB⟩⟩
    have h2 : ClassGroup.mk0 ⟨A * B, hABm⟩ = ClassGroup.mk0 ⟨A, hA⟩ * ClassGroup.mk0 ⟨B, hBm⟩ := by
      rw [← map_mul]; rfl
    rw [h2, hAc] at h1
    exact (inv_mul_eq_one.1 h1).symm
  choose P hPm hPf hPc using rep
  have hPcop : ∀ c, CoprimeTo F 𝔣 (P c) := by
    intro c
    have := nonZeroDivisors.ne_zero (hPm c)
    rw [Ne, Ideal.zero_eq_bot] at this
    exact (show P c ≠ ⊥ ∧ P c ⊔ 𝔣 = ⊤ from ⟨this, hPf c⟩)
  have hcov : ∀ I : Ideal (𝓞 F), CoprimeTo F 𝔣 I → ∃ (c : ClassGroup (𝓞 F)) (a b : 𝓞 F),
      a ≠ 0 ∧ b ≠ 0 ∧ b - 1 ∈ 𝔣 ∧ Ideal.span {a} ⊔ 𝔣 = ⊤ ∧
        Ideal.span {a} * I = Ideal.span {b} * P c := by
    intro I hI
    have hI' : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤ := hI
    have hIm : I ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.zero_eq_bot]; exact hI'.1)
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hPc (ClassGroup.mk0 ⟨I, hIm⟩)).symm
    obtain ⟨a, b, ha, hb, hb1, haq, he⟩ :=
      Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.exists_rel_of_class 𝔣 I (P (ClassGroup.mk0 ⟨I, hIm⟩)) hI (hPcop _) x y hx hy hxy
    exact ⟨_, a, b, ha, hb, hb1, haq, he⟩
  choose cl a b ha hb hb1 haq he using hcov
  obtain ⟨κ, hκ⟩ : ∃ κ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} →
      ClassGroup (𝓞 F) × (𝓞 F ⧸ 𝔣) × Set (F →+* ℝ),
      κ = fun I => (cl I.1 I.2, Ideal.Quotient.mk 𝔣 (a I.1 I.2),
        {σ : F →+* ℝ | 0 < σ ((a I.1 I.2 * b I.1 I.2 : 𝓞 F) : F)}) := ⟨_, rfl⟩
  have hrel : ∀ I J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = κ J → RayRel F 𝔣 I.1 J.1 := by
    intro I J h
    rw [hκ] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hc, hq, hs⟩ := h
    refine rayRel_of_signs 𝔣 I.1 J.1 (P (cl I.1 I.2)) (a I.1 I.2) (a J.1 J.2) (b I.1 I.2) (b J.1 J.2)
      (ha _ _) (ha _ _) (hb _ _) (hb _ _) (hb1 _ _) (hb1 _ _) (haq _ _) (Ideal.Quotient.eq.1 hq)
      (fun σ => Set.ext_iff.1 hs σ) (he _ _) ?_
    rw [hc]; exact he _ _
  haveI : Nonempty {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} :=
    ⟨⟨⊤, show (⊤ : Ideal (𝓞 F)) ≠ ⊥ ∧ (⊤ : Ideal (𝓞 F)) ⊔ 𝔣 = ⊤ from ⟨top_ne_bot, top_sup_eq _⟩⟩⟩
  have hfin : (Set.range κ).Finite := Set.toFinite _
  have hne : ∀ d ∈ Set.range κ, ∃ I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, κ I = d := fun d hd => hd
  choose! g hg using hne
  obtain ⟨T, hTc, hTcov⟩ : ∃ T : Finset (Ideal (𝓞 F)), (∀ t ∈ T, CoprimeTo F 𝔣 t) ∧
      ∀ I, CoprimeTo F 𝔣 I → ∃ t ∈ T, RayRel F 𝔣 I t := by
    refine ⟨hfin.toFinset.image (fun d => (g d).1), ?_, ?_⟩
    · intro t ht
      obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 ht
      exact (g d).2
    · intro I hI
      have hd : κ ⟨I, hI⟩ ∈ Set.range κ := ⟨_, rfl⟩
      refine ⟨(g (κ ⟨I, hI⟩)).1, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hd), ?_⟩
      exact hrel ⟨I, hI⟩ (g (κ ⟨I, hI⟩)) (hg _ hd).symm
  obtain ⟨f, hf⟩ : ∃ f : Ideal (𝓞 F) → Ideal (𝓞 F),
      f = fun t => Classical.epsilon (fun s => s ∈ T ∧ RayRel F 𝔣 t s) := ⟨_, rfl⟩
  have hfT : ∀ t ∈ T, f t ∈ T ∧ RayRel F 𝔣 t (f t) := by
    intro t ht
    rw [hf]
    exact Classical.epsilon_spec (p := fun s => s ∈ T ∧ RayRel F 𝔣 t s) ⟨t, ht, rayRel_refl t⟩
  have hfeq : ∀ t t', RayRel F 𝔣 t t' → f t = f t' := by
    intro t t' h
    simp only [hf]
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨hs, h'⟩
      exact ⟨hs, rayRel_trans (rayRel_symm h) h'⟩
    · rintro ⟨hs, h'⟩
      exact ⟨hs, rayRel_trans h h'⟩
  refine ⟨T.image f, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    exact hTc _ (hfT t ht).1
  · intro s hs s' hs' h
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs'
    apply hfeq
    exact rayRel_trans (hfT t ht).2 (rayRel_trans h (rayRel_symm (hfT t' ht').2))
  · intro I hI
    obtain ⟨t, ht, hIt⟩ := hTcov I hI
    exact ⟨f t, Finset.mem_image_of_mem _ ht, rayRel_trans hIt (hfT t ht).2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_group_finite_representatives : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ S : Finset (Ideal (𝓞 F)), (∀ a ∈ S, CoprimeTo F 𝔣 a) ∧ (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) ∧
    ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finRay
end

section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable {F : Type} [Field F] [NumberField F]

theorem TotPos.ne_zero [IsTotallyReal F] {x : F} (h : TotPos F x) : x ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hw : w.IsReal := IsTotallyReal.isReal w
  have := h (InfinitePlace.embedding_of_isReal hw)
  rintro rfl
  simp at this

def RayPoint (𝔣 𝔟 : Ideal (𝓞 F)) (ξ : 𝓞 F) : Prop := ξ ∈ 𝔟 ∧ ξ - 1 ∈ 𝔣 ∧ TotPos F (ξ : F)

theorem exists_complement {𝔣 𝔞 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) (h𝔞 : CoprimeTo F 𝔣 𝔞) :
    ∃ (𝔟 : Ideal (𝓞 F)) (x₀ : 𝓞 F), CoprimeTo F 𝔣 𝔟 ∧ x₀ ≠ 0 ∧ x₀ - 1 ∈ 𝔣 ∧ TotPos F (x₀ : F) ∧
      𝔞 * 𝔟 = Ideal.span {x₀} := by
  classical
  have h0 : 𝔞 ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero h𝔞.1
  obtain ⟨h, hh, hp⟩ : ∃ h : ℕ, 0 < h ∧ (𝔞 ^ h).IsPrincipal := by
    refine ⟨Fintype.card (ClassGroup (𝓞 F)), Fintype.card_pos, ?_⟩
    have hmem : 𝔞 ^ Fintype.card (ClassGroup (𝓞 F)) ∈ nonZeroDivisors (Ideal (𝓞 F)) :=
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ h𝔞.1)
    have h1 : ClassGroup.mk0 ⟨𝔞 ^ Fintype.card (ClassGroup (𝓞 F)), hmem⟩ = 1 := by
      have e : (⟨𝔞 ^ Fintype.card (ClassGroup (𝓞 F)), hmem⟩ : nonZeroDivisors (Ideal (𝓞 F))) =
          ⟨𝔞, h0⟩ ^ Fintype.card (ClassGroup (𝓞 F)) := Subtype.ext (by simp)
      rw [e, map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff hmem).1 h1
  obtain ⟨α, hα⟩ := hp.principal
  have hα' : 𝔞 ^ h = Ideal.span {α} := hα
  have hne : ∀ n : ℕ, 𝔞 ^ n ≠ ⊥ := fun n => pow_ne_zero n h𝔞.1
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hne h (by rw [hα']; simp)
  have hco : IsCoprime 𝔞 𝔣 := Ideal.isCoprime_iff_sup_eq.2 h𝔞.2
  have hsup : Ideal.span {α} ⊔ 𝔣 = ⊤ := by rw [← hα']; exact Ideal.isCoprime_iff_sup_eq.1 hco.pow_left
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 F) ∈ Ideal.span {α} ⊔ 𝔣)
  haveI : Finite (𝓞 F ⧸ 𝔣) := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  have hu : IsUnit (Ideal.Quotient.mk 𝔣 α) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔣 a) ?_
    have : Ideal.Quotient.mk 𝔣 b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
    rw [mul_comm, ← map_mul, ← map_one (Ideal.Quotient.mk 𝔣), ← hab, map_add, this, add_zero]
  obtain ⟨u, hu⟩ := hu
  set e := Nat.card (𝓞 F ⧸ 𝔣)ˣ with he
  have he0 : 0 < e := Nat.card_pos
  have hpow : Ideal.Quotient.mk 𝔣 (α ^ (2 * e)) = 1 := by
    rw [map_pow, ← hu, pow_mul', ← Units.val_pow_eq_pow_val, pow_card_eq_one']
    simp
  refine ⟨𝔞 ^ (h * (2 * e) - 1), α ^ (2 * e), ⟨hne _, ?_⟩, pow_ne_zero _ hα0, ?_, ?_, ?_⟩
  · exact Ideal.isCoprime_iff_sup_eq.1 hco.pow_left
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hpow, map_one, sub_self]
  · intro σ
    have : σ ((α : F)) ≠ 0 := (map_ne_zero σ).2 (by simpa using hα0)
    have e1 : ((α ^ (2 * e) : 𝓞 F) : F) = (α : F) ^ (2 * e) := rfl
    rw [e1, map_pow]
    exact (even_two_mul e).pow_pos this
  · have hpos : 0 < h * (2 * e) := by positivity
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_mul, hα', Ideal.span_singleton_pow]

theorem RayPoint.exists_ideal [IsTotallyReal F] {𝔣 𝔞 𝔟 : Ideal (𝓞 F)} {x₀ ξ : 𝓞 F} (hx0 : x₀ ≠ 0) (hx1 : x₀ - 1 ∈ 𝔣)
    (hxp : TotPos F (x₀ : F)) (hab : 𝔞 * 𝔟 = Ideal.span {x₀}) (h : RayPoint 𝔣 𝔟 ξ) :
    ∃ I : Ideal (𝓞 F), (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞) ∧ I * 𝔟 = Ideal.span {ξ} := by
  obtain ⟨h1, h2, h3⟩ := h
  have hξ : ξ ≠ 0 := fun e => h3.ne_zero (by simp [e])
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  refine ⟨I, ⟨⟨?_, ?_⟩, x₀, ξ, hx0, hξ, hx1, h2, fun σ => ⟨hxp σ, h3 σ⟩, ?_⟩, by rw [mul_comm, hI]⟩
  · rintro rfl
    simp at hI
    exact hξ hI
  · have hle : ξ ∈ I := (Ideal.mul_le_right : 𝔟 * I ≤ I) (hI ▸ Ideal.mem_span_singleton_self ξ)
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 F) = ξ - (ξ - 1) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hle) (Ideal.mem_sup_right h2)
  · rw [← hab, hI]
    ring

theorem RayPoint.of_ideal {𝔣 𝔞 𝔟 I : Ideal (𝓞 F)} {x₀ : 𝓞 F} (hx0 : x₀ ≠ 0) (hx1 : x₀ - 1 ∈ 𝔣)
    (hxp : TotPos F (x₀ : F)) (hab : 𝔞 * 𝔟 = Ideal.span {x₀}) (hI : RayRel F 𝔣 I 𝔞) :
    ∃ ξ : 𝓞 F, RayPoint 𝔣 𝔟 ξ ∧ I * 𝔟 = Ideal.span {ξ} := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hp, e⟩ := hI
  have e1 : Ideal.span {a} * (I * 𝔟) = Ideal.span {b * x₀} := by
    rw [← mul_assoc, e, mul_assoc, hab, Ideal.span_singleton_mul_span_singleton]
  obtain ⟨ξ, hξ, hξe⟩ := Ideal.mem_span_singleton_mul.1 (e1 ▸ Ideal.mem_span_singleton_self (b * x₀))
  have e2 : I * 𝔟 = Ideal.span {ξ} := by
    rw [← Ideal.span_singleton_mul_right_inj ha, e1, ← hξe, Ideal.span_singleton_mul_span_singleton]
  refine ⟨ξ, ⟨(Ideal.mul_le_right : I * 𝔟 ≤ 𝔟) hξ, ?_, fun σ => ?_⟩, e2⟩
  · have : ξ - 1 = (b * (x₀ - 1) + (b - 1) - (a - 1)) - (a - 1) * (ξ - 1) := by linear_combination hξe
    rw [this]
    exact 𝔣.sub_mem (𝔣.sub_mem (𝔣.add_mem (𝔣.mul_mem_left _ hx1) hb1) ha1) (𝔣.mul_mem_right _ ha1)
  · have e3 : σ (a : F) * σ (ξ : F) = σ (b : F) * σ (x₀ : F) := by
      have : (a : F) * (ξ : F) = (b : F) * (x₀ : F) := congrArg (fun z : 𝓞 F => (z : F)) hξe
      have h2 := congrArg σ this
      rwa [map_mul, map_mul] at h2
    exact (mul_pos_iff_of_pos_left (hp σ).1).1 (e3 ▸ mul_pos (hp σ).2 (hxp σ))

theorem RayPoint.exists_unit [IsTotallyReal F] {𝔣 𝔟 : Ideal (𝓞 F)} {ξ ξ' : 𝓞 F} (h : RayPoint 𝔣 𝔟 ξ) (h' : RayPoint 𝔣 𝔟 ξ')
    (e : Ideal.span {ξ} = Ideal.span {ξ'}) : ∃ u ∈ congUnits 𝔣, ξ' = (u : 𝓞 F) * ξ := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 e
  refine ⟨u, ⟨?_, fun σ => ?_⟩, by rw [← hu, mul_comm]⟩
  · have : (u : 𝓞 F) - 1 = ((ξ' - 1) - (ξ - 1)) - (ξ - 1) * ((u : 𝓞 F) - 1) := by linear_combination hu
    rw [this]
    exact 𝔣.sub_mem (𝔣.sub_mem h'.2.1 h.2.1) (𝔣.mul_mem_right _ h.2.1)
  · have e3 : σ (ξ : F) * σ (((u : 𝓞 F)) : F) = σ (ξ' : F) := by
      rw [← map_mul]
      congr 1
      exact congrArg (fun z : 𝓞 F => (z : F)) hu
    exact (mul_pos_iff_of_pos_left (h.2.2 σ)).1 (e3 ▸ h'.2.2 σ)

theorem RayPoint.unit_mul {𝔣 𝔟 : Ideal (𝓞 F)} {ξ : 𝓞 F} (h : RayPoint 𝔣 𝔟 ξ) {u : (𝓞 F)ˣ} (hu : u ∈ congUnits 𝔣) :
    RayPoint 𝔣 𝔟 ((u : 𝓞 F) * ξ) := by
  refine ⟨𝔟.mul_mem_left _ h.1, ?_, fun σ => ?_⟩
  · have : (u : 𝓞 F) * ξ - 1 = (u : 𝓞 F) * (ξ - 1) + ((u : 𝓞 F) - 1) := by ring
    rw [this]
    exact 𝔣.add_mem (𝔣.mul_mem_left _ h.2.1) hu.1
  · have e1 : (((u : 𝓞 F) * ξ : 𝓞 F) : F) = ((u : 𝓞 F) : F) * (ξ : F) := rfl
    rw [e1, map_mul]
    exact mul_pos (hu.2 σ) (h.2.2 σ)

theorem exists_nat_mul_integer (x : F) : ∃ (D : ℕ) (z : 𝓞 F), 0 < D ∧ (z : F) = (D : F) * x := by
  obtain ⟨y, hy, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 F, (z : F) = y • x := ⟨⟨_, hi⟩, rfl⟩
  refine ⟨y.natAbs * y.natAbs, (y : 𝓞 F) * z, Nat.mul_pos (Int.natAbs_pos.2 hy) (Int.natAbs_pos.2 hy), ?_⟩
  have e1 : (((y : 𝓞 F) * z : 𝓞 F) : F) = (y : F) * (z : F) := by simp [RingOfIntegers.coe_eq_algebraMap]
  have e2 : ((y.natAbs * y.natAbs : ℕ) : F) = (y : F) * (y : F) := by
    have := congrArg (Int.cast : ℤ → F) (Int.natAbs_mul_self' y)
    rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast] at this
    rw [Nat.cast_mul]
    exact this
  rw [e1, hz, e2, zsmul_eq_mul]
  ring

theorem exists_scaled {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {ι : Type} [Fintype ι] (r : ι → ℕ) (v : ∀ c, Fin (r c) → F) :
    ∃ (N : ℕ) (w : ∀ c, Fin (r c) → 𝓞 F), 0 < N ∧ ∀ c i, w c i ∈ 𝔪 ∧ (w c i : F) = (N : F) * v c i := by
  classical
  choose D z hD hz using fun c i => exists_nat_mul_integer (v c i)
  set P : ℕ := ∏ c, ∏ i, D c i with hP
  have hP0 : 0 < P := Finset.prod_pos fun c _ => Finset.prod_pos fun i _ => hD c i
  have hdvd : ∀ c i, D c i ∣ P := fun c i =>
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans (Finset.dvd_prod_of_mem (fun c => ∏ i, D c i) (Finset.mem_univ c))
  choose k hk using hdvd
  set M : ℕ := Ideal.absNorm 𝔪 with hM
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by simpa [hM, Ideal.absNorm_eq_zero_iff] using h𝔪)
  refine ⟨M * P, fun c i => (M : 𝓞 F) * ((k c i : 𝓞 F) * z c i), Nat.mul_pos hM0 hP0, fun c i => ⟨𝔪.mul_mem_right _ (Ideal.absNorm_mem 𝔪), ?_⟩⟩
  have e1 : (((M : 𝓞 F) * ((k c i : 𝓞 F) * z c i) : 𝓞 F) : F) = (M : F) * ((k c i : F) * (z c i : F)) := by
    simp [RingOfIntegers.coe_eq_algebraMap]
  rw [e1, hz, hk c i]
  push_cast
  ring

theorem mem_openCone_scale {r : ℕ} {v : Fin r → F} {N : ℕ} (hN : 0 < N) {u : Fin r → F} (hu : ∀ i, u i = (N : F) * v i) {x : F} :
    x ∈ openCone u ↔ x ∈ openCone v := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t i * N, fun i => mul_pos (ht i) hNq, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [hu]
    push_cast
    ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t i / N, fun i => div_pos (ht i) hNq, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [hu]
    push_cast
    field_simp

theorem IsConeDomain.scale {𝔣 : Ideal (𝓞 F)} {ι : Type} {r : ι → ℕ} {v : ∀ c, Fin (r c) → F} (h : IsConeDomain 𝔣 r v) {N : ℕ} (hN : 0 < N)
    {u : ∀ c, Fin (r c) → F} (hu : ∀ c i, u c i = (N : F) * v c i) : IsConeDomain 𝔣 r u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨h1, fun c => ?_, fun c i σ => ?_, fun x hx => ?_⟩
  · have := (h2 c).units_smul (fun _ => Units.mk0 (N : ℚ) hNq)
    convert this using 1
    funext i
    simp [hu, Units.smul_def, Rat.smul_def]
  · rw [hu, map_mul, map_natCast]
    exact mul_pos (by exact_mod_cast hN) (h3 c i σ)
  · simpa only [mem_openCone_scale hN (hu _)] using h4 x hx

theorem sum_coef_unique {r : ℕ} {u : Fin r → F} (h : LinearIndependent ℚ u) {t s : Fin r → ℚ}
    (e : ∑ i, (t i : F) * u i = ∑ i, (s i : F) * u i) : t = s := by
  funext i
  have := Fintype.linearIndependent_iff.1 h (fun i => t i - s i) (by
    simp only [Rat.smul_def, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib, e, sub_self]) i
  linarith

theorem frac_unique {s s' : ℚ} {m m' : ℕ} (h0 : 0 < s) (h1 : s ≤ 1) (h0' : 0 < s') (h1' : s' ≤ 1) (e : s + m = s' + m') : m = m' := by
  have a : (m : ℚ) < m' + 1 := by linarith
  have b : (m' : ℚ) < m + 1 := by linarith
  have a' : m < m' + 1 := by exact_mod_cast a
  have b' : m' < m + 1 := by exact_mod_cast b
  omega

theorem exists_frac {t : ℚ} (h : 0 < t) : ∃ (m : ℕ) (s : ℚ), 0 < s ∧ s ≤ 1 ∧ t = s + m := by
  have hc : 0 < ⌈t⌉₊ := Nat.ceil_pos.2 h
  refine ⟨⌈t⌉₊ - 1, t - ((⌈t⌉₊ - 1 : ℕ) : ℚ), ?_, ?_, by ring⟩
  · rw [Nat.cast_sub hc]
    have := Nat.ceil_lt_add_one h.le
    push_cast
    linarith
  · rw [Nat.cast_sub hc]
    have := Nat.le_ceil t
    push_cast
    linarith

theorem totPos_sum {r : ℕ} (hr : 0 < r) {u : Fin r → F} (hu : ∀ i, TotPos F (u i)) {t : Fin r → ℚ} (ht : ∀ i, 0 < t i) :
    TotPos F (∑ i, (t i : F) * u i) := fun σ => by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [map_sum]
  refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
  rw [map_mul, map_ratCast]
  exact mul_pos (by exact_mod_cast ht i) (hu i σ)

def coneBox (𝔣 𝔟 : Ideal (𝓞 F)) {r : ℕ} (w : Fin r → 𝓞 F) : Set (𝓞 F) :=
  {y | RayPoint 𝔣 𝔟 y ∧ ∃ t : Fin r → ℚ, (∀ i, 0 < t i ∧ t i ≤ 1) ∧ (y : F) = ∑ i, (t i : F) * (w i : F)}

theorem coneBox_finite (𝔣 𝔟 : Ideal (𝓞 F)) {r : ℕ} (w : Fin r → 𝓞 F) : (coneBox 𝔣 𝔟 w).Finite := by
  have hB := Embeddings.finite_of_norm_le F ℂ (∑ φ : F →+* ℂ, ∑ i, ‖φ (w i : F)‖)
  refine Set.Finite.of_finite_image (f := fun y : 𝓞 F => (y : F)) (hB.subset ?_) RingOfIntegers.coe_injective.injOn
  rintro _ ⟨y, ⟨-, t, ht, e⟩, rfl⟩
  refine ⟨y.isIntegral_coe, fun φ => ?_⟩
  have h1 : ‖φ (y : F)‖ ≤ ∑ i, ‖φ (w i : F)‖ := by
    rw [e, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, map_ratCast, norm_mul, Complex.norm_ratCast]
    have : |((t i : ℚ) : ℝ)| ≤ 1 := by
      rw [abs_of_pos (by exact_mod_cast (ht i).1)]
      exact_mod_cast (ht i).2
    exact mul_le_of_le_one_left (norm_nonneg _) this
  exact h1.trans (Finset.single_le_sum (f := fun φ : F →+* ℂ => ∑ i, ‖φ (w i : F)‖)
    (fun φ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ φ))

theorem coe_add_sum {r : ℕ} (w : Fin r → 𝓞 F) {a : 𝓞 F} {t : Fin r → ℚ} (e : (a : F) = ∑ i, (t i : F) * (w i : F)) (m : Fin r → ℕ) :
    ((a + ∑ i, (m i : 𝓞 F) * w i : 𝓞 F) : F) = ∑ i, ((t i + m i : ℚ) : F) * (w i : F) := by
  have h1 : ((a + ∑ i, (m i : 𝓞 F) * w i : 𝓞 F) : F) = (a : F) + ∑ i, ((m i : ℚ) : F) * (w i : F) := by
    simp [RingOfIntegers.coe_eq_algebraMap]
  rw [h1, e, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by push_cast; ring

theorem classParam_of_scaled [IsTotallyReal F] {𝔣 𝔞 𝔟 : Ideal (𝓞 F)} {x₀ : 𝓞 F} (h𝔟 : 𝔟 ≠ ⊥) (hx0 : x₀ ≠ 0) (hx1 : x₀ - 1 ∈ 𝔣)
    (hxp : TotPos F (x₀ : F)) (hab : 𝔞 * 𝔟 = Ideal.span {x₀}) {ι : Type} [Fintype ι] {r : ι → ℕ} {w : ∀ c, Fin (r c) → 𝓞 F}
    (hdom : IsConeDomain 𝔣 r (fun c i => (w c i : F))) (hwb : ∀ c i, w c i ∈ 𝔟) (hwf : ∀ c i, w c i ∈ 𝔣) :
    ∃ (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r' y v' := by
  classical
  obtain ⟨hr, hli, hpos, hun⟩ := hdom
  haveI : ∀ c, Fintype (coneBox 𝔣 𝔟 (w c)) := fun c => (coneBox_finite 𝔣 𝔟 (w c)).fintype
  let J : Type := Σ c, coneBox 𝔣 𝔟 (w c)
  let r' : J → ℕ := fun j => r j.1
  let y : J → 𝓞 F := fun j => j.2.1
  let v' : ∀ j : J, Fin (r' j) → 𝓞 F := fun j => w j.1
  let ξ : (Σ j : J, (Fin (r' j) → ℕ)) → 𝓞 F := fun p => y p.1 + ∑ i, (p.2 i : 𝓞 F) * v' p.1 i
  have hcoef : ∀ p : (Σ j : J, (Fin (r' j) → ℕ)), ∃ t : Fin (r p.1.1) → ℚ, (∀ i, 0 < t i ∧ t i ≤ 1) ∧
      ((ξ p : 𝓞 F) : F) = ∑ i, ((t i + p.2 i : ℚ) : F) * (w p.1.1 i : F) := fun p => by
    obtain ⟨t, ht, e⟩ := p.1.2.2.2
    exact ⟨t, ht, coe_add_sum (w p.1.1) e p.2⟩
  have hcone : ∀ p : (Σ j : J, (Fin (r' j) → ℕ)), ((ξ p : 𝓞 F) : F) ∈ openCone (fun i => (w p.1.1 i : F)) := fun p => by
    obtain ⟨t, ht, e⟩ := hcoef p
    exact ⟨fun i => t i + p.2 i, fun i => add_pos_of_pos_of_nonneg (ht i).1 (Nat.cast_nonneg _), e⟩
  have hpoint : ∀ p, RayPoint 𝔣 𝔟 (ξ p) := fun p => by
    have ha := p.1.2.2.1
    refine ⟨𝔟.add_mem ha.1 (𝔟.sum_mem fun i _ => 𝔟.mul_mem_left _ (hwb _ i)), ?_, ?_⟩
    · have : ξ p - 1 = (y p.1 - 1) + ∑ i, (p.2 i : 𝓞 F) * v' p.1 i := by
        change y p.1 + ∑ i, (p.2 i : 𝓞 F) * v' p.1 i - 1 = _
        ring
      rw [this]
      exact 𝔣.add_mem ha.2.1 (𝔣.sum_mem fun i _ => 𝔣.mul_mem_left _ (hwf _ i))
    · obtain ⟨t, ht, e⟩ := hcoef p
      rw [e]
      exact totPos_sum (hr _) (hpos _) fun i => add_pos_of_pos_of_nonneg (ht i).1 (Nat.cast_nonneg _)
  have hI := fun p => (hpoint p).exists_ideal hx0 hx1 hxp hab
  choose f hf hfe using hI
  let f' : (Σ j : J, (Fin (r' j) → ℕ)) → {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} := fun p => ⟨f p, hf p⟩
  have hinj : Function.Injective f' := by
    intro p p' hpp
    have hs : Ideal.span {ξ p} = Ideal.span {ξ p'} := by
      rw [← hfe p, ← hfe p']
      exact congrArg (· * 𝔟) (congrArg Subtype.val hpp)
    obtain ⟨u, hu, hue⟩ := (hpoint p).exists_unit (hpoint p') hs
    obtain ⟨q, -, hq⟩ := hun _ (hpoint p).2.2
    have h1u : (1 : (𝓞 F)ˣ) ∈ congUnits 𝔣 := ⟨by simp, fun σ => by simp⟩
    have e1 := hq (⟨1, h1u⟩, p.1.1) (by simpa using hcone p)
    have e2 := hq (⟨u, hu⟩, p'.1.1) (by
      have := hcone p'
      rw [hue] at this
      exact this)
    have e3 := e1.trans e2.symm
    have hc : p.1.1 = p'.1.1 := congrArg Prod.snd e3
    have hu1 : u = 1 := (congrArg (fun z : congUnits 𝔣 × ι => (z.1 : (𝓞 F)ˣ)) e3).symm
    have hξ : ξ p' = ξ p := by rw [hue, hu1]; simp
    obtain ⟨t, ht, e⟩ := hcoef p
    obtain ⟨t', ht', e'⟩ := hcoef p'
    obtain ⟨⟨c, a, ha⟩, m⟩ := p
    obtain ⟨⟨c', a', ha'⟩, m'⟩ := p'
    obtain rfl : c = c' := hc
    rw [hξ] at e'
    have ht2 := sum_coef_unique (hli c) (e.symm.trans e')
    have hm : m = m' := funext fun i => frac_unique (ht i).1 (ht i).2 (ht' i).1 (ht' i).2 (congrFun ht2 i)
    subst hm
    have ha2 : a' = a := add_right_cancel hξ
    subst ha2
    rfl
  have hsurj : Function.Surjective f' := by
    rintro ⟨I, hI1, hI2⟩
    obtain ⟨ξ₀, hξ₀, hIe⟩ := RayPoint.of_ideal hx0 hx1 hxp hab hI2
    obtain ⟨⟨⟨u, hu⟩, c⟩, hmem, -⟩ := hun _ hξ₀.2.2
    obtain ⟨t, ht, e⟩ := hmem
    have h₁ := hξ₀.unit_mul hu
    have hspan : Ideal.span {(u : 𝓞 F) * ξ₀} = Ideal.span {ξ₀} :=
      Ideal.span_singleton_eq_span_singleton.2 (Associated.symm ⟨u, mul_comm _ _⟩)
    choose m s hs0 hs1 hts using fun i => exists_frac (ht i)
    set S : 𝓞 F := ∑ i, (m i : 𝓞 F) * w c i with hS
    have hSc : (S : F) = ∑ i, ((m i : ℚ) : F) * (w c i : F) := by simp [hS, RingOfIntegers.coe_eq_algebraMap]
    have hSf : S ∈ 𝔣 := 𝔣.sum_mem fun i _ => 𝔣.mul_mem_left _ (hwf c i)
    have hSb : S ∈ 𝔟 := 𝔟.sum_mem fun i _ => 𝔟.mul_mem_left _ (hwb c i)
    have ha_coe : ((((u : 𝓞 F) * ξ₀ - S : 𝓞 F)) : F) = ∑ i, (s i : F) * (w c i : F) := by
      have h3 : ((((u : 𝓞 F) * ξ₀ - S : 𝓞 F)) : F) = ((u : 𝓞 F) : F) * (ξ₀ : F) - (S : F) := by
        simp [RingOfIntegers.coe_eq_algebraMap]
      rw [h3, e, hSc, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hts i]; push_cast; ring
    have ha : RayPoint 𝔣 𝔟 ((u : 𝓞 F) * ξ₀ - S) := by
      refine ⟨𝔟.sub_mem h₁.1 hSb, ?_, ?_⟩
      · have : (u : 𝓞 F) * ξ₀ - S - 1 = ((u : 𝓞 F) * ξ₀ - 1) - S := by ring
        rw [this]
        exact 𝔣.sub_mem h₁.2.1 hSf
      · rw [ha_coe]
        exact totPos_sum (hr c) (hpos c) hs0
    let p : (Σ j : J, (Fin (r' j) → ℕ)) := ⟨⟨c, _, ha, s, fun i => ⟨hs0 i, hs1 i⟩, ha_coe⟩, m⟩
    have hp : ξ p = (u : 𝓞 F) * ξ₀ := sub_add_cancel _ _
    refine ⟨p, Subtype.ext (mul_right_cancel₀ h𝔟 ?_)⟩
    change f p * 𝔟 = I * 𝔟
    rw [hfe, hp, hspan, hIe]
  refine ⟨J, inferInstance, r', y, v', h𝔟, fun j => ⟨j.2.2.1.1, j.2.2.1.2.2⟩, fun j i => ⟨hwb _ _, hpos _ _⟩, fun j => ?_,
    Equiv.ofBijective f' ⟨hinj, hsurj⟩, fun p => hfe p⟩
  simpa using (hli j.1).fintype_card_le_finrank

theorem exists_classParam : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v →
      ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
        ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
          ClassParam 𝔣 𝔞 𝔟 r' y v' := by
  intro F _ _ _ 𝔣 h𝔣 ι _ r v hdom 𝔞 h𝔞
  obtain ⟨𝔟, x₀, hb, hx0, hx1, hxp, hab⟩ := exists_complement h𝔣 h𝔞
  obtain ⟨N, w, hN, hw⟩ := exists_scaled (𝔪 := 𝔟 * 𝔣) (mul_ne_zero hb.1 h𝔣) r v
  have hd := hdom.scale hN (u := fun c i => (w c i : F)) (fun c i => (hw c i).2)
  obtain ⟨J, a, b, c, d, e⟩ := classParam_of_scaled hb.1 hx0 hx1 hxp hab hd
    (fun c i => (Ideal.mul_le_left : 𝔟 * 𝔣 ≤ 𝔟) (hw c i).1)
    (fun c i => (Ideal.mul_le_right : 𝔟 * 𝔣 ≤ 𝔣) (hw c i).1)
  exact ⟨𝔟, J, a, b, c, d, e⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_cone_parametrization : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam <;> assumption)
end

section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_zeta_twisted_entire_difference : AbelContinuation → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
    (∀ j i, v j i ∉ 𝔠 * 𝔟) →
    ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classTwist_entire <;> assumption)
end

section
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem norm_natCast_cpow_neg (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : -s ≠ 0 := fun h => by
      have : s = 0 := neg_eq_zero.mp h
      simp [this] at hs
      linarith
    have h1 : -s.re ≠ 0 := by linarith
    simp [Complex.zero_cpow h0, Real.zero_rpow h1]
  · simpa using Complex.norm_natCast_cpow_of_pos hn (-s)

theorem classSummable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
    (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
      Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  intro F _ _ _ 𝔣 𝔞 𝔟 J _ r y v _ s hs
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).subtype
    {I : Ideal (𝓞 F) | CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞}
  refine Summable.of_norm (h.congr fun I => ?_)
  exact (norm_natCast_cpow_neg _ hs).symm

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_zeta_ray_class_summable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
  (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classSummable
end

section
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
open Polynomial

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_large_prime_dvd_eval (f : ℤ[X]) (hf : 0 < f.natDegree) (N : ℕ) :
    ∃ (p : ℕ) (m : ℤ), p.Prime ∧ N < p ∧ (p : ℤ) ∣ f.eval m :=
  _root_.UpperTheory.Reformulated.B.P6.LargePrimeDivisors.GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_large_prime_dvd_eval f hf N

theorem exists_exponent_ne_zero (F : Type) [Field F] [NumberField F] :
    ∃ θ : 𝓞 F, RingOfIntegers.exponent θ ≠ 0 := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic α))
  obtain ⟨θ, hθ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨θ, ?_⟩
  have hθ' : (θ : F) = y • α := hθ
  have hprim : IntermediateField.adjoin ℚ {(θ : F)} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
    have h : (θ : F) ∈ IntermediateField.adjoin ℚ {(θ : F)} :=
      IntermediateField.mem_adjoin_simple_self ℚ _
    have hyF : (y : F) ≠ 0 := by exact_mod_cast hy
    have e : α = ((y : ℚ)⁻¹) • (θ : F) := by
      rw [hθ', Algebra.smul_def, zsmul_eq_mul]
      simp [hyF]
    rw [e]
    exact (IntermediateField.adjoin ℚ {(θ : F)}).smul_mem h
  have hintZ : IsIntegral ℤ (θ : F) := RingOfIntegers.isIntegral_coe θ
  have hintQ : IsIntegral ℚ (θ : F) := Algebra.IsIntegral.isIntegral _
  have htop : Algebra.adjoin ℚ {(θ : F)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hintQ.isAlgebraic, hprim,
      IntermediateField.top_toSubalgebra]
  let B := PowerBasis.ofAdjoinEqTop hintQ htop
  have hgen : B.gen = θ := PowerBasis.ofAdjoinEqTop_gen hintQ htop
  have hintB : IsIntegral ℤ B.gen := hgen ▸ hintZ
  have hdi : IsIntegral ℤ (Algebra.discr ℚ B.basis) := Algebra.discr_isIntegral ℚ (fun i => by
    rw [PowerBasis.coe_basis]
    exact hintB.pow _)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hdi
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Algebra.discr_not_zero_of_basis ℚ B.basis (by simpa using hn.symm)
  have hcond : (n : 𝓞 F) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro b
    have h1 := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hintB (RingOfIntegers.isIntegral_coe b)
    rw [hgen, ← hn] at h1
    have h2 : ((n : F) * (b : F)) ∈ Algebra.adjoin ℤ {(θ : F)} := by
      simpa [Algebra.smul_def] using h1
    have h3 : Algebra.adjoin ℤ {(θ : F)} =
        (Algebra.adjoin ℤ {θ}).map (IsScalarTower.toAlgHom ℤ (𝓞 F) F) := by
      rw [AlgHom.map_adjoin, Set.image_singleton]
      rfl
    rw [h3] at h2
    obtain ⟨u, hu, hue⟩ := h2
    have hub : u = (n : 𝓞 F) * b := RingOfIntegers.coe_injective (by simpa using hue)
    exact hub ▸ hu
  intro h0
  rw [RingOfIntegers.exponent, Ideal.absNorm_eq_zero_iff] at h0
  have hm : n ∈ Ideal.under ℤ (conductor ℤ θ) := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using hcond
  rw [h0] at hm
  exact hn0 (by simpa using hm)

theorem exists_isPrime_absNorm_eq {F : Type} [Field F] [NumberField F] (θ : 𝓞 F) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) (m : ℤ) (hm : (p : ℤ) ∣ (minpoly ℤ θ).eval m) :
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ Ideal.absNorm 𝔠 = p := by
  have h₀ : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have hQ : (X - C ((m : ℤ) : ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff h₀]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.2 ?_⟩
    rw [IsRoot.def, eval_intCast_map]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hm
  let P := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩
  have hf := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ
  have hPp : (P : Ideal (𝓞 F)).IsPrime := P.2.1
  have hPl : (P : Ideal (𝓞 F)).LiesOver (Ideal.span {(p : ℤ)}) := P.2.2
  refine ⟨P, hPp, ?_⟩
  rw [← Ideal.pow_inertiaDeg p (P : Ideal (𝓞 F)), hf, natDegree_X_sub_C, pow_one]

theorem exists_prime_absNorm_avoiding : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  intro F _ _ 𝔣 h𝔣 W B hW
  obtain ⟨θ, hθ⟩ := exists_exponent_ne_zero F
  obtain ⟨p, m, hp, hN, hdvd⟩ := exists_large_prime_dvd_eval (minpoly ℤ θ)
    (minpoly.natDegree_pos θ.isIntegral)
    (B + RingOfIntegers.exponent θ + Ideal.absNorm 𝔣 + ∑ x ∈ W, Ideal.absNorm (Ideal.span {x}))
  have := Fact.mk hp
  have hexp : ¬ p ∣ RingOfIntegers.exponent θ := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hθ) h
    omega
  obtain ⟨𝔠, hprime, hnorm⟩ := exists_isPrime_absNorm_eq θ p hexp m hdvd
  have small : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → Ideal.absNorm I < p → ¬ I ≤ 𝔠 := fun I hI hlt hle => by
    have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Ideal.absNorm_dvd_absNorm_of_le hle)
    omega
  have hbot : 𝔠 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hnorm
    exact hp.ne_zero hnorm.symm
  have hmax : 𝔠.IsMaximal := hprime.isMaximal hbot
  refine ⟨𝔠, hprime, hnorm ▸ hp, by omega, ?_, ?_⟩
  · by_contra h
    exact small 𝔣 h𝔣 (by omega) (sup_eq_left.1 (hmax.eq_of_le h le_sup_left).symm)
  · intro x hx hxc
    have hle : Ideal.absNorm (Ideal.span {x}) ≤ ∑ x ∈ W, Ideal.absNorm (Ideal.span {x}) :=
      Finset.single_le_sum (f := fun x => Ideal.absNorm (Ideal.span {x})) (fun _ _ => Nat.zero_le _) hx
    exact small (Ideal.span {x}) (by simpa using hW x hx) (by omega)
      ((Ideal.span_singleton_le_iff_mem _).2 hxc)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_degree_one_avoiding : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
  ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ 𝔠 ⊔ 𝔣 = ⊤ ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_prime_absNorm_avoiding
end

section
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations

open Filter Topology

noncomputable def mult (l : ℕ) (s : ℂ) : ℂ := (l : ℂ) ^ (1 - s)

noncomputable def efac (l h : ℕ) (s : ℂ) : ℂ := mult l s ^ h - 1

noncomputable def wsum {G : Type} (T : G → ℂ → ℂ) (l : ℕ) (τ : Equiv.Perm G) (h : ℕ)
    (c : G) (s : ℂ) : ℂ :=
  ∑ e ∈ Finset.range h, mult l s ^ e * T ((τ ^ e) c) s

lemma mult_differentiable {l : ℕ} (hl : l.Prime) : Differentiable ℂ (mult l) := by
  intro s
  have h0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  exact ((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl h0)

lemma efac_differentiable {l : ℕ} (hl : l.Prime) (h : ℕ) : Differentiable ℂ (efac l h) := by
  intro s
  exact (((mult_differentiable hl) s).pow h).sub (differentiableAt_const _)

lemma wsum_differentiable {G : Type} {T : G → ℂ → ℂ} {l : ℕ} (hl : l.Prime)
    (hT : ∀ c, Differentiable ℂ (T c)) (τ : Equiv.Perm G) (h : ℕ) (c : G) :
    Differentiable ℂ (wsum T l τ h c) := by
  intro s
  unfold wsum
  refine DifferentiableAt.fun_sum fun e _ => ?_
  exact (((mult_differentiable hl) s).pow e).mul (hT _ s)

lemma norm_mult_lt_one {l : ℕ} (hl : l.Prime) {s : ℂ} (hs : 1 < s.re) : ‖mult l s‖ < 1 := by
  unfold mult
  rw [Complex.norm_natCast_cpow_of_pos hl.pos]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hl.one_lt
  · simp only [Complex.sub_re, Complex.one_re]; linarith

lemma efac_ne_zero {l h : ℕ} (hl : l.Prime) (hh : h ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    efac l h s ≠ 0 := by
  intro h0
  have h1 : mult l s ^ h = 1 := sub_eq_zero.mp h0
  have h2 : ‖mult l s‖ ^ h = 1 := by rw [← norm_pow, h1, norm_one]
  have h3 := pow_lt_one₀ (norm_nonneg _) (norm_mult_lt_one hl hs) hh
  linarith

lemma telescope {G : Type} {D T : G → ℂ → ℂ} {l : ℕ} {τ : Equiv.Perm G} {s : ℂ}
    (hrel : ∀ c, mult l s * D (τ c) s - D c s = T c s) (c : G) (n : ℕ) :
    wsum T l τ n c s = mult l s ^ n * D ((τ ^ n) c) s - D c s := by
  induction n with
  | zero => simp [wsum]
  | succ n ih =>
    have ih' : ∑ e ∈ Finset.range n, mult l s ^ e * T ((τ ^ e) c) s
        = mult l s ^ n * D ((τ ^ n) c) s - D c s := ih
    have hstep : (τ ^ (n + 1)) c = τ ((τ ^ n) c) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    unfold wsum
    rw [Finset.sum_range_succ, ih', ← hrel ((τ ^ n) c), hstep]
    ring

lemma efac_mul_eq {G : Type} [Fintype G] {D T : G → ℂ → ℂ} {l : ℕ} {τ : Equiv.Perm G} {s : ℂ}
    (hrel : ∀ c, mult l s * D (τ c) s - D c s = T c s) (c : G) :
    efac l (orderOf τ) s * D c s = wsum T l τ (orderOf τ) c s := by
  rw [telescope hrel c, pow_orderOf_eq_one]
  simp only [efac, Equiv.Perm.coe_one, id_eq]
  ring

lemma no_common_zero {l l' h h' : ℕ} (hl : l.Prime) (hl' : l'.Prime) (hne : l ≠ l')
    (hh : h ≠ 0) (hh' : h' ≠ 0) {s : ℂ} (hs : s ≠ 1)
    (h1 : efac l h s = 0) (h2 : efac l' h' s = 0) : False := by
  have hexp : ∀ {p : ℕ}, p.Prime → ∀ m : ℕ, mult p s ^ m
      = Complex.exp ((m : ℂ) * (((Real.log p : ℝ) : ℂ) * (1 - s))) := by
    intro p hp m
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [Complex.exp_nat_mul, mult, Complex.cpow_def_of_ne_zero hp0, Complex.natCast_log]
  have hu : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hL : 0 < Real.log l := Real.log_pos (by exact_mod_cast hl.one_lt)
  have hL' : 0 < Real.log l' := Real.log_pos (by exact_mod_cast hl'.one_lt)
  have e1 : Complex.exp ((h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s))) = 1 := by
    rw [← hexp hl]; exact sub_eq_zero.mp h1
  have e2 : Complex.exp ((h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s))) = 1 := by
    rw [← hexp hl']; exact sub_eq_zero.mp h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e1
  obtain ⟨n', hn'⟩ := Complex.exp_eq_one_iff.mp e2
  have hLc : ((Real.log l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLc' : ((Real.log l' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL'.ne'
  have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hhc' : (h' : ℂ) ≠ 0 := by exact_mod_cast hh'
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : (h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s)) ≠ 0 :=
      mul_ne_zero hhc (mul_ne_zero hLc hu)
    apply this; rw [hn]; simp
  have hn0' : n' ≠ 0 := by
    rintro rfl
    have : (h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s)) ≠ 0 :=
      mul_ne_zero hhc' (mul_ne_zero hLc' hu)
    apply this; rw [hn']; simp
  have hcross : ((n' : ℂ) * h * ((Real.log l : ℝ) : ℂ)) = (n : ℂ) * h' * ((Real.log l' : ℝ) : ℂ) := by
    apply mul_right_cancel₀ hu
    calc (n' : ℂ) * h * ((Real.log l : ℝ) : ℂ) * (1 - s)
        = (n' : ℂ) * ((h : ℂ) * (((Real.log l : ℝ) : ℂ) * (1 - s))) := by ring
      _ = (n : ℂ) * ((h' : ℂ) * (((Real.log l' : ℝ) : ℂ) * (1 - s))) := by
          rw [hn, hn']; ring
      _ = (n : ℂ) * h' * ((Real.log l' : ℝ) : ℂ) * (1 - s) := by ring
  have hreal : (n' : ℝ) * h * Real.log l = (n : ℝ) * h' * Real.log l' := by
    exact_mod_cast hcross
  have habs : (n'.natAbs : ℝ) * h * Real.log l = (n.natAbs : ℝ) * h' * Real.log l' := by
    have := congrArg abs hreal
    simp only [abs_mul, Nat.abs_cast, abs_of_pos hL, abs_of_pos hL'] at this
    rw [Nat.cast_natAbs, Nat.cast_natAbs]
    push_cast
    exact this
  have hlog : Real.log ((l : ℝ) ^ (n'.natAbs * h)) = Real.log ((l' : ℝ) ^ (n.natAbs * h')) := by
    rw [Real.log_pow, Real.log_pow]
    push_cast
    exact habs
  have hpos : (0 : ℝ) < (l : ℝ) ^ (n'.natAbs * h) := by
    have : (0 : ℝ) < l := by exact_mod_cast hl.pos
    positivity
  have hpos' : (0 : ℝ) < (l' : ℝ) ^ (n.natAbs * h') := by
    have : (0 : ℝ) < l' := by exact_mod_cast hl'.pos
    positivity
  have heq := Real.log_injOn_pos (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hpos') hlog
  have hnat : l ^ (n'.natAbs * h) = l' ^ (n.natAbs * h') := by exact_mod_cast heq
  have hexp0 : n'.natAbs * h ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hn0') hh
  have hdvd : l ∣ l' ^ (n.natAbs * h') := by
    rw [← hnat]; exact dvd_pow_self l hexp0
  exact hne ((Nat.prime_dvd_prime_iff_eq hl hl').mp (hl.dvd_of_dvd_pow hdvd))

lemma entire_eq_of_halfplane {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  have hfa : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := hopen.mem_nhds (by simp)
  refine hfa.eq_of_eventuallyEq hga (z₀ := 2) ?_
  filter_upwards [hmem] with s hs using hfg s hs

lemma glue_differentiableAt {E E' W W' : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hE' : Differentiable ℂ E') (hW : Differentiable ℂ W) (hW' : Differentiable ℂ W')
    (hcross : ∀ s, W s * E' s = W' s * E s) {s : ℂ} (hs : E s ≠ 0 ∨ E' s ≠ 0) :
    DifferentiableAt ℂ (fun t => if E t ≠ 0 then W t / E t else W' t / E' t) s := by
  by_cases h : E s ≠ 0
  · have hev : ∀ᶠ t in 𝓝 s, E t ≠ 0 := hE.continuous.continuousAt.eventually_ne h
    refine ((hW s).div (hE s) h).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    simp [ht]
  · have h' : E' s ≠ 0 := hs.resolve_left h
    have hev : ∀ᶠ t in 𝓝 s, E' t ≠ 0 := hE'.continuous.continuousAt.eventually_ne h'
    refine ((hW' s).div (hE' s) h').congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [Pi.div_apply]
    by_cases h0 : E t ≠ 0
    · rw [if_pos h0, div_eq_div_iff h0 ht]
      exact hcross t
    · rw [if_neg h0]

lemma mult_at_neg {l k : ℕ} : mult l (1 - (k : ℂ)) = ((l ^ k : ℕ) : ℂ) := by
  simp [mult]

theorem continuation_of_two_relations :
    ∀ (G : Type) [Fintype G] (D T T' : G → ℂ → ℂ) (l l' : ℕ) (τ τ' : Equiv.Perm G),
    l.Prime → l'.Prime → l ≠ l' →
    (∀ c, Differentiable ℂ (T c)) → (∀ c, Differentiable ℂ (T' c)) →
    (∀ c s, 1 < s.re → (l : ℂ) ^ (1 - s) * D (τ c) s - D c s = T c s) →
    (∀ c s, 1 < s.re → (l' : ℂ) ^ (1 - s) * D (τ' c) s - D c s = T' c s) →
    ∃ Z : G → ℂ → ℂ, (∀ c, DifferentiableOn ℂ (Z c) {1}ᶜ) ∧ (∀ c s, 1 < s.re → Z c s = D c s) ∧
      ∀ k : ℕ, 1 ≤ k → (∀ c, ∃ q : ℚ, T c (1 - (k : ℂ)) = (q : ℂ)) →
        ∀ c, ∃ q : ℚ, Z c (1 - (k : ℂ)) = (q : ℂ) := by
  intro G _ D T T' l l' τ τ' hl hl' hne hT hT' hrel hrel'
  have hh : orderOf τ ≠ 0 := (orderOf_pos τ).ne'
  have hh' : orderOf τ' ≠ 0 := (orderOf_pos τ').ne'
  have hED : ∀ c s, 1 < s.re →
      efac l (orderOf τ) s * D c s = wsum T l τ (orderOf τ) c s :=
    fun c s hs => efac_mul_eq (fun c => hrel c s hs) c
  have hED' : ∀ c s, 1 < s.re →
      efac l' (orderOf τ') s * D c s = wsum T' l' τ' (orderOf τ') c s :=
    fun c s hs => efac_mul_eq (fun c => hrel' c s hs) c
  have hEd := efac_differentiable hl (orderOf τ)
  have hEd' := efac_differentiable hl' (orderOf τ')
  have hWd := fun c => wsum_differentiable hl hT τ (orderOf τ) c
  have hWd' := fun c => wsum_differentiable hl' hT' τ' (orderOf τ') c
  have hcross : ∀ c s, wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s
      = wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s := by
    intro c s
    have := entire_eq_of_halfplane
      (f := fun s => wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s)
      (g := fun s => wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s)
      ((hWd c).mul hEd') ((hWd' c).mul hEd)
      (fun s hs => by
        show wsum T l τ (orderOf τ) c s * efac l' (orderOf τ') s
          = wsum T' l' τ' (orderOf τ') c s * efac l (orderOf τ) s
        rw [← hED c s hs, ← hED' c s hs]; ring)
    exact congrFun this s
  refine ⟨fun c t => if efac l (orderOf τ) t ≠ 0 then
      wsum T l τ (orderOf τ) c t / efac l (orderOf τ) t
    else wsum T' l' τ' (orderOf τ') c t / efac l' (orderOf τ') t, ?_, ?_, ?_⟩
  · intro c s hs
    have hs1 : s ≠ 1 := hs
    have hor : efac l (orderOf τ) s ≠ 0 ∨ efac l' (orderOf τ') s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact no_common_zero hl hl' hne hh hh' hs1 hcon.1 hcon.2
    exact (glue_differentiableAt hEd hEd' (hWd c) (hWd' c) (hcross c) hor).differentiableWithinAt
  · intro c s hs
    have h0 := efac_ne_zero hl hh hs
    show (if efac l (orderOf τ) s ≠ 0 then _ else _) = _
    rw [if_pos h0, ← hED c s hs, mul_div_cancel_left₀ _ h0]
  · intro k hk hq c
    choose q hq using hq
    have hm : mult l (1 - (k : ℂ)) = ((l ^ k : ℕ) : ℂ) := mult_at_neg
    have hnat : (l ^ k) ^ orderOf τ ≠ 1 :=
      ne_of_gt (Nat.one_lt_pow hh (Nat.one_lt_pow (by omega) hl.one_lt))
    have hE : efac l (orderOf τ) (1 - (k : ℂ)) = (((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1 : ℚ) : ℂ) := by
      simp only [efac, hm]
      push_cast
      ring
    have h0 : efac l (orderOf τ) (1 - (k : ℂ)) ≠ 0 := by
      rw [hE]
      intro hz
      have hz' : ((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1 : ℚ) = 0 := by exact_mod_cast hz
      apply hnat
      have : (((l ^ k) ^ orderOf τ : ℕ) : ℚ) = 1 := by linarith
      exact_mod_cast this
    have hW : wsum T l τ (orderOf τ) c (1 - (k : ℂ))
        = ((∑ e ∈ Finset.range (orderOf τ), (((l ^ k : ℕ) : ℚ)) ^ e * q ((τ ^ e) c) : ℚ) : ℂ) := by
      simp only [wsum, hm, hq]
      push_cast
      rfl
    refine ⟨(∑ e ∈ Finset.range (orderOf τ), (((l ^ k : ℕ) : ℚ)) ^ e * q ((τ ^ e) c)) /
      ((((l ^ k) ^ orderOf τ : ℕ) : ℚ) - 1), ?_⟩
    show (if efac l (orderOf τ) (1 - (k : ℂ)) ≠ 0 then _ else _) = _
    rw [if_pos h0, hW, hE, Rat.cast_div]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_zeta_meromorphic_from_twists : ∀ (G : Type) [Fintype G] (D T T' : G → ℂ → ℂ) (l l' : ℕ) (τ τ' : Equiv.Perm G), l.Prime → l'.Prime → l ≠ l' →
  (∀ c, Differentiable ℂ (T c)) → (∀ c, Differentiable ℂ (T' c)) →
  (∀ c s, 1 < s.re → (l : ℂ) ^ (1 - s) * D (τ c) s - D c s = T c s) →
  (∀ c s, 1 < s.re → (l' : ℂ) ^ (1 - s) * D (τ' c) s - D c s = T' c s) →
  ∃ Z : G → ℂ → ℂ, (∀ c, DifferentiableOn ℂ (Z c) {1}ᶜ) ∧ (∀ c s, 1 < s.re → Z c s = D c s) ∧
    ∀ k : ℕ, 1 ≤ k → (∀ c, ∃ q : ℚ, T c (1 - (k : ℂ)) = (q : ℂ)) → ∀ c, ∃ q : ℚ, Z c (1 - (k : ℂ)) = (q : ℂ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.TwoRelations.continuation_of_two_relations
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem rayRel_of_mul_left {F : Type} [Field F] [NumberField F] {𝔣 𝔠 I J : Ideal (𝓞 F)} (h𝔠 : 𝔠 ≠ ⊥)
    (h : RayRel F 𝔣 (𝔠 * I) (𝔠 * J)) : RayRel F 𝔣 I J := by
  obtain ⟨a, b, ha, hb, ha', hb', hp, e⟩ := h
  refine ⟨a, b, ha, hb, ha', hb', hp, mul_left_cancel₀ h𝔠 ?_⟩
  rw [mul_left_comm, e, mul_left_comm]

theorem shift_perm (F : Type) [Field F] [NumberField F] (𝔣 𝔠 : Ideal (𝓞 F)) (S : Finset (Ideal (𝓞 F))) (_h𝔣 : 𝔣 ≠ ⊥)
    (_hp : 𝔠.IsPrime) (h0 : 𝔠 ≠ ⊥) (hs : 𝔠 ⊔ 𝔣 = ⊤)
    (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a) (hu : ∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b)
    (hr : ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) :
    ∃ τ : Equiv.Perm S, ∀ c : S,
      ∃ e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} ≃
          {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠},
        ∀ J, (e J).1 = 𝔠 * J.1 := by
  have hc : CoprimeTo F 𝔣 𝔠 := ⟨h0, hs⟩
  have hex : ∀ d : S, ∃ a : S, RayRel F 𝔣 (𝔠 * d.1) a.1 := fun d => by
    obtain ⟨a, ha, h⟩ := hr _ (coprimeTo_mul hc (hS d.1 d.2))
    exact ⟨⟨a, ha⟩, h⟩
  choose φ hφ using hex
  have hinj : Function.Injective φ := fun d d' h => by
    have h1 : RayRel F 𝔣 (𝔠 * d.1) (𝔠 * d'.1) := rayRel_trans (hφ d) (h ▸ rayRel_symm (hφ d'))
    exact Subtype.ext (hu _ d.2 _ d'.2 (rayRel_of_mul_left h0 h1))
  let τ : Equiv.Perm S := (Equiv.ofBijective φ (Finite.injective_iff_bijective.1 hinj)).symm
  have hτ : ∀ c : S, RayRel F 𝔣 (𝔠 * (τ c).1) c.1 := fun c => by
    have h1 : φ (τ c) = c := (Equiv.ofBijective φ (Finite.injective_iff_bijective.1 hinj)).apply_symm_apply c
    have h2 := hφ (τ c)
    rwa [h1] at h2
  refine ⟨τ, fun c => ?_⟩
  let f : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} →
      {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠} := fun J =>
    ⟨𝔠 * J.1, ⟨coprimeTo_mul hc J.2.1, rayRel_trans (rayRel_mul_left 𝔠 J.2.2) (hτ c)⟩, Ideal.mul_le_left⟩
  have hf : Function.Bijective f := by
    constructor
    · intro J J' h
      have h1 : 𝔠 * J.1 = 𝔠 * J'.1 := congrArg (fun x : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠} => x.1) h
      exact Subtype.ext (mul_left_cancel₀ h0 h1)
    · rintro ⟨I, ⟨hI, hIc⟩, hle⟩
      obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 hle
      have hJ0 : J ≠ ⊥ := fun h => hI.1 (by rw [h, Ideal.mul_bot])
      have hJ : CoprimeTo F 𝔣 J :=
        ⟨hJ0, top_le_iff.1 (hI.2 ▸ sup_le_sup_right Ideal.mul_le_right 𝔣)⟩
      exact ⟨⟨J, hJ, rayRel_of_mul_left h0 (rayRel_trans hIc (rayRel_symm (hτ c)))⟩, rfl⟩
  exact ⟨Equiv.ofBijective f hf, fun J => rfl⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_prime_multiplication_permutation : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔠 : Ideal (𝓞 F)) (S : Finset (Ideal (𝓞 F))), 𝔣 ≠ ⊥ → 𝔠.IsPrime → 𝔠 ≠ ⊥ → 𝔠 ⊔ 𝔣 = ⊤ →
  (∀ a ∈ S, CoprimeTo F 𝔣 a) → (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) → (∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) →
  ∃ τ : Equiv.Perm S, ∀ c : S,
    ∃ e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} ≃
        {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1) ∧ I ≤ 𝔠},
      ∀ J, (e J).1 = 𝔠 * J.1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.shift_perm
end

section
section
set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem classWeight_relation (F : Type) [Field F] [NumberField F] (𝔣 𝔠 A B : Ideal (𝓞 F)) (hc : (Ideal.absNorm 𝔠).Prime)
    (e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} ≃
      {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠}) (he : ∀ J, (e J).1 = 𝔠 * J.1)
    (s : ℂ) (t : ℂ) (_hs : 1 < s.re)
    (hA : Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)))
    (hB : Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)))
    (ht : HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) t) :
    ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (1 - s) *
        (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) -
      (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) = t := by
  classical
  have hp0 : ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne_zero
  have hf1 : (fun J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} =>
      ((Ideal.absNorm (e J).1 : ℕ) : ℂ) ^ (-s)) = fun J =>
      ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
    funext J
    rw [he J, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  have h1 : HasSum (fun J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} =>
      ((Ideal.absNorm (e J).1 : ℕ) : ℂ) ^ (-s))
      (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) *
        ∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
    rw [hf1]
    exact hA.hasSum.mul_left _
  have h2 := (e.hasSum_iff (f := fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))).mp h1
  have hι : Function.Injective (fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      (⟨I.1, I.2.1⟩ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B})) := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact h
  have hf3 : ((fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0) ∘
      (fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      (⟨I.1, I.2.1⟩ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B}))) =
      fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
    funext I
    simp only [Function.comp_apply, if_pos I.2.2]
  have h3 : HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0)
      (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) *
        ∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
    refine (hι.hasSum_iff ?_).mp ?_
    · intro x hx
      rw [if_neg]
      intro hle
      exact hx ⟨⟨x.1, x.2, hle⟩, rfl⟩
    · rw [hf3]
      exact h2
  have h4 := (h3.mul_left ((Ideal.absNorm 𝔠 : ℕ) : ℂ)).sub hB.hasSum
  have hf5 : (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) =
      fun I => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * (if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0) -
        ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
    funext I
    unfold classWeight
    split_ifs <;> push_cast <;> ring
  rw [hf5] at ht
  rw [ht.unique h4, sub_eq_add_neg (1 : ℂ) s, Complex.cpow_add _ _ hp0, Complex.cpow_one, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_zeta_prime_twist_summable : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔠 A B : Ideal (𝓞 F)), (Ideal.absNorm 𝔠).Prime →
  ∀ e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} ≃
      {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠}, (∀ J, (e J).1 = 𝔠 * J.1) →
  ∀ (s : ℂ) (t : ℂ), 1 < s.re →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) →
    Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) →
    HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) t →
    ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (1 - s) *
        (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) -
      (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) = t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.classWeight_relation
end

section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def classSeries {F : Type} [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)) (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)

theorem exists_avoid_one (𝔣 𝔞 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (h𝔞 : CoprimeTo F 𝔣 𝔞) (ι : Type) [Fintype ι] (r : ι → ℕ)
    (v : ∀ c, Fin (r c) → F) (hv : IsConeDomain 𝔣 r v) :
    ∃ W : Finset (𝓞 F), (∀ x ∈ W, x ≠ 0) ∧
      (∀ s : ℂ, 1 < s.re → Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))) ∧
      ∀ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ x ∈ W, x ∉ 𝔠) →
        ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
          (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
            (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
          ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨𝔟, J, _, r', y, v', hP⟩ := GlobalTheory.T.ray_class_cone_parametrization F 𝔣 h𝔣 ι r v hv 𝔞 h𝔞
  refine ⟨Finset.univ.biUnion fun j : J => Finset.univ.image (v' j), ?_, GlobalTheory.T.partial_zeta_ray_class_summable F 𝔣 𝔞 𝔟 J r' y v' hP, ?_⟩
  · intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, i, rfl⟩ := hx
    intro h0
    have hpos := (hP.2.2.1 j i).2
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have := hpos ((NumberField.InfinitePlace.mk φ).embedding_of_isReal (IsTotallyReal.isReal _))
    simp [h0] at this
  · intro 𝔠 hpr hl hav
    refine GlobalTheory.T.partial_zeta_twisted_entire_difference GlobalTheory.T.abel_continuation F 𝔣 𝔞 𝔟 𝔠 J r' y v' hP hpr hl fun j i hmem => ?_
    have hle : 𝔠 * 𝔟 ≤ 𝔠 := Ideal.mul_le_left
    refine hav (v' j i) ?_ (hle hmem)
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨j, i, rfl⟩

theorem exists_avoid (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (S : Finset (Ideal (𝓞 F))) (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a) :
    ∃ W : Finset (𝓞 F), (∀ x ∈ W, x ≠ 0) ∧
      (∀ c : S, ∀ s : ℂ, 1 < s.re → Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} =>
        ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))) ∧
      ∀ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ x ∈ W, x ∉ 𝔠) → ∀ c : S,
        ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
          (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} =>
            (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) ∧
          ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨ι, _, r, v, hv⟩ := GlobalTheory.T.exists_shintani_cone_domain F 𝔣 h𝔣
  have h := fun c : S => exists_avoid_one F 𝔣 c.1 h𝔣 (hS _ c.2) ι r v hv
  choose W hW0 hWs hWt using h
  refine ⟨Finset.univ.biUnion W, ?_, hWs, fun 𝔠 hpr hl hav c => hWt c 𝔠 hpr hl fun x hx => hav x ?_⟩
  · intro x hx
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 hx
    exact hW0 c x hc
  · exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, hx⟩

theorem exists_classZeta (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (S : Finset (Ideal (𝓞 F))) (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a)
    (hd : ∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) (hc : ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) :
    ∃ Z : S → ℂ → ℂ, ∀ c, IsRayZeta 𝔣 c.1 (Z c) ∧ ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, Z c (1 - (k : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨W, hW0, hsum, hWt⟩ := exists_avoid F 𝔣 h𝔣 S hS
  have key : ∀ B : ℕ, ∃ 𝔠 : Ideal (𝓞 F), (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧
      ∃ (τ : Equiv.Perm S) (T : S → ℂ → ℂ), (∀ c, Differentiable ℂ (T c)) ∧
        (∀ c s, 1 < s.re → ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (1 - s) * classSeries 𝔣 (τ c).1 s - classSeries 𝔣 c.1 s = T c s) ∧
        ∀ c, ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T c (1 - (k : ℂ)) = (q : ℂ) := by
    intro B
    obtain ⟨𝔠, hpr, hl, hB, hcop, hav⟩ := GlobalTheory.T.exists_prime_degree_one_avoiding F 𝔣 h𝔣 W B hW0
    have h𝔠0 : 𝔠 ≠ ⊥ := by
      rintro rfl
      simp only [Ideal.absNorm_bot] at hl
      exact Nat.not_prime_zero hl
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.ray_class_prime_multiplication_permutation F 𝔣 𝔠 S h𝔣 hpr h𝔠0 hcop hS hd hc
    choose T hTd hTs hTq using hWt 𝔠 hpr hl hav
    refine ⟨𝔠, hl, hB, τ, T, hTd, fun c s hs => ?_, hTq⟩
    obtain ⟨e, he⟩ := hτ c
    exact GlobalTheory.T.partial_zeta_prime_twist_summable F 𝔣 𝔠 (τ c).1 c.1 hl e he s _ hs (hsum _ s hs) (hsum _ s hs) (hTs c s hs)
  obtain ⟨𝔠, hl, -, τ, T, hTd, hTr, hTq⟩ := key 0
  obtain ⟨𝔠', hl', hB', τ', T', hTd', hTr', -⟩ := key (Ideal.absNorm 𝔠)
  obtain ⟨Z, hZd, hZD, hZq⟩ := GlobalTheory.T.partial_zeta_meromorphic_from_twists S (fun c => classSeries 𝔣 c.1) T T' _ _ τ τ' hl hl' hB'.ne hTd hTd' hTr hTr'
  refine ⟨Z, fun c => ⟨⟨hZd c, fun s hs => ?_⟩, fun k hk => hZq k hk (fun c => hTq c k hk) c⟩⟩
  rw [hZD c s hs]
  exact (hsum c s hs).hasSum

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open GlobalTheory.CompanionTheory.Hypotheses₂.Shintani in

theorem siegelKlingen : GlobalTheory.Published.SiegelKlingen := by
  classical
  intro F _ _ _ 𝔣 h𝔣 ε hε
  obtain ⟨S, hS, hd, hc⟩ := GlobalTheory.T.ray_class_group_finite_representatives F 𝔣 h𝔣
  obtain ⟨Z, hZ⟩ := exists_classZeta F 𝔣 h𝔣 S hS hd hc
  have hZ' : ∀ c : S, IsRayL 𝔣 (rayIndicator 𝔣 c.1) (Z c) := fun c => isRayZeta_iff.1 (hZ c).1
  have hind : ∀ I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I}, ∑ c : S, (ε c.1 : ℂ) * ((rayIndicator 𝔣 c.1 I.1 : ℚ) : ℂ) = (ε I.1 : ℂ) := by
    intro I
    obtain ⟨a, ha, hIa⟩ := hc I.1 I.2
    rw [Finset.sum_eq_single (⟨a, ha⟩ : S)]
    · have : ε a = ε I.1 := hε _ _ (hS a ha) I.2 (rayRel_symm hIa)
      simp [rayIndicator, hIa, this]
    · intro b _ hb
      have : ¬ RayRel F 𝔣 I.1 b.1 := fun h =>
        hb (Subtype.ext (hd _ b.2 _ ha (rayRel_trans (rayRel_symm h) hIa)))
      simp [rayIndicator, this]
    · simp
  refine ⟨fun s => ∑ c : S, (ε c.1 : ℂ) * Z c s, ⟨?_, fun s hs => ?_⟩, fun k hk => ?_⟩
  · intro s hs
    refine DifferentiableWithinAt.fun_sum fun c _ => ?_
    exact (differentiableWithinAt_const _).mul ((hZ' c).1 s hs)
  · have h1 := hasSum_sum (s := Finset.univ) fun c (_ : c ∈ (Finset.univ : Finset S)) => ((hZ' c).2 s hs).mul_left (ε c.1 : ℂ)
    have he : (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} => (ε I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) =
        fun I => ∑ c : S, (ε c.1 : ℂ) * (((rayIndicator 𝔣 c.1 I.1 : ℚ) : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
      funext I
      rw [← hind I, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [he]
    exact h1
  · choose q hq using fun c : S => (hZ c).2 k hk
    refine ⟨∑ c : S, ε c.1 * q c, ?_⟩
    simp only [hq]
    push_cast
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂
end
end
