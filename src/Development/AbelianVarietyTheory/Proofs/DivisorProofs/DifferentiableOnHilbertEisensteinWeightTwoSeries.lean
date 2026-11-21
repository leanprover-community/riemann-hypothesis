import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfA
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import BuildAid.ForwardExisting

section
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory

theorem card_le_absNorm_of_forall_le : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ →
    ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by
  intro F _ _ I hI s hs
  classical
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  have hgen : ∀ J : Ideal (𝓞 F), ∃ a : 𝓞 F, I ≤ J → I ⊔ Ideal.span {a} = J := by
    intro J
    by_cases h : I ≤ J
    · obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq h hI
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose g hg using hgen
  have hle : ∀ J K : Ideal (𝓞 F), I ≤ J → I ≤ K →
      Ideal.Quotient.mk I (g J) = Ideal.Quotient.mk I (g K) → J ≤ K := by
    intro J K hJ hK heq
    rw [← hg J hJ]
    refine sup_le hK ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have hd : g J - g K ∈ I := Ideal.Quotient.eq.mp heq
    have hk : g K ∈ K := by
      have h0 : g K ∈ I ⊔ Ideal.span {g K} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      rwa [hg K hK] at h0
    have : g J = (g J - g K) + g K := by ring
    rw [this]
    exact K.add_mem (hK hd) hk
  have hinj : Set.InjOn (fun J => Ideal.Quotient.mk I (g J)) (s : Set (Ideal (𝓞 F))) := by
    intro J hJ K hK heq
    exact le_antisymm (hle J K (hs J hJ) (hs K hK) heq) (hle K J (hs K hK) (hs J hJ) heq.symm)
  have h1 : s.card ≤ (Finset.univ : Finset (𝓞 F ⧸ I)).card :=
    Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply] at h1
  exact h1

end GlobalTheory
end

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_divisors_le_absNorm_numberField : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ s : Finset (Ideal (𝓞 F)), (∀ J ∈ s, I ≤ J) → s.card ≤ Ideal.absNorm I := by
  atlas_forward_decl GlobalTheory.card_le_absNorm_of_forall_le
end

section
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

noncomputable section

namespace GlobalTheory.QFiber

open FractionalIdeal

variable {F : Type} [Field F] [NumberField F]

def toIdeal (K : FractionalIdeal (𝓞 F)⁰ F) : Ideal (𝓞 F) :=
  open Classical in if h : K ≤ 1 then (le_one_iff_exists_coeIdeal.mp h).choose else ⊥

theorem coe_toIdeal {K : FractionalIdeal (𝓞 F)⁰ F} (h : K ≤ 1) :
    ((toIdeal K : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = K := by
  unfold toIdeal
  rw [dif_pos h]
  exact (le_one_iff_exists_coeIdeal.mp h).choose_spec

theorem nrm_nonneg (𝔞 : Frac F) : 0 ≤ nrm 𝔞 := by
  unfold nrm; exact_mod_cast absNorm_nonneg _

theorem emb_nonempty [IsTotallyReal F] : Nonempty (Emb F) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩

theorem card_le_norm : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F)
    (s : Finset (Quotient (qRel 𝔞 𝔟))), (∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) →
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := by
  intro F _ _ _ 𝔞 𝔟 ξ s hs
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨c0, hc0⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (abs_nonneg _) (mul_nonneg (nrm_nonneg 𝔞) (nrm_nonneg 𝔟))
  have hA : ((𝔞 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔞.ne_zero
  have hB : ((𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := 𝔟.ne_zero
  have hξ : ξ ≠ 0 := by
    obtain ⟨τ⟩ := emb_nonempty (F := F)
    have h := c0.out.2.2.2 τ
    rw [hs c0 hc0] at h
    intro h0
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hle : ∀ c : Quotient (qRel 𝔞 𝔟),
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := fun c => by
    calc _ ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
          by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.1
      _ = 1 := mul_inv_cancel₀ hA
  have hIle : ∀ c ∈ s, spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤
      spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    intro c hc
    have hb : spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := by
      calc _ ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
            by gcongr; exact spanSingleton_le_iff_mem.mpr c.out.2.2.1
        _ = 1 := mul_inv_cancel₀ hB
    rw [← hs c hc, ← spanSingleton_mul_spanSingleton]
    calc spanSingleton (𝓞 F)⁰ c.out.1.1 * spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ *
          (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
          (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) *
          (spanSingleton (𝓞 F)⁰ c.out.1.2 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) := by ring
      _ ≤ (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) * 1 := by gcongr
      _ = _ := mul_one _
  have hI1 := (hIle c0 hc0).trans (hle c0)
  set I := toIdeal (spanSingleton (𝓞 F)⁰ ξ * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔟 : FractionalIdeal (𝓞 F)⁰ F)⁻¹) with hIdef
  let f : Quotient (qRel 𝔞 𝔟) → Ideal (𝓞 F) := fun c =>
    toIdeal (spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹)
  have hIJ : ∀ c ∈ s, I ≤ f c := by
    intro c hc
    rw [← coeIdeal_le_coeIdeal F, coe_toIdeal hI1, coe_toIdeal (hle c)]
    exact hIle c hc
  have hI0 : I ≠ ⊥ := by
    intro h
    have h' := coe_toIdeal hI1
    rw [← hIdef, h, coeIdeal_bot] at h'
    have := h'.symm
    simp only [mul_eq_zero, spanSingleton_eq_zero_iff, inv_eq_zero] at this
    tauto
  have hinj : Set.InjOn f s := by
    intro c hc c' hc' hcc
    have h1 : spanSingleton (𝓞 F)⁰ c.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ =
        spanSingleton (𝓞 F)⁰ c'.out.1.1 * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
      rw [← coe_toIdeal (hle c), ← coe_toIdeal (hle c')]
      exact congrArg _ hcc
    have h2 := mul_right_cancel₀ (inv_ne_zero hA) h1
    obtain ⟨u, hu⟩ := spanSingleton_eq_spanSingleton.mp h2
    rw [Units.smul_def, Algebra.smul_def] at hu
    have hν : c.out.1.1 ≠ 0 := left_ne_zero_of_mul (by rw [hs c hc]; exact hξ)
    have hu0 : algebraMap (𝓞 F) F (u : 𝓞 F) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]; exact u.ne_zero
    have h4 : algebraMap (𝓞 F) F (u : 𝓞 F) * (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
      rw [mul_comm]; exact unit_inv_mul u
    have e1 := hs c hc
    have e2 := hs c' hc'
    rw [← hu] at e2
    have hb : c'.out.1.2 = (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * c.out.1.2 := by
      apply mul_left_cancel₀ (mul_ne_zero hu0 hν)
      linear_combination e2 - e1 - c.out.1.1 * c.out.1.2 * h4
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    apply Quotient.sound
    refine ⟨u⁻¹, ?_, hb⟩
    rw [inv_inv, ← hu]
  have key : (FractionalIdeal.absNorm ((I : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : ℚ) =
      |Algebra.norm ℚ ξ| / (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) *
        FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [coe_toIdeal hI1, map_mul, map_mul, map_inv₀, map_inv₀, absNorm_span_singleton]
    ring
  rw [coeIdeal_absNorm] at key
  calc (s.card : ℝ) = ((s.image f).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast GlobalTheory.T.card_divisors_le_absNorm_numberField F I hI0 (s.image f) (by
        intro J hJ
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hJ
        exact hIJ c hc)
    _ = _ := by
      unfold nrm
      have := congrArg (Rat.cast : ℚ → ℝ) key
      push_cast at this
      exact this

end GlobalTheory.QFiber
end
end

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hilbertEisensteinFourierFiber_le_norm : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F) (s : Finset (Quotient (qRel 𝔞 𝔟))), (∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) → (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := by
  atlas_forward_decl GlobalTheory.QFiber.card_le_norm
end

section
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory.NormLe

theorem absNorm_le_abs_norm {F : Type} [Field F] [NumberField F] (𝔟 : Frac F) {b : F}
    (hb : b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) (hb0 : b ≠ 0) :
    FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≤ |Algebra.norm ℚ b| := by
  set B : FractionalIdeal (𝓞 F)⁰ F := (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
  set S : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.spanSingleton (𝓞 F)⁰ b
  set J : FractionalIdeal (𝓞 F)⁰ F := ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * S
  have hSB : S ≤ B := (FractionalIdeal.spanSingleton_le_iff_mem).2 hb
  have hSJ : S = B * J := by
    simp only [J, B, ← mul_assoc, Units.mul_inv, one_mul]
  have hJ1 : J ≤ 1 := by
    have : J ≤ ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * B := by
      simp only [J]; gcongr
    simpa [B, Units.inv_mul] using this
  obtain ⟨I₀, hI₀⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1
  have hS0 : S ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb0
  have hJ0 : J ≠ 0 := by
    rintro h; rw [h, mul_zero] at hSJ; exact hS0 hSJ
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hI₀, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I₀ ≠ 0 := by
      intro h
      rw [Ideal.absNorm_eq_zero_iff] at h
      apply hJ0; rw [← hI₀, h]; simp
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have key : FractionalIdeal.absNorm S = FractionalIdeal.absNorm B * FractionalIdeal.absNorm J := by
    rw [hSJ, map_mul]
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 F) b]
  change FractionalIdeal.absNorm B ≤ FractionalIdeal.absNorm S
  rw [key]
  have := FractionalIdeal.absNorm_nonneg B
  nlinarith

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟),
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := by
  intro F _ _ _ 𝔞 𝔟 p
  obtain ⟨⟨ν, b⟩, h𝔞, h𝔟, hpos⟩ := p
  dsimp only at h𝔞 h𝔟 hpos ⊢
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have τ : Emb F := w.embedding_of_isReal (IsTotallyReal.isReal w)
  have hνb : ν * b ≠ 0 := fun h => by have := hpos τ; rw [h, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hle := absNorm_le_abs_norm 𝔟 h𝔟 hb0
  have hB0 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔟.ne_zero
  have hnpos : 0 < nrm 𝔟 := by
    unfold nrm
    have h1 := FractionalIdeal.absNorm_nonneg (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
    have h2 : FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      fun h => hB0 (FractionalIdeal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)
  have hle' : nrm 𝔟 ≤ |(Algebra.norm ℚ b : ℝ)| := by
    unfold nrm; rw [← Rat.cast_abs]; exact_mod_cast hle
  rw [le_div_iff₀ hnpos, map_mul, Rat.cast_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hle' (abs_nonneg _)

end GlobalTheory.NormLe
end

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_norm_le_abs_norm_mul_div_absNorm_of_eisensteinIndexPair : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟), |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := by
  atlas_forward_decl GlobalTheory.NormLe.main
end

section
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

noncomputable section

namespace GlobalTheory.LatExpSum

theorem trace_eq_sum_emb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ τ : Emb F, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (E := ℂ) (x := x)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [eq_ratCast] at h
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ τ : Emb F, ((τ x : ℝ) : ℂ) := by
    refine (Fintype.sum_bijective (fun τ : Emb F => (ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩ _ _ (fun _ => rfl)).symm
    · intro τ τ' hτ
      ext y
      have := DFunLike.congr_fun hτ y
      simpa using this
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
      exact ⟨hr.embedding, by ext y; simp⟩
  rw [h2, ← ofReal_sum] at h
  exact_mod_cast h

theorem summable_pi_prod {ι : Type} [Fintype ι] {f : ι → ℤ → ℝ} (h0 : ∀ i x, 0 ≤ f i x)
    (hf : ∀ i, Summable (f i)) : Summable fun n : ι → ℤ => ∏ i, f i (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' x, f i x)
    (fun n => Finset.prod_nonneg fun i _ => h0 i _) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f i (n i)
      ≤ ∑ n ∈ Fintype.piFinset fun i => s.image (· i), ∏ i, f i (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
          fun n _ _ => Finset.prod_nonneg fun i _ => h0 i _
    _ = ∏ i, ∑ x ∈ s.image (· i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun x _ => h0 i x)
        fun i _ => (hf i).sum_le_tsum _ fun x _ => h0 i x

theorem summable_exp_neg_abs {ε : ℝ} (hε : 0 < ε) : Summable fun n : ℤ => Real.exp (-ε * |(n : ℝ)|) := by
  have hg : Summable fun n : ℕ => Real.exp (-ε) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  apply Summable.of_nat_of_neg
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_of_nonneg (by positivity)]; ring_nf
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring_nf

end GlobalTheory.LatExpSum

namespace GlobalTheory.LatExpSum

theorem repr_eq_trace (F : Type) [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ F) (y : F) (i : ι) :
    b.repr y i = Algebra.trace ℚ F ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i * y) := by
  rw [← Algebra.traceForm_apply]
  symm
  calc _ = (Algebra.traceForm ℚ F) ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i) (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.repr y j * (Algebra.traceForm ℚ F) ((Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b i) (b j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = b.repr y i := by simp [LinearMap.BilinForm.apply_dualBasis_left]
end GlobalTheory.LatExpSum

namespace GlobalTheory.LatExpSum

theorem summable_exp_neg_trace : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
  intro F _ _ _ L δ hδ
  classical
  obtain ⟨a, ha, hint⟩ := L.isFractional
  have hz : ∀ x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x}, ∃ w : 𝓞 F,
      algebraMap (𝓞 F) F w = algebraMap (𝓞 F) F a * x.1 := fun x => by
    obtain ⟨w, hw⟩ := hint x.1 x.2.1
    exact ⟨w, by rw [hw, Algebra.smul_def]⟩
  choose z hz using hz
  let b := integralBasis F
  let d := (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b
  have hrepr : ∀ (y : F) i, b.repr y i = Algebra.trace ℚ F (d i * y) := fun y i => repr_eq_trace F b y i
  let c : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} → Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ :=
    fun x => (RingOfIntegers.basis F).repr (z x)
  have hc : ∀ x i, ((c x i : ℚ)) = Algebra.trace ℚ F ((d i * algebraMap (𝓞 F) F a) * x.1) := by
    intro x i
    have := integralBasis_repr_apply (K := F) (z x) i
    rw [hz x] at this
    rw [mul_assoc, ← hrepr]
    rw [this, eq_intCast]
  let Mi : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ := fun i => ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)|
  have hMi : ∀ i, 0 ≤ Mi i := fun i => Finset.sum_nonneg fun τ _ => abs_nonneg _
  let M : ℝ := ∑ i, Mi i + 1
  have hM : 0 < M := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hMi i
    show 0 < ∑ i, Mi i + 1
    linarith
  have hbound : ∀ x, ∑ i, |(c x i : ℝ)| ≤ M * ∑ τ : Emb F, τ x.1 := by
    intro x
    have hT : 0 ≤ ∑ τ : Emb F, τ x.1 := Finset.sum_nonneg fun τ _ => (x.2.2 τ).le
    have h1 : ∀ i, |(c x i : ℝ)| ≤ Mi i * ∑ τ : Emb F, τ x.1 := by
      intro i
      have e : (c x i : ℝ) = ∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1 := by
        have h := congrArg (fun q : ℚ => (q : ℝ)) (hc x i)
        simp only [Rat.cast_intCast] at h
        rw [h, trace_eq_sum_emb]
        simp only [map_mul]
      rw [e]
      calc |∑ τ : Emb F, τ (d i * algebraMap (𝓞 F) F a) * τ x.1|
          ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a) * τ x.1| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * τ x.1 := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [abs_mul, abs_of_pos (x.2.2 τ)]
        _ ≤ ∑ τ : Emb F, |τ (d i * algebraMap (𝓞 F) F a)| * ∑ σ : Emb F, σ x.1 :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun σ : Emb F => σ x.1) (fun σ _ => (x.2.2 σ).le) (Finset.mem_univ τ)) (abs_nonneg _)
        _ = Mi i * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
    calc ∑ i, |(c x i : ℝ)| ≤ ∑ i, Mi i * ∑ τ : Emb F, τ x.1 := Finset.sum_le_sum fun i _ => h1 i
      _ = (∑ i, Mi i) * ∑ τ : Emb F, τ x.1 := by rw [Finset.sum_mul]
      _ ≤ M * ∑ τ : Emb F, τ x.1 := mul_le_mul_of_nonneg_right (by simp [M]) hT
  have ha0 : algebraMap (𝓞 F) F a ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero ha)
  have hinj : Function.Injective c := by
    intro x y hxy
    have h1 : z x = z y := (RingOfIntegers.basis F).repr.injective (Finsupp.ext fun i => congrFun hxy i)
    have h2 : algebraMap (𝓞 F) F a * x.1 = algebraMap (𝓞 F) F a * y.1 := by rw [← hz, ← hz, h1]
    exact Subtype.ext (mul_left_cancel₀ ha0 h2)
  have hε : 0 < δ / M := div_pos hδ hM
  have hg : Summable fun n : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ => ∏ i, Real.exp (-(δ / M) * |(n i : ℝ)|) :=
    summable_pi_prod (f := fun _ x => Real.exp (-(δ / M) * |(x : ℝ)|)) (fun _ _ => (Real.exp_pos _).le) fun _ => summable_exp_neg_abs hε
  refine (hg.comp_injective hinj).of_nonneg_of_le (fun _ => (Real.exp_pos _).le) fun x => ?_
  simp only [Function.comp_apply]
  rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
  have h3 : δ / M * ∑ i, |(c x i : ℝ)| ≤ δ * ∑ τ : Emb F, τ x.1 := by
    calc δ / M * ∑ i, |(c x i : ℝ)| ≤ δ / M * (M * ∑ τ : Emb F, τ x.1) := mul_le_mul_of_nonneg_left (hbound x) hε.le
      _ = δ * ∑ τ : Emb F, τ x.1 := by field_simp
  linarith

end GlobalTheory.LatExpSum
end
end

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
  atlas_forward_decl GlobalTheory.LatExpSum.summable_exp_neg_trace
end

section
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory

theorem norm_sq_mul_exp_neg_trace_le : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : ℝ), 0 < δ →
    ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) →
      |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤
        C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) := by
  intro F _ _ _ δ hδ
  set n := 2 * Fintype.card (Emb F) with hn
  refine ⟨(n.factorial : ℝ) * (2 / δ) ^ n, fun x hx => ?_⟩
  set T := ∑ τ : Emb F, τ x with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun τ _ => (hx τ).le
  have hnorm : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ τ : Emb F, τ x := by
    have h := prod_emb x
    have h' : ((∏ τ : Emb F, τ x : ℝ) : ℂ) = (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) := by
      rw [ofReal_prod, h]; simp
    exact_mod_cast h'.symm
  have hprod : |((Algebra.norm ℚ x : ℚ) : ℝ)| ≤ T ^ Fintype.card (Emb F) := by
    rw [hnorm, abs_of_nonneg (Finset.prod_nonneg fun τ _ => (hx τ).le)]
    calc ∏ τ : Emb F, τ x ≤ ∏ _τ : Emb F, T :=
          Finset.prod_le_prod (fun τ _ => (hx τ).le) (fun τ _ =>
            Finset.single_le_sum (f := fun σ : Emb F => σ x) (fun σ _ => (hx σ).le) (Finset.mem_univ τ))
      _ = T ^ Fintype.card (Emb F) := by rw [Finset.prod_const, Finset.card_univ]
  have hsq : |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ 2 ≤ T ^ n := by
    calc _ ≤ (T ^ Fintype.card (Emb F)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hprod 2
      _ = T ^ n := by rw [← pow_mul, mul_comm]
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hexp : (δ * T / 2) ^ n / n.factorial ≤ Real.exp (δ * T / 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have e2 : (δ * T / 2) ^ n ≤ Real.exp (δ * T / 2) * n.factorial := (div_le_iff₀ hf).1 hexp
  have e1 : T ^ n = (2 / δ) ^ n * (δ * T / 2) ^ n := by
    rw [← mul_pow]; congr 1; field_simp
  have hTn : T ^ n ≤ (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (δ * T / 2) := by
    rw [e1]
    calc _ ≤ (2 / δ) ^ n * (Real.exp (δ * T / 2) * n.factorial) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = _ := by ring
  calc |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ 2 * Real.exp (-δ * T)
        ≤ T ^ n * Real.exp (-δ * T) := mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ ≤ (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (δ * T / 2) * Real.exp (-δ * T) :=
          mul_le_mul_of_nonneg_right hTn (Real.exp_pos _).le
    _ = (n.factorial : ℝ) * (2 / δ) ^ n * Real.exp (-(δ / 2) * T) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end GlobalTheory
end

open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_mul_exp_neg_trace_le' : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : ℝ), 0 < δ → ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) → |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) := by
  atlas_forward_decl GlobalTheory.norm_sq_mul_exp_neg_trace_le
end

section
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.QHolo

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_upperHalf : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, (fun z : Emb F → ℂ => (z τ).im) ⁻¹' Set.Ioi 0 := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun τ => isOpen_Ioi.preimage (by fun_prop)

theorem qClass_two (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : qClass 𝔞 𝔟 2 z c =
    ((|(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 : ℝ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * I * ∑ τ, (τ (c.out.1.1 * c.out.1.2) : ℂ) * z τ) := by
  simp [qClass, qTerm, qPow]

theorem differentiable_qClass (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) :
    Differentiable ℂ (fun z => qClass 𝔞 𝔟 2 z c) := by
  simp only [qClass_two]
  fun_prop

theorem norm_qClass (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : ‖qClass 𝔞 𝔟 2 z c‖ =
    |(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 *
      Real.exp (-(2 * Real.pi) * ∑ τ, τ (c.out.1.1 * c.out.1.2) * (z τ).im) := by
  rw [qClass_two, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _))]
  congr 2
  simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

theorem summable_of_fiber {α β : Type} (g : α → β) (f : α → ℝ) (B : β → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hB : Summable B) (hfib : ∀ (b : β) (s : Finset α), (∀ a ∈ s, g a = b) → ∑ a ∈ s, f a ≤ B b) :
    Summable f := by
  classical
  have hB0 : ∀ b, 0 ≤ B b := fun b => by simpa using hfib b ∅ (by simp)
  refine summable_of_sum_le hf (c := ∑' b, B b) fun u => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (s := u) (t := u.image g) (g := g)
    (fun x hx => Finset.mem_image_of_mem g hx)]
  calc ∑ b ∈ u.image g, ∑ a ∈ u with g a = b, f a ≤ ∑ b ∈ u.image g, B b :=
        Finset.sum_le_sum fun b _ => hfib b _ fun a ha => (Finset.mem_filter.1 ha).2
    _ ≤ ∑' b, B b := hB.sum_le_tsum _ fun b _ => hB0 b

theorem card_fiber_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F) (s : Finset (Quotient (qRel 𝔞 𝔟)))
    (hs : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) :
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := GlobalTheory.T.card_hilbertEisensteinFourierFiber_le_norm F 𝔞 𝔟 ξ s hs

theorem abs_norm_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟) :
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := GlobalTheory.T.abs_norm_le_abs_norm_mul_div_absNorm_of_eisensteinIndexPair F 𝔞 𝔟 p

theorem summable_exp_trace [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) :=
  GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal F L δ hδ

theorem norm_sq_exp_le [IsTotallyReal F] {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) →
    |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) :=
  GlobalTheory.T.norm_sq_mul_exp_neg_trace_le' F δ hδ

theorem summable_key [IsTotallyReal F] (𝔞 𝔟 : Frac F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun c : Quotient (qRel 𝔞 𝔟) =>
      |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))) := by
  have hna : 0 ≤ nrm 𝔞 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  have hnb : 0 ≤ nrm 𝔟 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  let β := {x : F // x ∈ ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) ∧ ∀ τ : Emb F, 0 < τ x}
  let g : Quotient (qRel 𝔞 𝔟) → β := fun c =>
    ⟨c.out.1.1 * c.out.1.2, FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1, c.out.2.2.2⟩
  let B : β → ℝ := fun x => |(Algebra.norm ℚ x.1 : ℝ)| / (nrm 𝔞 * nrm 𝔟) *
    (|(Algebra.norm ℚ x.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ x.1))
  obtain ⟨C, hC⟩ := norm_sq_exp_le (F := F) hδ
  have hB : Summable B := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
      ((summable_exp_trace (F := F) ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) (half_pos hδ)).mul_left
        ((nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ * C))
    have h := hC x.1 x.2.2
    have : B x = (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ *
        (|(Algebra.norm ℚ x.1 : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
      simp only [B]; field_simp
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left h (show 0 ≤ (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ by positivity)
    linarith
  refine summable_of_fiber g _ B (fun c => by positivity) hB fun b s hs => ?_
  have hξ : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = b.1 := fun c hc => by rw [← hs c hc]
  calc ∑ c ∈ s, |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))
      ≤ ∑ c ∈ s, |(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1) := by
        refine Finset.sum_le_sum fun c hc => ?_
        rw [← hξ c hc]
        exact mul_le_mul_of_nonneg_right (abs_norm_le 𝔞 𝔟 c.out) (Real.exp_pos _).le
    _ = (s.card : ℝ) * (|(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B b := mul_le_mul_of_nonneg_right (card_fiber_le 𝔞 𝔟 b.1 s hξ) (by positivity)

theorem exists_im_bound {y : Emb F → ℂ} (hy : y ∈ upperHalf F) :
    ∃ ε > 0, ∀ v ∈ Metric.ball y ε, ∀ τ, ε ≤ (v τ).im := by
  obtain ⟨ε, hε, hle⟩ : ∃ ε > 0, ∀ τ, 2 * ε ≤ (y τ).im := by
    rcases isEmpty_or_nonempty (Emb F) with h | h
    · exact ⟨1, one_pos, fun τ => isEmptyElim τ⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min (fun τ => (y τ).im)
      exact ⟨(y τ₀).im / 2, half_pos (hy τ₀), fun τ => by linarith [hτ₀ τ]⟩
  refine ⟨ε, hε, fun v hv τ => ?_⟩
  have h1 : dist (v τ) (y τ) < ε := (dist_le_pi_dist v y τ).trans_lt (Metric.mem_ball.1 hv)
  have h2 : |(v τ).im - (y τ).im| < ε := by
    rw [Complex.dist_eq] at h1
    exact (by simpa using Complex.abs_im_le_norm (v τ - y τ) : |(v τ).im - (y τ).im| ≤ ‖v τ - y τ‖).trans_lt h1
  linarith [hle τ, (abs_lt.1 h2).1]

theorem qholo : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    DifferentiableOn ℂ (fun z => ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  intro F _ _ _ 𝔞 𝔟
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiableOn_tsum_loc isOpen_upperHalf
    (fun c z => qClass 𝔞 𝔟 2 z c) (fun c => (differentiable_qClass 𝔞 𝔟 c).differentiableOn) ?_
  intro y hy
  obtain ⟨ε, hε, hv⟩ := exists_im_bound hy
  refine ⟨ε, hε, fun c => (nrm 𝔞)⁻¹ * (|(Algebra.norm ℚ c.out.1.1 : ℝ)| *
      Real.exp (-(2 * Real.pi * ε) * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))),
    (summable_key 𝔞 𝔟 (by positivity)).mul_left _, fun c v hvb => ?_⟩
  rw [norm_qClass, div_eq_inv_mul, mul_assoc]
  have hn : 0 ≤ (nrm 𝔞)⁻¹ := inv_nonneg.2 (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hn
  refine Real.exp_le_exp.2 ?_
  have hpos := c.out.2.2.2
  have : ε * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) ≤ ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) * (v τ).im := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hv v hvb τ]
  have hπ := Real.pi_pos
  nlinarith

end GlobalTheory.QHolo
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableOn_hilbertEisensteinWeightTwoSeries : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), DifferentiableOn ℂ (fun z => ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  atlas_forward_decl GlobalTheory.QHolo.qholo
end
