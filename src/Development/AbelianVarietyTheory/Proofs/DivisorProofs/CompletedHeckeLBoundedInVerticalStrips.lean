import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TsumIdealEqSumClassGroup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassGroupCoprimeRepresentative
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSmoothHomogeneousHasSumUnitSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableWeightedHeckeThetaKernelHalfSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierHarmonicMonomialMulGaussianComplex
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsValuedHeckeCharRamified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchFactorMulPSeriesEqIntegral

section
section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeStrip

open Classical in

theorem tsum_ideal_eq_sum_classGroup_of_summable {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (G : Ideal (𝓞 K) → ℂ) (H : ClassGroup (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (h0 : G ⊥ = 0) (hsum : Summable G)
    (hH : ∀ c I, I ≠ ⊥ → H c (I * b c) = G I) :
    ∑' I, G I = ∑ c, ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ (b c : Ideal (𝓞 K))}, H c J := by
  let S : ClassGroup (𝓞 K) → Set (Ideal (𝓞 K)) :=
    fun c => {I | I ≠ ⊥ ∧ (I * (b c : Ideal (𝓞 K))).IsPrincipal}
  have h1 : ∀ I, G I = ∑ c, (S c).indicator G I := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0]
      exact (Finset.sum_eq_zero fun c _ => Set.indicator_of_notMem (fun h => h.1 rfl) _).symm
    · obtain ⟨c, hc, hu⟩ := GlobalTheory.existsUnique_isPrincipal_mul_classRep b hb I hI
      rw [Finset.sum_eq_single c]
      · exact (Set.indicator_of_mem (show I ∈ S c from ⟨hI, hc⟩) _).symm
      · intro c' _ hne
        exact Set.indicator_of_notMem (fun h => hne (hu c' h.2)) _
      · simp
  rw [tsum_congr h1, Summable.tsum_finsetSum (fun c _ => hsum.indicator (S c))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← tsum_subtype, ← GlobalTheory.tsum_isPrincipal_mul_eq (b c : Ideal (𝓞 K))
    (mem_nonZeroDivisors_iff_ne_zero.mp (b c).2) (H c)]
  exact tsum_congr fun I => (hH c I.1 I.2.1).symm

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

def classUnitPart (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (α : 𝓞 K) : ℂ :=
  open Classical in if m = ⊤ then 1 else X (Ideal.span {α}) * (wt φ n (α : K))⁻¹

def classPartFun (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (b : Ideal (𝓞 K))
    (α : 𝓞 K) : ℂ :=
  open Classical in if α ∈ b then classUnitPart φ n m X α else 0

theorem wt_ne_zero_of_ne_zero (φ : I → K →+* ℂ) (n : I → ℤ) {α : 𝓞 K} (hα : α ≠ 0) : wt φ n (α : K) ≠ 0 := by
  have hαK : (α : K) ≠ 0 := fun h => hα (RingOfIntegers.coe_eq_zero_iff.mp h)
  intro h
  have := norm_wt φ n hαK
  rw [h, norm_zero] at this
  exact zero_ne_one this

section

variable {φ : I → K →+* ℂ} {n : I → ℤ} {m : Ideal (𝓞 K)} {X : Ideal (𝓞 K) → ℂ}

theorem classPartFun_mul_wt
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) {α : 𝓞 K} (hα : α ≠ 0) :
    classPartFun φ n m X b α * wt φ n (α : K) = open Classical in if α ∈ b then X (Ideal.span {α}) else 0 := by
  unfold classPartFun classUnitPart
  by_cases hb : α ∈ b
  · rw [if_pos hb, if_pos hb]
    by_cases hm : m = ⊤
    · rw [if_pos hm, one_mul, hβ α hα (hm ▸ Submodule.mem_top)]
    · rw [if_neg hm, mul_assoc, inv_mul_cancel₀ (wt_ne_zero_of_ne_zero φ n hα), mul_one]
  · rw [if_neg hb, if_neg hb, zero_mul]

theorem classUnitPart_eq_of_inv
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (hm : m ≠ ⊤) {α γ : 𝓞 K} (h : γ * α - 1 ∈ m) :
    classUnitPart φ n m X α = wt φ n (γ : K) * (X (Ideal.span {γ}))⁻¹ := by
  have hγα : γ * α ≠ 0 := by
    intro h0
    rw [h0, zero_sub] at h
    exact hm ((Ideal.eq_top_iff_one m).2 (by simpa using m.neg_mem h))
  have hα : α ≠ 0 := right_ne_zero_of_mul hγα
  have hγ : γ ≠ 0 := left_ne_zero_of_mul hγα
  have key := hβ _ hγα h
  rw [← Ideal.span_singleton_mul_span_singleton, hmul] at key
  have hc : ((γ * α : 𝓞 K) : K) = (γ : K) * α := by push_cast; rfl
  rw [hc, wt_mul] at key
  have hwα := wt_ne_zero_of_ne_zero φ n hα
  have hwγ := wt_ne_zero_of_ne_zero φ n hγ
  have hXγ : X (Ideal.span {γ}) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at key
    exact mul_ne_zero hwγ hwα key.symm
  unfold classUnitPart
  rw [if_neg hm]
  field_simp
  linear_combination key

theorem classUnitPart_add
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hzero : ∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    {α μ : 𝓞 K} (hμ : μ ∈ m) :
    classUnitPart φ n m X (α + μ) = classUnitPart φ n m X α := by
  by_cases hm : m = ⊤
  · simp [classUnitPart, hm]
  have hsup : Ideal.span {α + μ} ⊔ m = Ideal.span {α} ⊔ m := by
    apply le_antisymm
    · exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.add_mem _
        (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α)) (Ideal.mem_sup_right hμ))) le_sup_right
    · refine sup_le ((Ideal.span_singleton_le_iff_mem _).2 ?_) le_sup_right
      have h : (α + μ) + -μ ∈ Ideal.span {α + μ} ⊔ m :=
        Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_right (m.neg_mem hμ))
      simpa using h
  by_cases hc : Ideal.span {α} ⊔ m = ⊤
  · have h1 : (1 : 𝓞 K) ∈ Ideal.span {α} ⊔ m := hc ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨γ, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have e1 : γ * α - 1 ∈ m := by
      have e : γ * α - 1 = -z := by rw [← hyz]; ring
      rw [e]; exact m.neg_mem hz
    have e2 : γ * (α + μ) - 1 ∈ m := by
      have e : γ * (α + μ) - 1 = (γ * α - 1) + γ * μ := by ring
      rw [e]; exact m.add_mem e1 (m.mul_mem_left γ hμ)
    rw [classUnitPart_eq_of_inv hmul hβ hm e1, classUnitPart_eq_of_inv hmul hβ hm e2]
  · have hc' : Ideal.span {α + μ} ⊔ m ≠ ⊤ := hsup ▸ hc
    simp only [classUnitPart, if_neg hm, hzero _ hc, hzero _ hc', zero_mul]

theorem classPartFun_add
    (hmul : ∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b)
    (hzero : ∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0)
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) {α μ : 𝓞 K} (hμ : μ ∈ m * b) :
    classPartFun φ n m X b (α + μ) = classPartFun φ n m X b α := by
  have hμm : μ ∈ m := (Ideal.mul_le_inf.trans inf_le_left) hμ
  have hμb : μ ∈ b := (Ideal.mul_le_inf.trans inf_le_right) hμ
  unfold classPartFun
  by_cases h : α ∈ b
  · rw [if_pos h, if_pos (b.add_mem h hμb), classUnitPart_add hmul hzero hβ hμm]
  · have h' : α + μ ∉ b := fun h' => h (by simpa using b.sub_mem h' hμb)
    rw [if_neg h, if_neg h']

theorem classPartFun_unit
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) (u : (𝓞 K)ˣ) (α : 𝓞 K) :
    classPartFun φ n m X b ((u : 𝓞 K) * α) * wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) =
      classPartFun φ n m X b α * wt φ n (α : K) := by
  by_cases hα : α = 0
  · subst hα; simp
  have huα : (u : 𝓞 K) * α ≠ 0 := mul_ne_zero u.ne_zero hα
  rw [classPartFun_mul_wt hβ b huα, classPartFun_mul_wt hβ b hα, Ideal.span_singleton_mul_left_unit u.isUnit]
  have hiff : (u : 𝓞 K) * α ∈ b ↔ α ∈ b :=
    ⟨fun h => by simpa using b.mul_mem_left ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) h, fun h => b.mul_mem_left _ h⟩
  by_cases h : α ∈ b
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem pval_classPartFun
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b J : Ideal (𝓞 K)) [J.IsPrincipal] (hJ : J ≠ ⊥) :
    pval (classPartFun φ n m X b) φ n J = open Classical in if J ≤ b then X J else 0 := by
  have hg : Submodule.IsPrincipal.generator J ≠ 0 := by
    rwa [Ne, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]
  have hle : Submodule.IsPrincipal.generator J ∈ b ↔ J ≤ b := by
    conv_rhs => rw [← Ideal.span_singleton_generator J]
    exact (Ideal.span_singleton_le_iff_mem b).symm
  unfold pval
  rw [classPartFun_mul_wt hβ b hg, Ideal.span_singleton_generator]
  by_cases h : J ≤ b
  · rw [if_pos (hle.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hle.1 h')), if_neg h]

theorem pSeries_classPartFun
    (hβ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : K))
    (b : Ideal (𝓞 K)) (s : ℂ) :
    pSeries (classPartFun φ n m X b) φ n s =
      ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b}, X J.1 * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
  classical
  let f : Ideal (𝓞 K) → ℂ := fun J => (if J ≤ b then X J else 0) * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)
  let g : Ideal (𝓞 K) → ℂ := fun J => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s)
  have h1 : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal},
      (haveI := J.2.2; pval (classPartFun φ n m X b) φ n J.1) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) = f J.1 := by
    rintro ⟨J, hJ, hP⟩
    simp only [f]
    rw [pval_classPartFun hβ b J hJ]
  unfold pSeries
  rw [tsum_congr h1]
  have e1 := tsum_subtype {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} f
  have e2 := tsum_subtype {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} g
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine tsum_congr fun J => ?_
  by_cases hJ : J ≠ ⊥ ∧ J.IsPrincipal
  · by_cases h : J ≤ b
    · rw [Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
        Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from ⟨hJ.1, hJ.2, h⟩)]
      simp only [f, g, if_pos h]
    · rw [Set.indicator_of_mem (show J ∈ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
        Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from fun h' => h h'.2.2)]
      simp only [f, if_neg h, zero_mul]
  · rw [Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal} from hJ),
      Set.indicator_of_notMem (show J ∉ {J : Ideal (𝓞 K) | J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ b} from
        fun h' => hJ ⟨h'.1, h'.2.1⟩)]

end

theorem heckeSeries_eq_sum_pSeries : ∀ (K : Type) [Field K] [NumberField K] (I : Type) [Fintype I] (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b) → (∀ a : Ideal (𝓞 K), a ≠ ⊥ → a ⊔ m = ⊤ → ‖X a‖ = 1) → (∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = GlobalTheory.HeckeStrip.wt φ n (β : K)) → ∃ (r : ℕ) (c : Fin r → ℂ) (B : Fin r → ℕ) (M : Fin r → Ideal (𝓞 K)) (F : Fin r → 𝓞 K → ℂ), (∀ k, 0 < B k) ∧ (∀ k, M k ≠ ⊥) ∧ (∀ k (α μ : 𝓞 K), μ ∈ M k → F k (α + μ) = F k α) ∧ (∀ k (u : (𝓞 K)ˣ) (α : 𝓞 K), F k ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F k α * GlobalTheory.HeckeStrip.wt φ n (α : K)) ∧ ∀ s : ℂ, 1 < s.re → ∑' a : Ideal (𝓞 K), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s) = ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * GlobalTheory.HeckeStrip.pSeries (F k) φ n s := by
  intro K _ _ I _ φ n m X hm hX0 hmul hnorm hzero hβ
  choose b hb hbm using GlobalTheory.exists_integral_ideal_in_class_coprime K m hm
  have hbij : Function.Bijective (fun c => ClassGroup.mk0 (b c)) := by
    have e : (fun c => ClassGroup.mk0 (b c)) = id := funext hb
    rw [e]; exact Function.bijective_id
  have hb0 : ∀ c, (b c : Ideal (𝓞 K)) ≠ ⊥ := fun c => nonZeroDivisors.coe_ne_zero (b c)
  have hXb : ∀ c, X (b c) ≠ 0 := fun c h => by
    have := hnorm _ (hb0 c) (hbm c)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hNb : ∀ c, Ideal.absNorm (b c : Ideal (𝓞 K)) ≠ 0 := fun c h => hb0 c (Ideal.absNorm_eq_zero_iff.mp h)
  let e := Fintype.equivFin (ClassGroup (𝓞 K))
  refine ⟨Fintype.card (ClassGroup (𝓞 K)), fun k => (X (b (e.symm k)))⁻¹,
    fun k => Ideal.absNorm (b (e.symm k) : Ideal (𝓞 K)), fun k => m * (b (e.symm k) : Ideal (𝓞 K)),
    fun k => classPartFun φ n m X (b (e.symm k)), fun k => Nat.pos_of_ne_zero (hNb _),
    fun k => mul_ne_zero hm (hb0 _), fun k α μ hμ => classPartFun_add hmul hzero hβ _ hμ,
    fun k u α => classPartFun_unit hβ _ u α, fun s hs => ?_⟩
  have hXle : ∀ J, ‖X J‖ ≤ 1 := by
    intro J
    by_cases h0 : J = ⊥
    · rw [h0, hX0, norm_zero]; exact zero_le_one
    by_cases hc : J ⊔ m = ⊤
    · rw [hnorm J h0 hc]
    · rw [hzero J hc, norm_zero]; exact zero_le_one
  have hsum : Summable fun J : Ideal (𝓞 K) => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) :=
    (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs).of_norm_bounded fun J => by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hXle J)
  have hH : ∀ c (J : Ideal (𝓞 K)), J ≠ ⊥ →
      (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
        (X (J * (b c : Ideal (𝓞 K))) * ((Ideal.absNorm (J * (b c : Ideal (𝓞 K))) : ℕ) : ℂ) ^ (-s)) =
      X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) := by
    intro c J _
    have hpow : ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
        ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) = 1 := by
      rw [Complex.cpow_neg, mul_inv_cancel₀]
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Nat.cast_ne_zero.mpr (hNb c))
    rw [hmul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    calc (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
          (X J * X (b c) * (((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) *
            ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)))
        = X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) * ((X (b c))⁻¹ * X (b c)) *
          (((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
            ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) := by ring
      _ = X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s) := by rw [inv_mul_cancel₀ (hXb c), hpow, mul_one, mul_one]
  rw [tsum_ideal_eq_sum_classGroup_of_summable b (fun J => X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s))
    (fun c J => (X (b c))⁻¹ * ((Ideal.absNorm (b c : Ideal (𝓞 K)) : ℕ) : ℂ) ^ s *
      (X J * ((Ideal.absNorm J : ℕ) : ℂ) ^ (-s))) hbij (by simp only [hX0, zero_mul]) hsum hH]
  refine (Equiv.sum_comp e.symm _).symm.trans (Finset.sum_congr rfl fun k _ => ?_)
  beta_reduce
  rw [tsum_mul_left, pSeries_classPartFun hβ]

end GlobalTheory.HeckeStrip
end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeLSeries_eq_sum_principalPartialSeries : ∀ (K : Type) [Field K] [NumberField K] (I : Type) [Fintype I] (φ : I → K →+* ℂ) (n : I → ℤ) (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ a b : Ideal (𝓞 K), X (a * b) = X a * X b) → (∀ a : Ideal (𝓞 K), a ≠ ⊥ → a ⊔ m = ⊤ → ‖X a‖ = 1) → (∀ a : Ideal (𝓞 K), a ⊔ m ≠ ⊤ → X a = 0) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = GlobalTheory.HeckeStrip.wt φ n (β : K)) → ∃ (r : ℕ) (c : Fin r → ℂ) (B : Fin r → ℕ) (M : Fin r → Ideal (𝓞 K)) (F : Fin r → 𝓞 K → ℂ), (∀ k, 0 < B k) ∧ (∀ k, M k ≠ ⊥) ∧ (∀ k (α μ : 𝓞 K), μ ∈ M k → F k (α + μ) = F k α) ∧ (∀ k (u : (𝓞 K)ˣ) (α : 𝓞 K), F k ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F k α * GlobalTheory.HeckeStrip.wt φ n (α : K)) ∧ ∀ s : ℂ, 1 < s.re → ∑' a : Ideal (𝓞 K), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s) = ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * GlobalTheory.HeckeStrip.pSeries (F k) φ n s := by
  atlas_forward_decl GlobalTheory.HeckeStrip.heckeSeries_eq_sum_pSeries
end

section
section
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.LaplaceStrip

theorem norm_integrand {α : Type} (ℓ : α → ℝ) (g : α → ℂ) (s : ℂ) (x : α) :
    ‖g x * Complex.exp (s * (ℓ x : ℂ))‖ = ‖g x‖ * Real.exp (s.re * ℓ x) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem laplace_entire_boundedInStrips {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ)
    (hℓ : Measurable ℓ) (hg : MeasureTheory.AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ ℓ x)
    (hint : ∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) :
    Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    hg.mul (by fun_prop : Measurable fun x => Complex.exp (s * (ℓ x : ℂ))).aestronglyMeasurable
  have hI : ∀ s : ℂ, Integrable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    (hint s.re).mono' (hmeas s) (Filter.Eventually.of_forall fun x => (norm_integrand ℓ g s x).le)
  refine ⟨fun s₀ => ?_, fun a b _ => ⟨∫ x, ‖g x‖ * Real.exp (b * ℓ x) ∂μ, fun s _ hsb => ?_⟩⟩
  · have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x => g x * Complex.exp (s * (ℓ x : ℂ)))
      (F' := fun s x => g x * (Complex.exp (s * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))))
      (x₀ := s₀) (bound := fun x => ‖g x‖ * Real.exp ((s₀.re + 2) * ℓ x)) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall hmeas) (hI s₀)
      (hg.mul (by fun_prop : Measurable fun x =>
        Complex.exp (s₀ * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))).aestronglyMeasurable)
      ?_ (hint _) ?_
    · exact key.2.differentiableAt
    · filter_upwards [hpos] with x hx s hs
      have hre : s.re ≤ s₀.re + 1 := by
        have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        have h2 : ‖s - s₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
        have h3 := (abs_le.mp h1).2
        simp only [Complex.sub_re] at h3
        linarith
      rw [one_mul, ← mul_assoc, norm_mul, norm_integrand, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      have e1 : Real.exp (s.re * ℓ x) ≤ Real.exp ((s₀.re + 1) * ℓ x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hx)
      have e2 : ℓ x ≤ Real.exp (ℓ x) := by linarith [Real.add_one_le_exp (ℓ x)]
      have e3 : Real.exp ((s₀.re + 2) * ℓ x) = Real.exp ((s₀.re + 1) * ℓ x) * Real.exp (ℓ x) := by
        rw [← Real.exp_add]; ring_nf
      rw [e3, mul_assoc]
      gcongr
    · exact Filter.Eventually.of_forall fun x s _ => by
        have := (((hasDerivAt_id s).mul_const (ℓ x : ℂ)).cexp).const_mul (g x)
        simpa using this
  · refine norm_integral_le_of_norm_le (hint b) ?_
    filter_upwards [hpos] with x hx
    rw [norm_integrand]
    gcongr

end GlobalTheory.LaplaceStrip
end
end

open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips : ∀ {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ), Measurable ℓ → MeasureTheory.AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, 0 ≤ ℓ x) → (∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) → Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  atlas_forward_decl GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips
end

section
section
open NumberField MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory
namespace UnitLogPartition

open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

theorem exists_nonneg_hasSum_lattice_translates (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ η : V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ z, 0 ≤ η z) ∧
      ∀ y, HasSum (fun l : L => η (y + l)) 1 := by
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_radius_lattice_translate_norm_le V L
  let b : ContDiffBump (0 : V) := ⟨R, R + 1, hR, by linarith⟩
  have hφc : HasCompactSupport (b : V → ℝ) := b.hasCompactSupport
  have hφs : ContDiff ℝ ∞ (b : V → ℝ) := b.contDiff
  have hlf := GlobalTheory.PeriodicPartition.locallyFinite_support_translate L b hφc
  set S : V → ℝ := fun z => ∑ᶠ l : L, b (z + l) with hS
  have hSs : ContDiff ℝ ∞ S := by
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : L) (z : V) => b (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  have hSp : ∀ (l : L) z, S (z + l) = S z := by
    intro l z
    show ∑ᶠ m : L, b (z + l + m) = ∑ᶠ m : L, b (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : L => b (z + m))]
    simp [add_assoc]
  have hSpos : ∀ z, 0 < S z := by
    intro z
    obtain ⟨l, hl⟩ := hcov z
    have h1 := single_le_finsum (f := fun l : L => b (z + l)) l (hlf.point_finite z)
      (fun l => b.nonneg)
    have h2 : b (z + l) = 1 := b.one_of_mem_closedBall (by simpa using hl)
    simp only [h2] at h1
    exact lt_of_lt_of_le one_pos h1
  refine ⟨fun z => b z / S z, hφs.div hSs fun z => (hSpos z).ne', ?_,
    fun z => div_nonneg b.nonneg (hSpos z).le, fun y => ?_⟩
  · simp only [div_eq_mul_inv]
    exact hφc.mul_right
  · simp only [hSp]
    have hfin : (Function.support fun l : L => b (y + l)).Finite := hlf.point_finite y
    have h1 : HasSum (fun l : L => b (y + l)) (S y) := by
      have hs : Summable (fun l : L => b (y + l)) := summable_of_finite_support hfin
      have := hs.hasSum
      rwa [tsum_eq_finsum hfin] at this
    have := h1.div_const (S y)
    rwa [div_self (hSpos y).ne'] at this

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I] {φ : I → K →+* ℂ}

def idx (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) : I := (hφ w.embedding).exists.choose

theorem idx_spec (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) :
    w.embedding = φ (idx hφ w) ∨ w.embedding = ComplexEmbedding.conjugate (φ (idx hφ w)) :=
  (hφ w.embedding).exists.choose_spec

theorem apply_eq_norm (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) (x : K) :
    w x = ‖φ (idx hφ w) x‖ := by
  rcases idx_spec hφ w with h | h
  · rw [← norm_embedding_eq, h]
  · rw [← norm_embedding_eq, h, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

theorem idx_surjective (hφ : GlobalTheory.CMVal.IsCMType φ) (i : I) : ∃ w, idx hφ w = i := by
  refine ⟨InfinitePlace.mk (φ i), ?_⟩
  exact (hφ (InfinitePlace.mk (φ i)).embedding).unique (idx_spec hφ _) (embedding_mk_eq (φ i))

theorem ulog_idx [IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = w.mult * Real.log (w (u : K)) := by
  unfold GlobalTheory.HeckeTheta.ulog
  rw [(IsTotallyComplex.isComplex w).mult_eq_two, ← apply_eq_norm hφ, Real.log_pow]

theorem sum_ulog_idx [IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = 0 := by
  simp only [ulog_idx hφ]
  exact sum_mult_mul_log u

def mean (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : ℝ :=
  (∑ w : InfinitePlace K, y (idx hφ w)) / Fintype.card (InfinitePlace K)

def proj (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : logSpace K :=
  fun w => y (idx hφ w.1) - mean hφ y

theorem proj_add_ulog [IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) (u : (𝓞 K)ˣ) :
    proj hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = proj hφ y + logEmbedding K (Additive.ofMul u) := by
  funext w
  have hm : mean hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = mean hφ y := by
    unfold mean
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_ulog_idx hφ, add_zero]
  simp only [proj, hm, Pi.add_apply, logEmbedding_component, ← ulog_idx hφ]
  ring

theorem continuous_proj (hφ : GlobalTheory.CMVal.IsCMType φ) : Continuous (proj hφ) := by
  unfold proj mean
  fun_prop

end UnitLogPartition

open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace UnitLogPartition in

theorem exists_measurable_nonneg_hasSum_ulog_translates : ∀ (K : Type) [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ →
    ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧
      (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧
      ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  classical
  intro K _ _ _ I _ φ hφ
  obtain ⟨η, hη, hc, h0, hs⟩ := exists_nonneg_hasSum_lattice_translates (logSpace K) (unitLattice K)
  refine ⟨fun y => η (proj hφ y) / Nat.card (torsion K), ?_, ?_, ?_, ?_⟩
  · exact ((hη.continuous.comp (continuous_proj hφ)).div_const _).measurable
  · intro y
    exact div_nonneg (h0 _) (Nat.cast_nonneg _)
  · intro y
    have h1 := ((Additive.ofMul.trans (logEmbeddingEquiv K).toEquiv).hasSum_iff).mpr (hs (proj hφ y))
    have h2 := GlobalTheory.UnitPartition.hasSum_quot (torsion K) _ _ h1
    convert h2 using 2 with u
    beta_reduce
    rw [proj_add_ulog hφ]
    rfl
  · obtain ⟨ρ, hρ⟩ := hc.isCompact.isBounded.exists_norm_le
    set n : ℝ := (Fintype.card (InfinitePlace K) : ℝ) with hn_def
    refine ⟨2 * (n * |ρ|), fun y hy i j => ?_⟩
    have hη0 : η (proj hφ y) ≠ 0 := fun h => hy (by simp [h])
    have hn : ‖proj hφ y‖ ≤ ρ := hρ _ (subset_tsupport _ hη0)
    set d : InfinitePlace K → ℝ := fun w => y (idx hφ w) - mean hφ y with hd
    have hn1 : (1 : ℝ) ≤ n := by
      rw [hn_def]; exact Nat.one_le_cast.mpr (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
    have hsub : ∀ w : {w : InfinitePlace K // w ≠ w₀}, |d w.1| ≤ |ρ| := fun w =>
      ((norm_le_pi_norm (proj hφ y) w).trans hn).trans (le_abs_self ρ)
    have hsum : ∑ w, d w = 0 := by
      have hn0 : n ≠ 0 := by positivity
      simp only [hd, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mean]
      rw [← hn_def, mul_div_cancel₀ _ hn0, sub_self]
    have hall : ∀ w, |d w| ≤ n * |ρ| := by
      intro w
      by_cases hw : w = w₀
      · rw [hw]
        rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
        rw [eq_neg_of_add_eq_zero_left hsum, abs_neg]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ |ρ| fun v _ => hsub v).trans ?_
        rw [nsmul_eq_mul]
        gcongr
        rw [Finset.card_univ, hn_def]
        exact_mod_cast Fintype.card_subtype_le _
      · exact (hsub ⟨w, hw⟩).trans (le_mul_of_one_le_left (abs_nonneg _) hn1)
    obtain ⟨v, rfl⟩ := idx_surjective hφ i
    obtain ⟨v', rfl⟩ := idx_surjective hφ j
    have e : y (idx hφ v) - y (idx hφ v') = d v - d v' := by simp [hd]
    rw [e]
    linarith [le_abs_self (d v), neg_abs_le (d v'), hall v, hall v']

end GlobalTheory
end
end

open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧ (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧ ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  atlas_forward_decl GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates
end

section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace : ∀ (I : Type) [Fintype I] {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (q : (I → ℝ) → ℝ) (B R : ℝ), (∃ i, n i ≠ 0) → (∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) → (∃ δ : ℝ, 0 < δ ∧ ∀ j, a j ≠ 0 → e j ≠ 0 → δ ≤ ‖e j‖) → Measurable q → (∀ y, |q y| ≤ B) → (∀ y, q y ≠ 0 → ∀ i j, y i - y j ≤ R) → MeasureTheory.AEStronglyMeasurable (fun y => (q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y) MeasureTheory.volume ∧ ∀ σ : ℝ, MeasureTheory.Integrable (fun y => ‖(q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y‖ * Real.exp (σ * ∑ i, y i)) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) := by
  first | exact @GlobalTheory.HeckeTheta.Decay.integrable_weight_theta | exact GlobalTheory.HeckeTheta.Decay.integrable_weight_theta | (intros; apply GlobalTheory.HeckeTheta.Decay.integrable_weight_theta <;> assumption)
end

section
section
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeLat

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

theorem exists_one_le_norm {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K} (hα : α ≠ 0) :
    ∃ i, 1 ≤ ‖φ i (α : K)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ w : InfinitePlace K, w (α : K) < 1 := by
    intro w
    obtain ⟨i, hi, -⟩ := hφ w.embedding
    rw [← InfinitePlace.norm_embedding_eq]
    rcases hi with hi | hi
    · rw [hi]; exact h i
    · rw [hi, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]; exact h i
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one hα (fun z _ => hlt z)) (not_le.2 (hlt w))

theorem one_le_norm_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K}
    (hα : GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0) : 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  have h0 : α ≠ 0 := by
    rintro rfl
    apply hα
    funext i
    simp [GlobalTheory.HeckeTheta.emb]
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  exact hi.trans (norm_le_pi_norm (GlobalTheory.HeckeTheta.emb φ (α : K)) i)

def embHom (φ : I → K →+* ℂ) : 𝓞 K →+ (I → ℂ) where
  toFun α := GlobalTheory.HeckeTheta.emb φ (α : K)
  map_zero' := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by funext i; simp [GlobalTheory.HeckeTheta.emb]

theorem embHom_injective {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : Function.Injective (embHom φ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  have : φ i (a : K) = 0 := congrFun ha i
  rw [this, norm_zero] at hi
  exact absurd hi (by norm_num)

omit [Fintype I] in

theorem summable_exp_neg_mul_norm_sq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2) := by
  set k := Module.finrank ℤ L + 1 with hk
  have h := (ZLattice.summable_norm_pow_inv L (2 * k) (by omega)).mul_left
    ((k.factorial : ℝ) / a ^ k)
  refine .of_norm_bounded_eventually h ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with x h0
  have hn : 0 < ‖(x : E)‖ := norm_pos_iff.2 (by simpa using h0)
  have h1 := Real.pow_div_factorial_le_exp (a * ‖(x : E)‖ ^ 2) (by positivity) k
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul, Real.exp_neg]
  refine (inv_anti₀ (by positivity) h1).trans_eq ?_
  change _ = _ * ‖(x : E)‖⁻¹ ^ (2 * k)
  rw [mul_pow, ← pow_mul, inv_pow]
  field_simp

def embLat (φ : I → K →+* ℂ) : Submodule ℤ (I → ℂ) := LinearMap.range (embHom φ).toIntLinearMap

theorem discrete_embLat {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : DiscreteTopology (embLat φ) := by
  refine DiscreteTopology.of_forall_le_dist one_pos fun x y hxy => ?_
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  rw [Subtype.dist_eq, dist_eq_norm]
  have hsub : (x : I → ℂ) - y = GlobalTheory.HeckeTheta.emb φ ((a - b : 𝓞 K) : K) := by
    rw [← ha, ← hb]
    funext i
    simp [embHom, GlobalTheory.HeckeTheta.emb]
  rw [hsub]
  apply one_le_norm_emb hφ
  rw [← hsub, sub_ne_zero]
  exact fun h => hxy (Subtype.ext h)

theorem summable_exp_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun α : 𝓞 K => Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2) := by
  haveI := discrete_embLat hφ
  have hs : Summable fun x : embLat φ ↦ Real.exp (-ε * ‖(x : I → ℂ)‖ ^ 2) :=
    summable_exp_neg_mul_norm_sq (embLat φ) hε
  have hmem : ∀ α : 𝓞 K, embHom φ α ∈ embLat φ := fun α => LinearMap.mem_range_self _ α
  let j : 𝓞 K → embLat φ := fun α => ⟨embHom φ α, hmem α⟩
  have hj : Function.Injective j := fun a b h => embHom_injective hφ (congrArg Subtype.val h)
  have h2 := hs.comp_injective hj
  refine h2.congr fun α => ?_
  simp only [Function.comp_apply, j]
  rfl

theorem bounded_of_periodic {M : Ideal (𝓞 K)} (F : 𝓞 K → ℂ) (hM : M ≠ ⊥)
    (hF : ∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) : ∃ C : ℝ, ∀ α, ‖F α‖ ≤ C := by
  haveI := Ideal.finiteQuotientOfFreeOfNeBot M hM
  haveI := Fintype.ofFinite (𝓞 K ⧸ M)
  refine ⟨∑ q : 𝓞 K ⧸ M, ‖F (Quotient.out q)‖, fun α => ?_⟩
  have hmem : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  have hα : F α = F (Quotient.out (Ideal.Quotient.mk M α)) := by
    have := hF (Quotient.out (Ideal.Quotient.mk M α)) _ hmem
    rwa [add_sub_cancel] at this
  rw [hα]
  exact Finset.single_le_sum (f := fun q : 𝓞 K ⧸ M => ‖F (Quotient.out q)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)

theorem periodic_bound_summable_norm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ),
      M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K =>
        ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧
      ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  intro K _ _ _ I _ φ hφ M F hM hF
  obtain ⟨C, hC⟩ := bounded_of_periodic F hM hF
  refine ⟨⟨C, hC⟩, fun ε hε => ?_, fun α hα => one_le_norm_emb hφ hα⟩
  refine ((summable_exp_emb hφ hε).mul_left C).of_nonneg_of_le (fun α => by positivity) fun α => ?_
  exact mul_le_mul_of_nonneg_right (hC α) (Real.exp_pos _).le

end GlobalTheory.HeckeLat
end
end

open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_bounded_gaussian_summable_cmType : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧ (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K => ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧ ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  atlas_forward_decl GlobalTheory.HeckeLat.periodic_bound_summable_norm
end

section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex : ∀ (k : ℤ) (l : ℂ), 𝓕 (fun w : ℂ => GlobalTheory.HeckeTheta.hmon k w * Complex.exp ((-2 * Real.pi * ‖w‖ ^ 2 : ℝ) : ℂ)) l = (1 / 2 : ℂ) * (-Complex.I) ^ k.natAbs * (GlobalTheory.HeckeTheta.hmon k (l / 2) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian | exact GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian | (intros; apply GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian <;> assumption)
end

section
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory

theorem fourier_prod_coord_complex (I : Type) [Fintype I] (f : I → ℂ → ℂ)
    (_hf : ∀ i, Integrable (f i)) (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by
  simp only [Real.fourier_eq']
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (volume_preserving_ofLp_complex I).integral_comp
      (MeasurableEquiv.toLp 2 (I → ℂ)).symm.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum,
    Complex.ofReal_sum, Finset.sum_mul]

end GlobalTheory
end

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_prod_single_coordinate_functions : ∀ (I : Type) [Fintype I] (f : I → ℂ → ℂ), (∀ i, Integrable (f i)) → ∀ l : EuclideanSpace ℂ I, 𝓕 (fun w : EuclideanSpace ℂ I => ∏ i, f i (w i)) l = ∏ i, 𝓕 (f i) (l i) := by
  atlas_forward_decl GlobalTheory.fourier_prod_coord_complex
end

section
section
noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckePoisson.Dilation

open GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

def dilPi (y : I → ℝ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) :=
  LinearMap.pi fun i => (Real.exp (y i / 2) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)

def dilE (y : I → ℝ) : EuclideanSpace ℂ I →ₗ[ℝ] EuclideanSpace ℂ I :=
  ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm : (I → ℂ) →ₗ[ℝ] EuclideanSpace ℂ I) ∘ₗ dilPi y ∘ₗ
    ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm.symm : EuclideanSpace ℂ I →ₗ[ℝ] (I → ℂ))

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_apply_eq_toLp_dil (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE y w = WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)) := by
  ext i
  simp [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, _root_.GlobalTheory.HeckeTheta.dil]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_neg_apply_dilE_apply (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y w) = w := by
  ext i
  simp only [dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, WithLp.ofLp_toLp, Pi.neg_apply, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma det_dilE_eq_exp_sum (y : I → ℝ) : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) = Real.exp (∑ i, y i) := by
  rw [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, LinearMap.det_conj, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, LinearMap.det_pi, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma inner_dilE_dilE_neg (y : I → ℝ) (v l : EuclideanSpace ℂ I) :
    ⟪_root_.GlobalTheory.HeckePoisson.Dilation.dilE y v, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫ = ⟪v, l⟫ := by
  simp [-Complex.ofReal_exp, dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, real_inner_eq_re_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Real.exp (y i / 2) * Real.exp (-y i / 2) = 1 := by
    rw [← Real.exp_add, show y i / 2 + -y i / 2 = 0 by ring, Real.exp_zero]
  linear_combination ((l.ofLp i).re * (v.ofLp i).re + (l.ofLp i).im * (v.ofLp i).im) * h

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in

theorem _root_.GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ)
    (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l =
      (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  let e : EuclideanSpace ℂ I ≃ₗ[ℝ] EuclideanSpace ℂ I :=
    LinearEquiv.ofLinear (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y))
      (LinearMap.ext fun w => by simpa using dilE_neg_apply_dilE_apply (-y) w)
      (LinearMap.ext fun w => dilE_neg_apply_dilE_apply y w)
  have hemb : MeasurableEmbedding (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) :=
    e.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hdet : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) ≠ 0 := by
    rw [det_dilE_eq_exp_sum]
    exact (Real.exp_pos _).ne'
  have key := hemb.integral_map (μ := volume)
    (fun u => 𝐞 (-⟪u, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫) • f u)
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, integral_smul_measure] at key
  simp only [inner_dilE_dilE_neg] at key
  simp only [dilE_apply_eq_toLp_dil] at key
  rw [Real.fourier_eq, Real.fourier_eq, ← key, det_dilE_eq_exp_sum, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (inv_pos.mpr (Real.exp_pos _)), ← Real.exp_neg, Complex.real_smul]

end GlobalTheory.HeckePoisson.Dilation
end
end

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_comp_coordDilationByHalfExp : ∀ (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ) (l : EuclideanSpace ℂ I), 𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l = (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  atlas_forward_decl GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil
end

section
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

noncomputable section

namespace GlobalTheory.HeckePoisson

open GlobalTheory.CMVal InfinitePlace ComplexConjugate
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]

def toMixed {φ : I → K →+* ℂ} (h : IsCMType φ) : EuclideanSpace ℂ I ≃ₗ[ℝ] mixedEmbedding.mixedSpace K := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  let b : I ≃ InfinitePlace K := Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)
  exact
  { toFun := fun z => (0, fun w => if φ (b.symm w.1) = (InfinitePlace.mk (φ (b.symm w.1))).embedding
        then z (b.symm w.1) else conj (z (b.symm w.1)))
    invFun := fun x => WithLp.toLp 2 (fun i => if φ i = (InfinitePlace.mk (φ i)).embedding
        then x.2 ⟨InfinitePlace.mk (φ i), IsTotallyComplex.isComplex _⟩
        else conj (x.2 ⟨InfinitePlace.mk (φ i), IsTotallyComplex.isComplex _⟩))
    map_add' := fun x y => Prod.ext (by simp) (funext fun w => by
      simp only [Prod.snd_add, Pi.add_apply, PiLp.add_apply]; split_ifs <;> simp)
    map_smul' := fun r x => Prod.ext (by simp) (funext fun w => by
      simp only [Prod.smul_snd, Pi.smul_apply, PiLp.smul_apply, RingHom.id_apply]
      split_ifs <;> simp [Complex.real_smul])
    left_inv := fun z => by
      ext i
      have hi : b.symm (InfinitePlace.mk (φ i)) = i := b.symm_apply_apply i
      simp only [hi]
      split_ifs <;> simp
    right_inv := fun x => by
      refine Prod.ext (Subsingleton.elim _ _) (funext fun w => ?_)
      have e : (⟨InfinitePlace.mk (φ (b.symm w.1)), IsTotallyComplex.isComplex _⟩ : {w : InfinitePlace K // w.IsComplex}) = w :=
        Subtype.ext (b.apply_symm_apply w.1)
      simp only [e]
      split_ifs <;> simp }

theorem toMixed_embA {φ : I → K →+* ℂ} (h : IsCMType φ) (α : 𝓞 K) :
    toMixed h (embA φ α) = mixedEmbedding K (α : K) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  refine Prod.ext (Subsingleton.elim _ _) (funext fun w => ?_)
  rw [mixedEmbedding.mixedEmbedding_apply_isComplex]
  simp only [toMixed, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, embA_apply]
  set i := (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).symm w.1 with hi
  have hw : InfinitePlace.mk (φ i) = w.1 :=
    (Equiv.ofBijective _ (GlobalTheory.CMVal.Model.IsCMType.bijective h)).apply_symm_apply w.1
  split_ifs with hs
  · rw [hs, hw]
  · have hc := (InfinitePlace.embedding_mk_eq (φ i)).resolve_left (fun e => hs e.symm)
    rw [← hw, hc]
    simp [ComplexEmbedding.conjugate_coe_eq]

open Classical in
theorem lat_eq_comap {φ : I → K →+* ℂ} (h : IsCMType φ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    lat φ M = ZLattice.comap (E := mixedEmbedding.mixedSpace K) (F := EuclideanSpace ℂ I) ℝ (mixedEmbedding.idealLattice K
      (Units.mk0 (M : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hM)))
      (toMixed h).toContinuousLinearEquiv.toLinearMap := by
  ext z
  rw [mem_lat]
  change _ ↔ toMixed h z ∈ mixedEmbedding.idealLattice K _
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨(μ : K), (FractionalIdeal.mem_coeIdeal _).2 ⟨μ, hμ, rfl⟩, (toMixed_embA h μ).symm⟩
  · rintro ⟨y, hy, hyz⟩
    have hy' : y ∈ (M : FractionalIdeal (𝓞 K)⁰ K) := hy
    obtain ⟨μ, hμ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy'
    exact ⟨μ, hμ, (toMixed h).injective (by rw [toMixed_embA]; exact hyz)⟩

theorem lat_isZLattice : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ →
      ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  intro K _ _ _ I _ φ h M hM
  classical
  rw [lat_eq_comap h M hM]
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.HeckePoisson
end
end

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ → ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  atlas_forward_decl GlobalTheory.HeckePoisson.lat_isZLattice
end

section
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

noncomputable section

namespace GlobalTheory.HeckeTheta.GaussBound

open GlobalTheory.HeckeTheta

theorem gauss_cont_bound : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  intro I _ n
  refine ⟨?_, ⟨Decay.gC n, fun w => ?_⟩⟩
  · unfold gauss
    refine continuous_finset_prod _ fun i _ => ?_
    have hc : Continuous fun w : EuclideanSpace ℂ I => (WithLp.ofLp w) i :=
      (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
    exact ((Decay.continuous_hmon _).comp hc).mul (by fun_prop)
  · have h := Decay.norm_gauss_le n (WithLp.ofLp w)
    have e : ‖w‖ ^ 2 = ∑ i, ‖(WithLp.ofLp w) i‖ ^ 2 := EuclideanSpace.norm_sq_eq w
    rw [e]; exact h

end GlobalTheory.HeckeTheta.GaussBound
end
end

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded : ∀ (I : Type) [Fintype I] (n : I → ℤ), Continuous (fun w : EuclideanSpace ℂ I => GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)) ∧ ∃ C : ℝ, ∀ w : EuclideanSpace ℂ I, ‖GlobalTheory.HeckeTheta.gauss n (WithLp.ofLp w)‖ ≤ C * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  atlas_forward_decl GlobalTheory.HeckeTheta.GaussBound.gauss_cont_bound
end

section
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory

noncomputable def quotCosetProdEquiv (R : Type) [CommRing R] (M : Ideal R) : (R ⧸ M) × M ≃ R where
  toFun p := Quotient.out p.1 + (p.2 : R)
  invFun α := (Ideal.Quotient.mk M α, ⟨α - Quotient.out (Ideal.Quotient.mk M α), by
    rw [← Ideal.Quotient.eq]
    exact (Ideal.Quotient.mk_out _).symm⟩)
  left_inv p := by
    obtain ⟨c, μ⟩ := p
    have hc : Ideal.Quotient.mk M (Quotient.out c + (μ : R)) = c := by
      rw [map_add, Ideal.Quotient.mk_out, Ideal.Quotient.eq_zero_iff_mem.mpr μ.2, add_zero]
    ext
    · exact hc
    · simp only [hc]; ring
  right_inv α := by simp

theorem tsum_eq_sum_quotient_tsum_ideal (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)]
    (h : R → ℂ) (hs : Summable h) :
    ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) := by
  rw [← (quotCosetProdEquiv R M).tsum_eq h]
  have hs' : Summable (h ∘ quotCosetProdEquiv R M) := (quotCosetProdEquiv R M).summable_iff.mpr hs
  rw [show (∑' c : (R ⧸ M) × ↥M, h (quotCosetProdEquiv R M c)) = ∑' p, (h ∘ quotCosetProdEquiv R M) p from rfl,
    hs'.tsum_prod, tsum_fintype]
  rfl

theorem cosets_main : ∀ (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)] (h : R → ℂ), Summable h → ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) :=
  fun R _ M _ h hs => tsum_eq_sum_quotient_tsum_ideal R M h hs

end GlobalTheory
end

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_ring_eq_sum_ideal_cosets_tsum : ∀ (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)] (h : R → ℂ), Summable h → ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) := by
  atlas_forward_decl GlobalTheory.cosets_main
end

section
section
noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckePoisson

open GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

theorem gauss_unit (k : ℤ) (z : ℂ) :
    gauss (fun _ : Unit => k) (fun _ => z) = hmon k z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  simp [gauss]

theorem norm_toLp_unit (z : ℂ) : ‖(WithLp.toLp 2 (fun _ : Unit => z) : EuclideanSpace ℂ Unit)‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq]; simp

theorem integrable_hmon_gauss (k : ℤ) :
    Integrable (fun z : ℂ => hmon k z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨hc, C, hC⟩ := GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded Unit (fun _ => k)
  have hcont : Continuous (fun z : ℂ => hmon k z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ)) := by
    have : Continuous (fun z : ℂ => (WithLp.toLp 2 (fun _ : Unit => z) : EuclideanSpace ℂ Unit)) := by fun_prop
    simpa [Function.comp_def, gauss_unit] using hc.comp this
  have hint : Integrable (fun z : ℂ => C * Real.exp (-Real.pi * ‖z‖ ^ 2)) := by
    have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos) 0 0).norm
    refine (this.const_mul C).congr (ae_of_all _ fun z => ?_)
    simp only [inner_zero_left, Complex.norm_exp]
    congr 2
    simp [← Complex.ofReal_pow]
  refine hint.mono' hcont.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have h := hC (WithLp.toLp 2 (fun _ : Unit => z))
  rw [norm_toLp_unit] at h
  simpa [gauss_unit] using h

theorem fourier_gauss (n : I → ℤ) (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => gauss n (WithLp.ofLp w)) l = kappa n * gauss n (fun i => l i / 2) := by
  have h := GlobalTheory.T.fourier_prod_single_coordinate_functions I (fun i z => hmon (n i) z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ))
    (fun i => integrable_hmon_gauss (n i)) l
  have e : (fun w : EuclideanSpace ℂ I => gauss n (WithLp.ofLp w)) =
      fun w => ∏ i, (hmon (n i) (w i) * Complex.exp ((-2 * Real.pi * ‖w i‖ ^ 2 : ℝ) : ℂ)) := rfl
  rw [e, h]
  simp only [GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex]
  unfold kappa gauss
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]
  simp [one_div, inv_pow]

theorem norm_half_sq (l : EuclideanSpace ℂ I) :
    ‖l‖ ^ 2 ≤ 4 * Fintype.card I * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖l i‖ ^ 2 ≤ ∑ _i : I, 4 * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := norm_le_pi_norm (fun i => l i / 2 : I → ℂ) i
        have h2 : ‖l i‖ = 2 * ‖(fun i => l i / 2 : I → ℂ) i‖ := by
          simp only [norm_div, Complex.norm_ofNat]; ring
        rw [h2]
        nlinarith [norm_nonneg ((fun i => l i / 2 : I → ℂ) i)]
    _ = 4 * Fintype.card I * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem norm_toLp_half (l : EuclideanSpace ℂ I) :
    ‖(WithLp.toLp 2 (fun i => l i / 2) : EuclideanSpace ℂ I)‖ = ‖l‖ / 2 := by
  have : (WithLp.toLp 2 (fun i => l i / 2) : EuclideanSpace ℂ I) = (2⁻¹ : ℝ) • l := by
    ext i; simp [div_eq_mul_inv, mul_comm]
  rw [this, norm_smul]; simp [div_eq_inv_mul]

theorem norm_dil_sq_ge (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    Real.exp (-∑ i, |y i|) * ‖w‖ ^ 2 ≤ ‖(WithLp.toLp 2 (dil y (WithLp.ofLp w)) : EuclideanSpace ℂ I)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have he : Real.exp (y i / 2) ^ 2 = Real.exp (y i) := by rw [sq, ← Real.exp_add, add_halves]
  have h1 : ‖(WithLp.toLp 2 (dil y (WithLp.ofLp w)) : EuclideanSpace ℂ I) i‖ ^ 2 = Real.exp (y i) * ‖w i‖ ^ 2 := by
    simp only [dil, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, he]
  rw [h1]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
  have := Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have := neg_abs_le (y i)
  simp only at *
  linarith

theorem gauss_dil_bound (n : I → ℤ) (y : I → ℝ) : ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ w : EuclideanSpace ℂ I,
    ‖gauss n (dil y (WithLp.ofLp w))‖ ≤ C * Real.exp (-a * ‖w‖ ^ 2) := by
  obtain ⟨-, C, hC⟩ := GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded I n
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0)
    exact le_of_mul_le_mul_right (by rw [zero_mul]; exact h) (Real.exp_pos _)
  refine ⟨C, Real.pi * Real.exp (-∑ i, |y i|), hC0, by positivity, fun w => ?_⟩
  have h := hC (WithLp.toLp 2 (dil y (WithLp.ofLp w)))
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0)
  have := norm_dil_sq_ge y w
  nlinarith [Real.pi_pos]

theorem poisson_coset (L : Submodule ℤ (EuclideanSpace ℂ I)) [DiscreteTopology L] [IsZLattice ℝ L]
    (n : I → ℤ) (y : I → ℝ) (u : EuclideanSpace ℂ I) :
    Summable (fun l : GlobalTheory.dualLattice L => ‖gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2))‖) ∧
    ∑' x : L, gauss n (dil y (WithLp.ofLp ((x : EuclideanSpace ℂ I) + u))) =
      ((ZLattice.covolume L : ℝ) : ℂ)⁻¹ * ((Real.exp (-∑ i, y i) : ℂ) * kappa n) *
        ∑' l : GlobalTheory.dualLattice L, Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u⟫ : ℝ) : ℂ)) *
          gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2)) := by
  set f : EuclideanSpace ℂ I → ℂ := fun w => gauss n (dil y (WithLp.ofLp w)) with hf
  have hF : ∀ l : EuclideanSpace ℂ I, 𝓕 f l =
      (Real.exp (-∑ i, y i) : ℂ) * kappa n * gauss n (dil (-y) (fun i => l i / 2)) := by
    intro l
    have h := GlobalTheory.T.fourier_comp_coordDilationByHalfExp I (fun w => gauss n (WithLp.ofLp w)) y l
    rw [hf, h, fourier_gauss, mul_assoc]
    congr 3
    funext i
    simp only [dil]
    ring
  obtain ⟨C, a, hC0, ha, hC⟩ := gauss_dil_bound n y
  obtain ⟨C', a', hC0', ha', hC'⟩ := gauss_dil_bound n (-y)
  have hcont : Continuous f := by
    have h1 := (GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded I n).1
    have h2 : Continuous (fun w : EuclideanSpace ℂ I => (WithLp.toLp 2 (dil y (WithLp.ofLp w)) : EuclideanSpace ℂ I)) := by
      unfold dil; fun_prop
    have h3 := h1.comp h2
    simpa only [Function.comp_def, WithLp.ofLp_toLp, hf] using h3
  have hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (v : EuclideanSpace ℂ I), ‖v‖ ≤ R → ‖f (x + v)‖ ≤ g x := by
    intro R
    refine ⟨fun x => C * (Real.exp (a * R ^ 2) * Real.exp (-(a / 2) * ‖(x : EuclideanSpace ℂ I)‖ ^ 2)),
      ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left _).mul_left _, fun x v hv => ?_⟩
    exact (hC _).trans (mul_le_mul_of_nonneg_left (GlobalTheory.exp_neg_mul_norm_add_sq_le ha.le _ hv) hC0)
  have hG : Summable (fun l : GlobalTheory.dualLattice L => ‖gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2))‖) := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
      ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq (GlobalTheory.dualLattice L) (div_pos ha' (by norm_num : (0:ℝ) < 4))).mul_left C')
    have h := hC' (WithLp.toLp 2 (fun i => (l : EuclideanSpace ℂ I) i / 2))
    rw [norm_toLp_half] at h
    refine h.trans_eq ?_
    congr 2
    ring
  have hs : Summable fun l : GlobalTheory.dualLattice L => ‖𝓕 f l‖ := by
    simp only [hF, norm_mul]
    exact hG.mul_left _
  refine ⟨hG, ?_⟩
  have hP := GlobalTheory.tsum_poisson_lattice L hcont hdom hs u
  simp only [hf] at hP
  rw [hP, Complex.real_smul, Complex.ofReal_inv, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  rw [smul_eq_mul, (hF l : 𝓕 (fun w : EuclideanSpace ℂ I => gauss n (dil y (WithLp.ofLp w))) l = _)]
  ring

theorem discrete_norm_ge {E : Type} [NormedAddCommGroup E] (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ r : ℝ, 0 < r ∧ ∀ x : L, x ≠ 0 → r ≤ ‖(x : E)‖ := by
  obtain ⟨r, hr, h⟩ := Metric.isOpen_singleton_iff.1 (isOpen_discrete ({0} : Set L))
  refine ⟨r, hr, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  exact hx (h x (by rw [dist_zero_right]; exact hlt))

theorem theta_poisson : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (M : Ideal (NumberField.RingOfIntegers K))
    (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) →
    ∃ (a : (I → ℂ) → ℂ) (κ : ℂ), (∀ ε : ℝ, 0 < ε → Summable (fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2))) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ v, a v ≠ 0 → v ≠ 0 → δ ≤ ‖v‖) ∧
      ∀ y : I → ℝ, GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y =
        κ * (Real.exp (-∑ i, y i) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n (-y) := by
  intro K _ _ _ I _ φ hφ n M F hM hF
  classical
  obtain ⟨hd, hz⟩ := GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice K I φ hφ M hM
  haveI : Finite (𝓞 K ⧸ M) := Ideal.finiteQuotientOfFreeOfNeBot M hM
  letI : Fintype (𝓞 K ⧸ M) := Fintype.ofFinite _
  set L := lat φ M with hL
  set D := GlobalTheory.dualLattice L with hD
  have hI : Nonempty I := by
    obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
    obtain ⟨i, -, -⟩ := hφ σ
    exact ⟨i⟩
  have hinj : Function.Injective (embA φ) := by
    intro x x' h
    obtain ⟨i⟩ := hI
    have h2 := congrArg (fun z : EuclideanSpace ℂ I => z i) h
    simp only [embA_apply] at h2
    exact RingOfIntegers.ext ((φ i).injective h2)

  set u : 𝓞 K ⧸ M → EuclideanSpace ℂ I := fun c => embA φ (Quotient.out c) with hu
  set half : D → (I → ℂ) := fun l i => (l : EuclideanSpace ℂ I) i / 2 with hhalf_def
  have hhalf : Function.Injective half := by
    intro l l' h
    apply Subtype.ext
    ext i
    have := congrFun h i
    simp only [hhalf_def] at this
    linear_combination 2 * this
  set cov : ℂ := ((ZLattice.covolume L : ℝ) : ℂ) with hcov
  set A : D → ℂ := fun l => cov⁻¹ * ∑ c : 𝓞 K ⧸ M, F (Quotient.out c) *
    Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) with hA
  set a : (I → ℂ) → ℂ := fun v => if h : ∃ l : D, half l = v then A (Classical.choose h) else 0 with ha_def
  have ha_half : ∀ l, a (half l) = A l := by
    intro l
    have h : ∃ l' : D, half l' = half l := ⟨l, rfl⟩
    simp only [ha_def, dif_pos h]
    rw [hhalf (Classical.choose_spec h)]
  have ha_zero : ∀ v, v ∉ Set.range half → a v = 0 := by
    intro v hv
    have h : ¬ ∃ l : D, half l = v := fun ⟨l, hl⟩ => hv ⟨l, hl⟩
    simp only [ha_def, dif_neg h]
  set B : ℝ := ‖cov⁻¹‖ * ∑ c : 𝓞 K ⧸ M, ‖F (Quotient.out c)‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have hAB : ∀ l, ‖A l‖ ≤ B := by
    intro l
    simp only [hA, hB, norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) (norm_nonneg _)
    rw [norm_mul, GlobalTheory.norm_cexp_two_pi_I, mul_one]
  set cI : ℝ := (Fintype.card I : ℝ) with hcI
  have hcI0 : 0 ≤ cI := by positivity
  have hnorm : ∀ l : D, ‖(l : EuclideanSpace ℂ I)‖ ^ 2 ≤ (4 * cI + 1) * ‖half l‖ ^ 2 := by
    intro l
    have := norm_half_sq (l : EuclideanSpace ℂ I)
    nlinarith [sq_nonneg ‖half l‖]
  refine ⟨a, kappa n, ?_, ?_, ?_⟩
  ·
    intro ε hε
    have hpos : 0 < ε / (4 * cI + 1) := by positivity
    have key : Summable (fun l : D => ‖a (half l)‖ * Real.exp (-ε * ‖half l‖ ^ 2)) := by
      refine .of_nonneg_of_le (fun _ => by positivity) (fun l => ?_)
        ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq D hpos).mul_left B)
      rw [ha_half]
      refine mul_le_mul (hAB l) (Real.exp_le_exp.2 ?_) (by positivity) hB0
      have h1 := hnorm l
      have h2 : ε / (4 * cI + 1) * ‖(l : EuclideanSpace ℂ I)‖ ^ 2 ≤ ε * ‖half l‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    exact (hhalf.summable_iff (f := fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2))
      (fun v hv => by simp [ha_zero v hv])).1 key
  ·
    obtain ⟨r, hr, hr'⟩ := discrete_norm_ge (GlobalTheory.dualLattice L)
    refine ⟨r / (4 * cI + 1), by positivity, fun v hav hv0 => ?_⟩
    by_cases hv : v ∈ Set.range half
    · obtain ⟨l, rfl⟩ := hv
      have hl0 : l ≠ 0 := by
        rintro rfl
        apply hv0
        funext i
        simp [hhalf_def]
      have h1 : r ≤ ‖(l : EuclideanSpace ℂ I)‖ := hr' ⟨l, l.2⟩ (fun h => hl0 (Subtype.ext (congrArg Subtype.val h)))
      have h2 := hnorm l
      have h3 : r ^ 2 ≤ ((4 * cI + 1) * ‖half l‖) ^ 2 := by
        have : r ^ 2 ≤ ‖(l : EuclideanSpace ℂ I)‖ ^ 2 := pow_le_pow_left₀ hr.le h1 2
        have h4 : (4 * cI + 1) * ‖half l‖ ^ 2 ≤ ((4 * cI + 1) * ‖half l‖) ^ 2 := by
          rw [mul_pow]
          have : (4 * cI + 1) ≤ (4 * cI + 1) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        linarith
      have h5 : r ≤ (4 * cI + 1) * ‖half l‖ := (pow_le_pow_iff_left₀ hr.le (by positivity) two_ne_zero).1 h3
      rw [div_le_iff₀ (by positivity)]
      linarith
    · exact absurd (ha_zero v hv) hav
  ·
    intro y
    obtain ⟨hd', hz'⟩ := GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice K I φ hφ ⊤ (by simp)
    obtain ⟨C, b, hC0, hb, hC⟩ := gauss_dil_bound n y
    set BF : ℝ := ∑ c : 𝓞 K ⧸ M, ‖F (Quotient.out c)‖ with hBF
    have hFc : ∀ α : 𝓞 K, F α = F (Quotient.out (Ideal.Quotient.mk M α)) := by
      intro α
      have hm : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M := by
        rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
      have := hF (Quotient.out (Ideal.Quotient.mk M α)) _ hm
      rw [add_sub_cancel] at this
      exact this
    have hFB : ∀ α : 𝓞 K, ‖F α‖ ≤ BF := by
      intro α
      rw [hFc α]
      exact Finset.single_le_sum (f := fun c => ‖F (Quotient.out c)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
    have hemb : ∀ α : 𝓞 K, emb φ (α : K) = WithLp.ofLp (embA φ α) := fun α => rfl
    have hsum : Summable (fun α : 𝓞 K => F α * gauss n (dil y (emb φ (α : K)))) := by
      have hT : Summable (fun x : lat φ ⊤ => BF * (C * Real.exp (-b * ‖(x : EuclideanSpace ℂ I)‖ ^ 2))) :=
        ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq (lat φ ⊤) hb).mul_left C).mul_left BF
      have hi : Function.Injective (fun α : 𝓞 K => (⟨embA φ α, mem_lat.2 ⟨α, Submodule.mem_top, rfl⟩⟩ : lat φ ⊤)) :=
        fun x x' h => hinj (congrArg Subtype.val h)
      refine Summable.of_norm_bounded (hT.comp_injective hi) (fun α => ?_)
      simp only [Function.comp_apply, norm_mul]
      exact mul_le_mul (hFB α) (hC (embA φ α)) (norm_nonneg _) (by positivity)

    let e : M ≃ L := Equiv.ofBijective (fun μ => (⟨embA φ μ, mem_lat.2 ⟨μ, μ.2, rfl⟩⟩ : L))
      ⟨fun x x' h => Subtype.ext (hinj (congrArg Subtype.val h)), fun x => by
        obtain ⟨μ, hμ, h⟩ := mem_lat.1 x.2
        exact ⟨⟨μ, hμ⟩, Subtype.ext h⟩⟩
    have hcoset : ∀ c : 𝓞 K ⧸ M, ∑' μ : M, F (Quotient.out c + μ) * gauss n (dil y (emb φ ((Quotient.out c + μ : 𝓞 K) : K))) =
        F (Quotient.out c) * (cov⁻¹ * ((Real.exp (-∑ i, y i) : ℂ) * kappa n) *
          ∑' l : D, Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) *
            gauss n (dil (-y) (half l))) := by
      intro c
      have h1 : ∀ μ : M, F (Quotient.out c + μ) * gauss n (dil y (emb φ ((Quotient.out c + μ : 𝓞 K) : K))) =
          F (Quotient.out c) * gauss n (dil y (WithLp.ofLp (((e μ : L) : EuclideanSpace ℂ I) + u c))) := by
        intro μ
        rw [hF _ _ μ.2]
        have hx : emb φ ((Quotient.out c + μ : 𝓞 K) : K) = WithLp.ofLp (((e μ : L) : EuclideanSpace ℂ I) + u c) := by
          funext i
          show φ i ((Quotient.out c + μ : 𝓞 K) : K) = (embA φ μ + embA φ (Quotient.out c)) i
          rw [PiLp.add_apply, embA_apply, embA_apply]
          push_cast
          rw [map_add, add_comm]
        rw [hx]
      rw [tsum_congr h1, tsum_mul_left,
        e.tsum_eq (fun x : L => gauss n (dil y (WithLp.ofLp ((x : EuclideanSpace ℂ I) + u c)))),
        (poisson_coset L n y (u c)).2]
    have hLHS := GlobalTheory.T.tsum_ring_eq_sum_ideal_cosets_tsum (𝓞 K) M _ hsum
    unfold GlobalTheory.HeckeTheta.theta
    rw [hLHS, Finset.sum_congr rfl (fun c _ => hcoset c)]

    have hsupp : Function.support (fun v : I → ℂ => a v * gauss n (dil (-y) v)) ⊆ Set.range half := by
      intro v hv
      by_contra h
      exact hv (by simp [ha_zero v h])
    rw [← hhalf.tsum_eq hsupp]
    simp only [ha_half, hA]
    have hsc : ∀ c ∈ (Finset.univ : Finset (𝓞 K ⧸ M)), Summable (fun l : D => cov⁻¹ * (F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l))) := by
      intro c _
      refine Summable.of_norm_bounded (((poisson_coset L n y (u c)).1).mul_left (‖cov⁻¹‖ * ‖F (Quotient.out c)‖)) (fun l => ?_)
      rw [norm_mul, norm_mul, norm_mul, GlobalTheory.norm_cexp_two_pi_I, mul_one]
    have hre : ∀ l : D, cov⁻¹ * (∑ c : 𝓞 K ⧸ M, F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) =
        ∑ c : 𝓞 K ⧸ M, cov⁻¹ * (F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) := by
      intro l
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [tsum_congr hre, Summable.tsum_finsetSum hsc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hre2 : ∀ l : D, cov⁻¹ * (F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) =
        (cov⁻¹ * F (Quotient.out c)) * (Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) *
          gauss n (dil (-y) (half l))) := fun l => by ring
    rw [tsum_congr hre2, tsum_mul_left]
    ring

end GlobalTheory.HeckePoisson
end
end

open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeThetaKernel_poisson_summation : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → ∃ (a : (I → ℂ) → ℂ) (κ : ℂ), (∀ ε : ℝ, 0 < ε → Summable (fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2))) ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ v, a v ≠ 0 → v ≠ 0 → δ ≤ ‖v‖) ∧ ∀ y : I → ℝ, GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y = κ * (Real.exp (-∑ i, y i) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n (-y) := by
  atlas_forward_decl GlobalTheory.HeckePoisson.theta_poisson
end

section
section
open NumberField MeasureTheory

namespace GlobalTheory

theorem mellinSplit_hyperplane_null (I : Type) [Fintype I] [Nonempty I] :
    (volume : Measure (I → ℝ)) {y : I → ℝ | ∑ i, y i = 0} = 0 := by
  let L : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hL : ∀ y, L y = ∑ i, y i := by intro y; simp [L]
  have hset : {y : I → ℝ | ∑ i, y i = 0} = (LinearMap.ker L : Set (I → ℝ)) := by
    ext y; simp [hL]
  rw [hset]
  apply Measure.addHaar_submodule
  intro htop
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  have hmem : Pi.single i (1:ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hmem
  simp at hmem

theorem mellinSplit_neg (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ)
    (hθ : ∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y))
    (h1 : MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}))
    (h2 : MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i})) :
    ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  set f : (I → ℝ) → ℂ := fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf
  set g : (I → ℝ) → ℂ := fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) with hg
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hS
  set P : Set (I → ℝ) := {y | 0 < ∑ i, y i} with hP
  have hcont : Continuous (fun y : I → ℝ => ∑ i, y i) :=
    continuous_finset_sum _ fun i _ => continuous_apply i
  have hSm : MeasurableSet S := (isClosed_le continuous_const hcont).measurableSet
  have hsumneg : ∀ y : I → ℝ, ∑ i, (-y) i = -∑ i, y i := by
    intro y; simp [Finset.sum_neg_distrib]
  have hfg : ∀ y, f y = κ * g (-y) := by
    intro y
    simp only [hf, hg, hθ, neg_neg, hsumneg]
    have e : Complex.exp (-((∑ i, y i : ℝ) : ℂ)) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))
        = Complex.exp ((1 - s) * ((-∑ i, y i : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have e2 : ((Real.exp (-∑ i, y i) : ℝ) : ℂ) = Complex.exp (-((∑ i, y i : ℝ) : ℂ)) := by
      push_cast; rfl
    rw [e2]
    linear_combination ((p y : ℂ) * κ * θ' (-y)) * e
  have hpre : (Neg.neg : (I → ℝ) → (I → ℝ)) ⁻¹' P = Sᶜ := by
    ext y; simp [hP, hS, hsumneg]
  have hmp : MeasurePreserving (Neg.neg : (I → ℝ) → (I → ℝ)) volume volume :=
    Measure.measurePreserving_neg _
  have hemb : MeasurableEmbedding (Neg.neg : (I → ℝ) → (I → ℝ)) :=
    (MeasurableEquiv.neg (I → ℝ)).measurableEmbedding
  have hPS : P =ᵐ[volume] S := by
    rw [ae_eq_set]
    constructor
    · have : P \ S = ∅ := Set.diff_eq_empty.mpr (fun y (hy : 0 < ∑ i, y i) => (le_of_lt hy : 0 ≤ ∑ i, y i))
      rw [this, measure_empty]
    · apply measure_mono_null _ (mellinSplit_hyperplane_null I)
      intro y hy
      simp only [hP, hS, Set.mem_diff, Set.mem_setOf_eq, not_lt] at hy
      exact le_antisymm hy.2 hy.1
  have hgP : IntegrableOn g P volume :=
    IntegrableOn.congr_set_ae (show IntegrableOn g S volume from h2) hPS
  have hfc : IntegrableOn f Sᶜ volume := by
    have := (hmp.integrableOn_comp_preimage hemb).2 hgP
    rw [hpre] at this
    have h3 := this.const_mul κ
    refine IntegrableOn.congr_fun h3 (fun y _ => ?_) hSm.compl
    simp [hfg y]
  have hfint : Integrable f volume := by
    have := IntegrableOn.union (show IntegrableOn f S volume from h1) hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  rw [← integral_add_compl hSm hfint]
  congr 1
  calc ∫ y in Sᶜ, f y = ∫ y in Sᶜ, κ * g (-y) := by simp_rw [hfg]
    _ = κ * ∫ y in Sᶜ, g (-y) := integral_const_mul _ _
    _ = κ * ∫ y in P, g y := by
        rw [← hpre, hmp.setIntegral_preimage_emb hemb]
    _ = κ * ∫ y in S, g y := by rw [setIntegral_congr_set hPS]

end GlobalTheory
end

open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellin_integral_split_functional_equation : ∀ (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ), (∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y)) → MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  atlas_forward_decl GlobalTheory.mellinSplit_neg
end

section
section
noncomputable section
open NumberField MeasureTheory

namespace GlobalTheory.HeckeStrip

theorem completed_pSeries_entire_bounded : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  intro K _ _ _ I _ φ hφ n hn M F hM hper hinv
  haveI : Nonempty I := ⟨hn.choose⟩
  obtain ⟨p, hpm, hp0, hpsum, R, hpR⟩ := GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates K I φ hφ
  obtain ⟨⟨C, hC⟩, hsumm, hge⟩ := GlobalTheory.T.periodic_bounded_gaussian_summable_cmType K I φ hφ M F hM hper
  obtain ⟨a, κ, hasumm, ⟨δ, hδ, hδa⟩, hfe⟩ := GlobalTheory.T.heckeThetaKernel_poisson_summation K I φ hφ n M F hM hper
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hpsum y) 1 (fun u _ => hp0 _)
    have h0 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by
      funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h0] using h
  have hpB : ∀ y, |p y| ≤ 1 := fun y => abs_le.2 ⟨by linarith [hp0 y], hp1 y⟩
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hℓ : Measurable (fun y : I → ℝ => ∑ i, y i) := by fun_prop
  have hS0 : ∀ᵐ y ∂(volume.restrict S), 0 ≤ ∑ i, y i := ae_restrict_of_forall_mem hSm fun y hy => hy
  obtain ⟨D1m, D1i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n p 1 R hn hsumm
    ⟨1, one_pos, fun α _ h => hge α h⟩ hpm hpB hpR
  obtain ⟨D2m, D2i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun v : I → ℂ => v) a n (fun y => p (-y)) 1 R hn hasumm ⟨δ, hδ, hδa⟩
    (hpm.comp measurable_neg) (fun y => hpB _) (fun y hy i j => by
      have := hpR (-y) hy j i
      simp only [Pi.neg_apply] at this
      linarith)
  have A1 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D1m.restrict hS0 D1i
  have A2 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D2m.restrict hS0 D2i
  have hint : ∀ (g : (I → ℝ) → ℂ) (t : ℂ), AEStronglyMeasurable g volume →
      (∀ σ : ℝ, Integrable (fun y => ‖g y‖ * Real.exp (σ * ∑ i, y i)) (volume.restrict S)) →
      Integrable (fun y => g y * Complex.exp (t * ((∑ i, y i : ℝ) : ℂ))) (volume.restrict S) := by
    intro g t hg hgi
    refine (hgi t.re).mono' (hg.restrict.mul (Continuous.aestronglyMeasurable (by fun_prop))) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp [Complex.mul_re]
  set f1 : ℂ → ℂ := fun s => ∫ y in S, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf1
  set f2 : ℂ → ℂ := fun s => ∫ y in S, (p (-y) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf2
  have hd1 : Differentiable ℂ f1 := A1.1
  have hd2 : Differentiable ℂ f2 := A2.1
  have hb1 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f1 := A1.2
  have hb2 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f2 := A2.2
  refine ⟨fun s => 2 ^ Fintype.card I * (f1 s + κ * f2 (1 - s)), ?_, ?_, ?_⟩
  · exact (hd1.add ((hd2.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul κ)).const_mul _
  · intro a' b' hab
    obtain ⟨C1, hC1⟩ := hb1 a' b' hab
    obtain ⟨C2, hC2⟩ := hb2 (1 - b') (1 - a') (by linarith)
    refine ⟨‖(2 : ℂ) ^ Fintype.card I‖ * (C1 + ‖κ‖ * C2), fun s h1 h2 => ?_⟩
    rw [norm_mul]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add (hC1 s h1 h2) ?_)
    rw [norm_mul]
    gcongr
    exact hC2 (1 - s) (by simp; linarith) (by simp; linarith)
  · intro s hs
    rw [GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt K I φ hφ n hn F C hC hinv p hpm hp0 hpsum s hs,
      GlobalTheory.T.mellin_integral_split_functional_equation I p _ _ κ s hfe (hint _ s D1m D1i) (hint _ (1 - s) D2m D2i)]

end GlobalTheory.HeckeStrip
end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  atlas_forward_decl GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeStrip

theorem completedLBoundedInStrips : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips := by
  intro E _ _ _ I _ φ hφ χ n hu hi hn
  obtain ⟨m, X, hm, hX0, hX1, hXm, hXn, hXz, hXP, hXβ⟩ := GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar E χ hu
  have hβ : ∀ β : 𝓞 E, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = wt φ n (β : E) := by
    intro β h0 h1
    have h0' : (β : E) ≠ 0 := by exact_mod_cast h0
    rw [hXβ β (Units.mk0 _ h0') rfl h1, hi (Units.mk0 _ h0')]
    simp only [wt, Units.val_mk0, zpow_neg, Finset.prod_inv_distrib]
  have hle : ∀ a, ‖X a‖ ≤ 1 := fun a => by
    by_cases ha : a = ⊥
    · simp [ha, hX0]
    by_cases ha' : a ⊔ m = ⊤
    · exact (hXn a ha ha').le
    · simp [hXz a ha']
  obtain ⟨r, c, B, M, F, hB, hM, hper, hinv, hdec⟩ := GlobalTheory.T.heckeLSeries_eq_sum_principalPartialSeries E I φ n m X hm hX0 hXm hXn hXz hβ
  choose Λ hΛd hΛb hΛe using fun k => GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips E I φ hφ n hn (M k) (F k) (hM k) (hper k) (hinv k)
  have hB0 : ∀ k, ((B k : ℕ) : ℂ) ≠ 0 := fun k => by exact_mod_cast (hB k).ne'
  refine ⟨fun s => ∑ k, c k * ((B k : ℕ) : ℂ) ^ s * Λ k s, ⟨?_, fun s hs => ?_⟩, ?_⟩
  · intro s
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((differentiableAt_const _).mul ((differentiableAt_id.const_cpow (Or.inl (hB0 k))))).mul ((hΛd k).differentiableAt)
  · refine ⟨∑' a : Ideal (𝓞 E), X a * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-s), ?_, ?_⟩
    · rw [GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum E X hX0 hX1 hXm hle s hs]
      convert GlobalTheory.HeckeOne.hasProd_exp hu hs using 1
      simp only [hXP, GlobalTheory.HeckeOne.cf]
    · rw [hdec s hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hΛe k s hs]
      ring
  · intro a b hab
    choose C hC using fun k => hΛb k a b hab
    refine ⟨∑ k, ‖c k‖ * ((B k : ℝ) ^ b * |C k|), fun s h1 h2 => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_natCast_cpow_of_pos (hB k)]
    have hB1 : (1 : ℝ) ≤ (B k : ℝ) := by exact_mod_cast hB k
    gcongr
    exact (hC k s h1 h2).trans (le_abs_self _)

end GlobalTheory.HeckeStrip
end
end
