import Formalism.SharpRestriction.GrowthBounds.RootWeights.RaiseLowerPowCommutatorOnWeight
import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorLinftyBound

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

inductive IsLoweringWord (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : (Fin n → ℤ) → V → Prop
  | base : IsLoweringWord E lam v lam v
  | step (c d : Fin n) (h : d < c) (l : ℕ) (hl : 1 ≤ l) (nu : Fin n → ℤ) (x : V) :
      IsLoweringWord E lam v nu x → IsLoweringWord E lam v (nu + (l : ℤ) • rootW c d) (divPowE E c d l x)

theorem weight_height_add_root_smul (nu : Fin n → ℤ) (a b : Fin n) (l : ℕ) :
    weightHeightAscending (nu + (l : ℤ) • rootW a b) = weightHeightAscending nu + l * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have e : nu + ((l + 1 : ℕ) : ℤ) • rootW a b = nu + (l : ℤ) • rootW a b + rootW a b := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    rw [e, weightHeightAscending_add_root, ih]; push_cast; ring

theorem dividedPower_mem_shifted_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu)
    (a c : Fin n) (j : ℕ) : divPowE E a c j x ∈ weightSp E (nu + (j : ℤ) • rootW a c) := by
  rw [divPowE, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (integral_operator_pow_shifts_weight hE hx a c j)

theorem loweringWord_mem_weightSpace {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V} (hv : v ∈ weightSp E lam)
    {nu : Fin n → ℤ} {x : V} (h : IsLoweringWord E lam v nu x) : x ∈ weightSp E nu := by
  induction h with
  | base => exact hv
  | step c d _ l _ nu x _ ih => exact dividedPower_mem_shifted_weight hE ih c d l

theorem loweringWord_height_ge_highest {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    {nu : Fin n → ℤ} {x : V} (h : IsLoweringWord E lam v nu x) : weightHeightAscending lam ≤ weightHeightAscending nu := by
  induction h with
  | base => exact le_refl _
  | step c d hdc l _ nu x _ ih =>
    rw [weight_height_add_root_smul]
    have h1 : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast hdc
    have : (0 : ℤ) ≤ (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)) := mul_nonneg (by positivity) (by omega)
    omega

def loweringSpanOfHeight (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) (N : ℤ) : Submodule O V :=
  Submodule.span O {x | ∃ nu, IsLoweringWord E lam v nu x ∧ weightHeightAscending nu ≤ weightHeightAscending lam + N}

theorem loweringSpan_height_monotone (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) {N N' : ℤ} (h : N ≤ N') :
    loweringSpanOfHeight (O := O) E lam v N ≤ loweringSpanOfHeight (O := O) E lam v N' := by
  refine Submodule.span_mono ?_
  rintro x ⟨nu, h1, h2⟩
  exact ⟨nu, h1, by omega⟩

theorem loweringSpan_map_le_of_words {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {N : ℤ} {L : Submodule O V}
    (T : Module.End (KK O) V)
    (h : ∀ nu x, IsLoweringWord E lam v nu x → weightHeightAscending nu ≤ weightHeightAscending lam + N → T x ∈ L) :
    ∀ y ∈ loweringSpanOfHeight (O := O) E lam v N, T y ∈ L := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨nu, h1, h2⟩ := hy; exact h nu y h1 h2
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul (KK O) r y, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ hy

theorem loweringSpan_lower_dividedPower_mem (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) {c d : Fin n} (hdc : d < c) (i : ℕ) (M : ℤ) :
    ∀ y ∈ loweringSpanOfHeight (O := O) E lam v M,
      divPowE E c d i y ∈ loweringSpanOfHeight (O := O) E lam v (M + i * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))) := by
  refine loweringSpan_map_le_of_words _ fun nu x h1 h2 => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have : divPowE E c d 0 x = x := by simp [divPowE]
    rw [this]
    exact Submodule.subset_span ⟨nu, h1, by simpa using h2⟩
  · exact Submodule.subset_span ⟨_, IsLoweringWord.step c d hdc i hi nu x h1, by rw [weight_height_add_root_smul]; omega⟩

theorem dividedPower_eq_divPowE (E : GLOps n (KK O) V) (a b : Fin n) (k : ℕ) : dividedPower (KK O) (E a b) k = divPowE E a b k := rfl

theorem dividedPower_neg_sign (X : Module.End (KK O) V) (j : ℕ) :
    dividedPower (KK O) (-X) j = (((-1 : ℤ) ^ j : ℤ) : KK O) • dividedPower (KK O) X j := by
  rw [dividedPower, dividedPower, neg_pow, smul_smul]
  push_cast
  rw [mul_comm, ← smul_smul]
  congr 1
  rcases Nat.even_or_odd j with h | h <;> simp [h.neg_one_pow]

theorem raising_dividedPower_loweringSpan [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) (N : ℕ) : ∀ nu x, IsLoweringWord E lam v nu x → weightHeightAscending nu ≤ weightHeightAscending lam + N →
      ∀ a b : Fin n, a < b → ∀ k : ℕ, divPowE E a b k x ∈ loweringSpanOfHeight (O := O) E lam v N := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro nu x hLW hht a b hab k
  cases hLW with
  | base =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : divPowE E a b 0 v = v := by simp [divPowE]
      rw [this]
      exact Submodule.subset_span ⟨lam, IsLoweringWord.base, by omega⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have : divPowE E a b (k' + 1) v = 0 := by
        rw [divPowE, LinearMap.smul_apply, pow_succ, Module.End.mul_apply, hv.2.2 a b hab, map_zero, smul_zero]
      rw [this]; exact Submodule.zero_mem _
  | step c d hdc l hl nu' x' hLW' =>
    have hgap : (1 : ℤ) ≤ ((c : ℕ) : ℤ) - ((d : ℕ) : ℤ) := by
      have : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast hdc
      omega
    have hab' : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
    rw [weight_height_add_root_smul] at hht
    have hlow := loweringWord_height_ge_highest hLW'
    have hlg : (1 : ℤ) ≤ (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)) := by
      have h1 : (1 : ℤ) ≤ (l : ℤ) := by exact_mod_cast hl
      nlinarith
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = N - (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)) :=
      ⟨(N - (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))).toNat, by omega⟩
    have hMN : M < N := by omega
    have hx'M : weightHeightAscending nu' ≤ weightHeightAscending lam + M := by omega
    have IHM := IH M hMN
    have RL : ∀ a' b' : Fin n, a' < b' → ∀ k' : ℕ, ∀ y ∈ loweringSpanOfHeight (O := O) E lam v M,
        divPowE E a' b' k' y ∈ loweringSpanOfHeight (O := O) E lam v M := fun a' b' h' k' =>
      loweringSpan_map_le_of_words _ fun nu2 x2 h1 h2 => IHM nu2 x2 h1 h2 a' b' h' k'
    have hx'w := loweringWord_mem_weightSpace hE hv.2.1 hLW'
    by_cases hcase : c = b ∧ d = a
    · obtain ⟨rfl, rfl⟩ := hcase
      rw [raise_lower_dividedPower_binomial hE (ne_of_lt hab) hx'w k l]
      refine Submodule.sum_mem _ fun j _ => ?_
      split_ifs with hj
      · refine intCast_smul_mem_submodule _ _ ?_
        refine loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v hdc (l - j) M _ (IHM nu' x' hLW' hx'M d c hab (k - j)))
        have : ((l - j : ℕ) : ℤ) ≤ (l : ℤ) := by exact_mod_cast Nat.sub_le l j
        nlinarith
      · exact Submodule.zero_mem _
    ·
      have key : ∀ Z : Module.End (KK O) V, E a b * E c d = E c d * E a b + Z → Z * E c d = E c d * Z →
          E a b * Z = Z * E a b →
          (∀ j : ℕ, ∀ y ∈ loweringSpanOfHeight (O := O) E lam v M,
            dividedPower (KK O) Z j y ∈ loweringSpanOfHeight (O := O) E lam v (M + j * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)))) →
          divPowE E a b k (divPowE E c d l x') ∈ loweringSpanOfHeight (O := O) E lam v N := by
        intro Z h1 h2 h3 h4
        have e := heisenberg_dividedPower_expansion (K := KK O) h1 h2 h3 k l
        have e2 : divPowE E a b k (divPowE E c d l x') =
            (dividedPower (KK O) (E a b) k * dividedPower (KK O) (E c d) l) x' := rfl
        rw [e2, e, LinearMap.sum_apply]
        refine Submodule.sum_mem _ fun j _ => ?_
        split_ifs with hj
        · rw [Module.End.mul_apply, Module.End.mul_apply]
          have s1 := IHM nu' x' hLW' hx'M a b hab (k - j)
          have s2 := h4 j _ s1
          have s3 := loweringSpan_lower_dividedPower_mem E lam v hdc (l - j) _ _ s2
          refine loweringSpan_height_monotone E lam v ?_ s3
          push_cast [Nat.cast_sub hj]
          rw [hM]; ring_nf; exact le_refl _
        · simp
      have hr := hE.1 a b c d
      by_cases hbc : b = c
      · have hda : d ≠ a := fun e => hcase ⟨hbc.symm, e⟩
        subst hbc
        refine key (E a d) ?_ ?_ ?_ ?_
        · rw [if_pos rfl, if_neg hda, sub_zero] at hr
          rw [← hr]; abel
        · have := hE.1 a d b d
          rw [if_neg (ne_of_lt hdc), if_neg hda, sub_zero] at this
          exact sub_eq_zero.1 this
        · have := hE.1 a b a d
          rw [if_neg (ne_of_gt hab), if_neg hda, sub_zero] at this
          exact sub_eq_zero.1 this
        · intro j y hy
          rw [dividedPower_eq_divPowE]
          rcases lt_or_gt_of_ne hda with h | h
          · have hh : ((d : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast h
            refine loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v h j M y hy)
            have : (0 : ℤ) ≤ (j : ℤ) := by positivity
            nlinarith
          · refine loweringSpan_height_monotone E lam v ?_ (RL a d h j y hy)
            have : (0 : ℤ) ≤ (j : ℤ) := by positivity
            nlinarith
      · by_cases hda : d = a
        · subst hda
          refine key (-E c b) ?_ ?_ ?_ ?_
          · rw [if_neg hbc, if_pos rfl, zero_sub] at hr
            rw [← hr]; abel
          · have := hE.1 c b c d
            rw [if_neg hbc, if_neg (ne_of_lt hdc), sub_zero] at this
            rw [neg_mul, mul_neg, sub_eq_zero.1 this]
          · have := hE.1 d b c b
            rw [if_neg hbc, if_neg (ne_of_gt hab), sub_zero] at this
            rw [neg_mul, mul_neg, sub_eq_zero.1 this]
          · intro j y hy
            rw [dividedPower_neg_sign, LinearMap.smul_apply, dividedPower_eq_divPowE]
            refine intCast_smul_mem_submodule _ _ ?_
            rcases lt_or_gt_of_ne hbc with h | h
            · have hh : ((b : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast h
              refine loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v h j M y hy)
              have : (0 : ℤ) ≤ (j : ℤ) := by positivity
              nlinarith
            · refine loweringSpan_height_monotone E lam v ?_ (RL c b h j y hy)
              have : (0 : ℤ) ≤ (j : ℤ) := by positivity
              nlinarith
        · refine key 0 ?_ (by simp) (by simp) ?_
          · rw [if_neg hbc, if_neg hda, sub_zero] at hr
            rw [add_zero]; exact sub_eq_zero.1 hr
          · intro j y hy
            rcases Nat.eq_zero_or_pos j with rfl | hj
            · simpa [dividedPower] using hy
            · have : dividedPower (KK O) (0 : Module.End (KK O) V) j = 0 := by
                rw [dividedPower, zero_pow (by omega), smul_zero]
              rw [this]; exact Submodule.zero_mem _

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def loweringOperatorSpan (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : Submodule O V :=
  Submodule.span O {x | ∃ nu, IsLoweringWord E lam v nu x}

theorem loweringSpanOfHeight_le_total (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) (N : ℤ) :
    loweringSpanOfHeight (O := O) E lam v N ≤ loweringOperatorSpan (O := O) E lam v := by
  unfold loweringSpanOfHeight loweringOperatorSpan
  exact Submodule.span_mono fun x ⟨nu, h, _⟩ => ⟨nu, h⟩

private theorem eq_of_isLoweringWord_of_weight_eq {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    {nu : Fin n → ℤ} {x : V} (h : IsLoweringWord E lam v nu x) : nu = lam → x = v := by
  cases h with
  | base => intro _; rfl
  | step c d hdc l hl nu' x' h' =>
    intro heq
    have h1 := loweringWord_height_ge_highest h'
    have h2 := weight_height_add_root_smul nu' c d l
    rw [heq] at h2
    have hl' : (1 : ℤ) ≤ l := by exact_mod_cast hl
    have hcd : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast (Fin.lt_iff_val_lt_val.mp hdc)
    nlinarith

theorem loweringSpan_divided_power_stable [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) : UZStable (O := O) E (loweringOperatorSpan (O := O) E lam v) := by
  intro u hu y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨nu, hnu⟩ := hx
    have hxL : x ∈ loweringSpanOfHeight (O := O) E lam v (weightHeightAscending nu - weightHeightAscending lam) :=
      Submodule.subset_span ⟨nu, hnu, by omega⟩
    rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · rcases lt_or_gt_of_ne hab with h | h
      · refine loweringSpanOfHeight_le_total E lam v ((weightHeightAscending nu - weightHeightAscending lam).toNat) ?_
        exact raising_dividedPower_loweringSpan hE hv _ nu x hnu (by omega) a b h k
      · exact loweringSpanOfHeight_le_total E lam v _ (loweringSpan_lower_dividedPower_mem E lam v h k _ x hxL)
    · have hw := loweringWord_mem_weightSpace hE hv.2.1 hnu
      rw [binomial_diagonal_on_weight hw a k]
      have : ((Ring.choose (nu a) k : ℤ) : KK O) = algebraMap O (KK O) ((Ring.choose (nu a) k : ℤ) : O) := by
        simp
      rw [this, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨nu, hnu⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx

theorem loweringSpan_highest_component_integral {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) : ∀ y ∈ loweringOperatorSpan (O := O) E lam v,
      ∃ c : O, y - (algebraMap O (KK O) c) • v ∈ otherWts E lam := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨nu, hnu⟩ := hx
    by_cases h : nu = lam
    · refine ⟨1, ?_⟩
      rw [eq_of_isLoweringWord_of_weight_eq hnu h, map_one, one_smul, sub_self]
      exact Submodule.zero_mem _
    · refine ⟨0, ?_⟩
      rw [map_zero, zero_smul, sub_zero]
      exact Submodule.mem_iSup_of_mem nu (Submodule.mem_iSup_of_mem h (loweringWord_mem_weightSpace hE hv.2.1 hnu))
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, h1⟩ := hx
    obtain ⟨c2, h2⟩ := hy
    refine ⟨c1 + c2, ?_⟩
    have : x + y - algebraMap O (KK O) (c1 + c2) • v =
        (x - algebraMap O (KK O) c1 • v) + (y - algebraMap O (KK O) c2 • v) := by
      rw [map_add, add_smul]; abel
    rw [this]; exact Submodule.add_mem _ h1 h2
  | smul a x _ hx =>
    obtain ⟨c, h⟩ := hx
    refine ⟨a * c, ?_⟩
    rw [map_mul, mul_smul, algebraMap_smul, ← smul_sub]
    exact Submodule.smul_of_tower_mem _ a h

theorem highest_vector_mem_nabla [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) : v ∈ Nabla (O := O) E lam v := by
  intro u hu
  exact loweringSpan_highest_component_integral hE hv (u v)
    (integral_enveloping_preserves_submodule (loweringSpan_divided_power_stable hE hv) hu v (Submodule.subset_span ⟨lam, IsLoweringWord.base⟩))

end hw

theorem highest_vector_integrality : HighestWeightVectorIntegrality := by
  intro p n' O _ _ _ S hG n _ lam V _ _ _ _ E v hI
  haveI := dvr_fraction_field_char_zero_prime S hG.prime
  exact highest_vector_mem_nabla hI.1 hI.2.2.1

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem linf_adjoint_le_ellWt_highest [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V}
    {lam : Fin n → ℤ} {v : V} (hI : IsIrrHW E lam v) : linf (adjointEndAction E) ⊤ ≤ ellWt lam := by
  refine csSup_le' ?_
  rintro k ⟨ka, hk, -, a, rfl⟩
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 hk
  have hfw := hf.1
  obtain ⟨nu, x, hx, hfx⟩ : ∃ nu x, x ∈ weightSp E nu ∧ f x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf0
    have hk : (⊤ : Submodule (KK O) V) ≤ LinearMap.ker f := by
      rw [← hI.1.2.2]
      exact iSup_le fun nu x hx => hcon nu x hx
    exact LinearMap.ext fun x => hk Submodule.mem_top
  have hx0 : x ≠ 0 := by rintro rfl; simp at hfx
  have hfxw : f x ∈ weightSp E (nu + ka) := by
    rw [mem_weightSpace_iff_diag_scalar]
    intro c
    have h1 := congrArg (fun T : Module.End (KK O) V => T x) (mem_weightSpace_iff_diag_scalar.1 hfw c)
    simp only [adjointEndAction_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h1
    rw [mem_weightSpace_iff_diag_scalar.1 hx c, map_smul] at h1
    rw [sub_eq_iff_eq_add.1 h1, ← add_smul]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  have h1 := weight_entries_between_extreme_highest hI hfxw hfx a
  have h2 := weight_entries_between_extreme_highest hI hx hx0 a
  simp only [Pi.add_apply] at h1
  unfold ellWt
  omega

end hw

theorem restA_of_linf_integrality (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorLinftyBound) (hK : HighestWeightVectorIntegrality) : LatticeNablaDeltaBound := by
  intro p n' O _ _ _ S hR n _ lam V _ _ _ _ E v hI x hx
  have := dvr_fraction_field_char_zero_prime S hR.prime
  have := irreducible_highest_weight_findim hI
  have hCR := h2 (KK O) V n E hI.1
  obtain ⟨xi, x1, x2, x3⟩ := exists_highest_coordinate_functional hI
  have hKv := hK p n' O S hR n lam V E v hI
  have hlat : UZLattice (O := O) (adjointEndAction E) (nablaToDeltaMaps (O := O) E lam v) :=
    ⟨nabla_to_delta_maps_stable hI.1 lam v, nabla_to_delta_maps_fg hI hCR x1 x2 x3 hKv⟩
  have hMQ := nabla_to_delta_maps_span_top (O := O) hI (nabla_finitely_generated hI hCR x1 x2 x3)
  have key := h p n' O S hR n (Module.End (KK O) V) (adjointEndAction E) (adjoint_end_isGLRep hI.1) _ hlat hMQ
    (traceInvariantProjection O V) (trace_projection_isInvProj hI) (xi.smulRight v) (coordinate_rank_one_mem_maps x1 x2 x3)
  rw [hMQ] at key
  have hd : (Module.finrank (KK O) V : KK O) ≠ 0 := by
    have : Nontrivial V := ⟨⟨v, 0, hI.2.2.1.1⟩⟩
    exact_mod_cast (Module.finrank_pos (R := KK O) (M := V)).ne'
  have hInv : traceInvariantProjection O V (xi.smulRight v) = ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V) := by
    rw [traceInvariantProjection, LinearMap.smulRight_apply, LinearMap.trace_smulRight, x1, one_smul]
  rw [hInv] at key
  set D' := N0 n * deF p n (linf (adjointEndAction E) ⊤) with hD'
  set D0 := N0 n * deF p n (ellWt lam) with hD0
  have hle : D' ≤ D0 := by
    refine Nat.mul_le_mul_left _ ?_
    unfold deF
    exact Nat.log_mono_right (by have := linf_adjoint_le_ellWt_highest hI; omega)
  have h3 : ((Module.finrank (KK O) V : ℕ) : O) • ((p : O) ^ (D0 - D')) •
      ((p : O) ^ D' • ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)) ∈ nablaToDeltaMaps (O := O) E lam v :=
    Submodule.smul_mem _ _ (Submodule.smul_mem _ _ key)
  have h4 : ((Module.finrank (KK O) V : ℕ) : O) • ((p : O) ^ (D0 - D')) •
      ((p : O) ^ D' • ((Module.finrank (KK O) V : KK O)⁻¹) • (1 : Module.End (KK O) V)) =
      (p : O) ^ D0 • (1 : Module.End (KK O) V) := by
    rw [smul_smul ((p : O) ^ (D0 - D')), ← pow_add, Nat.sub_add_cancel hle, smul_comm,
      ← algebraMap_smul (KK O) ((Module.finrank (KK O) V : ℕ) : O), smul_smul, map_natCast, mul_inv_cancel₀ hd,
      one_smul]
  rw [h4] at h3
  have := h3 x hx
  simpa using this

theorem integral_form_of_linf_lemma (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorLinftyBound) : NablaDeltaComparisonField D :=
  highest_weight_lattice_of_first_part D (restA_of_linf_integrality D h2 h highest_vector_integrality)

end Formalism.MainNotions.G.GLWeightTheory
end
end
