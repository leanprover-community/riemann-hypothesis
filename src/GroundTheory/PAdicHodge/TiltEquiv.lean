import Mathlib
import GroundTheory.PAdicHodge.UntiltPerfectoid
import GroundTheory.PAdicHodge.UntiltField
import GroundTheory.PAdicHodge.TiltAlgebra
import GroundTheory.PAdicHodge.AxLemma
import GroundTheory.PAdicHodge.TiltAlgClosed
import GroundTheory.PAdicHodge.PerfectoidField

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial

section Conj

variable {F E : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [NormedField E] [NormedAlgebra F E]

theorem norm_eq_of_isConjRoot {x x' : E} (hx : IsIntegral F x) (h : IsConjRoot F x x') :
    ‖x‖ = ‖x'‖ := by
  have hx' : IsIntegral F x' := h.isIntegral hx
  have e1 := NormedAlgebra.norm_eq_spectralNorm F (⟨x, hx⟩ : algebraicClosure F E)
  have e2 := NormedAlgebra.norm_eq_spectralNorm F (⟨x', hx'⟩ : algebraicClosure F E)
  change ‖x‖ = _ at e1
  change ‖x'‖ = _ at e2
  rw [e1, e2, spectralNorm, spectralNorm, IntermediateField.minpoly_eq,
    IntermediateField.minpoly_eq]
  change spectralValue (minpoly F x) = spectralValue (minpoly F x')
  rw [h]

theorem mem_range_of_norm_sub_lt [IsAlgClosed E] {α : E} (b : F) (hα : IsSeparable F α)
    (h : ∀ α' : E, IsConjRoot F α α' → α ≠ α' → ‖α - algebraMap F E b‖ < ‖α - α'‖) :
    α ∈ Set.range (algebraMap F E) := by
  have hαi : IsIntegral F α := hα.isIntegral
  let L := algebraicClosure F E
  let x : L := ⟨α, hαi⟩
  have : IsKrasner F L := IsKrasner.of_completeSpace F L
  have hxsep : (minpoly F x).Separable := by
    rw [IntermediateField.minpoly_eq]; exact hα
  have sp : ((minpoly F x).map (algebraMap F L)).Splits := by
    rw [IntermediateField.minpoly_eq]
    refine IntermediateField.splits_of_splits (IsAlgClosed.splits _) fun z hz => ?_
    rw [mem_rootSet] at hz
    exact ⟨minpoly F α, minpoly.monic hαi, by rw [← aeval_def]; exact hz.2⟩
  have key := IsKrasner.krasner hxsep sp (isIntegral_algebraMap (x := b)) fun x' hx' hne => by
    have hc : IsConjRoot F α (x' : E) := by
      unfold IsConjRoot at hx' ⊢
      rwa [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq] at hx'
    have hne' : α ≠ (x' : E) := fun e => hne (Subtype.ext e)
    exact h x' hc hne'
  rw [IntermediateField.adjoin_simple_eq_bot_iff.2 (IntermediateField.algebraMap_mem _ _)] at key
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 key
  exact ⟨c, congrArg Subtype.val hc⟩

end Conj

section Roots

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

theorem norm_le_one_of_eval_eq_zero {f : E[X]} (hf : f.Monic) (hc : ∀ n, ‖f.coeff n‖ ≤ 1)
    {r : E} (hr : f.eval r = 0) : ‖r‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  set d := f.natDegree
  have hr0 : 0 < ‖r‖ := one_pos.trans hlt
  have hsum : ‖∑ i ∈ Finset.range d, f.coeff i * r ^ i‖ < ‖r‖ ^ d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd]; simp
    have hle : ∀ i ∈ Finset.range d, ‖f.coeff i * r ^ i‖ ≤ ‖r‖ ^ (d - 1) := by
      intro i hi
      rw [norm_mul, norm_pow]
      calc ‖f.coeff i‖ * ‖r‖ ^ i ≤ 1 * ‖r‖ ^ i := by gcongr; exact hc i
        _ = ‖r‖ ^ i := one_mul _
        _ ≤ ‖r‖ ^ (d - 1) := pow_le_pow_right₀ hlt.le (by
            have := Finset.mem_range.1 hi; omega)
    calc ‖∑ i ∈ Finset.range d, f.coeff i * r ^ i‖ ≤ ‖r‖ ^ (d - 1) := by
          have := norm_multiset_sum_le_of_forall_le (s := (Finset.range d).val.map
            fun i => f.coeff i * r ^ i) (pow_nonneg hr0.le _) (by
              intro a ha
              obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 ha
              exact hle i hi)
          simpa [Finset.sum_eq_multiset_sum] using this
      _ < ‖r‖ ^ d := pow_lt_pow_right₀ hlt (by omega)
  have heval : f.eval r = ∑ i ∈ Finset.range d, f.coeff i * r ^ i + r ^ d := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, one_mul]
  rw [heval] at hr
  have : ‖r ^ d‖ = ‖∑ i ∈ Finset.range d, f.coeff i * r ^ i‖ := by
    rw [eq_neg_of_add_eq_zero_right hr, norm_neg]
  rw [norm_pow] at this
  exact (lt_irrefl _) (this ▸ hsum)

theorem norm_coeff_prod_X_sub_C_le_one {s : Multiset E} (hs : ∀ r ∈ s, ‖r‖ ≤ 1) (k : ℕ) :
    ‖((s.map fun r => X - C r).prod).coeff k‖ ≤ 1 := by
  by_cases hk : k ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hk, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    simpa using norm_esymm_le zero_le_one hs (Multiset.card s - k)
  · rw [coeff_eq_zero_of_natDegree_lt]
    · simp
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

end Roots

section Tilt

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]

local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem exists_multiset_eq_prod [IsAlgClosed C♭] {Q : 𝒪C♭[X]} (hQ : Q.Monic) :
    ∃ s : Multiset 𝒪C♭, Q = (s.map fun b => X - Polynomial.C b).prod := by
  set f := Q.map (algebraMap 𝒪C♭ C♭)
  have hfm : f.Monic := hQ.map _
  have hfc : ∀ n, ‖f.coeff n‖ ≤ 1 := fun n => by
    rw [coeff_map, norm_algebraMap_preTilt]; exact preTilt_norm_le_one _
  have hroot : ∀ r ∈ f.roots, ‖r‖ ≤ 1 := fun r hr =>
    norm_le_one_of_eval_eq_zero hfm hfc (isRoot_of_mem_roots hr)
  classical
  let g : C♭ → 𝒪C♭ := fun r =>
    if h : ‖r‖ ≤ 1 then (norm_le_one_iff_exists_algebraMap.1 h).choose else 0
  have hg : ∀ r ∈ f.roots, algebraMap 𝒪C♭ C♭ (g r) = r := fun r hr => by
    simp only [g, dif_pos (hroot r hr)]
    exact (norm_le_one_iff_exists_algebraMap.1 (hroot r hr)).choose_spec
  have hf : f = (f.roots.map fun r => X - Polynomial.C r).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic hfm
  refine ⟨f.roots.map g, map_injective _ (IsFractionRing.injective 𝒪C♭ C♭) ?_⟩
  change f = _
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  conv_lhs => rw [hf]
  congr 1
  refine Multiset.map_congr rfl fun r hr => ?_
  simp [hg r hr]

theorem norm_prod_sub_untilt_le (s : Multiset 𝒪C♭) {Q : (normInteger C)[X]}
    (hQ : Q.map (Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})) =
      ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0))
    {z : normInteger C} (hz : Q.eval z = 0) :
    ‖(s.map fun b => (z : C) - ((PreTilt.untilt b : normInteger C) : C)).prod‖ ≤ ‖(p : C)‖ := by
  set mk := Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})
  set R : (normInteger C)[X] := (s.map fun b => X - Polynomial.C (PreTilt.untilt b)).prod
  have h1 : ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0) = R.map mk := by
    simp only [R, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, mk, PreTilt.mk_untilt_eq_coeff_zero]
  have h2 : mk (R.eval z) = 0 := by
    rw [← eval₂_at_apply, ← eval_map, ← h1, ← hQ, eval_map, eval₂_at_apply, hz, map_zero]
  have h3 := (mk_eq_zero_iff_norm_le (p := p)).1 h2
  have h4 : ((R.eval z : normInteger C) : C) =
      (s.map fun b => (z : C) - ((PreTilt.untilt b : normInteger C) : C)).prod := by
    simp only [R, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_X,
      eval_C]
    rw [← (normInteger C).subtype_apply, map_multiset_prod, Multiset.map_map]
    rfl
  rw [← h4]
  exact h3

def monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) : 𝒪C♭[X] :=
  X ^ e + ∑ m ∈ Finset.range e, Polynomial.C (a m) * X ^ m

theorem monic_monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) : (monicOfCoeffs e a).Monic := by
  refine Polynomial.monic_X_pow_add ?_
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe e)).2 fun m hm => ?_
  refine (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt ?_
  exact WithBot.coe_lt_coe.2 (Finset.mem_range.1 hm)

theorem coeff_monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) (m : ℕ) :
    (monicOfCoeffs e a).coeff m = if m = e then 1 else if m < e then a m else 0 := by
  simp only [monicOfCoeffs, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with h1 h2
  · subst h1
    rw [Finset.sum_eq_zero fun i hi => if_neg (by have := Finset.mem_range.1 hi; omega), add_zero]
  · rw [Finset.sum_eq_single m (fun i _ hi => if_neg (Ne.symm hi)) (fun h => absurd
      (Finset.mem_range.2 h2) h), if_pos rfl, zero_add]
  · rw [zero_add, Finset.sum_eq_zero fun i hi => if_neg (by
      have := Finset.mem_range.1 hi; omega)]

theorem natDegree_monicOfCoeffs (e : ℕ) (a : ℕ → 𝒪C♭) : (monicOfCoeffs e a).natDegree = e := by
  have hm := monic_monicOfCoeffs e a
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun m hm' => ?_) ?_
  · rw [coeff_monicOfCoeffs, if_neg (by
      have : e < m := by exact_mod_cast hm'
      omega), if_neg (by
      have : e < m := by exact_mod_cast hm'
      omega)]
  · refine le_natDegree_of_ne_zero ?_
    rw [coeff_monicOfCoeffs, if_pos rfl]
    exact one_ne_zero

theorem exists_root_norm_sub_untilt_pow_le [IsAlgClosed C♭] {Q : (normInteger C)[X]}
    (hQ : Q.Monic) (hdeg : 0 < Q.natDegree) (a : ℕ → 𝒪C♭)
    (ha : ∀ m < Q.natDegree, Ideal.Quotient.mk (Ideal.span {(p : normInteger C)}) (Q.coeff m) =
      PreTilt.coeff 0 (a m))
    {z : normInteger C} (hz : Q.eval z = 0) :
    ∃ b : 𝒪C♭, (monicOfCoeffs Q.natDegree a).eval b = 0 ∧
      ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ^ Q.natDegree ≤ ‖(p : C)‖ := by
  set e := Q.natDegree
  obtain ⟨s, hs⟩ := exists_multiset_eq_prod (monic_monicOfCoeffs (C := C) (p := p) e a)
  have hcard : Multiset.card s = e := by
    have := natDegree_monicOfCoeffs (C := C) (p := p) e a
    rw [hs, natDegree_multiset_prod_X_sub_C_eq_card] at this
    exact this
  have hQ' : Q.map (Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})) =
      ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0) := by
    rw [← hs]
    ext m
    rw [coeff_map, coeff_map, coeff_monicOfCoeffs]
    split_ifs with h1 h2
    · subst h1; rw [hQ.coeff_natDegree, map_one, map_one]
    · exact ha m h2
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero, map_zero]
  have hprod := norm_prod_sub_untilt_le s hQ' hz
  rw [norm_multiset_prod_eq, Multiset.map_map] at hprod
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hcard; omega
  obtain ⟨b, hb, hbl⟩ := exists_pow_card_le_of_prod_le hs0 (fun _ _ => norm_nonneg _) hprod
  refine ⟨b, ?_, by rwa [hcard] at hbl⟩
  rw [hs, eval_multiset_prod]
  exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map.2 ⟨b, hb, rfl⟩,
    by simp⟩)

end Tilt

section Scale

theorem exists_lt_one_le_pow {q : ℝ} (hq : q < 1) (d : ℕ) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ q ≤ μ ^ d := by
  set q' := max q 0
  have hq' : q' < 1 := max_lt hq one_pos
  have hq0 : 0 ≤ q' := le_max_right _ _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · exact ⟨1 / 2, by norm_num, by norm_num, by rw [hd, pow_zero]; exact hq.le⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set a : ℝ := -((1 - q') / (2 * d))
  have ha1 : (1 - q') / (2 * d) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have ha0 : 0 < (1 - q') / (2 * d) := by
    apply div_pos <;> linarith
  refine ⟨1 + a, by simp only [a]; linarith, by simp only [a]; linarith, ?_⟩
  have hb := one_add_mul_le_pow (a := a) (by simp only [a]; linarith) d
  have : (d : ℝ) * a = -((1 - q') / 2) := by
    simp only [a]; field_simp
  rw [this] at hb
  calc q ≤ q' := le_max_left _ _
    _ ≤ 1 + -((1 - q') / 2) := by linarith
    _ ≤ _ := hb

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]

theorem map_scale_eq_prod {Q : F[X]} (hQ : Q.Monic) (β c : F) (hc : c ≠ 0) :
    (Polynomial.C (c⁻¹ ^ Q.natDegree) * Q.comp (Polynomial.C β + Polynomial.C c * X)).map
        (algebraMap F E) =
      ((Q.map (algebraMap F E)).roots.map fun γ =>
        X - Polynomial.C ((γ - algebraMap F E β) / algebraMap F E c)).prod := by
  set f := Q.map (algebraMap F E)
  have hf : f = (f.roots.map fun γ => X - Polynomial.C γ).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic (hQ.map _)
  have hcard : Multiset.card f.roots = Q.natDegree := by
    rw [← (IsAlgClosed.splits f).natDegree_eq_card_roots, natDegree_map]
  have hc' : algebraMap F E c ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).2 hc
  rw [Polynomial.map_mul, Polynomial.map_C, map_comp, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
  change _ * f.comp _ = _
  conv_lhs => rw [hf]
  rw [multiset_prod_comp, Multiset.map_map, ← hcard]
  have key : ∀ γ : E, (X - Polynomial.C γ).comp (Polynomial.C (algebraMap F E β) +
      Polynomial.C (algebraMap F E c) * X) = Polynomial.C (algebraMap F E c) *
      (X - Polynomial.C ((γ - algebraMap F E β) / algebraMap F E c)) := by
    intro γ
    simp only [sub_comp, X_comp, C_comp, mul_sub, ← Polynomial.C_mul]
    rw [mul_div_cancel₀ _ hc', Polynomial.C_sub]
    ring
  simp only [Function.comp_def, key]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← mul_assoc,
    map_pow, map_inv₀, ← Polynomial.C_pow, ← Polynomial.C_mul, ← mul_pow, inv_mul_cancel₀ hc',
    one_pow, Polynomial.C_1, one_mul]

end Scale

section IntermediateField

variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]

instance normedAlgebraIntermediateField (F : IntermediateField K C) : NormedAlgebra F C where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul]
    rfl

end IntermediateField

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial

theorem perfectField_of_isPerfectoidField (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] : PerfectField K := by
  rcases CharP.exists' K with h | ⟨q, hq, hqK⟩
  · infer_instance
  · have hqp : q = p := by
      by_contra hne
      have : NeZero q := ⟨hq.out.ne_zero⟩
      have hdvd : ¬ q ∣ p := fun h =>
        hne ((Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h)
      have hp0 : (p : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact hdvd
      set u := (p : ZMod q)⁻¹
      have h1 : (p : ZMod q) * u = 1 := mul_inv_cancel₀ hp0
      have h2 := congrArg (ZMod.castHom (dvd_refl q) K) h1
      rw [map_mul, map_one, map_natCast, ZMod.castHom_apply, ZMod.cast_eq_val] at h2
      have h3 : ‖(p : K)‖ * ‖((u.val : ℕ) : K)‖ = 1 := by
        rw [← norm_mul, h2, norm_one]
      have h4 : ‖((u.val : ℕ) : K)‖ ≤ 1 :=
        (isUltrametricDist_iff_forall_norm_natCast_le_one.1 inferInstance) _
      have h5 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
      nlinarith [norm_nonneg ((u.val : ℕ) : K), norm_nonneg (p : K)]
    subst hqp
    have := IsPerfectoidField.perfectRing (K := K) q
    exact PerfectRing.toPerfectField K q

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p

omit [IsUltrametricDist K] [IsUltrametricDist C] [Fact p.Prime] [IsPerfectoidField K p]
  [IsPerfectoidField C p] in
theorem norm_natCast_eq_of_normedAlgebra : ‖(p : C)‖ = ‖(p : K)‖ := by
  rw [← map_natCast (algebraMap K C), norm_algebraMap']

set_option synthInstance.maxHeartbeats 200000 in

theorem exists_untiltField_norm_sub_le [IsAlgClosed C] [IsAlgClosed C♭]
    (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [FiniteDimensional K (untiltField K C p N)]
    (happrox : ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
      ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    {α : C} (hα : IsIntegral K α) {μ ε : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hμ : ‖(p : K)‖ ≤ μ ^ (minpoly K α).natDegree) (hε0 : 0 < ε) (hε1 : ε < 1)
    {β : C} (hβ : β ∈ untiltField K C p N) :
    ∃ N' : IntermediateField K♭ C♭, N ≤ N' ∧ FiniteDimensional K♭ N' ∧
      ∃ β' ∈ untiltField K C p N', ‖α - β'‖ ≤ μ / ε * ‖α - β‖ := by
  classical
  by_cases hαβ : α = β
  · exact ⟨N, le_rfl, inferInstance, β, hβ, by rw [hαβ, sub_self, norm_zero, mul_zero]⟩
  set F := untiltField K C p N with hFdef
  have hδ : 0 < ‖α - β‖ := norm_pos_iff.2 (sub_ne_zero.2 hαβ)
  have : CompleteSpace K := IsPerfectoidField.completeSpace p
  have : CompleteSpace F := FiniteDimensional.complete K F
  obtain ⟨c, hc1, hc2⟩ := exists_norm_mem_Ioc (K := K) p hδ
    (b := ‖α - β‖ / ε) (by rw [lt_div_iff₀ hε0]; nlinarith)
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [norm_zero] at hc1; linarith
  set c' : C := algebraMap K C c
  have hc'0 : c' ≠ 0 := (map_ne_zero_iff _ (algebraMap K C).injective).2 hc0
  have hnc' : ‖c'‖ = ‖c‖ := norm_algebraMap' C c
  have hαF : IsIntegral F α := hα.tower_top
  set Q := minpoly F α
  have hQm : Q.Monic := minpoly.monic hαF
  set e := Q.natDegree with hedef
  have he0 : 0 < e := minpoly.natDegree_pos hαF
  have hed : e ≤ (minpoly K α).natDegree := by
    have hdvd : Q ∣ (minpoly K α).map (algebraMap K F) :=
      minpoly.dvd_map_of_isScalarTower K F α
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.map_ne_zero (minpoly.ne_zero hα))
    rwa [natDegree_map] at this
  set βF : F := ⟨β, hβ⟩
  set cF : F := algebraMap K F c
  have hcF : cF ≠ 0 := (map_ne_zero_iff _ (algebraMap K F).injective).2 hc0
  set Qt : F[X] := Polynomial.C (cF⁻¹ ^ e) * Q.comp (Polynomial.C βF + Polynomial.C cF * X)
  set R := (Q.map (algebraMap F C)).roots
  have hQt : Qt.map (algebraMap F C) = (R.map fun γ => X - Polynomial.C ((γ - β) / c')).prod :=
    map_scale_eq_prod (E := C) hQm βF cF hcF

  have hQne : Q.map (algebraMap F C) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hαF)
  have hαR : α ∈ R := by
    rw [mem_roots hQne, IsRoot, eval_map_algebraMap]
    exact minpoly.aeval F α
  have hdist : ∀ γ ∈ R, ‖γ - β‖ = ‖α - β‖ := by
    intro γ hγ
    have hγ' : aeval γ Q = 0 := by
      have := (mem_roots hQne).1 hγ
      rwa [IsRoot, eval_map_algebraMap] at this
    have hconj : IsConjRoot F α γ :=
      (isConjRoot_iff_mem_minpoly_rootSet hαF).2 (mem_rootSet.2 ⟨minpoly.ne_zero hαF, hγ'⟩)
    have := norm_eq_of_isConjRoot (F := F) (E := C) (hαF.sub isIntegral_algebraMap)
      (hconj.sub_algebraMap βF)
    exact this.symm
  have hrootle : ∀ r ∈ R.map (fun γ => (γ - β) / c'), ‖r‖ ≤ 1 := by
    intro r hr
    obtain ⟨γ, hγ, rfl⟩ := Multiset.mem_map.1 hr
    rw [norm_div, hdist γ hγ, hnc']
    exact div_le_one_of_le₀ hc1.le (norm_nonneg _)
  set Qt' := Qt.map (algebraMap F C) with hQt'def
  have hQt' : Qt' = ((R.map (fun γ => (γ - β) / c')).map fun r => X - Polynomial.C r).prod := by
    rw [hQt, Multiset.map_map]; rfl
  have hcoef : ∀ n, ‖Qt'.coeff n‖ ≤ 1 := fun n => by
    rw [hQt']; exact norm_coeff_prod_X_sub_C_le_one hrootle n
  have hcard : Multiset.card R = e := by
    rw [← (IsAlgClosed.splits (Q.map (algebraMap F C))).natDegree_eq_card_roots, natDegree_map]
  have hQt'deg : Qt'.natDegree = e := by
    rw [hQt', natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, hcard]
  have hQt'mon : Qt'.Monic := by
    rw [hQt']; exact monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r

  have hsub : (↑Qt'.coeffs : Set C) ⊆ normInteger C := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
    exact mem_normInteger.2 (hcoef n)
  set Qi := Qt'.toSubring (normInteger C) hsub
  have hQi : Qi.map (normInteger C).subtype = Qt' := Polynomial.map_toSubring _ _ hsub
  have hQimon : Qi.Monic := by
    refine Polynomial.monic_of_injective (normInteger C).subtype_injective ?_
    rw [hQi]; exact hQt'mon
  have hQideg : Qi.natDegree = e := by
    rw [← hQt'deg, ← hQi, natDegree_map_eq_of_injective (normInteger C).subtype_injective]
  have hz1 : ‖(α - β) / c'‖ ≤ 1 :=
    hrootle _ (Multiset.mem_map.2 ⟨α, hαR, rfl⟩)
  set z : normInteger C := ⟨(α - β) / c', mem_normInteger.2 hz1⟩
  have hz : Qi.eval z = 0 := by
    apply (normInteger C).subtype_injective
    rw [map_zero, ← eval₂_at_apply, ← eval_map, hQi, hQt, eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map.2 ⟨α, hαR, rfl⟩, ?_⟩)
    simp [z]

  have happ : ∀ m, ∃ a : 𝒪C♭, m < e → a ∈ integerTilt K C p N ∧
      Ideal.Quotient.mk (Ideal.span {(p : normInteger C)}) (Qi.coeff m) = PreTilt.coeff 0 a := by
    intro m
    by_cases hm : m < e
    · have hy : ((Qt.coeff m : F) : C) ∈ F := (Qt.coeff m).2
      have hy1 : ‖((Qt.coeff m : F) : C)‖ ≤ 1 := by
        have := hcoef m
        rwa [hQt'def, coeff_map] at this
      obtain ⟨a, ha, hab⟩ := happrox _ hy hy1
      refine ⟨a, fun _ => ⟨ha, ?_⟩⟩
      rw [← PreTilt.mk_untilt_eq_coeff_zero, mk_eq_mk_iff_norm_sub_le,
        norm_natCast_eq_of_normedAlgebra (K := K)]
      have : ((Qi.coeff m : normInteger C) : C) = ((Qt.coeff m : F) : C) := by
        rw [← (normInteger C).subtype_apply, ← coeff_map, hQi, hQt'def, coeff_map]; rfl
      rw [this]; exact hab
    · exact ⟨0, fun h => absurd h hm⟩
  choose a ha using happ
  have hdeg : 0 < Qi.natDegree := hQideg ▸ he0
  obtain ⟨b, hbroot, hbnorm⟩ := exists_root_norm_sub_untilt_pow_le (C := C) (p := p) hQimon hdeg a
    (fun m hm => (ha m (hQideg ▸ hm)).2) hz
  rw [hQideg] at hbnorm hbroot

  have hbμ : ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ≤ μ := by
    have h1 : ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ^ e ≤ μ ^ e := by
      refine hbnorm.trans ?_
      rw [norm_natCast_eq_of_normedAlgebra (K := K)]
      exact hμ.trans (pow_le_pow_of_le_one hμ0 hμ1 hed)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hμ0 he0.ne').1 h1

  set b' : C♭ := algebraMap 𝒪C♭ C♭ b
  set g : C♭[X] := (monicOfCoeffs e a).map (algebraMap 𝒪C♭ C♭)
  have hgmon : g.Monic := (monic_monicOfCoeffs e a).map _
  have hgmem : ∀ n, g.coeff n ∈ N := by
    intro n
    rw [coeff_map, coeff_monicOfCoeffs]
    split_ifs with h1 h2
    · rw [map_one]; exact one_mem N
    · exact (ha n h2).1
    · rw [map_zero]; exact zero_mem N
  have hlift : g ∈ Polynomial.lifts (algebraMap N C♭) :=
    (lifts_iff_coeff_lifts g).2 fun n => ⟨⟨g.coeff n, hgmem n⟩, rfl⟩
  obtain ⟨gN, hgN, -, hgNmon⟩ := lifts_and_natDegree_eq_and_monic hlift hgmon
  have hbN : IsIntegral N b' := by
    refine ⟨gN, hgNmon, ?_⟩
    rw [← eval_map, hgN, eval_map, eval₂_at_apply, hbroot, map_zero]
  have hbK : IsIntegral K♭ b' := isIntegral_trans b' hbN
  have : FiniteDimensional K♭ (IntermediateField.adjoin K♭ {b'}) :=
    IntermediateField.adjoin.finiteDimensional hbK
  set N' := N ⊔ IntermediateField.adjoin K♭ {b'}
  have hb'N' : b' ∈ N' :=
    (le_sup_right : IntermediateField.adjoin K♭ {b'} ≤ N')
      (IntermediateField.mem_adjoin_simple_self K♭ b')
  refine ⟨N', le_sup_left, inferInstance, β + c' * ((PreTilt.untilt b : normInteger C) : C), ?_, ?_⟩
  · refine add_mem (untiltField_mono le_sup_left hβ) (mul_mem ?_ ?_)
    · exact IntermediateField.algebraMap_mem _ c
    · have := tiltSharp_mem_untiltField (K := K) (N := N') hb'N'
      rwa [tiltSharp_algebraMap] at this
  · have hsplit : α - (β + c' * ((PreTilt.untilt b : normInteger C) : C)) =
        c' * ((z : C) - ((PreTilt.untilt b : normInteger C) : C)) := by
      simp only [z]; field_simp; ring
    rw [hsplit, norm_mul, hnc']
    calc ‖c‖ * ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ≤ ‖α - β‖ / ε * μ := by
          gcongr
      _ = μ / ε * ‖α - β‖ := by ring

theorem exists_mem_untiltField_of_approx [IsAlgClosed C] [IsAlgClosed C♭]
    (hfin : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      FiniteDimensional K (untiltField K C p N))
    (happrox : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
        ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    {α : C} (hα : IsIntegral K α) :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ α ∈ untiltField K C p N := by
  classical
  set d := (minpoly K α).natDegree
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := exists_lt_one_le_pow
    (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)) d
  set ε := (1 + μ) / 2
  have hε0 : 0 < ε := by simp only [ε]; linarith
  have hε1 : ε < 1 := by simp only [ε]; linarith
  set lam := μ / ε
  have hlam0 : 0 ≤ lam := div_nonneg hμ0.le hε0.le
  have hlam1 : lam < 1 := by
    rw [div_lt_one hε0]; simp only [ε]; linarith

  have iter : ∀ k : ℕ, ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧
      ∃ β ∈ untiltField K C p N, ‖α - β‖ ≤ lam ^ k * ‖α‖ := by
    intro k
    induction k with
    | zero => exact ⟨⊥, inferInstance, 0, zero_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨N, hN, β, hβ, hβα⟩ := ih
      have := hN
      have := hfin N hN
      obtain ⟨N', -, hN', β', hβ', hle⟩ := exists_untiltField_norm_sub_le N (happrox N hN) hα
        hμ0.le hμ1.le hμ hε0 hε1 hβ
      refine ⟨N', hN', β', hβ', hle.trans ?_⟩
      rw [pow_succ, mul_comm (lam ^ k) lam, mul_assoc]
      exact mul_le_mul_of_nonneg_left hβα hlam0

  set T : Finset C := ((minpoly K α).aroots C).toFinset.erase α
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ α' ∈ T, ρ ≤ ‖α - α'‖ := by
    by_cases hT : T.Nonempty
    · refine ⟨T.inf' hT fun α' => ‖α - α'‖, ?_, fun α' h => Finset.inf'_le _ h⟩
      rw [Finset.lt_inf'_iff]
      intro α' h
      exact norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase h)))
    · exact ⟨1, one_pos, fun α' h => absurd ⟨α', h⟩ hT⟩
  by_cases hα0 : α = 0
  · exact ⟨⊥, inferInstance, by rw [hα0]; exact zero_mem _⟩
  have hαn : 0 < ‖α‖ := norm_pos_iff.2 hα0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hρ0 hαn) hlam1
  obtain ⟨N, hN, β, hβ, hβα⟩ := iter k
  have hclose : ‖α - β‖ < ρ := by
    refine hβα.trans_lt ?_
    rwa [lt_div_iff₀ hαn] at hk
  have := hN
  have := hfin N hN
  set F := untiltField K C p N
  have : CompleteSpace K := IsPerfectoidField.completeSpace p
  have : CompleteSpace F := FiniteDimensional.complete K F
  have : PerfectField K := perfectField_of_isPerfectoidField K p
  have hsepK : IsSeparable K α := Algebra.IsSeparable.isSeparable K (⟨α, hα⟩ :
    algebraicClosure K C) |> fun h => by
      rwa [IsSeparable, IntermediateField.minpoly_eq] at h
  have hsep : IsSeparable F α := hsepK.tower_top F
  refine ⟨N, hN, ?_⟩
  obtain ⟨c, hc⟩ := mem_range_of_norm_sub_lt (F := F) (E := C) ⟨β, hβ⟩ hsep fun α' hα' hne => by
    refine hclose.trans_le (hρ α' ?_)
    rw [Finset.mem_erase, Multiset.mem_toFinset]
    refine ⟨Ne.symm hne, ?_⟩
    have hαF : IsIntegral F α := hα.tower_top
    have h1 : aeval α' (minpoly F α) = 0 := by
      rw [hα']; exact minpoly.aeval F α'
    have h2 : aeval α' ((minpoly K α).map (algebraMap K F)) = 0 := by
      obtain ⟨r, hr⟩ := minpoly.dvd_map_of_isScalarTower K F α
      rw [hr, map_mul, h1, zero_mul]
    rw [aeval_map_algebraMap] at h2
    rw [mem_aroots]
    exact ⟨minpoly.ne_zero hα, h2⟩
  rw [← hc]
  exact (c : F).2

theorem exists_le_untiltField_of_approx [IsAlgClosed C] [IsAlgClosed C♭]
    (hfin : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      FiniteDimensional K (untiltField K C p N))
    (happrox : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
        ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ L ≤ untiltField K C p N := by
  have : PerfectField K := perfectField_of_isPerfectoidField K p
  obtain ⟨γ, hγ⟩ := Field.exists_primitive_element K L
  have hγi : IsIntegral K (γ : C) := (IsIntegral.of_finite K γ).map (IsScalarTower.toAlgHom K L C)
  obtain ⟨N, hN, hmem⟩ := exists_mem_untiltField_of_approx hfin happrox hγi
  refine ⟨N, hN, ?_⟩
  have hL : L = IntermediateField.adjoin K {(γ : C)} := by
    rw [← IntermediateField.lift_adjoin_simple, hγ, IntermediateField.lift_top]
  rw [hL, IntermediateField.adjoin_simple_le_iff]
  exact hmem

theorem exists_mem_untiltField [IsAlgClosed C] {α : C} (hα : IsIntegral K α) :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ α ∈ untiltField K C p N :=
  exists_mem_untiltField_of_approx (fun N hN => by have := hN; infer_instance)
    (fun N hN _ hy hy1 => by have := hN; exact exists_norm_sub_untilt_le N hy hy1) hα

theorem exists_le_untiltField [IsAlgClosed C] (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ L ≤ untiltField K C p N :=
  exists_le_untiltField_of_approx (fun N hN => by have := hN; infer_instance)
    (fun N hN _ hy hy1 => by have := hN; exact exists_norm_sub_untilt_le N hy hy1) L

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

section Norm

theorem norm_tiltAlgEquiv_apply (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (x : N) : ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖ := by
  change ‖σ x‖ = ‖x‖
  rw [NormedAlgebra.norm_eq_spectralNorm K♭, NormedAlgebra.norm_eq_spectralNorm K♭,
    ← spectralNorm_eq_of_equiv σ]

theorem norm_tiltAlgEquiv_toAlgHom_apply (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (x : N) : ‖((σ.toAlgHom x : N) : C♭)‖ = ‖(x : C♭)‖ :=
  norm_tiltAlgEquiv_apply N σ x

end Norm

section IntegerHom

theorem exists_algebraMap_eq_of_mem {N : IntermediateField K♭ C♭} {x : C♭} (hx : x ∈ N)
    (hx1 : ‖x‖ ≤ 1) : ∃ a : 𝒪C♭, a ∈ integerTilt K C p N ∧ algebraMap 𝒪C♭ C♭ a = x := by
  obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hx1
  exact ⟨a, hx, rfl⟩

def integerTiltHom (N : IntermediateField K♭ C♭) (σ : N →ₐ[K♭] N)
    (hσ : ∀ x : N, ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖) :
    integerTilt K C p N →+* integerTilt K C p N :=
  have hex : ∀ a : integerTilt K C p N, ∃ a' : 𝒪C♭, a' ∈ integerTilt K C p N ∧
      algebraMap 𝒪C♭ C♭ a' = ((σ ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ : N) : C♭) := fun a =>
    exists_algebraMap_eq_of_mem (σ _).2 (by
      rw [hσ]; change ‖algebraMap 𝒪C♭ C♭ a‖ ≤ 1
      rw [norm_algebraMap_preTilt]; exact preTilt_norm_le_one _)
  { toFun := fun a => ⟨(hex a).choose, (hex a).choose_spec.1⟩
    map_one' := by
      apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
      rw [(hex 1).choose_spec.2]
      have : (⟨algebraMap 𝒪C♭ C♭ ((1 : integerTilt K C p N) : 𝒪C♭), (1 : integerTilt K C p N).2⟩ :
          N) = 1 := by
        apply Subtype.ext; simp
      rw [this, map_one]; simp
    map_mul' := fun a b => by
      apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
      rw [(hex (a * b)).choose_spec.2]
      change _ = algebraMap 𝒪C♭ C♭ ((hex a).choose * (hex b).choose)
      rw [map_mul, (hex a).choose_spec.2, (hex b).choose_spec.2]
      have : (⟨algebraMap 𝒪C♭ C♭ ((a * b : integerTilt K C p N) : 𝒪C♭), (a * b).2⟩ : N) =
          ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ * ⟨algebraMap 𝒪C♭ C♭ b, b.2⟩ := by
        apply Subtype.ext; simp
      rw [this, map_mul]; rfl
    map_zero' := by
      apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
      rw [(hex 0).choose_spec.2]
      have : (⟨algebraMap 𝒪C♭ C♭ ((0 : integerTilt K C p N) : 𝒪C♭), (0 : integerTilt K C p N).2⟩ :
          N) = 0 := by
        apply Subtype.ext; simp
      rw [this, map_zero]; simp
    map_add' := fun a b => by
      apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
      rw [(hex (a + b)).choose_spec.2]
      change _ = algebraMap 𝒪C♭ C♭ ((hex a).choose + (hex b).choose)
      rw [map_add, (hex a).choose_spec.2, (hex b).choose_spec.2]
      have : (⟨algebraMap 𝒪C♭ C♭ ((a + b : integerTilt K C p N) : 𝒪C♭), (a + b).2⟩ : N) =
          ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ + ⟨algebraMap 𝒪C♭ C♭ b, b.2⟩ := by
        apply Subtype.ext; simp
      rw [this, map_add]; rfl }

theorem algebraMap_integerTiltHom (N : IntermediateField K♭ C♭) (σ : N →ₐ[K♭] N)
    (hσ : ∀ x : N, ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖) (a : integerTilt K C p N) :
    algebraMap 𝒪C♭ C♭ (integerTiltHom N σ hσ a : 𝒪C♭) =
      ((σ ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ : N) : C♭) :=
  (Exists.choose_spec (p := fun a' => a' ∈ integerTilt K C p N ∧
      algebraMap 𝒪C♭ C♭ a' = ((σ ⟨algebraMap 𝒪C♭ C♭ a, a.2⟩ : N) : C♭)) _).2


theorem integerTiltHom_id (N : IntermediateField K♭ C♭)
    (h : ∀ x : N, ‖(((AlgHom.id K♭ N) x : N) : C♭)‖ = ‖(x : C♭)‖) :
    integerTiltHom (p := p) N (AlgHom.id K♭ N) h = RingHom.id _ := by
  ext a
  apply IsFractionRing.injective 𝒪C♭ C♭
  rw [algebraMap_integerTiltHom]
  rfl

theorem integerTiltHom_preTiltMap (N : IntermediateField K♭ C♭) (σ : N →ₐ[K♭] N)
    (hσ : ∀ x : N, ‖((σ x : N) : C♭)‖ = ‖(x : C♭)‖) (β : 𝒪K♭)
    (hβ : preTiltMap p (algebraMap K C) (norm_algebraMap' C) β ∈ integerTilt K C p N) :
    integerTiltHom N σ hσ ⟨_, hβ⟩ = ⟨_, hβ⟩ := by
  apply Subtype.ext
  apply IsFractionRing.injective 𝒪C♭ C♭
  rw [algebraMap_integerTiltHom]
  have h1 : algebraMap 𝒪C♭ C♭ (preTiltMap p (algebraMap K C) (norm_algebraMap' C) β) =
      algebraMap K♭ C♭ (algebraMap 𝒪K♭ K♭ β) := (tiltMap_algebraMap _ _ β).symm
  have h2 : (⟨algebraMap 𝒪C♭ C♭ (preTiltMap p (algebraMap K C) (norm_algebraMap' C) β), hβ⟩ : N) =
      algebraMap K♭ N (algebraMap 𝒪K♭ K♭ β) := Subtype.ext h1
  change ((σ ⟨algebraMap 𝒪C♭ C♭ (preTiltMap p (algebraMap K C) (norm_algebraMap' C) β), hβ⟩ :
    N) : C♭) = _
  rw [h2, AlgHom.commutes]
  exact h1.symm

end IntegerHom

section Identify

abbrev untiltPreTiltMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    PreTilt (normInteger (untiltField K C p N)) p →+* 𝒪C♭ :=
  preTiltMap p ((untiltField K C p N).val : untiltField K C p N →+* C) (norm_val _)

theorem untiltPreTiltMap_mem (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (b : PreTilt (normInteger (untiltField K C p N)) p) : untiltPreTiltMap N b ∈ integerTilt K C p N := by
  rw [mem_integerTilt]
  have h := tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N
  rw [← tiltMap_algebraMap]
  have hm : tiltMap p ((untiltField K C p N).val : untiltField K C p N →+* C) (norm_val _)
      (algebraMap _ _ b) ∈ tiltIntermediateField p (untiltField K C p N) := ⟨_, rfl⟩
  rw [h] at hm
  exact hm

theorem untiltPreTiltMap_surj (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] {a : 𝒪C♭}
    (ha : a ∈ integerTilt K C p N) :
    ∃ b : PreTilt (normInteger (untiltField K C p N)) p, untiltPreTiltMap N b = a := by
  have h := tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N
  have ha' : algebraMap 𝒪C♭ C♭ a ∈ tiltIntermediateField p (untiltField K C p N) := by
    rw [h]; exact ha
  obtain ⟨y, hy⟩ := ha'
  have hy1 : ‖y‖ ≤ 1 := by
    have := norm_tiltMap (p := p) ((untiltField K C p N).val : untiltField K C p N →+* C)
      (norm_val _) y
    rw [← this]
    change ‖tiltInclusion p (untiltField K C p N) y‖ ≤ 1
    rw [hy, norm_algebraMap_preTilt]; exact preTilt_norm_le_one _
  obtain ⟨b, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hy1
  refine ⟨b, IsFractionRing.injective 𝒪C♭ C♭ ?_⟩
  rw [← hy]
  exact (tiltMap_algebraMap _ _ b).symm

def preTiltUntiltEquiv (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    PreTilt (normInteger (untiltField K C p N)) p ≃+* integerTilt K C p N :=
  RingEquiv.ofBijective ((untiltPreTiltMap N).codRestrict _ (untiltPreTiltMap_mem N))
    ⟨fun b b' h => preTiltMap_injective _ _ (congrArg Subtype.val h), fun a => by
      obtain ⟨b, hb⟩ := untiltPreTiltMap_surj N a.2
      exact ⟨b, Subtype.ext hb⟩⟩

@[simp]
theorem coe_preTiltUntiltEquiv (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (b : PreTilt (normInteger (untiltField K C p N)) p) :
    (preTiltUntiltEquiv N b : 𝒪C♭) = untiltPreTiltMap N b :=
  rfl

end Identify

theorem wittVector_map_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (x : WittVector p R) :
    WittVector.map (g.comp f) x = WittVector.map g (WittVector.map f x) :=
  WittVector.ext fun _ => rfl

theorem preTiltMap_congr {L M : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
    [NontriviallyNormedField M] [IsUltrametricDist M] [IsPerfectoidField L p]
    [IsPerfectoidField M p] {f g : L →+* M} (hfg : f = g) (hf : ∀ x, ‖f x‖ = ‖x‖)
    (hg : ∀ x, ‖g x‖ = ‖x‖) : preTiltMap p f hf = preTiltMap p g hg := by
  subst hfg; rfl

section Aut

def untiltPreTiltAut (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) :
    PreTilt (normInteger (untiltField K C p N)) p →+* PreTilt (normInteger (untiltField K C p N)) p :=
  (preTiltUntiltEquiv N).symm.toRingHom.comp
    ((integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)).comp (preTiltUntiltEquiv N).toRingHom)

theorem preTiltUntiltEquiv_untiltPreTiltAut (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (b : PreTilt (normInteger (untiltField K C p N)) p) :
    preTiltUntiltEquiv N (untiltPreTiltAut N σ b) =
      integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) (preTiltUntiltEquiv N b) := by
  simp [untiltPreTiltAut]

theorem untiltPreTiltAut_mul (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ τ : N ≃ₐ[K♭] N) :
    untiltPreTiltAut N (σ * τ) = (untiltPreTiltAut N σ).comp (untiltPreTiltAut N τ) := by
  ext b
  apply (preTiltUntiltEquiv N).injective
  rw [RingHom.comp_apply, preTiltUntiltEquiv_untiltPreTiltAut, preTiltUntiltEquiv_untiltPreTiltAut,
    preTiltUntiltEquiv_untiltPreTiltAut]
  set x := preTiltUntiltEquiv N b
  apply Subtype.ext; apply IsFractionRing.injective 𝒪C♭ C♭
  rw [algebraMap_integerTiltHom, algebraMap_integerTiltHom]
  have : (⟨algebraMap 𝒪C♭ C♭ (integerTiltHom N τ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N τ) x : 𝒪C♭),
      (integerTiltHom N τ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N τ) x).2⟩ : N) =
      τ ⟨algebraMap 𝒪C♭ C♭ x, x.2⟩ := Subtype.ext (algebraMap_integerTiltHom N _ _ x)
  rw [this]; rfl

theorem untiltPreTiltAut_one (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    untiltPreTiltAut (K := K) (C := C) (p := p) N 1 = RingHom.id _ := by
  ext b
  apply (preTiltUntiltEquiv N).injective
  rw [preTiltUntiltEquiv_untiltPreTiltAut]
  have h := integerTiltHom_id (K := K) (C := C) (p := p) N (norm_tiltAlgEquiv_toAlgHom_apply N 1)
  exact congrArg (fun f => f (preTiltUntiltEquiv N b)) h

theorem untiltPreTiltMap_preTiltMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (β : 𝒪K♭) :
    untiltPreTiltMap N (preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) β) =
      preTiltMap p (algebraMap K C) (norm_algebraMap' C) β := by
  rw [untiltPreTiltMap, ← RingHom.comp_apply, ← preTiltMap_comp]
  exact congrArg (fun f => f β) (preTiltMap_congr (L := K) (M := C)
    (f := ((untiltField K C p N).val : untiltField K C p N →+* C).comp
      (algebraMap K (untiltField K C p N))) (g := algebraMap K C) (RingHom.ext fun _ => rfl) _ _)

theorem untiltPreTiltAut_preTiltMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (β : 𝒪K♭) :
    untiltPreTiltAut N σ (preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) β) =
      preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) β := by
  apply (preTiltUntiltEquiv N).injective
  rw [preTiltUntiltEquiv_untiltPreTiltAut]
  have hβ : preTiltMap p (algebraMap K C) (norm_algebraMap' C) β ∈ integerTilt K C p N := by
    rw [← untiltPreTiltMap_preTiltMap N β]; exact untiltPreTiltMap_mem N _
  have he : preTiltUntiltEquiv N
      (preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) β) = ⟨_, hβ⟩ :=
    Subtype.ext (untiltPreTiltMap_preTiltMap N β)
  rw [he]
  exact integerTiltHom_preTiltMap N σ.toAlgHom _ β hβ

end Aut

section Theta

theorem map_untiltPreTiltAut_mem_ker (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) {x : WittVector p (PreTilt (normInteger (untiltField K C p N)) p)}
    (hx : x ∈ RingHom.ker (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p)) :
    WittVector.map (untiltPreTiltAut N σ) x ∈
      RingHom.ker (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p) := by
  obtain ⟨ξK, hξK, hξ1⟩ :=
    IsPerfectoidField.exists_mem_ker_fontaineTheta_isUnit_coeff_one (K := K) (p := p)
  set φKF := preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _)
  set ξF := WittVector.map φKF ξK
  have hξF : ξF ∈ RingHom.ker (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p) := by
    rw [RingHom.mem_ker, fontaineTheta_map_preTiltMap, RingHom.mem_ker.1 hξK, map_zero]
  have hξF1 : IsUnit (ξF.coeff 1) := by
    rw [WittVector.map_coeff]; exact hξ1.map _
  have hker := IsPerfectoidField.ker_fontaineTheta_eq_span (K := untiltField K C p N) hξF hξF1
  have hfix : WittVector.map (untiltPreTiltAut N σ) ξF = ξF := by
    ext n
    simp only [ξF, WittVector.map_coeff, φKF, untiltPreTiltAut_preTiltMap]
  rw [hker] at hx ⊢
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, hfix]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def untiltIntegerHom (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) :
    normInteger (untiltField K C p N) →+* normInteger (untiltField K C p N) :=
  (Ideal.Quotient.lift (RingHom.ker (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p))
      ((WittVector.fontaineTheta (normInteger (untiltField K C p N)) p).comp
        (WittVector.map (untiltPreTiltAut N σ)))
      (fun _ hx => map_untiltPreTiltAut_mem_ker N σ hx)).comp
    (RingHom.quotientKerEquivOfSurjective
      (IsPerfectoidField.surjective_fontaineTheta (K := untiltField K C p N) p)).symm.toRingHom

theorem untiltIntegerHom_fontaineTheta (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (w : WittVector p (PreTilt (normInteger (untiltField K C p N)) p)) :
    untiltIntegerHom N σ (WittVector.fontaineTheta (normInteger (untiltField K C p N)) p w) =
      WittVector.fontaineTheta (normInteger (untiltField K C p N)) p
        (WittVector.map (untiltPreTiltAut N σ) w) := by
  simp only [untiltIntegerHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingHom.quotientKerEquivOfSurjective_symm_apply]
  exact Ideal.Quotient.lift_mk _ _ _

theorem untiltIntegerHom_mul (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ τ : N ≃ₐ[K♭] N) :
    untiltIntegerHom N (σ * τ) = (untiltIntegerHom N σ).comp (untiltIntegerHom N τ) := by
  ext y
  obtain ⟨w, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := untiltField K C p N) p y
  rw [RingHom.comp_apply, untiltIntegerHom_fontaineTheta, untiltIntegerHom_fontaineTheta,
    untiltIntegerHom_fontaineTheta, untiltPreTiltAut_mul, wittVector_map_comp]

theorem untiltIntegerHom_one (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    untiltIntegerHom (K := K) (C := C) (p := p) N 1 = RingHom.id _ := by
  ext y
  obtain ⟨w, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := untiltField K C p N) p y
  rw [untiltIntegerHom_fontaineTheta, untiltPreTiltAut_one, WittVector.map_id]
  rfl

def untiltIntegerEquiv (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) :
    normInteger (untiltField K C p N) ≃+* normInteger (untiltField K C p N) :=
  RingEquiv.ofRingHom (untiltIntegerHom N σ) (untiltIntegerHom N σ⁻¹)
    (by rw [← untiltIntegerHom_mul, mul_inv_cancel, untiltIntegerHom_one])
    (by rw [← untiltIntegerHom_mul, inv_mul_cancel, untiltIntegerHom_one])

@[simp]
theorem untiltIntegerEquiv_apply (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (y : normInteger (untiltField K C p N)) :
    untiltIntegerEquiv N σ y = untiltIntegerHom N σ y :=
  rfl

theorem untiltIntegerHom_integerMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (k : normInteger K) :
    untiltIntegerHom N σ (integerMap (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) k) =
      integerMap (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) k := by
  obtain ⟨w, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) p k
  rw [← fontaineTheta_map_preTiltMap, untiltIntegerHom_fontaineTheta, ← wittVector_map_comp,
    show (untiltPreTiltAut N σ).comp
        (preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _)) =
      preTiltMap p (algebraMap K (untiltField K C p N)) (norm_algebraMap' _) from
      RingHom.ext (untiltPreTiltAut_preTiltMap N σ)]

end Theta

section FieldAut

theorem ringEquivOfRingEquiv_untiltIntegerEquiv_algebraMap (N : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) (k : K) :
    IsFractionRing.ringEquivOfRingEquiv (A := normInteger (untiltField K C p N))
        (K := untiltField K C p N) (B := normInteger (untiltField K C p N))
        (L := untiltField K C p N) (untiltIntegerEquiv N σ) (algebraMap K _ k) =
      algebraMap K _ k := by
  set f := IsFractionRing.ringEquivOfRingEquiv (A := normInteger (untiltField K C p N))
    (K := untiltField K C p N) (B := normInteger (untiltField K C p N))
    (L := untiltField K C p N) (untiltIntegerEquiv N σ)
  have key : ∀ k : K, ‖k‖ ≤ 1 → f (algebraMap K _ k) = algebraMap K _ k := by
    intro k hk
    have : algebraMap K (untiltField K C p N) k =
        algebraMap (normInteger (untiltField K C p N)) (untiltField K C p N)
          (integerMap (algebraMap K (untiltField K C p N)) (norm_algebraMap' _)
            ⟨k, mem_normInteger.2 hk⟩) := rfl
    rw [this, IsFractionRing.ringEquivOfRingEquiv_algebraMap, untiltIntegerEquiv_apply,
      untiltIntegerHom_integerMap]
  rcases le_or_gt ‖k‖ 1 with h | h
  · exact key k h
  · have := key k⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le)
    rw [map_inv₀, map_inv₀] at this
    exact inv_injective this

def untiltAut (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N) :
    untiltField K C p N ≃ₐ[K] untiltField K C p N :=
  AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv
    (A := normInteger (untiltField K C p N)) (K := untiltField K C p N)
    (B := normInteger (untiltField K C p N)) (L := untiltField K C p N) (untiltIntegerEquiv N σ))
    (ringEquivOfRingEquiv_untiltIntegerEquiv_algebraMap N σ)

theorem untiltAut_coe (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N)
    (y : normInteger (untiltField K C p N)) :
    untiltAut N σ (y : untiltField K C p N) = (untiltIntegerHom N σ y : untiltField K C p N) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ y

theorem untiltAut_algebraMap (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (y : normInteger (untiltField K C p N)) :
    untiltAut N σ (algebraMap _ (untiltField K C p N) y) =
      algebraMap _ (untiltField K C p N) (untiltIntegerHom N σ y) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ y

theorem untiltAut_untilt (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ : N ≃ₐ[K♭] N)
    (b : PreTilt (normInteger (untiltField K C p N)) p) :
    untiltAut N σ ((PreTilt.untilt b : normInteger (untiltField K C p N)) : untiltField K C p N) =
      ((PreTilt.untilt (untiltPreTiltAut N σ b) : normInteger (untiltField K C p N)) :
        untiltField K C p N) := by
  rw [untiltAut_coe, ← WittVector.fontaineTheta_teichmuller, untiltIntegerHom_fontaineTheta,
    WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]

theorem untiltAut_mul (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] (σ τ : N ≃ₐ[K♭] N) :
    untiltAut N (σ * τ) = untiltAut N σ * untiltAut N τ := by
  have h : (untiltAut N (σ * τ) : untiltField K C p N →+* untiltField K C p N) =
      ((untiltAut N σ * untiltAut N τ : untiltField K C p N ≃ₐ[K] untiltField K C p N) :
        untiltField K C p N →+* untiltField K C p N) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (normInteger (untiltField K C p N))) ?_
    refine RingHom.ext fun y => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.mul_apply]
    rw [untiltAut_algebraMap, untiltAut_algebraMap, untiltAut_algebraMap, untiltIntegerHom_mul,
      RingHom.comp_apply]
  exact AlgEquiv.ext fun x => congrArg (fun f => f x) h

theorem untiltAut_one (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    untiltAut (K := K) (C := C) (p := p) N 1 = 1 := by
  have h : (untiltAut N 1 : untiltField K C p N →+* untiltField K C p N) =
      RingHom.id (untiltField K C p N) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (normInteger (untiltField K C p N))) ?_
    refine RingHom.ext fun y => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, RingHom.id_apply]
    rw [untiltAut_algebraMap, untiltIntegerHom_one]
    rfl
  exact AlgEquiv.ext fun x => congrArg (fun f => f x) h

def untiltAutHom (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    (N ≃ₐ[K♭] N) →* (untiltField K C p N ≃ₐ[K] untiltField K C p N) where
  toFun := untiltAut N
  map_one' := untiltAut_one N
  map_mul' := untiltAut_mul N

end FieldAut

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem ringHom_frobeniusEquiv_symm {R S : Type*} [CommRing R] [CommRing S] [CharP R p]
    [CharP S p] [PerfectRing R p] [PerfectRing S p] (f : R →+* S) (x : R) :
    f ((frobeniusEquiv R p).symm x) = (frobeniusEquiv S p).symm (f x) := by
  apply (frobeniusEquiv S p).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    frobeniusEquiv_symm_pow_p]

theorem ringHom_iterate_frobeniusEquiv_symm {R S : Type*} [CommRing R] [CommRing S] [CharP R p]
    [CharP S p] [PerfectRing R p] [PerfectRing S p] (f : R →+* S) (x : R) (n : ℕ) :
    f ((frobeniusEquiv R p).symm^[n] x) = (frobeniusEquiv S p).symm^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ringHom_frobeniusEquiv_symm, ih]

section Injective

theorem untiltPreTiltAut_eq_id (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (h : untiltAut N σ = 1)
    (b : PreTilt (normInteger (untiltField K C p N)) p) : untiltPreTiltAut N σ b = b := by
  have hu : ∀ b : PreTilt (normInteger (untiltField K C p N)) p,
      PreTilt.untilt (untiltPreTiltAut N σ b) = PreTilt.untilt b := by
    intro b
    have := untiltAut_untilt N σ b
    rw [h, AlgEquiv.one_apply] at this
    exact Subtype.ext this.symm
  refine IsPerfectoidField.preTilt_ext p fun n => ?_
  rw [← IsPerfectoidField.mk_untilt_iterate, ← IsPerfectoidField.mk_untilt_iterate,
    ← ringHom_iterate_frobeniusEquiv_symm, hu]

theorem untiltAutHom_injective (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    Function.Injective (untiltAutHom (K := K) (C := C) (p := p) N) := by
  refine (injective_iff_map_eq_one _).2 fun σ h => ?_
  have h' : untiltAut N σ = 1 := h

  have hint : ∀ a : integerTilt K C p N,
      integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) a = a := by
    intro a
    obtain ⟨b, rfl⟩ := (preTiltUntiltEquiv N).surjective a
    rw [← preTiltUntiltEquiv_untiltPreTiltAut, untiltPreTiltAut_eq_id N σ h' b]
  have key : ∀ x : N, ‖(x : C♭)‖ ≤ 1 → σ x = x := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := exists_algebraMap_eq_of_mem (p := p) x.2 hx
    apply Subtype.ext
    have := algebraMap_integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) ⟨a, ha⟩
    rw [hint] at this
    have hx' : (⟨algebraMap 𝒪C♭ C♭ a, ha⟩ : N) = x := Subtype.ext hax
    rw [hx'] at this
    exact this.symm.trans hax
  ext x
  rcases le_or_gt ‖(x : C♭)‖ 1 with hx | hx
  · exact congrArg Subtype.val (key x hx)
  · have hx0 : x ≠ 0 := by
      rintro rfl; norm_num at hx
    have := key x⁻¹ (by
      rw [IntermediateField.coe_inv, norm_inv]; exact inv_le_one_of_one_le₀ hx.le)
    rw [map_inv₀] at this
    exact congrArg Subtype.val (inv_injective this)

end Injective

section Galois

theorem untiltAutHom_bijective (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] :
    Function.Bijective (untiltAutHom (K := K) (C := C) (p := p) N) ∧
      IsGalois K (untiltField K C p N) := by
  have hinj := untiltAutHom_injective (K := K) (C := C) (p := p) N
  have h1 : Nat.card (N ≃ₐ[K♭] N) = Module.finrank K (untiltField K C p N) := by
    rw [IsGalois.card_aut_eq_finrank, finrank_untiltField]
  have h2 : Nat.card (untiltField K C p N ≃ₐ[K] untiltField K C p N) ≤
      Module.finrank K (untiltField K C p N) := by
    refine le_trans ?_ (card_algHom_le_finrank K (untiltField K C p N) (untiltField K C p N))
    exact Nat.card_le_card_of_injective _ AlgEquiv.coe_toAlgHom_injective
  have h3 : Nat.card (N ≃ₐ[K♭] N) ≤
      Nat.card (untiltField K C p N ≃ₐ[K] untiltField K C p N) :=
    Nat.card_le_card_of_injective _ hinj
  have heq : Nat.card (untiltField K C p N ≃ₐ[K] untiltField K C p N) =
      Module.finrank K (untiltField K C p N) := le_antisymm h2 (h1 ▸ h3)
  exact ⟨hinj.bijective_of_nat_card_le (by rw [heq, h1]), IsGalois.of_card_aut_eq_finrank _ _ heq⟩

theorem isGalois_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] : IsGalois K (untiltField K C p N) :=
  (untiltAutHom_bijective N).2

end Galois

section Theta

theorem untiltPreTiltMap_symm (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (a : integerTilt K C p N) :
    untiltPreTiltMap N ((preTiltUntiltEquiv N).symm a) = a := by
  rw [← coe_preTiltUntiltEquiv, RingEquiv.apply_symm_apply]

theorem fontaineTheta_map_subtype (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (u : WittVector p (integerTilt K C p N)) :
    ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u) :
        normInteger C) : C) =
      ((WittVector.fontaineTheta (normInteger (untiltField K C p N)) p
          (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) :
        normInteger (untiltField K C p N)) : untiltField K C p N) := by
  have hu : WittVector.map (integerTilt K C p N).subtype u =
      WittVector.map (untiltPreTiltMap N) (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) := by
    rw [← wittVector_map_comp]
    exact WittVector.ext fun n => (untiltPreTiltMap_symm N (u.coeff n)).symm
  rw [hu, untiltPreTiltMap, fontaineTheta_map_preTiltMap, coe_integerMap]
  rfl

theorem coe_untiltAut_fontaineTheta (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    (σ : N ≃ₐ[K♭] N) (u : WittVector p (integerTilt K C p N))
    (hu : ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u) :
        normInteger C) : C) ∈ untiltField K C p N) :
    ((untiltAut N σ ⟨_, hu⟩ : untiltField K C p N) : C) =
      ((WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype
        (WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u)) :
        normInteger C) : C) := by
  have he : (⟨_, hu⟩ : untiltField K C p N) =
      ((WittVector.fontaineTheta (normInteger (untiltField K C p N)) p
          (WittVector.map (preTiltUntiltEquiv N).symm.toRingHom u) :
        normInteger (untiltField K C p N)) : untiltField K C p N) :=
    Subtype.ext (fontaineTheta_map_subtype N u)
  rw [he, untiltAut_coe, untiltIntegerHom_fontaineTheta, fontaineTheta_map_subtype,
    ← wittVector_map_comp, ← wittVector_map_comp]
  congr 3
  ext a
  simp [untiltPreTiltAut]

end Theta

section Correspondence

theorem exists_untiltField_eq_of_le (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] (L : IntermediateField K C) (hL : L ≤ untiltField K C p N) :
    ∃ M : IntermediateField K♭ C♭, M ≤ N ∧ FiniteDimensional K♭ M ∧ untiltField K C p M = L := by
  classical
  obtain ⟨hbij, hgal⟩ := untiltAutHom_bijective (K := K) (C := C) (p := p) N
  set F := untiltField K C p N
  set Φ := untiltAutHom (K := K) (C := C) (p := p) N
  set L' : IntermediateField K F := IntermediateField.restrict hL
  set H := L'.fixingSubgroup
  set J := H.comap Φ
  set M0 : IntermediateField K♭ N := IntermediateField.fixedField J
  set M : IntermediateField K♭ C♭ := M0.map N.val
  have hMN : M ≤ N := by
    rintro _ ⟨y, -, rfl⟩; exact y.2
  have hMfin : FiniteDimensional K♭ M :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap M0 N.val).toLinearEquiv
  refine ⟨M, hMN, hMfin, ?_⟩

  have hle : untiltField K C p M ≤ L := by
    rw [untiltField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, ⟨u, rfl⟩, rfl⟩
    set u' := WittVector.map (Subring.inclusion (integerTilt_mono hMN)) u
    have hz : ((RingHom.comp (WittVector.fontaineTheta (normInteger C) p)
        (WittVector.map (integerTilt K C p M).subtype)) u : normInteger C) =
        WittVector.fontaineTheta (normInteger C) p (WittVector.map (integerTilt K C p N).subtype u') := by
      simp only [RingHom.comp_apply, u']
      congr 1
    have hzF : ((WittVector.fontaineTheta (normInteger C) p
        (WittVector.map (integerTilt K C p N).subtype u') : normInteger C) : C) ∈ F :=
      coe_mem_untiltField ⟨u', rfl⟩
    change ((RingHom.comp (WittVector.fontaineTheta (normInteger C) p)
        (WittVector.map (integerTilt K C p M).subtype)) u : C) ∈ L
    rw [hz]
    have hfix : (⟨_, hzF⟩ : F) ∈ IntermediateField.fixedField H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro τ hτ
      obtain ⟨σ, rfl⟩ := hbij.2 τ
      have hσ : σ ∈ J := hτ
      apply Subtype.ext

      have hcoeff : ∀ n, integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)
          (u'.coeff n) = u'.coeff n := by
        intro n
        set c := u'.coeff n
        have hcM : algebraMap 𝒪C♭ C♭ (c : 𝒪C♭) ∈ M := (u.coeff n).2
        obtain ⟨y, hy, hyc⟩ := hcM
        have hyfix : σ y = y := (IntermediateField.mem_fixedField_iff J y).1 hy σ hσ
        apply Subtype.ext
        apply IsFractionRing.injective 𝒪C♭ C♭
        rw [algebraMap_integerTiltHom]
        have : (⟨algebraMap 𝒪C♭ C♭ (c : 𝒪C♭), c.2⟩ : N) = y := Subtype.ext hyc.symm
        rw [this]
        change ((σ y : N) : C♭) = _
        rw [hyfix]
        exact hyc
      have hmap : WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ))
          u' = u' := WittVector.ext fun n => by rw [WittVector.map_coeff, hcoeff n]
      change ((untiltAut N σ ⟨_, hzF⟩ : F) : C) = _
      rw [coe_untiltAut_fontaineTheta, hmap]
    rw [IsGalois.fixedField_fixingSubgroup] at hfix
    exact (IntermediateField.mem_restrict hL _).1 hfix

  have hL'fin : FiniteDimensional K L' := inferInstance
  have hcard : Nat.card J = Nat.card H := by
    refine Nat.card_congr (Equiv.ofBijective (fun σ : J => (⟨Φ σ, σ.2⟩ : H)) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (hbij.1 (congrArg Subtype.val hab))
    · rintro ⟨τ, hτ⟩
      obtain ⟨σ, rfl⟩ := hbij.2 τ
      exact ⟨⟨σ, hτ⟩, rfl⟩
  have hN : Module.finrank K♭ M0 * Nat.card J = Module.finrank K♭ N := by
    rw [← IntermediateField.finrank_fixedField_eq_card, Module.finrank_mul_finrank]
  have hF : Module.finrank K L' * Nat.card H = Module.finrank K F := by
    have h := IntermediateField.finrank_fixedField_eq_card H
    rw [IsGalois.fixedField_fixingSubgroup] at h
    rw [← h, Module.finrank_mul_finrank]
  have hFN : Module.finrank K F = Module.finrank K♭ N := finrank_untiltField N
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hL'M0 : Module.finrank K L' = Module.finrank K♭ M0 := by
    have := hF.trans (hFN.trans hN.symm)
    rw [hcard] at this
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hLL' : Module.finrank K L = Module.finrank K L' :=
    (AlgEquiv.ofInjectiveField (IntermediateField.inclusion hL)).toLinearEquiv.finrank_eq
  have hMM0 : Module.finrank K♭ M = Module.finrank K♭ M0 :=
    (IntermediateField.equivMap M0 N.val).toLinearEquiv.finrank_eq.symm
  have : FiniteDimensional K L :=
    LinearEquiv.finiteDimensional
      (AlgEquiv.ofInjectiveField (IntermediateField.inclusion hL)).toLinearEquiv.symm
  exact IntermediateField.eq_of_le_of_finrank_le hle
    (by rw [finrank_untiltField, hMM0, ← hL'M0, hLL'])

end Correspondence

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

def SpectralAlgClosure : Type _ := AlgebraicClosure K

namespace SpectralAlgClosure

instance : Field (SpectralAlgClosure K) := inferInstanceAs (Field (AlgebraicClosure K))

instance : Algebra K (SpectralAlgClosure K) := inferInstanceAs (Algebra K (AlgebraicClosure K))

instance : IsAlgClosed (SpectralAlgClosure K) := inferInstanceAs (IsAlgClosed (AlgebraicClosure K))

instance : Algebra.IsAlgebraic K (SpectralAlgClosure K) :=
  inferInstanceAs (Algebra.IsAlgebraic K (AlgebraicClosure K))

instance : NormedField (SpectralAlgClosure K) := spectralNorm.normedField K (SpectralAlgClosure K)

instance : NormedAlgebra K (SpectralAlgClosure K) :=
  spectralNorm.normedAlgebra K (SpectralAlgClosure K)

instance : IsUltrametricDist (SpectralAlgClosure K) := IsUltrametricDist.of_normedAlgebra K

theorem norm_eq_spectralNorm (x : SpectralAlgClosure K) :
    ‖x‖ = spectralNorm K (SpectralAlgClosure K) x :=
  rfl

end SpectralAlgClosure

abbrev CompletedAlgClosure : Type _ := UniformSpace.Completion (SpectralAlgClosure K)

namespace CompletedAlgClosure

instance : IsUltrametricDist (CompletedAlgClosure K) := IsUltrametricDist.of_normedAlgebra K

instance : NontriviallyNormedField (CompletedAlgClosure K) where
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    exact ⟨algebraMap K _ x, by rw [norm_algebraMap']; exact hx⟩

instance [CharZero K] : IsAlgClosed (CompletedAlgClosure K) := by
  have : CharZero (CompletedAlgClosure K) :=
    (RingHom.charZero_iff (algebraMap K (CompletedAlgClosure K)).injective).mp inferInstance
  exact IsAlgClosed.of_denseRange (K := SpectralAlgClosure K) UniformSpace.Completion.denseRange_coe

variable (L : Type*) [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]

def embedding : L →ₐ[K] CompletedAlgClosure K :=
  (IsScalarTower.toAlgHom K (SpectralAlgClosure K) (CompletedAlgClosure K)).comp
    (IsAlgClosed.lift : L →ₐ[K] SpectralAlgClosure K)

theorem norm_embedding (x : L) : ‖embedding K L x‖ = ‖x‖ := by
  set ι : L →ₐ[K] SpectralAlgClosure K := IsAlgClosed.lift
  have h1 : ‖embedding K L x‖ = ‖ι x‖ := by
    change ‖((ι x : SpectralAlgClosure K) : CompletedAlgClosure K)‖ = _
    exact UniformSpace.Completion.norm_coe _
  rw [h1, SpectralAlgClosure.norm_eq_spectralNorm]
  have h2 : spectralNorm K (SpectralAlgClosure K) (ι x) = spectralNorm K L x := by
    simp only [spectralNorm, minpoly.algHom_eq ι ι.injective x]
  rw [h2]
  exact (spectralNorm_unique_field_norm_ext (f := NormedField.toAbsoluteValue L)
    (fun k => norm_algebraMap' L k) x).symm

end CompletedAlgClosure

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem charZero_or_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] :
    CharZero K ∨ CharP K p := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
  · right
    have hq' : Fact (ringChar K).Prime := ⟨hq⟩
    by_contra hne
    have hpq : p ≠ ringChar K := fun h => hne (h ▸ ringChar.charP K)

    have hpz : ((p : ZMod (ringChar K))) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).1 hdvd).symm
    have hferm := ZMod.pow_card_sub_one_eq_one hpz
    have hK : (p : K) ^ (ringChar K - 1) = 1 := by
      have := congrArg (ZMod.castHom (dvd_refl (ringChar K)) K) hferm
      simpa using this
    have hn := congrArg norm hK
    rw [norm_pow, norm_one] at hn
    have hlt := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
    have hpos : ringChar K - 1 ≠ 0 := by have := hq.two_le; omega
    have : ‖(p : K)‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).1 hn
    linarith
  · left
    have : CharP K 0 := by rw [← hq]; exact ringChar.charP K
    exact CharP.charP_to_charZero K

theorem of_finiteDimensional_of_charP (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] [CharP K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by
  have := IsPerfectoidField.completeSpace (K := K) p
  have : CompleteSpace L := FiniteDimensional.complete K L
  have : PerfectRing K p := IsPerfectoidField.perfectRing p
  have : PerfectField K := PerfectRing.toPerfectField K p
  have : PerfectField L := Algebra.IsAlgebraic.perfectField (K := K)
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : PerfectRing L p := PerfectField.toPerfectRing p
  refine IsPerfectoidField.of_perfectRing p fun r hr => ?_
  obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r hr
  exact ⟨algebraMap K L x, by rwa [norm_algebraMap'], by rwa [norm_algebraMap']⟩

end IsPerfectoidField

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

theorem exists_isGalois_le {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    [PerfectField F] (N : IntermediateField F L) [FiniteDimensional F N] :
    ∃ N' : IntermediateField F L, N ≤ N' ∧ FiniteDimensional F N' ∧ IsGalois F N' := by
  classical
  set B := Module.finBasis F N
  set f : Polynomial F := ∏ i, minpoly F (B i : L)
  have hint : ∀ i, IsIntegral F (B i : L) := fun i =>
    (IsIntegral.of_finite F (B i)).map (IntermediateField.val N)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => minpoly.ne_zero (hint i)
  set N' := IntermediateField.adjoin F (f.rootSet L)
  have hsplit : (f.map (algebraMap F L)).Splits := IsAlgClosed.splits _
  have : Polynomial.IsSplittingField F N' f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hfin : FiniteDimensional F N' := Polynomial.IsSplittingField.finiteDimensional N' f
  have : Normal F N' := Normal.of_isSplittingField f
  have : IsGalois F N' := IsGalois.mk
  refine ⟨N', ?_, hfin, this⟩
  have hB : ∀ i, (B i : L) ∈ N' := fun i => by
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hf0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval F (B i : L))
  intro x hx
  have := congrArg (fun u : N => (u : L)) (B.sum_repr ⟨x, hx⟩)
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
  rw [← this]
  exact N'.sum_mem fun i _ => N'.smul_mem (hB i)

section InC

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p

variable (K C p) in
include K in

theorem isPerfectoidField_of_isAlgClosed_of_normedAlgebra [CompleteSpace C] :
    IsPerfectoidField C p :=
  IsPerfectoidField.of_isAlgClosed p (by
    rw [← map_natCast (algebraMap K C), norm_algebraMap']
    exact IsPerfectoidField.norm_natCast_lt_one)

variable [IsPerfectoidField C p]

theorem exists_eq_untiltField (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ M : IntermediateField K♭ C♭, FiniteDimensional K♭ M ∧ untiltField K C p M = L := by
  obtain ⟨N, hN, hLN⟩ := exists_le_untiltField (p := p) L
  have : PerfectField K♭ := PerfectRing.toPerfectField K♭ p
  obtain ⟨N', hNN', hN', hgal⟩ := exists_isGalois_le N
  obtain ⟨M, -, hM, hML⟩ :=
    exists_untiltField_eq_of_le N' L (hLN.trans (untiltField_mono hNN'))
  exact ⟨M, hM, hML⟩

instance isPerfectoidField_of_finiteDimensional (L : IntermediateField K C) [FiniteDimensional K L] :
    IsPerfectoidField L p := by
  obtain ⟨M, hM, hML⟩ := exists_eq_untiltField (p := p) L
  exact IsPerfectoidField.of_ringEquiv p (IntermediateField.equivOfEq hML).toRingEquiv
    fun _ => rfl

theorem untiltField_tiltIntermediateField (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ _ : FiniteDimensional K♭ (tiltIntermediateField p L),
      untiltField K C p (tiltIntermediateField p L) = L := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M) = M :=
    tiltIntermediateField_untiltField M
  rw [h]
  exact ⟨hM, rfl⟩

theorem finrank_tiltIntermediateField (L : IntermediateField K C) [FiniteDimensional K L] :
    Module.finrank K♭ (tiltIntermediateField p L) = Module.finrank K L := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M) = M :=
    tiltIntermediateField_untiltField M
  rw [h, finrank_untiltField]


end InC

section Abstract

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem IsPerfectoidField.of_finiteDimensional (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by
  rcases IsPerfectoidField.charZero_or_charP (K := K) p with h0 | hp
  · have := IsPerfectoidField.completeSpace (K := K) p
    have : IsPerfectoidField (CompletedAlgClosure K) p :=
      isPerfectoidField_of_isAlgClosed_of_normedAlgebra K (CompletedAlgClosure K) p
    set j := CompletedAlgClosure.embedding K L
    let e : L ≃ₐ[K] j.fieldRange := AlgEquiv.ofInjectiveField j
    have : FiniteDimensional K j.fieldRange := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine IsPerfectoidField.of_ringEquiv p e.symm.toRingEquiv fun y => ?_
    have h1 : ((e (e.symm y) : j.fieldRange) : CompletedAlgClosure K) = j (e.symm y) := rfl
    rw [AlgEquiv.apply_symm_apply] at h1
    change ‖e.symm y‖ = ‖(y : CompletedAlgClosure K)‖
    rw [h1, CompletedAlgClosure.norm_embedding]
  · exact IsPerfectoidField.of_finiteDimensional_of_charP (K := K) p L

end Abstract

end GroundTheory.PAdicHodge
end
end
