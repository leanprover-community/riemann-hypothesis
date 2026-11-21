import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKill
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendsTaylorPowerSeriesRing
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPolynomialSubMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldApplyConstantEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermOriginConstantSectionEqOriginStalkConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCommGroupLocalCoordinatesAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapFromSpecStalkOriginCompStructureEq

section
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_of_derivations_kill : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (c : A), (∀ i, ds i c = 0) → taylor ev (fun i => ⇑(ds i)) c = MvPowerSeries.C (ev c) := by
  first | exact @GlobalTheory.FormalOrigin.taylor_const | exact GlobalTheory.FormalOrigin.taylor_const | (intros; apply GlobalTheory.FormalOrigin.taylor_const <;> assumption)
end

section
section
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin.TaylorDeriv

theorem foldr_iterate_comm {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι → ℕ) (a : ι) (f : A) (l : List ι) :
    l.foldr (fun i g => (ds i)^[α i] g) (ds a f) = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, ih]
    have : Function.Commute (ds i) (ds a) := fun x => h i a x
    exact (this.iterate_left (α i)) _

theorem foldr_iterate_add_single {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι →₀ ℕ) (a : ι) (f : A) (l : List ι) (hl : l.Nodup) (ha : a ∈ l) :
    l.foldr (fun i g => (ds i)^[(α + Finsupp.single a 1 : ι →₀ ℕ) i] g) f
      = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  classical
  induction l with
  | nil => simp at ha
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    by_cases hi : i = a
    · subst hi
      have : l.foldr (fun j g => (ds j)^[(α + Finsupp.single i 1 : ι →₀ ℕ) j] g) f
          = l.foldr (fun j g => (ds j)^[α j] g) f := by
        apply List.foldr_ext
        intro j hj b
        have : j ≠ i := fun e => hl.1 (e ▸ hj)
        simp [Finsupp.single_apply, this.symm]
      rw [this]
      simp [Function.iterate_succ_apply']
    · have ha' : a ∈ l := by
        rcases List.mem_cons.1 ha with e | e
        · exact absurd e.symm hi
        · exact e
      rw [ih hl.2 ha']
      have e : (α + Finsupp.single a 1 : ι →₀ ℕ) i = α i := by
        simp [Finsupp.single_apply, Ne.symm hi]
      rw [e]
      have : Function.Commute (ds i) (ds a) := fun x => h i a x
      exact (this.iterate_left (α i)) _

theorem iterOp_apply_eq_add_single {A : Type} {n : ℕ} (ds : Fin n → A → A)
    (h : ∀ a b f, ds a (ds b f) = ds b (ds a f)) (α : Fin n →₀ ℕ) (a : Fin n) (f : A) :
    iterOp ds α (ds a f) = iterOp ds (α + Finsupp.single a 1) f := by
  unfold iterOp
  rw [foldr_iterate_comm ds h, foldr_iterate_add_single ds h α a f _ (List.nodup_finRange n) (List.mem_finRange a)]

theorem prod_factorial_add_single {n : ℕ} (α : Fin n →₀ ℕ) (a : Fin n) :
    ∏ i, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = (∏ i, ((α i).factorial : ℚ)) * ((α a : ℚ) + 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ (fun i => ((α i).factorial : ℚ)) (Finset.mem_univ a)]
  have : ∏ i ∈ Finset.univ.erase a, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = ∏ i ∈ Finset.univ.erase a, ((α i).factorial : ℚ) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, this.symm]
  rw [this]
  simp [Nat.factorial_succ]
  ring

theorem taylor_deriv_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv B a (taylor ev (fun i => ⇑(ds i)) f) := by
  intro A B _ _ _ n ev ds h a f
  ext α
  rw [MvPowerSeries.coeff_pderiv]
  simp only [MvPowerSeries.coeff_apply, taylor]
  rw [prod_factorial_add_single, ← iterOp_apply_eq_add_single (fun i => ⇑(ds i)) h]
  have e : ((α a : B) + 1) = algebraMap ℚ B ((α a : ℚ) + 1) := by simp
  have hp : ((α a : ℚ) + 1) ≠ 0 := by positivity
  rw [e, mul_comm _ (algebraMap ℚ B _), ← Algebra.smul_def, smul_smul]
  congr 1
  field_simp

end GlobalTheory.FormalOrigin.TaylorDeriv
end

open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv B a (taylor ev (fun i => ⇑(ds i)) f) := by
  atlas_forward_decl GlobalTheory.FormalOrigin.TaylorDeriv.taylor_deriv_eq_pderiv
end

section
section
open IsLocalRing GlobalTheory.FormalOrigin MvPowerSeries

noncomputable section
namespace GlobalTheory.TaylorInj

theorem foldr_ite {A : Type} {n : ℕ} (D : A → A) (a : Fin n) (f : A) (l : List (Fin n)) :
    l.foldr (fun i g => if i = a then D g else g) f = D^[l.count a] f := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons, ih, List.count_cons]
    by_cases h : i = a
    · subst h; simp [Function.iterate_succ_apply']
    · simp [h]

theorem iterOp_single {A : Type} {n : ℕ} (ds : Fin n → A → A) (a : Fin n) (f : A) :
    iterOp ds (Finsupp.single a 1) f = ds a f := by
  have e : (fun i g => (ds i)^[Finsupp.single a 1 i] g) = (fun i g => if i = a then ds a g else g) := by
    funext i g
    by_cases h : i = a
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h, h]
  unfold iterOp
  rw [e, foldr_ite, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange a)]
  rfl

theorem coeff_taylor {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ B] {n : ℕ} (ev : A →+* B)
    (ds : Fin n → A → A) (f : A) (α : Fin n →₀ ℕ) :
    coeff α (taylor ev ds f) = (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp ds α f) := rfl

theorem degree_eq_one {n : ℕ} {D : Fin n →₀ ℕ} (h : D.degree = 1) : ∃ s, D = Finsupp.single s 1 := by
  have hsum := h
  rw [Finsupp.degree_eq_sum] at hsum
  obtain ⟨s, hs⟩ : ∃ s, D s ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at hsum
  refine ⟨s, ?_⟩
  have hle : ∀ t, t ≠ s → D s + D t ≤ 1 := fun t ht => by
    rw [← hsum, ← Finset.sum_pair (Ne.symm ht)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  ext t
  by_cases ht : t = s
  · subst ht
    have : D t ≤ 1 := h ▸ Finsupp.le_degree t D
    simp only [Finsupp.single_eq_same]
    omega
  · have := hle t ht
    simp only [Finsupp.single_apply, if_neg (Ne.symm ht)]
    omega

section Rel
variable {σ S : Type} [CommRing S]

def Rel (e : ℕ) (F G : MvPowerSeries σ S) : Prop :=
  (e : ℕ∞) ≤ G.order ∧ ((e + 1 : ℕ) : ℕ∞) ≤ (F - G).order

theorem le_order_of_rel {e : ℕ} {F G : MvPowerSeries σ S} (h : Rel e F G) : (e : ℕ∞) ≤ F.order := by
  have : F = G + (F - G) := by ring
  rw [this]
  exact le_trans (le_min h.1 (le_trans (by exact_mod_cast Nat.le_succ e) h.2)) min_order_le_add

theorem rel_mul {a b : ℕ} {F G F' G' : MvPowerSeries σ S} (h : Rel a F G) (h' : Rel b F' G') :
    Rel (a + b) (F * F') (G * G') := by
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ le_order_mul
    push_cast; exact add_le_add h.1 h'.1
  · have e : F * F' - G * G' = (F - G) * F' + G * (F' - G') := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h.2 (le_order_of_rel h'))
      push_cast; ring
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h.1 h'.2)
      push_cast; ring

theorem rel_one : Rel 0 (1 : MvPowerSeries σ S) 1 := by
  refine ⟨by simp, by simp⟩

theorem rel_pow {a : ℕ} {F G : MvPowerSeries σ S} (h : Rel a F G) (k : ℕ) :
    Rel (a * k) (F ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using (rel_one (σ := σ) (S := S))
  | succ k ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ]
    exact rel_mul ih h

theorem rel_prod_pow {ι : Type} (s : Finset ι) (F G : ι → MvPowerSeries σ S) (β : ι → ℕ)
    (h : ∀ i, Rel 1 (F i) (G i)) :
    Rel (∑ i ∈ s, β i) (∏ i ∈ s, F i ^ β i) (∏ i ∈ s, G i ^ β i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rel_one (σ := σ) (S := S))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    have := rel_mul (rel_pow (h i) (β i)) ih
    rwa [one_mul] at this

end Rel

theorem ker_le_span {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R) (hev : ∀ r, ev (inc r) = r) {n : ℕ}
    (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hm : maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z)) :
    RingHom.ker ev ≤ Ideal.span (Set.range z) := by
  set K := RingHom.ker ev
  set J := Ideal.span (Set.range z)
  set I := (maximalIdeal R).map inc
  have hJK : J ≤ K := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
  have key : ∀ y ∈ I, y - inc (ev y) ∈ I * K := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => y - inc (ev y) ∈ I * K) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨r, -, rfl⟩; simp [hev]
    · simp
    · intro x y _ _ hx hy
      have := Ideal.add_mem _ hx hy
      convert this using 1; simp only [map_add]; ring
    · intro a x hx' hx
      have e : a • x - inc (ev (a • x)) = (a - inc (ev a)) * x + inc (ev a) * (x - inc (ev x)) := by
        simp only [smul_eq_mul, map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hx)
      rw [mul_comm (a - inc (ev a))]; exact Ideal.mul_mem_mul hx' (RingHom.mem_ker.2 (by simp [hev]))
  have hle : K ≤ J ⊔ I • K := by
    intro x hx
    have hxm : x ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
      have := hu.map ev; rw [RingHom.mem_ker.1 hx] at this; exact not_isUnit_zero this
    rw [hm, Submodule.mem_sup] at hxm
    obtain ⟨y, hy, w, hw, rfl⟩ := hxm
    have hw0 : ev w = 0 := hJK hw
    have hy0 : ev y = 0 := by
      have := RingHom.mem_ker.1 hx; rwa [map_add, hw0, add_zero] at this
    have := key y hy
    rw [hy0, map_zero, sub_zero] at this
    rw [add_comm]; exact Submodule.add_mem_sup hw this
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hm]; exact le_sup_left
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian K) hIj hle

end GlobalTheory.TaylorInj

namespace GlobalTheory.TaylorInj
section Main
variable {R A : Type} [CommRing R] [Algebra ℚ R] [CommRing A] {n : ℕ}

theorem rel_const (ev : A →+* R) (ds : Fin n → A → A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev ds f) (c : A) : Rel 0 (T c) (C (ev c)) := by
  refine ⟨by simp, ?_⟩
  have h0 : constantCoeff (T c) = ev c := by
    rw [← coeff_zero_eq_constantCoeff_apply, hT, coeff_taylor]; simp [iterOp_zero]
  rw [zero_add, Nat.cast_one, one_le_order_iff_constCoeff_eq_zero, map_sub, h0]
  simp

theorem rel_coord (ev : A →+* R) (ds : Fin n → Derivation ℤ A A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f) (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hd : ∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) (i : Fin n) :
    Rel 1 (T (z i)) (X i) := by
  refine ⟨?_, ?_⟩
  · exact one_le_order_iff_constCoeff_eq_zero.2 (by simp)
  · refine nat_le_order fun d hd2 => ?_
    rw [map_sub, hT, coeff_taylor]
    by_cases h0 : d.degree = 0
    · rw [(Finsupp.degree_eq_zero_iff d).1 h0]; simp [iterOp_zero, hz]
    · obtain ⟨a, rfl⟩ := degree_eq_one (by omega : d.degree = 1)
      rw [iterOp_single, hd, coeff_X]
      have hf : ∀ j, (((Finsupp.single a 1 : Fin n →₀ ℕ) j).factorial : ℚ) = 1 := by
        intro j; rw [Finsupp.single_apply]; split_ifs <;> simp
      simp only [hf, Finset.prod_const_one, inv_one, one_smul]
      by_cases hai : a = i
      · subst hai; simp
      · simp [hai, Finsupp.single_left_inj (one_ne_zero)]

theorem step (ev : A →+* R) (ds : Fin n → Derivation ℤ A A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f) (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hd : ∀ a i, ev (ds a (z i)) = if a = i then 1 else 0)
    (hker : RingHom.ker ev ≤ Ideal.span (Set.range z)) (k : ℕ) (f : A) (hf : T f = 0)
    (hk : f ∈ Ideal.span (Set.range z) ^ k) : f ∈ Ideal.span (Set.range z) ^ (k + 1) := by
  classical
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous z f).1 hk
  have hdeg : ∀ β ∈ p.support, β.degree = k := by
    intro β hβ
    have := hp (MvPolynomial.mem_support_iff.1 hβ)
    rw [Finsupp.degree_eq_weight_one]; exact this
  have hev : MvPolynomial.eval z p = ∑ β ∈ p.support, p.coeff β * ∏ i, z i ^ β i :=
    MvPolynomial.eval_eq' z p
  have hmon : ∀ (β : Fin n →₀ ℕ) (c : R), C c * ∏ i, (X i : MvPowerSeries (Fin n) R) ^ β i = monomial β c := by
    intro β c
    simp only [X_pow_eq]
    rw [prod_monomial, ← monomial_zero_eq_C_apply, monomial_mul_monomial]
    simp [Finsupp.univ_sum_single]
  set G : MvPowerSeries (Fin n) R := ∑ β ∈ p.support, monomial β (ev (p.coeff β)) with hGdef
  have hrel : ∀ β ∈ p.support,
      Rel k (T (p.coeff β * ∏ i, z i ^ β i)) (monomial β (ev (p.coeff β))) := by
    intro β hβ
    have h := rel_mul (rel_const ev _ T hT (p.coeff β))
      (rel_prod_pow Finset.univ (fun i => T (z i)) X (fun i => β i) (rel_coord ev ds T hT z hz hd))
    rw [zero_add, ← Finsupp.degree_eq_sum, hdeg β hβ, hmon] at h
    rw [map_mul, map_prod]; simp only [map_pow]; exact h
  have hcoef : ∀ α : Fin n →₀ ℕ, α.degree = k →
      coeff α (T (MvPolynomial.eval z p)) = coeff α G := by
    intro α hα
    rw [← sub_eq_zero, ← map_sub, hev, map_sum, hGdef, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun β hβ => coeff_of_lt_order ?_
    exact lt_of_lt_of_le (by rw [hα]; exact_mod_cast Nat.lt_succ_self k) (hrel β hβ).2
  have hG : ∀ α, coeff α G = ev (p.coeff α) := by
    intro α
    simp only [hGdef, map_sum, coeff_monomial, Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [MvPolynomial.mem_support_iff, not_not] at h; rw [h, map_zero]
  rw [hev]
  refine Ideal.sum_mem _ fun β hβ => ?_
  rw [pow_succ']
  refine Ideal.mul_mem_mul (hker (RingHom.mem_ker.2 ?_)) ?_
  · rw [← hG, ← hcoef β (hdeg β hβ), hf, map_zero]
  · rw [← hdeg β hβ, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

end Main

theorem taylor_injective : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ f, taylor ev (fun i => ⇑(ds i)) f = 0 → f = 0 := by
  intro R A _ _ _ _ _ _ inc ev hev n ds z hz hd hm f hf
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_ringHom_eq_taylor A R n ev ds
  have hker := ker_le_span inc ev hev z hz hm
  have hTf : T f = 0 := by rw [hT]; exact hf
  have hall : ∀ k, f ∈ Ideal.span (Set.range z) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact step ev ds T hT z hz hd hker k f hTf ih
  have hne : Ideal.span (Set.range z) ≠ ⊤ := by
    intro h
    apply (maximalIdeal.isMaximal A).ne_top
    rw [eq_top_iff, hm, ← h]; exact le_sup_right
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]; exact hall

end GlobalTheory.TaylorInj
end
end

open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_injective_localRing : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ f, taylor ev (fun i => ⇑(ds i)) f = 0 → f = 0 := by
  atlas_forward_decl GlobalTheory.TaylorInj.taylor_injective
end

section
section
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.PowerSeriesComplete

theorem isAdicComplete_map_C : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R))
      (MvPowerSeries (Fin n) R) := by
  intro R _ _ I hI n
  have hfg : I.FG := IsNoetherian.noetherian I
  have hC : (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R) = algebraMap R (MvPowerSeries (Fin n) R) := rfl
  have hP : IsPrecomplete I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isPrecomplete_pi (M := R) (Fin n →₀ ℕ) hfg
  have hH : IsHausdorff I (MvPowerSeries (Fin n) R) :=
    GlobalTheory.CompleteBaseChange.isHausdorff_pi (M := R) (Fin n →₀ ℕ) hfg
  rw [hC]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }

end GlobalTheory.PowerSeriesComplete
end

open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_isAdicComplete_map_C_of_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ n : ℕ, IsAdicComplete (I.map (MvPowerSeries.C : R →+* MvPowerSeries (Fin n) R)) (MvPowerSeries (Fin n) R) := by
  atlas_forward_decl GlobalTheory.PowerSeriesComplete.isAdicComplete_map_C
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerField

variable {X : Scheme.{0}} {W : X.Opens} {d : Fld X} {x : X}

theorem germ_field_congr (hd : IsField W d) {O O' : X.Opens} (hO : x ∈ O) (hO' : x ∈ O')
    (hOW : O ≤ W) (hO'W : O' ≤ W) (f : Γ(X, O)) (f' : Γ(X, O'))
    (h : (X.presheaf.germ O x hO).hom f = (X.presheaf.germ O' x hO').hom f') :
    (X.presheaf.germ O x hO).hom (d O f) = (X.presheaf.germ O' x hO').hom (d O' f') := by
  obtain ⟨V, hV, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hO hO' f f' h
  have h1 : (X.presheaf.germ O x hO).hom (d O f) =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iU) f)) := by
    rw [hd.2.2 O V (leOfHom iU) hOW f]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iU x hV _).symm
  have h2 : (X.presheaf.germ O' x hO').hom (d O' f') =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iV) f')) := by
    rw [hd.2.2 O' V (leOfHom iV) hO'W f']
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iV x hV _).symm
  have e' : resG X (leOfHom iU) f = resG X (leOfHom iV) f' := e
  rw [h1, h2, e']

theorem exists_rep (hxW : x ∈ W) (t : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f : Γ(X, O)), (X.presheaf.germ O x hO).hom f = t := by
  obtain ⟨U, m, s, hs⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf t
  refine ⟨U ⊓ W, ⟨m, hxW⟩, inf_le_right, resG X (inf_le_left : U ⊓ W ≤ U) s, ?_⟩
  rw [← hs]
  exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨m, hxW⟩ s

theorem exists_rep₂ (hxW : x ∈ W) (t t' : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f f' : Γ(X, O)),
      (X.presheaf.germ O x hO).hom f = t ∧ (X.presheaf.germ O x hO).hom f' = t' := by
  obtain ⟨O₁, h₁, hW₁, f₁, e₁⟩ := exists_rep hxW t
  obtain ⟨O₂, h₂, hW₂, f₂, e₂⟩ := exists_rep hxW t'
  refine ⟨O₁ ⊓ O₂, ⟨h₁, h₂⟩, inf_le_left.trans hW₁, resG X (inf_le_left : O₁ ⊓ O₂ ≤ O₁) f₁,
    resG X (inf_le_right : O₁ ⊓ O₂ ≤ O₂) f₂, ?_, ?_⟩
  · rw [← e₁]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨h₁, h₂⟩ f₁
  · rw [← e₂]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) x ⟨h₁, h₂⟩ f₂

def germMap (hxW : x ∈ W) (t : X.presheaf.stalk x) : X.presheaf.stalk x :=
  (X.presheaf.germ _ x (exists_rep hxW t).choose_spec.choose).hom
    (d _ (exists_rep hxW t).choose_spec.choose_spec.choose_spec.choose)

theorem germMap_germ (hd : IsField W d) (hxW : x ∈ W) {O : X.Opens} (hO : x ∈ O) (hOW : O ≤ W)
    (f : Γ(X, O)) :
    germMap (d := d) hxW ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  have hs := (exists_rep hxW ((X.presheaf.germ O x hO).hom f)).choose_spec.choose_spec
  exact germ_field_congr hd _ hO hs.choose hOW _ f hs.choose_spec.choose_spec

end GlobalTheory.StalkDerField

open GlobalTheory.StalkDerField in

theorem GlobalTheory.StalkDerField.exists_stalk_derivation : ∀ (X : Scheme.{0}) (W : X.Opens) (d : Fld X), IsField W d → ∀ (x : X), x ∈ W → ∃ δ : Derivation ℤ (X.presheaf.stalk x) (X.presheaf.stalk x), ∀ (O : X.Opens) (hO : x ∈ O), O ≤ W → ∀ f, δ ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  intro X W d hd x hxW
  let g : X.presheaf.stalk x →+ X.presheaf.stalk x := AddMonoidHom.mk' (germMap (d := d) hxW) (by
    intro t t'
    obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
    rw [← map_add, germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
      germMap_germ hd hxW hO hOW, hd.1 O hOW f f', map_add])
  refine ⟨Derivation.mk' g.toIntLinearMap ?_, fun O hO hOW f => germMap_germ hd hxW hO hOW f⟩
  intro t t'
  obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
  show germMap hxW _ = _ • germMap hxW _ + _ • germMap hxW _
  rw [← map_mul, germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
    germMap_germ hd hxW hO hOW, hd.2.1 O hOW f f', smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen : ∀ (X : Scheme.{0}) (W : X.Opens) (d : Fld X), IsField W d → ∀ (x : X), x ∈ W → ∃ δ : Derivation ℤ (X.presheaf.stalk x) (X.presheaf.stalk x), ∀ (O : X.Opens) (hO : x ∈ O), O ≤ W → ∀ f, δ ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  atlas_forward_decl GlobalTheory.StalkDerField.exists_stalk_derivation
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvFieldComm

section Rings

variable {S : Type} [CommRing S]

def fstH (S : Type) [CommRing S] : DualNumber S →+* S := (TrivSqZeroExt.fstHom S S S).toRingHom

@[simp] theorem fstH_apply (x : DualNumber S) : fstH S x = x.fst := rfl

def swap (S : Type) [CommRing S] : DualNumber (DualNumber S) →+* DualNumber (DualNumber S) where
  toFun x := TrivSqZeroExt.inl (TrivSqZeroExt.inl x.fst.fst + TrivSqZeroExt.inr x.snd.fst) +
    TrivSqZeroExt.inr (TrivSqZeroExt.inl x.fst.snd + TrivSqZeroExt.inr x.snd.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp <;> ring
  map_mul' a b := by ext <;> simp <;> ring

theorem swap_snd_snd (x : DualNumber (DualNumber S)) : (swap S x).snd.snd = x.snd.snd := by
  simp [swap]

end Rings

section Rings2

variable {R S : Type} [CommRing R] [CommRing S]

abbrev inc (S : Type) [CommRing S] : S →+* DualNumber S := algebraMap S (DualNumber S)

theorem dualMap_comp_inc (φ : R →+* S) : (dualMap φ).comp (inc R) = (inc S).comp φ := by
  refine RingHom.ext fun x => ?_; ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_inc : (fstH S).comp (inc S) = RingHom.id S := by
  refine RingHom.ext fun x => ?_; simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_inc_inc_comp (φ : R →+* S) : (swap S).comp ((inc (DualNumber S)).comp ((inc S).comp φ)) =
    (inc (DualNumber S)).comp ((inc S).comp φ) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_inc_dualMap (φ : R →+* S) : (swap S).comp ((inc (DualNumber S)).comp (dualMap φ)) = dualMap ((inc S).comp φ) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_dualMap_inc (φ : R →+* S) : (swap S).comp (dualMap ((inc S).comp φ)) = (inc (DualNumber S)).comp (dualMap φ) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : R →+* S) : (fstH S).comp (dualMap φ) = φ.comp (fstH R) := by
  refine RingHom.ext fun x => ?_; simp [dualMap]


end Rings2

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ψ' : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap ψ' = spMap (ψ.comp ψ') := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem dual_pt {S : Type} [CommRing S] (x : Sp (DualNumber S)) :
    (spMap (fstH S)) ((spMap (algebraMap S (DualNumber S))) x) = x := by
  apply PrimeSpectrum.ext
  ext y
  change algebraMap S (DualNumber S) (fstH S y) ∈ x.asIdeal ↔ y ∈ x.asIdeal
  have hn : (TrivSqZeroExt.inr y.snd : DualNumber S) ∈ x.asIdeal :=
    x.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)
  have hy : y = algebraMap S (DualNumber S) (fstH S y) + TrivSqZeroExt.inr y.snd :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq y).symm
  constructor
  · intro h; rw [hy]; exact add_mem h hn
  · intro h
    have e : algebraMap S (DualNumber S) (fstH S y) = y - TrivSqZeroExt.inr y.snd := by
      rw [eq_sub_iff_add_eq]; exact hy.symm
    rw [e]; exact sub_mem h hn

section Val

variable {A : Type} [CommRing A] {X : Scheme.{0}}

def evHom (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valR_eq_evHom (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = evHom x U h f := by
  unfold valR
  rw [dif_pos h]
  rfl

theorem top_le_spMap {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U := fun y _ => h (Set.mem_univ ((spMap ψ) y))

theorem valR_spMap_comp {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR (spMap ψ ≫ x) U f = ψ (valR x U f) := by
  have h' := top_le_spMap ψ x U h
  rw [valR_eq_evHom _ U h', valR_eq_evHom x U h]
  have e : (spMap ψ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap ψ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap ψ) x U ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f =
    (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f
  rw [e, Category.assoc, n]

theorem top_le_fromSpecStalk {x : X} {U : X.Opens} (hU : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
  have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU

theorem valR_fromSpecStalk {x : X} {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (A := X.presheaf.stalk x) (X.fromSpecStalk x) U a = X.presheaf.germ U x hU a := by
  have h := top_le_fromSpecStalk hU
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans
      (Category.comp_id _))
  unfold valR
  refine (dif_pos h).trans ?_
  change ((X.fromSpecStalk x).appLE U ⊤ h ≫ (Scheme.ΓSpecIso _).hom).hom a = _
  rw [e, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Val

section Tr

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]

theorem tv_hom (v : TanM (𝟙 (Sp R)) G) : (tv v).left ≫ G.hom = spMap (inc R) := by
  have := Over.w (tv v)
  simpa using this

theorem one_left' {T : Over (Sp R)} : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  show (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left, Over.toUnit_left]

theorem fst_tv (v : TanM (𝟙 (Sp R)) G) : spMap (fstH R) ≫ (tv v).left = η[G].left := by
  have h := congrArg (fun k => k.left) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem v)
  simp only [smT, Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, one_left'] at h
  have gen : ∀ ψ : DualNumber R →+* DualNumber R, (∀ x, ψ x = inc R x.fst) →
      spMap ψ ≫ (tv v).left = (overAt (𝟙 (Sp R)) (DualNumber R)).hom ≫ η[G].left →
      spMap ((inc R).comp (fstH R)) ≫ (tv v).left = spMap (inc R) ≫ η[G].left := by
    intro ψ hψ hh
    have : ψ = (inc R).comp (fstH R) := RingHom.ext fun x => hψ x
    subst this
    simpa using hh
  have e2 := gen _ (fun x => by ext <;> simp [tm, TrivSqZeroExt.algebraMap_eq_inl]) h
  have h2 := congrArg (fun k => spMap (fstH R) ≫ k) e2
  simp only [← spMap_comp, ← Category.assoc] at h2
  simp only [spMap_comp, fst_comp_inc, spMap_id] at h2
  simpa using h2

variable {S : Type} [CommRing S]

def gW (g : Sp S ⟶ G.left) : tEpsG (g ≫ G.hom) ⟶ G :=
  Over.homMk (spMap (inc S) ≫ g) (by simp)

def vW (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    tEpsG (g ≫ G.hom) ⟶ G :=
  Over.homMk (spMap (dualMap φ) ≫ (tv v).left) (by
    simp only [tEpsG, Over.mk_hom, Category.assoc, tv_hom, hg, spMap_comp, dualMap_comp_inc])

def trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    Sp (DualNumber S) ⟶ G.left :=
  (gW G g * vW G φ g hg v).left

theorem isTr_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    GlobalTheory.Heat.IsTr G φ g v (trP G φ g hg v) :=
  ⟨_, _, rfl, rfl, rfl⟩

theorem translateTangent_comp_hom (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    trP G φ g hg v ≫ G.hom = spMap ((inc S).comp φ) := by
  rw [trP, Over.w]
  simp only [tEpsG, Over.mk_hom, hg, spMap_comp]

theorem fst_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G) :
    spMap (fstH S) ≫ trP G φ g hg v = g := by
  let E : Over.mk (g ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (fstH S)) (by
      show spMap (fstH S) ≫ spMap (inc S) ≫ g ≫ G.hom = g ≫ G.hom
      rw [← Category.assoc, spMap_comp, fst_comp_inc, spMap_id]; exact Category.id_comp _)
  have e1 : E ≫ gW G g = Over.homMk g rfl := by
    ext
    show spMap (fstH S) ≫ spMap (inc S) ≫ g = g
    rw [← Category.assoc, spMap_comp, fst_comp_inc, spMap_id]; exact Category.id_comp _
  have e2 : E ≫ vW G φ g hg v = 1 := by
    ext
    simp only [E, vW, Over.comp_left, Over.homMk_left, one_left', Over.mk_hom]
    rw [← Category.assoc, spMap_comp, fst_comp_dualMap, ← spMap_comp, Category.assoc, fst_tv, hg]
  have := congrArg (fun k => k.left) (MonObj.comp_mul E (gW G g) (vW G φ g hg v))
  simpa only [e1, e2, _root_.mul_one, Over.comp_left, Over.homMk_left, E, trP] using this

theorem top_le_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v : TanM (𝟙 (Sp R)) G)
    (O : G.left.Opens) (hO : ⊤ ≤ g ⁻¹ᵁ O) : ⊤ ≤ trP G φ g hg v ⁻¹ᵁ O := by
  intro x _
  rw [← dual_pt x]
  show (spMap (fstH S) ≫ trP G φ g hg v) _ ∈ O
  rw [fst_trP]
  exact hO (Set.mem_univ _)

end Tr

section Swap

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]

theorem swap_inc_inc : (swap S).comp ((inc (DualNumber S)).comp (inc S)) = (inc (DualNumber S)).comp (inc S) := by
  refine RingHom.ext fun x => ?_; ext <;> simp [swap, TrivSqZeroExt.algebraMap_eq_inl]

theorem swap_trP (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ) (v v' : TanM (𝟙 (Sp R)) G) :
    trP G ((inc S).comp φ) (trP G φ g hg v) (translateTangent_comp_hom G φ g hg v) v' =
      spMap (swap S) ≫ trP G ((inc S).comp φ) (trP G φ g hg v') (translateTangent_comp_hom G φ g hg v') v := by
  have hw := translateTangent_comp_hom G φ g hg v'
  have hu := translateTangent_comp_hom G φ g hg v
  let P : tEpsG (trP G φ g hg v' ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (inc (DualNumber S))) (by
      show spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g ≫ G.hom =
        spMap (inc (DualNumber S)) ≫ trP G φ g hg v' ≫ G.hom
      rw [trP, Over.w]; rfl)
  let P' : tEpsG (trP G φ g hg v ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (inc (DualNumber S))) (by
      show spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g ≫ G.hom =
        spMap (inc (DualNumber S)) ≫ trP G φ g hg v ≫ G.hom
      rw [trP, Over.w]; rfl)
  let Q : tEpsG (trP G φ g hg v ≫ G.hom) ⟶ tEpsG (trP G φ g hg v' ≫ G.hom) :=
    Over.homMk (spMap (swap S)) (by
      show spMap (swap S) ≫ spMap (inc (DualNumber S)) ≫ trP G φ g hg v' ≫ G.hom =
        spMap (inc (DualNumber S)) ≫ trP G φ g hg v ≫ G.hom
      rw [hw, hu, spMap_comp, spMap_comp, swap_inc_inc_comp])
  have e1 : gW G (trP G φ g hg v') = P ≫ (gW G g * vW G φ g hg v') := Over.OverMorphism.ext rfl
  have e2 : gW G (trP G φ g hg v) = P' ≫ (gW G g * vW G φ g hg v) := Over.OverMorphism.ext rfl
  have hx : Q ≫ P ≫ gW G g = P' ≫ gW G g := by
    ext
    show spMap (swap S) ≫ spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g =
      spMap (inc (DualNumber S)) ≫ spMap (inc S) ≫ g
    simp only [← Category.assoc, spMap_comp]
    rw [swap_inc_inc]
  have hb : Q ≫ P ≫ vW G φ g hg v' = vW G ((inc S).comp φ) (trP G φ g hg v) hu v' := by
    ext
    show spMap (swap S) ≫ spMap (inc (DualNumber S)) ≫ spMap (dualMap φ) ≫ (tv v').left =
      spMap (dualMap ((inc S).comp φ)) ≫ (tv v').left
    simp only [← Category.assoc, spMap_comp]
    rw [swap_inc_dualMap]
  have hc : Q ≫ vW G ((inc S).comp φ) (trP G φ g hg v') hw v = P' ≫ vW G φ g hg v := by
    ext
    show spMap (swap S) ≫ spMap (dualMap ((inc S).comp φ)) ≫ (tv v).left =
      spMap (inc (DualNumber S)) ≫ spMap (dualMap φ) ≫ (tv v).left
    simp only [← Category.assoc, spMap_comp]
    rw [swap_dualMap_inc]
  have key : gW G (trP G φ g hg v) * vW G ((inc S).comp φ) (trP G φ g hg v) hu v' =
      Q ≫ (gW G (trP G φ g hg v') * vW G ((inc S).comp φ) (trP G φ g hg v') hw v) := by
    rw [MonObj.comp_mul, e1, e2, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, hx, hb, hc, mul_right_comm]
  exact congrArg (fun k => k.left) key

end Swap

end GlobalTheory.InvFieldComm

open GlobalTheory.InvFieldComm in
theorem GlobalTheory.InvFieldComm.invField_comm : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v v' : TanM (𝟙 (Sp R)) G) (dd dd' : Fld G.left), IsInv G v dd → IsInv G v' dd' → ∀ O f, dd O (dd' O f) = dd' O (dd O f) := by
  intro R _ G _ _ v v' dd dd' hv hv' O f
  have key : ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left) (hg : g ≫ G.hom = spMap φ),
      ⊤ ≤ g ⁻¹ᵁ O → valR g O (dd O (dd' O f)) = valR g O (dd' O (dd O f)) := by
    intro S _ φ g hg hO
    have hw1 := top_le_trP G φ g hg v' O hO
    have hu1 := top_le_trP G φ g hg v O hO
    have hw2 := top_le_trP G _ _ (translateTangent_comp_hom G φ g hg v') v O hw1
    have A1 := hv'.2 S φ g _ O (dd O f) hg hO (isTr_trP G φ g hg v')
    have A2 := hv.2 (DualNumber S) _ _ _ O f (translateTangent_comp_hom G φ g hg v') hw1 (isTr_trP G _ _ (translateTangent_comp_hom G φ g hg v') v)
    have B1 := hv.2 S φ g _ O (dd' O f) hg hO (isTr_trP G φ g hg v)
    have B2 := hv'.2 (DualNumber S) _ _ _ O f (translateTangent_comp_hom G φ g hg v) hu1 (isTr_trP G _ _ (translateTangent_comp_hom G φ g hg v) v')
    rw [← B1, ← B2, swap_trP, valR_spMap_comp _ _ _ hw2, swap_snd_snd, A2, A1]
  have hsub : ∀ (S : Type) [CommRing S] (φ : R →+* S) (g : Sp S ⟶ G.left), g ≫ G.hom = spMap φ →
      ⊤ ≤ g ⁻¹ᵁ O → valR g O (dd O (dd' O f) - dd' O (dd O f)) = 0 := by
    intro S _ φ g hg hO
    rw [valR_eq_evHom g O hO, map_sub, ← valR_eq_evHom g O hO, ← valR_eq_evHom g O hO, key S φ g hg hO, sub_self]
  refine sub_eq_zero.1 (TopCat.Presheaf.section_ext G.left.sheaf O _ 0 fun y hy => ?_)
  have h0 := hsub (G.left.presheaf.stalk y) (Spec.preimage (G.left.fromSpecStalk y ≫ G.hom)).hom
    (G.left.fromSpecStalk y) (Spec.map_preimage _).symm (top_le_fromSpecStalk hy)
  exact ((valR_fromSpecStalk hy _).symm.trans h0).trans (map_zero (G.left.presheaf.germ O y hy).hom).symm
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorFields_commute_of_commGroupScheme : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v v' : TanM (𝟙 (Sp R)) G) (dd dd' : Fld G.left), IsInv G v dd → IsInv G v' dd' → ∀ O f, dd O (dd' O f) = dd' O (dd O f) := by
  atlas_forward_decl GlobalTheory.InvFieldComm.invField_comm
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_apply_constant_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ O r, dd O (constFn G.hom O r) = 0 := by
  first | exact @GlobalTheory.Heat.isInv_constFn | exact GlobalTheory.Heat.isInv_constFn | (intros; apply GlobalTheory.Heat.isInv_constFn <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem scheme_constantSection_add {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a + b) = constFn p U a + constFn p U b := by
  simp [constFn, map_add]

theorem constFn_mul_on_open {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a * b) = constFn p U a * constFn p U b := by
  simp [constFn, map_mul]

theorem gammaSpecIso_appLE_of_eq_id_apply {R : Type} [CommRing R] (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (e : (⊤ : (Sp R).Opens) ≤ f ⁻¹ᵁ ⊤) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((f.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = r := by
  subst hf
  simp only [Scheme.Hom.appLE]
  erw [show (homOfLE e) = 𝟙 _ from Subsingleton.elim _ _]
  simp

theorem gammaSpecIso_appLE_section_constantSection_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (e : Sp R ⟶ X) (he : e ≫ p = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ e ⁻¹ᵁ U) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r)) = r := by
  have hc := Scheme.Hom.appLE_comp_appLE e p ⊤ U ⊤ (fun _ _ => trivial) h
  calc (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((p.appLE ⊤ U (fun _ _ => trivial) ≫ e.appLE U ⊤ h).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl
    _ = _ := by rw [hc]
    _ = r := gammaSpecIso_appLE_of_eq_id_apply _ he _ r

end GlobalTheory.Heat

namespace GlobalTheory.Heat

theorem liftDer_isDerivation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (D : R → R) (W : G.left.Opens)
    (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ D' : Derivation ℤ R R, ∀ r, D' r = D r := by
  intro R _ G _ D W d hL hW
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := by simpa using Over.w (η[G])
  let ev : Γ(G.left, W) →+* R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (((η[G]).left.appLE W ⊤ hW).hom)
  have hev : ∀ r, ev (constFn G.hom W r) = r := fun r => gammaSpecIso_appLE_section_constantSection_eq G.hom _ he W hW r
  have hc : ∀ r, d W (constFn G.hom W r) = constFn G.hom W (D r) := hL.2 W le_rfl
  have hadd : ∀ a b, D (a + b) = D a + D b := by
    intro a b
    have := congrArg ev (hc (a + b))
    rw [scheme_constantSection_add, hL.1.1 W le_rfl, hc, hc, map_add, hev, hev, hev] at this
    exact this.symm
  have hmul : ∀ a b, D (a * b) = a * D b + b * D a := by
    intro a b
    have := congrArg ev (hc (a * b))
    rw [constFn_mul_on_open, hL.1.2.1 W le_rfl, hc, hc, map_add, map_mul, map_mul, hev, hev, hev, hev, hev] at this
    exact this.symm
  let L : R →ₗ[ℤ] R := (AddMonoidHom.mk' D hadd).toIntLinearMap
  exact ⟨Derivation.mk' L (fun a b => by simpa [L, smul_eq_mul] using hmul a b), fun r => rfl⟩

end GlobalTheory.Heat
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_of_vectorFieldLift_near_unit : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ D' : Derivation ℤ R R, ∀ r, D' r = D r := by
  atlas_forward_decl GlobalTheory.Heat.liftDer_isDerivation
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (r : R), evO G (constO G r) = r := by
  first | exact @GlobalTheory.FormalOrigin.evO_constO | exact GlobalTheory.FormalOrigin.evO_constO | (intros; apply GlobalTheory.FormalOrigin.evO_constO <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (O : G.left.Opens) (hO : origin G ∈ O) (r : R), (G.left.presheaf.germ O (origin G) hO).hom (constFn G.hom O r) = constO G r := by
  first | exact @GlobalTheory.GermConst.germ_constFn_origin | exact GlobalTheory.GermConst.germ_constFn_origin | (intros; apply GlobalTheory.GermConst.germ_constFn_origin <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_map_fromSpecStalk_origin_comp_structure_eq : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type) [CommRing Ω] (ψ : G.left.presheaf.stalk (origin G) →+* Ω), spMap ψ ≫ G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (ψ.comp (constO G)) := by
  first | exact @GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom | exact GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom | (intros; apply GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem spMap_fromSpecStalk_le_preimage_iff (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω) (hψ : IsLocalHom ψ) (O : X.Opens) :
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O := by
  constructor
  · intro h
    let p : ↥(Sp Ω) := closedPoint Ω
    have hm : (spMap ψ ≫ X.fromSpecStalk x) p ∈ O := h (x := p) trivial
    rw [Scheme.Hom.comp_apply] at hm
    have e : (spMap ψ) p = (closedPoint (X.presheaf.stalk x) : ↥(Spec (X.presheaf.stalk x))) := by
      show PrimeSpectrum.comap ψ (closedPoint Ω) = _
      exact IsLocalRing.comap_closedPoint ψ
    rw [e, Scheme.fromSpecStalk_closedPoint] at hm
    exact hm
  · intro hx w _
    have : X.fromSpecStalk x (spMap ψ w) ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    show (spMap ψ ≫ X.fromSpecStalk x) w ∈ O
    rw [Scheme.Hom.comp_apply]
    exact Specializes.mem_open (x := X.fromSpecStalk x (spMap ψ w)) this O.isOpen hx

theorem spMap_fromSpecStalk_top_le_iff : ∀ (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω), IsLocalHom ψ → ∀ O : X.Opens,
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O :=
  fun X x Ω _ _ ψ hψ O => spMap_fromSpecStalk_le_preimage_iff X x Ω ψ hψ O

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem : ∀ (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (ψ : X.presheaf.stalk x →+* Ω), IsLocalHom ψ → ∀ O : X.Opens, ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O := by
  atlas_forward_decl GlobalTheory.spMap_fromSpecStalk_top_le_iff
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem exists_formalPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  intro R _ _ _ _ _ _ G _ _ hsm hint n v dd hdd D W d hd hW
  have hx0W : origin G ∈ W := hW (show IsLocalRing.closedPoint R ∈ (⊤ : (Sp R).Opens) from trivial)
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨D', hD'⟩ := GlobalTheory.T.exists_derivation_of_vectorFieldLift_near_unit R G D W d hd hW
  choose δ hδ using fun a => GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen G.left ⊤ (dd a) (hdd a).1 (origin G) trivial
  obtain ⟨dA, hdA⟩ := GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen G.left W d hd.1 (origin G) hx0W
  have hcomm : ∀ a b s, δ a (δ b s) = δ b (δ a s) := by
    intro a b s
    obtain ⟨O, hO, f, rfl⟩ := TopCat.Presheaf.germ_exist G.left.presheaf s
    rw [hδ b O hO le_top, hδ a O hO le_top, hδ a O hO le_top, hδ b O hO le_top,
      GlobalTheory.T.invariantVectorFields_commute_of_commGroupScheme R G (v a) (v b) (dd a) (dd b) (hdd a) (hdd b)]
  have hconst : ∀ a r, δ a (constO G r) = 0 := by
    intro a r
    rw [← GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants R G ⊤ trivial r, hδ a ⊤ trivial le_top, GlobalTheory.T.invariantVectorField_apply_constant_eq_zero R G (v a) (dd a) (hdd a), map_zero]
  have hdc : ∀ r, dA (constO G r) = constO G (D' r) := by
    intro r
    rw [← GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants R G W hx0W r, hdA W hx0W le_rfl, hd.2 W le_rfl, ← hD', GlobalTheory.T.germ_origin_constantSection_eq_originStalkConstants]
  obtain ⟨z, hz0, hz1, hm⟩ := GlobalTheory.T.smooth_commGroup_local_coordinates_at_origin R G hsm n v dd hdd δ (fun a O hO f => hδ a O hO le_top f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_ringHom_eq_taylor _ R n (evO G) δ
  have hTC : ∀ r, T (constO G r) = MvPowerSeries.C r := by
    intro r
    rw [hT, GlobalTheory.T.derivationTaylorPowerSeries_of_derivations_kill _ R n (evO G) δ _ (fun i => hconst i r), GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants]
  have hT0 : ∀ s, MvPowerSeries.constantCoeff (T s) = evO G s := by
    intro s
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hT]
    show (∏ i, (((0 : Fin n →₀ ℕ) i).factorial : ℚ))⁻¹ • evO G (iterOp _ 0 s) = _
    rw [iterOp_zero]
    simp
  haveI : IsLocalHom (evO G) := Scheme.isLocalHom_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left
  have : IsLocalHom T := ⟨fun s hs => by
    have h1 : IsUnit (evO G s) := by rw [← hT0]; exact (MvPowerSeries.isUnit_iff_constantCoeff).1 hs
    exact (isUnit_map_iff (evO G) s).1 h1⟩
  obtain ⟨dΩ, hdΩC, hdΩ⟩ := GlobalTheory.T.derivation_extends_taylorPowerSeriesRing R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm hconst dA D' hdc
  have hval : ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)),
      valR (spMap T ≫ G.left.fromSpecStalk (origin G)) O f = T ((G.left.presheaf.germ O (origin G) hO).hom f) :=
    fun O hO f => GlobalTheory.FlagBundle.valR_spMap_fromSpecStalk T hO f
  have htop : ∀ O : G.left.Opens, ⊤ ≤ (spMap T ≫ G.left.fromSpecStalk (origin G)) ⁻¹ᵁ O → origin G ∈ O :=
    fun O h => (GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem G.left (origin G) _ T inferInstance O).1 h
  refine ⟨MvPowerSeries (Fin n) R, inferInstance, NoZeroDivisors.to_isDomain _, inferInstance, MvPowerSeries.C,
    spMap T ≫ G.left.fromSpecStalk (origin G), fun a => intDer (MvPowerSeries.pderiv R a), intDer dΩ,
    GlobalTheory.T.mvPowerSeries_isAdicComplete_map_C_of_noetherian R _ ‹_› n, ?_, (GlobalTheory.T.preimage_spMap_fromSpecStalk_whole_iff_mem G.left (origin G) _ T inferInstance W).2 hx0W, fun r => ?_, fun a r => ?_,
    fun a O f hO => ?_, fun O f hOW hO => ?_, fun O f hO hf => ?_⟩
  · rw [Category.assoc, GlobalTheory.T.spec_map_fromSpecStalk_origin_comp_structure_eq R G _ T]
    congr 1
    exact RingHom.ext hTC
  · rw [← hD']; exact hdΩC r
  · exact MvPowerSeries.pderiv_C
  · have h := htop O hO
    rw [hval O h, hval O h, ← hδ a O h le_top, hT, hT, GlobalTheory.T.derivationTaylorPowerSeries_derivation_eq_pderiv _ R n (evO G) δ hcomm]
    rfl
  · have h := htop O hO
    rw [hval O h, hval O h, ← hdA O h hOW, hT, hT]
    exact (hdΩ _).symm
  · have h := htop O hO
    rw [hval O h, hT] at hf
    have h0 := GlobalTheory.T.derivationTaylorPowerSeries_injective_localRing R _ (constO G) (evO G) (GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants R G) n δ z hz0 hz1 hm _ hf
    exact germ_injective_of_isIntegral G.left (origin G) h (h0.trans (map_zero _).symm)

end GlobalTheory.FormalOrigin
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalPoint_origin_smoothCommGroupScheme : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsIntegral G.left → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (D : R → R) (W : G.left.Opens) (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ (Ω : Type) (_ : CommRing Ω) (_ : IsDomain Ω) (_ : IsLocalRing Ω) (φ : R →+* Ω) (x : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dΩ : Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω ∧ x ≫ G.hom = spMap φ ∧ ⊤ ≤ x ⁻¹ᵁ W ∧ (∀ r, dΩ (φ r) = φ (D r)) ∧ (∀ a r, δ a (φ r) = 0) ∧ (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) ∧ (∀ O f, O ≤ W → ⊤ ≤ x ⁻¹ᵁ O → valR x O (d O f) = dΩ (valR x O f)) ∧ ∀ O (f : Γ(G.left, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0 := by
  atlas_forward_decl GlobalTheory.FormalOrigin.exists_formalPoint
end
