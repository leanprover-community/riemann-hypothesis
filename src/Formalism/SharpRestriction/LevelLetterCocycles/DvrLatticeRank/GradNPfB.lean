import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfA
import Mathlib

section
namespace Formalism.MainNotions.N.Ln34

open Finset

section GradNPfVal

variable {L O : Type*} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L)
  (hι : Function.Injective ι) (hR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x)

include hR in
theorem gradNPf_v_nonneg (a : O) : 0 ≤ v (ι a) := (hR (ι a)).2 ⟨a, rfl⟩

include hι hR in
theorem gradNPf_isUnit_of_v (a : O) (ha : v (ι a) = 0) : IsUnit a := by
  have hne : ι a ≠ 0 := by
    intro h0
    rw [h0, v.map_zero] at ha
    first
      | simp at ha
      | exact WithTop.top_ne_zero ha
      | exact absurd ha (by decide)
  have hinv : v (ι a)⁻¹ = 0 := by
    have h1 : v (ι a * (ι a)⁻¹) = 0 := by rw [mul_inv_cancel₀ hne, v.map_one]
    rwa [v.map_mul, ha, zero_add] at h1
  obtain ⟨b, hb⟩ := (hR _).1 (le_of_eq hinv.symm)
  have hab : a * b = 1 := hι (by rw [_root_.map_mul, _root_.map_one, hb, mul_inv_cancel₀ hne])
  first
    | exact isUnit_iff_exists_inv.2 ⟨b, hab⟩
    | exact IsUnit.of_mul_eq_one b hab
    | exact isUnit_of_mul_eq_one_right hab

private theorem exists_one_add_pow_eq_one_add_mul_add_sq (a : O) (i : ℕ) :
    ∃ b : O, (1 + a) ^ i = 1 + (i : O) * a + a ^ 2 * b := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨(i : O) + b + b * a, by rw [pow_succ, hb]; push_cast; ring⟩

private theorem exists_geom_sum_one_add_eq_natCast_add_mul (a : O) (n : ℕ) :
    ∃ C : O, ∑ i ∈ range n, (1 + a) ^ i = (n : O) + a * C := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨b, hb⟩ := exists_one_add_pow_eq_one_add_mul_add_sq a n
    exact ⟨C + n + a * b, by rw [sum_range_succ, hC, hb]; push_cast; ring⟩

private theorem exists_geom_sum_one_add_eq_second_order (a : O) (n : ℕ) :
    ∃ B : O, ∑ i ∈ range n, (1 + a) ^ i =
      (n : O) + a * ((∑ i ∈ range n, i : ℕ) : O) + a ^ 2 * B := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨b, hb⟩ := exists_one_add_pow_eq_one_add_mul_add_sq a n
    refine ⟨B + b, ?_⟩
    simp only [sum_range_succ]
    rw [hB, hb]
    push_cast
    ring

private theorem val_add_eq_left_of_val_lt (x y : L) (h : v x < v y) : v (x + y) = v x := by
  have h1 : min (v x) (v y) ≤ v (x + y) := v.map_add x y
  rw [min_eq_left h.le] at h1
  refine le_antisymm ?_ h1
  by_contra hc
  push_neg at hc
  have h2 : min (v (x + y)) (v (-y)) ≤ v (x + y + -y) := v.map_add _ _
  have e : x + y + -y = x := by ring
  rw [e, v.map_neg] at h2
  exact lt_irrefl _ (lt_of_lt_of_le (lt_min hc h) h2)

theorem gradNPf_zero_lt_one : (0 : WithTop ℚ) < 1 := by
  first
    | exact WithTop.coe_lt_coe.2 zero_lt_one
    | exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)
    | norm_num
    | simp

include hι hR in
theorem gradNPf_unit_one_add (lO d : O) (hl : v (ι lO) = 1) : IsUnit (1 + lO * d) := by
  apply gradNPf_isUnit_of_v v ι hι hR
  have h0 : 0 ≤ v (ι d) := gradNPf_v_nonneg v ι hR d
  have hy : v (ι lO * ι d) = 1 + v (ι d) := by rw [v.map_mul, hl]
  have hle : (1 : WithTop ℚ) ≤ 1 + v (ι d) := by
    first
      | exact le_add_of_nonneg_right h0
      | simpa using add_le_add_left h0 1
  have hlt : v (1 : L) < v (ι lO * ι d) := by
    rw [v.map_one, hy]
    exact lt_of_lt_of_le gradNPf_zero_lt_one hle
  rw [_root_.map_add, _root_.map_one, _root_.map_mul, val_add_eq_left_of_val_lt v _ _ hlt, v.map_one]

include hι hR in
theorem gradNPf_unit_nat (l : ℕ) (hp : l.Prime) (hl : v (l : L) = 1) (m : ℕ) (hm : ¬ l ∣ m) :
    IsUnit (m : O) := by
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have hb : ((Nat.gcd l m : ℕ) : ℤ) = (l : ℤ) * Nat.gcdA l m + (m : ℤ) * Nat.gcdB l m :=
    Nat.gcd_eq_gcd_ab l m
  rw [show Nat.gcd l m = 1 from hcop] at hb
  have hO : (m : O) * ((Nat.gcdB l m : ℤ) : O) = 1 + (l : O) * (-((Nat.gcdA l m : ℤ) : O)) := by
    have h := congrArg (fun z : ℤ => (z : O)) hb
    push_cast at h
    linear_combination -1 * h
  have hlO : v (ι (l : O)) = 1 := by rw [_root_.map_natCast]; exact hl
  have hu := gradNPf_unit_one_add v ι hι hR (l : O) (-((Nat.gcdA l m : ℤ) : O)) hlO
  rw [← hO] at hu
  exact isUnit_of_mul_isUnit_left hu

include hι hR in
theorem gradNPf_sub_one (lO x : O) (hl : v (ι lO) = 1) (hx : v (ι x - 1) = 1) :
    ∃ t : O, IsUnit t ∧ x - 1 = lO * t := by
  have hne : ι lO ≠ 0 := by
    intro h0
    rw [h0, v.map_zero] at hl
    first
      | simp at hl
      | exact WithTop.top_ne_one hl
      | exact absurd hl (by decide)
  have hinv : 1 + v (ι lO)⁻¹ = 0 := by
    have h1 : v (ι lO * (ι lO)⁻¹) = 0 := by rw [mul_inv_cancel₀ hne, v.map_one]
    rwa [v.map_mul, hl] at h1
  have hq : v ((ι x - 1) * (ι lO)⁻¹) = 0 := by
    rw [v.map_mul, hx, hinv]
  obtain ⟨t, ht⟩ := (hR _).1 (le_of_eq hq.symm)
  refine ⟨t, gradNPf_isUnit_of_v v ι hι hR t (by rw [ht, hq]), hι ?_⟩
  rw [_root_.map_sub, _root_.map_one, _root_.map_mul, ht, mul_comm (ι lO), mul_assoc,
    inv_mul_cancel₀ hne, mul_one]

include hι hR in

theorem gradNPf_lte (l : ℕ) [hp : Fact l.Prime] (hl2 : l ≠ 2) (hl : v (l : L) = 1)
    (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) :
    ∀ m : ℕ, m ≠ 0 → ∃ ε : O, IsUnit ε ∧ x ^ m - 1 = (l : O) ^ (1 + padicValNat l m) * ε := by
  have lte_isUnit_add_mul_lemma_5 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (lO s c : O) (hl : v (ι lO) = 1)
      (hs : IsUnit s) : IsUnit (s + lO * c) := by
    obtain ⟨u, rfl⟩ := hs
    have h : (u : O) + lO * c = u * (1 + lO * (c * ↑u⁻¹)) := by
      linear_combination (-(lO * c)) * Units.mul_inv u
    rw [h]
    exact u.isUnit.mul (gradNPf_unit_one_add v ι hinj hRR lO _ hl)
  have lte_pow_coprime_step_lemma_6 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (l : ℕ) [hp : Fact l.Prime]
      (hl : v (l : L) = 1) (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) (s : ℕ)
      (hs : ¬ l ∣ s) : ∃ ε : O, IsUnit ε ∧ x ^ s - 1 = (l : O) * ε := by
    have hlO : v (ι (l : O)) = 1 := by rw [_root_.map_natCast]; exact hl
    obtain ⟨C, hC⟩ := exists_geom_sum_one_add_eq_natCast_add_mul (x - 1) s
    have e : 1 + (x - 1) = x := by ring
    rw [e, hxt] at hC
    have hsu : IsUnit (s : O) := gradNPf_unit_nat v ι hinj hRR l hp.out hl s hs
    refine ⟨t * ((s : O) + (l : O) * (t * C)),
      ht.mul (lte_isUnit_add_mul_lemma_5 v ι hinj hRR _ _ _ hlO hsu), ?_⟩
    rw [← geom_sum_mul, hC, hxt]
    ring
  have lte_pow_prime_step_lemma_7 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (l : ℕ) [hp : Fact l.Prime] (hl2 : l ≠ 2)
      (hl : v (l : L) = 1) (y u : O) (hu : IsUnit u) (j : ℕ)
      (hyu : y - 1 = (l : O) ^ (j + 1) * u) :
      ∃ ε : O, IsUnit ε ∧ y ^ l - 1 = (l : O) ^ (j + 2) * ε := by
    have hlO : v (ι (l : O)) = 1 := by rw [_root_.map_natCast]; exact hl
    obtain ⟨k, hk⟩ : ∃ k, l = 2 * k + 1 := by
      rcases hp.out.eq_two_or_odd' with h | h
      · exact absurd h hl2
      · obtain ⟨k, hk⟩ := h
        exact ⟨k, hk⟩
    have hsum : (∑ i ∈ range l, i) = l * k := by
      have h2 : (∑ i ∈ range l, i) * 2 = l * (l - 1) := sum_range_id_mul_two l
      have h3 : l - 1 = 2 * k := by omega
      rw [h3] at h2
      apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
      rw [h2]
      ring
    obtain ⟨B, hB⟩ := exists_geom_sum_one_add_eq_second_order (y - 1) l
    have e : 1 + (y - 1) = y := by ring
    rw [e, hsum, hyu] at hB
    refine ⟨u * (1 + (l : O) * ((l : O) ^ j * u * (k : O) + ((l : O) ^ j) ^ 2 * u ^ 2 * B)),
      hu.mul (gradNPf_unit_one_add v ι hinj hRR _ _ hlO), ?_⟩
    rw [← geom_sum_mul, hB, hyu]
    push_cast
    ring
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hdvd : l ∣ m
    · obtain ⟨m', rfl⟩ := hdvd
      have hm' : m' ≠ 0 := by
        rintro rfl
        exact hm (mul_zero l)
      have hl1 : 1 < l := hp.out.one_lt
      have hlt : m' < l * m' := by
        have hpos : 0 < m' := Nat.pos_of_ne_zero hm'
        nlinarith
      obtain ⟨ε, hε, he⟩ := ih m' hlt hm'
      obtain ⟨ε', hε', he'⟩ := lte_pow_prime_step_lemma_7 v ι hι hR l hl2 hl (x ^ m') ε hε
        (padicValNat l m') (by rw [he]; ring)
      have hv : padicValNat l (l * m') = padicValNat l m' + 1 := by
        rw [padicValNat.mul hp.out.ne_zero hm']
        first
          | rw [padicValNat_self]; ring
          | rw [padicValNat.self hl1]; ring
          | simp; ring
          | simp
      refine ⟨ε', hε', ?_⟩
      rw [hv, show l * m' = m' * l from Nat.mul_comm l m', pow_mul, he']
      ring
    · obtain ⟨ε, hε, he⟩ := lte_pow_coprime_step_lemma_6 v ι hι hR l hl x t ht hxt m hdvd
      refine ⟨ε, hε, ?_⟩
      rw [padicValNat.eq_zero_of_not_dvd hdvd, he]
      ring

theorem gradNPf_sum_val (l : ℕ) [hp : Fact l.Prime] (N : ℕ) :
    ∑ y ∈ Ico 1 (N + 1), (1 + padicValNat l y) = N + padicValNat l N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ico_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero N) (Nat.factorial_ne_zero N)]
    ring

include hι hR in

theorem gradNPf_prod (l : ℕ) [hp : Fact l.Prime] (hl2 : l ≠ 2) (hl : v (l : L) = 1)
    (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) (s : ℕ) (hs : s ≠ 0) (hsl : ¬ l ∣ s)
    (N : ℕ) : ∃ a : O, (l : O) ^ (N + padicValNat l N.factorial) =
      a * ∏ y ∈ Ico 1 (N + 1), ((x ^ s) ^ y - 1) := by
  have lte_isUnit_add_mul_lemma_5 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (lO s c : O) (hl : v (ι lO) = 1)
      (hs : IsUnit s) : IsUnit (s + lO * c) := by
    obtain ⟨u, rfl⟩ := hs
    have h : (u : O) + lO * c = u * (1 + lO * (c * ↑u⁻¹)) := by
      linear_combination (-(lO * c)) * Units.mul_inv u
    rw [h]
    exact u.isUnit.mul (gradNPf_unit_one_add v ι hinj hRR lO _ hl)
  have lte_pow_coprime_step_lemma_6 {L : Type _} {O : Type _} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L) (hinj : Function.Injective ι)
      (hRR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x) (l : ℕ) [hp : Fact l.Prime]
      (hl : v (l : L) = 1) (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) (s : ℕ)
      (hs : ¬ l ∣ s) : ∃ ε : O, IsUnit ε ∧ x ^ s - 1 = (l : O) * ε := by
    have hlO : v (ι (l : O)) = 1 := by rw [_root_.map_natCast]; exact hl
    obtain ⟨C, hC⟩ := exists_geom_sum_one_add_eq_natCast_add_mul (x - 1) s
    have e : 1 + (x - 1) = x := by ring
    rw [e, hxt] at hC
    have hsu : IsUnit (s : O) := gradNPf_unit_nat v ι hinj hRR l hp.out hl s hs
    refine ⟨t * ((s : O) + (l : O) * (t * C)),
      ht.mul (lte_isUnit_add_mul_lemma_5 v ι hinj hRR _ _ _ hlO hsu), ?_⟩
    rw [← geom_sum_mul, hC, hxt]
    ring
  obtain ⟨ε0, hε0, he0⟩ := lte_pow_coprime_step_lemma_6 v ι hι hR l hl x t ht hxt s hsl
  have key : ∀ n : ℕ, ∃ E : O, IsUnit E ∧ ∏ y ∈ Ico 1 (n + 1), ((x ^ s) ^ y - 1) =
      (l : O) ^ (∑ y ∈ Ico 1 (n + 1), (1 + padicValNat l y)) * E := by
    intro n
    induction n with
    | zero => exact ⟨1, isUnit_one, by simp⟩
    | succ n ih =>
      obtain ⟨E, hE, hEq⟩ := ih
      obtain ⟨ε, hε, he⟩ := gradNPf_lte v ι hι hR l hl2 hl (x ^ s) ε0 hε0 he0
        (n + 1) (Nat.succ_ne_zero n)
      refine ⟨E * ε, hE.mul hε, ?_⟩
      rw [prod_Ico_succ_top (by omega : 1 ≤ n + 1), sum_Ico_succ_top (by omega : 1 ≤ n + 1),
        hEq, he]
      ring
  obtain ⟨E, hE, hEq⟩ := key N
  obtain ⟨u, rfl⟩ := hE
  refine ⟨↑u⁻¹, ?_⟩
  rw [hEq, gradNPf_sum_val l N]
  linear_combination (-((l : O) ^ (N + padicValNat l N.factorial))) * Units.inv_mul u

end GradNPfVal

end Formalism.MainNotions.N.Ln34
end

section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem gradNPf_cc_γ₀ (g : W.Gam) (a : PowerSeries O) :
    PowerSeries.constantCoeff (W.γ₀ g a) = PowerSeries.constantCoeff a := by
  exact Formalism.MainNotions.LiftingTheory.constantCoeff_gamma W g a

theorem gradNPf_γA_comm (g h : W.Gam) (a : LetA O n) :
    W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  exact Formalism.MainNotions.LiftingTheory.frame_γA_comm W g h a

theorem gradNPf_cc_f (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hf : W.γA W.gam π' = π' * f) (i : ZMod n) :
    PowerSeries.constantCoeff (f i) = ((W.χΓ W.gam : Oˣ) : O) ^ s' := by
  have hi := congrFun hf i
  have hγi : (W.γA W.gam π') i = W.γ₀ W.gam (π' i) := rfl
  have hπi : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  have hX : W.γ₀ W.gam PowerSeries.X = PowerSeries.X *
      PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X)) := by
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (W.γ₀ W.gam PowerSeries.X)]
    rw [(W.γ₀_X W.gam).1, map_zero, add_zero]
  have hh : PowerSeries.constantCoeff (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1)
      (W.γ₀ W.gam PowerSeries.X))) = ((W.χΓ W.gam : Oˣ) : O) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact (W.γ₀_X W.gam).2
  rw [hγi, Pi.mul_apply, hπi, map_mul, map_pow, hX, mul_pow] at hi
  have h2 : PowerSeries.X ^ s' * (W.γ₀ W.gam ((w : LetA O n) i) *
      (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X))) ^ s') =
      PowerSeries.X ^ s' * ((w : LetA O n) i * f i) := by
    linear_combination hi
  have h3 := congrArg PowerSeries.constantCoeff (PowerSeries.X_pow_mul_cancel h2)
  rw [map_mul, map_mul, map_pow, hh, gradNPf_cc_γ₀] at h3
  have hwu : IsUnit (PowerSeries.constantCoeff ((w : LetA O n) i)) :=
    (w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)).map PowerSeries.constantCoeff
  exact (hwu.mul_left_cancel h3).symm

theorem gradNPf_fΔ (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hf : W.γA W.gam π' = π' * f) : ∀ δ ∈ W.DelF, W.γA δ f = f := by
  intro δ hδ
  have hu : IsUnit (algebraMap (LetA O n) W.EE π') := by
    rw [hw, map_mul, map_pow]
    have hl : IsUnit (algebraMap (LetA O n) W.EE letπ) := by simpa using Formalism.MainNotions.LiftingTheory.wmap_unit W 0
    exact (w.isUnit.map _).mul (hl.pow _)
  apply Formalism.MainNotions.LiftingTheory.lifta_reg W π' _ _ hu
  have h1 : W.γA δ (W.γA W.gam π') = W.γA W.gam π' := by
    rw [Formalism.MainNotions.LiftingTheory.frame_γA_comm, hπΔ δ hδ]
  rw [hf, map_mul, hπΔ δ hδ] at h1
  exact h1

theorem gradNPf_expand (π' a : LetA O n) (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0)
    (F : ZMod n → PowerSeries O) (hF : ∀ i, a i = PowerSeries.subst (π' i) (F i))
    (c₀ : O) (hc : ∀ i, PowerSeries.constantCoeff (a i) = c₀) :
    ∃ t : LetA O n, a - algebraMap O (LetA O n) c₀ = π' * t := by
  have hS : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
  refine ⟨fun i => PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)), ?_⟩
  funext i
  have e1 : a i = π' i * PowerSeries.subst (π' i)
      (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)) +
      PowerSeries.C (PowerSeries.constantCoeff (F i)) := by
    conv_lhs => rw [hF i, PowerSeries.eq_X_mul_shift_add_const (F i)]
    rw [PowerSeries.subst_add (hS i), PowerSeries.subst_mul (hS i), PowerSeries.subst_X (hS i),
      PowerSeries.subst_C]
    rfl
  have e3 : PowerSeries.constantCoeff (F i) = c₀ := by
    have := congrArg PowerSeries.constantCoeff e1
    rw [hc i, map_add, map_mul, hπ0 i, zero_mul, zero_add, PowerSeries.constantCoeff_C] at this
    exact this.symm
  rw [e3] at e1
  have hC : algebraMap O (PowerSeries O) c₀ = PowerSeries.C c₀ := by
    rw [PowerSeries.algebraMap_apply]
    rfl
  show a i - algebraMap O (PowerSeries O) c₀ = π' i * PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i))
  rw [hC, e1]
  ring

theorem exists_gam_pi_factor (T : LocLat G Qp LL O) (e s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n)
    (E : ZMod n → Polynomial O) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (π'₀ : LetA O n)
    (w₀ : (LetA O n)ˣ) (hw₀ : π'₀ = (w₀ : LetA O n) * letπ ^ s')
    (hm : ∀ y ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T y - y = π'₀ • x') :
    ∃ f t : LetA O n, W.γA W.gam π' = π' * f ∧
      f - algebraMap O (LetA O n) (((W.χΓ W.gam : Oˣ) : O) ^ s') = π' * t ∧
      IsUnit (algebraMap (LetA O n) W.EE π') ∧ (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
      (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π' := fun δ hδ => hR.1 δ hδ
  obtain ⟨w', hw'⟩ := hR.2.2.2.2.2.2.1
  obtain ⟨f, hfdef⟩ : ∃ f : LetA O n, f = 1 + (w' : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := ⟨_, rfl⟩
  have hf : W.γA W.gam π' = π' * f := by
    rw [hfdef]
    linear_combination hw'
  have hfΔ := gradNPf_fΔ W s' w π' f hw hπΔ hf
  obtain ⟨Fs, hFs, -⟩ := hR.2.1 f hfΔ
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  obtain ⟨t, ht⟩ := gradNPf_expand π' f hπ0 Fs hFs _ (gradNPf_cc_f W s' w π' f hw hf)
  refine ⟨f, t, hf, ht, ?_, hπΔ, ?_⟩
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  · intro y hy
    obtain ⟨x', hx', hxe⟩ := hm y hy
    refine ⟨((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) • x', (W.N T).smul_mem _ hx'.1, ?_⟩
    have hπ₀ : π'₀ = ((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) * π' := by
      rw [hw₀, hw, mul_assoc, ← mul_assoc ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.inv_mul, one_mul]
    rw [smul_smul, mul_comm π', ← hπ₀]
    exact hxe

end Local

set_option maxHeartbeats 1000000 in

theorem gradNPf_hyps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (hs : 1 ≤ sK l K) :
    ∃ (f t : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x u : ↥(OL LL)),
      IsUnit u ∧ x - 1 = (l : ↥(OL LL)) * u ∧
      ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' = π' * f ∧
      f - algebraMap ↥(OL LL) (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x ^ sK l K) = π' * t ∧
      IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
      (∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ π' = π') ∧
      (∀ y ∈ ((HW l).W K 1 LL hG).NΔ T, ∃ d ∈ ((HW l).W K 1 LL hG).N T,
        ((HW l).W K 1 LL hG).γD T ((HW l).W K 1 LL hG).gam y - y = π' • d) ∧
      ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
      ∀ N : ℕ, ∃ a : ↥(OL LL), (l : ↥(OL LL)) ^ (N + padicValNat l N.factorial) =
        a * ∏ y ∈ Finset.Ico 1 (N + 1), ((x ^ sK l K) ^ y - 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, hr₀, hm₀⟩, -⟩ := h9W T hT hs1 hp
  rw [hpl] at hr₀
  obtain ⟨w₀, hw₀⟩ := hr₀.2.2.1
  obtain ⟨f, t, hf, ht, hEE, hπΔ, hγN⟩ :=
    exists_gam_pi_factor _ T (eK K) (sK l K) hs π' E hR π'₀ w₀ hw₀ hm₀.2
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hlO : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL))) = 1 := by
    rw [map_natCast]
    exact hlv
  have hxv : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL hG).gam_gen
    rw [hs1, Nat.cast_one] at this
    exact this
  obtain ⟨u, hu, hxu⟩ := gradNPf_sub_one ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv
    (l : ↥(OL LL)) _ hlO hxv
  have hsl : ¬ l ∣ sK l K := by
    apply Nat.not_dvd_of_pos_of_lt hs
    have h2 := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  exact ⟨f, t, (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ), u, hu, hxu, hf, ht, hEE, hπΔ, hγN,
    ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp,
    fun N => gradNPf_prod ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hl hlv _ u hu hxu
      (sK l K) (by omega) hsl N⟩

end Formalism.MainNotions.N.Ln34

end
end
