import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
import Development.AutomorphicArithmetic.ThickFrames.ThickFrame2Large
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivLeRpowThreeQuarters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOnePrimeElements
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Development.AutomorphicArithmetic.EvenBoxes.BoxBoundForHost

section
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem Lwv_le_mul_log (s : Scale) (hy : 1 ≤ Real.log s.x) :
    (Lwv s : ℝ) ≤ (4084 + 60 / s.eps) * Real.log s.x := by
  have he := s.eps_pos
  have h1 : (⌈(405 : ℝ) * Real.log s.x⌉₊ : ℝ) < 405 * Real.log s.x + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have h2 : (⌈30 / s.eps⌉₊ : ℝ) < 30 / s.eps + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : 60 / s.eps = 2 * (30 / s.eps) := by ring
  have h4 : 0 < 30 / s.eps := by positivity
  unfold Lwv
  push_cast
  rw [h3]
  nlinarith [mul_nonneg h4.le (sub_nonneg.mpr hy)]

theorem exists_thick_set_sizes :
    ∃ CT2 : ℝ, ∀ eps Co : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.o : ℝ) ≤ Co → ∃ T : Finset ℕ, (∀ a ∈ T, 4 * Lwv s * a < R.n0) ∧ Formalism.FrobeniusOrbits.NoRel T (Lwv s) ∧ (R.n0 : ℝ) * Real.exp (-(CT2 * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log (Lwv s)))) / (Lwv s) ≤ T.card ∧ s.x ^ (-s.eps) * R.n ≤ (T.card : ℝ) ∧ 4 * Lwv s * T.card ≤ R.n0 ∧ 2 ≤ Lwv s := by
  obtain ⟨C, -, hT⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.thickFrame2
  refine ⟨C, fun eps Co he he' => ?_⟩
  obtain ⟨x0, hT⟩ := hT eps (max Co 2) (4084 + 60 / eps) he he'
  refine ⟨max x0 (Real.exp 1), fun s R hs hx hR ho => ?_⟩
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hy1 : 1 ≤ Real.log s.x := (Real.le_log_iff_exp_le hx0).mpr ((le_max_right _ _).trans hx)
  have hL : 2 ≤ Lwv s := by unfold Lwv; omega
  have hLK := Lwv_le_mul_log s hy1
  have hn1 := hR.n_lo
  have hn2 := hR.n_up
  rw [hs] at hLK hn1 hn2
  have hp0 : 0 < s.x ^ (2 + 8 * eps) := Real.rpow_pos_of_pos hx0 _
  have hlo : s.x ^ UpperTheory.BernoulliSumsFrobeniusOrbits.hE eps / 2 ≤ (R.n : ℝ) := by
    unfold UpperTheory.BernoulliSumsFrobeniusOrbits.hE
    linarith
  have hup : (R.n : ℝ) ≤ max Co 2 * s.x ^ UpperTheory.BernoulliSumsFrobeniusOrbits.hE eps :=
    hn2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp0.le)
  obtain ⟨T, t1, t2, t3, t4, t5⟩ := hT s.x ((le_max_left _ _).trans hx) R.toFrame (Lwv s) hL hLK
    (ho.trans (le_max_left _ _)) hlo hup
  exact ⟨T, t1, t2, t3, hs ▸ t4, t5, hL⟩

end GlobalTheory.EX
end

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noRel_finset_card_ge : ∃ CT2 : ℝ, ∀ eps Co : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.o : ℝ) ≤ Co → ∃ T : Finset ℕ, (∀ a ∈ T, 4 * Lwv s * a < R.n0) ∧ Formalism.FrobeniusOrbits.NoRel T (Lwv s) ∧ (R.n0 : ℝ) * Real.exp (-(CT2 * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log (Lwv s)))) / (Lwv s) ≤ T.card ∧ s.x ^ (-s.eps) * R.n ≤ (T.card : ℝ) ∧ 4 * Lwv s * T.card ≤ R.n0 ∧ 2 ≤ Lwv s := by
  atlas_forward_decl GlobalTheory.EX.exists_thick_set_sizes
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem excluded_count_lt {Y r : ℝ} (hY : 1 ≤ Y) (hr : 1 ≤ r) (h : 20 * r ^ 3 < Y ^ ((3 : ℝ) / 20)) :
    (3 * r + 1) * (1 + 2 * r ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) < Y ^ ((9 : ℝ) / 10) := by
  have hP : 1 ≤ Y ^ ((3 : ℝ) / 4) := Real.one_le_rpow hY (by norm_num)
  have hs : Y ^ ((9 : ℝ) / 10) = Y ^ ((3 : ℝ) / 20) * Y ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  rw [hs]
  generalize Y ^ ((3 : ℝ) / 4) = P at hP ⊢
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have h1 : 1 ≤ r ^ 2 * P := one_le_mul_of_one_le_of_one_le hr2 hP
  have h2 : r ^ 2 ≤ r ^ 2 * P := le_mul_of_one_le_right (by positivity) hP
  have h3 : 1 + 2 * r ^ 2 * (P + 1) ≤ 5 * (r ^ 2 * P) := by nlinarith
  calc (3 * r + 1) * (1 + 2 * r ^ 2 * (P + 1)) ≤ (4 * r) * (5 * (r ^ 2 * P)) :=
        mul_le_mul (by linarith) h3 (by positivity) (by positivity)
    _ = 20 * r ^ 3 * P := by ring
    _ < _ := mul_lt_mul_of_pos_right h (by linarith)

theorem exists_pair_disjoint_exceptional {Y : ℝ} {r : ℕ} (hY : 2 ≤ Y) (hr : 1 ≤ r)
    (h : 20 * (r : ℝ) ^ 3 < Y ^ ((3 : ℝ) / 20)) (G : Finset ℕ) (hG : ∀ g ∈ G, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y)
    (hc : Y ^ ((9 : ℝ) / 10) ≤ G.card) :
    ∃ a ∈ G, ∃ b ∈ G, a ≠ b ∧ Disjoint (Formalism.CyclotomicNorms.BB r a) (Formalism.CyclotomicNorms.BB r b) := by
  have hpos : 0 < Y ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos (by linarith) _
  have hne : G.Nonempty := Finset.card_pos.1 (by exact_mod_cast hpos.trans_le hc)
  obtain ⟨a, ha⟩ := hne
  have hex : ∃ b ∈ G, ¬ (Formalism.CyclotomicNorms.BB r b ∩ Formalism.CyclotomicNorms.BB r a).Nonempty := by
    by_contra hcon
    push Not at hcon
    have h1 := GlobalTheory.choice_count Y r a hY hr (hG a ha).1 (hG a ha).2 G
      (fun g hg => ⟨(hG g hg).1, (hG g hg).2, hcon g hg⟩)
    have h2 := excluded_count_lt (Y := Y) (r := r) (by linarith) (by exact_mod_cast hr) h
    linarith
  obtain ⟨b, hb, hab⟩ := hex
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · rintro rfl
    exact hab ⟨a, Or.inl rfl, Or.inl rfl⟩
  · rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
    exact Set.not_nonempty_iff_eq_empty.1 hab

theorem two_type_primes : NormPrimes → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → ModRow s N d → ∃ g : Fin 2 → ℕ, (∀ i, (g i).Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 ∧ NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) := by
  classical
  intro hN eps he0 he1
  obtain ⟨x1, h1⟩ := hN eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps 16 1 he0 one_pos
  obtain ⟨x3, h3⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max (max x1 x2) (max x3 21), fun s R q d hs hx hR hq => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  have hc := h1 s R q d hs hx1 hR hq
  have hb := (h2 s hs hx2).2.2.1
  obtain ⟨-, -, hr5, hkr, -⟩ := h3 s R hs hx3 hR
  have hmk := R.m_add_three_le_k
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have hx0 : 0 < s.x := by linarith
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  rw [Real.rpow_one, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hb
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hr5
  have hb1 : s.x ^ 16 ≤ s.b := (le_mul_of_one_le_right (by positivity) hX).trans hb
  have hx15 : 1 ≤ s.x ^ 15 := one_le_pow₀ (by linarith)
  have hx16 : 21 * s.x ^ 15 ≤ s.x ^ 16 := by
    rw [pow_succ s.x 15, mul_comm]; exact mul_le_mul_of_nonneg_left hx4 (by linarith)
  have hb2 : 2 ≤ s.b := by linarith
  have hkb : s.b ≤ (R.k : ℝ) * s.b := le_mul_of_one_le_left (by linarith) hk1
  have hkb1 : 1 ≤ (R.k : ℝ) * s.b := by linarith
  have hY : 2 ≤ ((R.k : ℝ) * s.b) ^ 8 :=
    (hb2.trans hkb).trans (le_self_pow₀ hkb1 (by norm_num))
  have hr3 : (R.r : ℝ) ^ 3 ≤ s.x ^ 15 := by
    calc (R.r : ℝ) ^ 3 ≤ (s.x ^ 5) ^ 3 := pow_le_pow_left₀ (by positivity) hr5 3
      _ = _ := by ring
  have hZ : (R.k : ℝ) * s.b ≤ (((R.k : ℝ) * s.b) ^ 8) ^ ((3 : ℝ) / 20) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.self_le_rpow_of_one_le hkb1 (by norm_num)
  obtain ⟨a, ha, b, hb', hab, hd⟩ := exists_pair_disjoint_exceptional (r := R.r) hY (by omega)
    (by linarith) _ (fun g hg => by
      rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by linarith)] at hg
      exact ⟨hg.2.2.1, hg.1⟩) hc
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by linarith)] at ha hb'
  refine ⟨![a, b], ?_, hab, hd⟩
  intro i
  fin_cases i
  · exact ⟨ha.2.1, ha.2.2.1, ha.1, ha.2.2.2⟩
  · exact ⟨hb'.2.1, hb'.2.2.1, hb'.1, hb'.2.2.2⟩

end GlobalTheory.EX
end

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_two_large_norm_one_primes : NormPrimes → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → ModRow s N d → ∃ g : Fin 2 → ℕ, (∀ i, (g i).Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 ∧ NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) := by
  atlas_forward_decl GlobalTheory.EX.two_type_primes
end

section
section
namespace GlobalTheory.EX

theorem lt_of_prime_mod_eq_one {p M : ℕ} (hp : p.Prime) (h : p % M = 1) (hM : 0 < M) : M < p := by
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt] at h
    exact hp.one_lt.ne' h
  · subst heq
    simp at h

theorem mod_eq_one_of_mod_mul {p M K : ℕ} (h : p % (M * K) = 1) (hM : 1 < M) : p % M = 1 := by
  rw [← Nat.mod_mul_right_mod p M K, h, Nat.mod_eq_of_lt hM]

theorem auxiliary_primes : SmallPrimeOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧ p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  rintro ⟨A, hA, hS⟩
  have hA0 : 0 ≤ A := by linarith
  refine ⟨(2 + 2 * A + (2 + 2 * A) * A) * A, by nlinarith [mul_nonneg hA0 hA0, mul_nonneg hA0 (mul_nonneg hA0 hA0)], ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have key : ∀ (M : ℕ) (e : ℝ), 2 ≤ M → (M : ℝ) ≤ (N : ℝ) ^ e →
      ∃ p : ℕ, p.Prime ∧ p % M = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ (e * A) := by
    intro M e hM hMe
    obtain ⟨p, hp, hpm, hple⟩ := hS M hM
    refine ⟨p, hp, hpm, hple.trans ?_⟩
    rw [Real.rpow_mul hN0.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hMe hA0
  have h15 : ((15 * N : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have : (30 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Real.rpow_two]; push_cast; nlinarith
  have hM1 : 2 ≤ 15 * N := by omega
  obtain ⟨p, hp, hpm, hple⟩ := key (15 * N) 2 hM1 h15
  have hM2 : 2 ≤ 15 * N * p := hM1.trans (Nat.le_mul_of_pos_right _ hp.pos)
  have hb2 : ((15 * N * p : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A) := by
    rw [Real.rpow_add hN0, Nat.cast_mul (15 * N) p]
    exact mul_le_mul h15 hple (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
  obtain ⟨p', hp', hpm', hple'⟩ := key (15 * N * p) _ hM2 hb2
  have hM3 : 2 ≤ 15 * N * p * p' := hM2.trans (Nat.le_mul_of_pos_right _ hp'.pos)
  have hb3 : ((15 * N * p * p' : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 + 2 * A + (2 + 2 * A) * A) := by
    rw [Real.rpow_add hN0, Nat.cast_mul (15 * N * p) p']
    exact mul_le_mul hb2 hple' (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
  obtain ⟨q, hq, hqm, hqle⟩ := key (15 * N * p * p') _ hM3 hb3
  have l1 : 15 * N * p < p' := lt_of_prime_mod_eq_one hp' hpm' (by omega)
  have l2 : 15 * N * p * p' < q := lt_of_prime_mod_eq_one hq hqm (by omega)
  have l3 : p ≤ 15 * N * p := Nat.le_mul_of_pos_left _ (by omega)
  have l4 : p' ≤ 15 * N * p * p' := Nat.le_mul_of_pos_left _ (by omega)
  have hAA := mul_nonneg hA0 hA0
  have hAAA := mul_nonneg hA0 hAA
  refine ⟨p, p', q, hp, hp', hq, by omega, by omega, by omega, hpm,
    mod_eq_one_of_mod_mul hpm' (by omega), ?_, ?_, ?_, hqle⟩
  · have : 15 * N * p * p' = N * (15 * p * p') := by ring
    rw [this] at hqm
    exact mod_eq_one_of_mod_mul hqm (by omega)
  · exact hple.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))
  · exact hple'.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith))

end GlobalTheory.EX
end

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primes_in_progression_bounded : SmallPrimeOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧ p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  atlas_forward_decl GlobalTheory.EX.auxiliary_primes
end

section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_prime_elements : ∀ (R : Ranks) (H : Host R) (M p : ℕ), 1 ≤ M → NormOne H.d M p → (∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)}) ∧ p % M = 1 % M := by
  first | exact @GlobalTheory.EX.normOne_host | exact GlobalTheory.EX.normOne_host | (intros; apply GlobalTheory.EX.normOne_host <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.HostExist

theorem kronSym_of_odd (a : ℤ) {n : ℕ} (h : ¬ 2 ∣ n) : GlobalTheoryTheory.kronSym a n = jacobiSym a n := by
  simp [GlobalTheoryTheory.kronSym, Nat.factorization_eq_zero_of_not_dvd h]

theorem quadraticChar_induces (d M : ℕ) [Fact d.Prime] (hd : d % 4 = 3) (hM : M ≠ 1) :
    GlobalTheoryTheory.Induces ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d)
      (GlobalTheoryTheory.chDir d) M := by
  have hp : d.Prime := Fact.out
  haveI : NeZero d := ⟨hp.ne_zero⟩
  have hch : ringChar (ZMod d) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  refine ⟨?_, fun a ha => ?_⟩
  · rcases (Nat.dvd_prime hp).1 (DirichletCharacter.conductor_dvd_level
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h)
        ((MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).2 (quadraticChar_ne_one hch))
    · exact h
  · have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h; exact absurd (Nat.coprime_zero_left M |>.1 ha) hM
      · exact h
    rw [GlobalTheoryTheory.chDir, GlobalTheoryTheory.kron, GlobalTheory.kronSym_neg_eq_jacobiSym_and_two.1 d a hd ha0,
      ← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
    simp

theorem abs_dlogH_le {R : Ranks} (H : Host R) {x eps C : ℝ} (h : QDq x eps C H.q H.d) :
    |dlogH H| ≤ C * Real.log x := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  have hd : H.d % 16 = 7 := H.hyp.2.2.2.1
  have h1 := (h.2.1 H.d _ (quadraticChar_induces H.d (8 * H.q * H.d) (by omega) (by
    rw [mul_assoc]; omega))).2
  exact (Complex.abs_re_le_norm _).trans h1

theorem exists_host (R : Ranks) (q d B : ℕ) (hyp : Formalism.FrobeniusOrbits.HostHyp q d)
    (hbig : 4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d) (h3 : q ≠ 3) (he : 2 ≤ R.e)
    (hinj : Function.Injective R.h) (ho : R.o ^ 64 ≤ 2 ^ R.e)
    (hsp : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ B → jacobiSym (-(d : ℤ)) p = 1)
    (g : Fin 2 → ℕ) (p p' q0 : ℕ) (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (hp : p.Prime) (hp' : p'.Prime)
    (hpp : p ≠ p') (hm : p % 15 = 1 ∧ p' % 15 = 1) (hpg : ∀ i, p ≠ g i ∧ p' ≠ g i)
    (hodd : ∀ l ∈ ({g 0, g 1, p, p', q0} : Finset ℕ), l % 2 = 1)
    (T : Finset ℕ) (Lw : ℕ) (hL : 2 ≤ Lw) (hT : ∀ a ∈ T, 4 * Lw * a < R.n0) (hT' : Formalism.FrobeniusOrbits.NoRel T Lw) (CT2 : ℝ) :
    ∃ H : Host R, H.q = q ∧ H.d = d ∧ H.splitBound = B ∧ H.g = g ∧ H.pde = p ∧ H.pde' = p' ∧
      H.levelPrimes = {g 0, g 1, p, p', q0} ∧ H.ccK = ⊤ ∧ H.T2 = T ∧ H.Lw = Lw ∧ H.CT2 = CT2 ∧ H.QS = 2 ^ (R.e + 2) := by
  obtain ⟨H, rfl, rfl, hQS, -, -, -, hPS, hEx, s, hs, hgs⟩ := Formalism.HC.exists_hostAx R.toFrame hinj he hyp
  have hcm : H.cmType.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [H.der.cmType.2.1]
    have := R.ord_pos
    omega
  obtain ⟨𝔟, h1, h2, h4⟩ := H.der.principal
  refine ⟨{ toHostAx := H, flPS := hPS, sqq := s, sqq_sq := hs, gal_sqq := hgs, QS_exact := hEx
            QS_le := by rw [hQS]; exact Formalism.HC.D7.qs_le R.toFrame hinj he
            o_pow := ho, q_ne_three := h3, qd_big := hbig, splitBound := B, split_small := hsp
            small_le := fun l hl h2 hd => by
              rw [hQS] at hd
              exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow hd)) h2
            φ₀ := hcm.some, φ₀_mem := hcm.some_mem,
            𝔟 := 𝔟, 𝔟_spec := ⟨h1, h2⟩, 𝔟_stable := h4, levelPrimes := {g 0, g 1, p, p', q0}, g := g, g_prime := hg, g_ne := hne,
            g_level := by intro i; fin_cases i <;> simp
            pde := p, pde' := p', pde_prime := hp, pde'_prime := hp', pde_ne := hpp, pde_level := by simp
            pde_mod := hm, pde_ne_g := hpg, ccK := ⊤, ccK_ne_bot := top_ne_bot,
            ccK_primitive := fun m hm => top_primitive m hm
            ccK_split := fun P hP hle => absurd (top_le_iff.1 hle) hP.ne_top
            ccK_coprime := fun p _ => by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left p
            ccK_coprimeS := by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _
            level_coprimeS := fun l hl => by
              rw [hQS]
              exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 (Nat.odd_iff.2 (hodd l hl)))
            TT := ∅, T2 := T, u0 := 0, Lw := Lw, two_le_Lw := hL, second_set_range := hT, second_set_no_relation := hT', CT2 := CT2 },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hQS⟩

theorem log_le_rpow_eventually (eps C : ℝ) (he : 0 < eps) (hC : 0 < C) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → C * Real.log x ≤ x ^ eps := by
  have h := (isLittleO_log_rpow_atTop he).bound (inv_pos.2 hC)
  obtain ⟨x0, h0⟩ := Filter.eventually_atTop.1 h
  refine ⟨max x0 1, fun x hx => ?_⟩
  have h1 := h0 x (le_of_max_le_left hx)
  have hx1 : 1 ≤ x := le_of_max_le_right hx
  rw [Real.norm_of_nonneg (Real.log_nonneg hx1), Real.norm_of_nonneg (by positivity)] at h1
  calc C * Real.log x ≤ C * (C⁻¹ * x ^ eps) := by gcongr
    _ = x ^ eps := by field_simp

theorem qd_big (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (q d : ℕ),
    s.eps = eps → x0 ≤ s.x → RankVal s R → Rowq s.x s.eps R.n q d →
      (4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d) ∧ q ≠ 3 := by
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps 814 1 he one_pos
  refine ⟨max (max x1 x2) 5, fun s R q d hs hx hR hrow => ?_⟩
  have hx5 : 5 ≤ s.x := le_of_max_le_right hx
  have hx0 : 0 < s.x := by linarith
  obtain ⟨-, -, hr, -, -, -, -, -, -, -, -, -, -, ht, -⟩ :=
    h1 s R hs (le_of_max_le_left (le_of_max_le_left hx)) hR
  have h814 := (h2 s hs (le_of_max_le_right (le_of_max_le_left hx))).1
  have hX1 : s.x ^ (814 : ℝ) ≤ GlobalTheoryTheory.X1 s.x s.eps := by
    refine h814.trans (Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le ?_))
    have := s.eps_pos; linarith
  have hlog : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9; linarith
  have hX2 : GlobalTheoryTheory.X1 s.x s.eps ≤ GlobalTheoryTheory.X2 s.x s.eps := by
    refine Real.exp_le_exp.2 (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hlog))
  have hsq : s.x ^ (407 : ℝ) ≤ Real.sqrt (GlobalTheoryTheory.X1 s.x s.eps) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num at hX1 ⊢
    exact hX1
  have h406 : (R.t : ℝ) * R.r ≤ s.x ^ (406 : ℝ) := by
    rw [show (406 : ℝ) = 401 + 5 by norm_num, Real.rpow_add hx0]
    gcongr
  have h1' : 1 ≤ s.x ^ (406 : ℝ) := Real.one_le_rpow s.one_lt_alt.le (by norm_num)
  have h407 : 5 * s.x ^ (406 : ℝ) ≤ s.x ^ (407 : ℝ) := by
    rw [show (407 : ℝ) = 1 + 406 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    gcongr
  have hb : ((4 * R.t * R.r + 1 : ℕ) : ℝ) ≤ Real.sqrt (GlobalTheoryTheory.X1 s.x s.eps) := by
    push_cast; linarith
  have hq := hrow.2.2.1
  have hd := (Real.sqrt_le_sqrt hX2).trans_lt hrow.2.2.2.2.2.2.1
  refine ⟨⟨by exact_mod_cast hb.trans_lt hq, by exact_mod_cast hb.trans_lt hd⟩, ?_⟩
  rintro rfl
  push_cast at hq
  linarith

theorem cond_pow_lt (eps C : ℝ) (he : 0 < eps) (hC : 1 ≤ C) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (q d : ℕ),
    s.eps = eps → x0 ≤ s.x → Rowq s.x s.eps R.n q d →
      (4 * (R.n : ℝ) * q * d) ^ C < ((R.k : ℝ) * s.b) ^ 8 := by
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (2 * C) 1 he one_pos
  refine ⟨x2, fun s R q d hs hx hrow => ?_⟩
  obtain ⟨-, -, h3, -, -, -, h7⟩ := h2 s hs hx
  rw [Real.rpow_one] at h3 h7
  have hxc : 1 ≤ s.x ^ (2 * C) := Real.one_le_rpow s.one_lt_alt.le (by linarith)
  have hn : (0 : ℝ) < R.n := by exact_mod_cast R.ord_pos
  have hq : (0 : ℝ) < q := by exact_mod_cast hrow.1.pos
  have hd : (0 : ℝ) < d := by exact_mod_cast hrow.2.2.2.2.1.pos
  have hN : (0 : ℝ) < 4 * (R.n : ℝ) * q * d := by positivity
  have hlog := hrow.2.2.2.2.2.2.2.2.2.2
  have a1 : (4 * (R.n : ℝ) * q * d) ^ C ≤ Real.exp (2 * C * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) := by
    rw [Real.rpow_def_of_pos hN]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hX : 0 < s.X' := Real.exp_pos _
  have a2 : Real.exp (2 * C * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤ s.X' :=
    (le_mul_of_one_le_right (Real.exp_pos _).le hxc).trans h7
  have a3 : s.X' ≤ s.b := (le_mul_of_one_le_left hX.le hxc).trans h3
  have hb : 1 < s.b := by
    have : 0 < s.L := Real.rpow_pos_of_pos (by have := s.one_lt_alt; linarith) _
    exact Real.one_lt_exp_iff.2 this
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have a4 : s.b ≤ R.k * s.b := le_mul_of_one_le_left (by linarith) hk
  have a5 : (R.k : ℝ) * s.b < ((R.k : ℝ) * s.b) ^ 8 := lt_self_pow₀ (by linarith) (by norm_num)
  linarith

theorem exists_hostGood (hThin : ThinChoice) (hNP : NormPrimes) (hSP : SmallPrimeOne) (hTops : TopsChoice) (eps C5 : ℝ)
    (he : 0 < eps) (he' : eps < 1 / 52) (hC5 : 0 < C5) :
    ∃ CT2 C8 c6 Cb x0 : ℝ, 1 ≤ C8 ∧ 0 < c6 ∧ 0 < Cb ∧ ∀ (s : Scale) (R : Ranks) (q d : ℕ), s.eps = eps → x0 ≤ s.x → s.J ≤ 4 →
      RankVal s R → 2 ≤ R.e → R.toFrame = Formalism.HC.cyclicFrame R.e → Rowq s.x s.eps R.n q d → QDq s.x s.eps C5 q d →
      Boxq s.x s.eps q d →
      ∃ (H : Host R) (q0 : ℕ), H.q = q ∧ H.d = d ∧ H.QS = 4 * R.n ∧ H.CT2 = CT2 ∧ HostGood s C8 C5 c6 Cb H q0 ∧
        R.toFrame.Shares H.TT (s.x ^ (-1 + s.eps)) := by
  obtain ⟨c6, hc6, hThin⟩ := hThin eps he he'
  obtain ⟨xb, hThin⟩ := hThin 4
  obtain ⟨Cb, xc, hCb, hTops⟩ := hTops eps 4 he he'
  obtain ⟨C8, hC8, hAux⟩ := GlobalTheory.T.exists_primes_in_progression_bounded hSP
  obtain ⟨xd, hG⟩ := GlobalTheory.T.exists_two_large_norm_one_primes hNP eps he he'
  obtain ⟨CT2, hT⟩ := GlobalTheory.T.exists_noRel_finset_card_ge
  obtain ⟨xe, hT⟩ := hT eps 4 he he'
  obtain ⟨xf, hlog⟩ := log_le_rpow_eventually eps C5 he hC5
  obtain ⟨xg, hbig⟩ := qd_big eps he he'
  obtain ⟨xh, hlt⟩ := cond_pow_lt eps C8 he hC8
  refine ⟨CT2, max C8 4, c6, Cb, max (max xb (max xc xd)) (max (max xe xf) (max xg xh)), le_max_of_le_left hC8, hc6, hCb,
    fun s R q d hs hx hJ hR h2e hφ hrow hqd hbox => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hb, hc, hd⟩, ⟨hxe, hf⟩, hg, hh⟩ := hx
  have hfr : ∀ (φ : Formalism.HC.Frame) (e : ℕ), φ = Formalism.HC.cyclicFrame e → Function.Injective φ.h ∧ φ.o = 1 ∧ φ.ord = 2 ^ e := by
    rintro _ e rfl
    exact ⟨Formalism.HC.frameCyc_h_injective e 1, Formalism.HC.cyclicFrame_index e, rfl⟩
  obtain ⟨hinj, ho1, hord⟩ := hfr _ _ hφ
  have ho4 : (R.o : ℝ) ≤ 4 := by rw [ho1]; norm_num
  have hn : 1 ≤ R.n := R.ord_pos
  have hq8 : q % 8 = 3 := hrow.2.1
  have hd16 : d % 16 = 7 := hrow.2.2.2.2.2.1
  have hyp : Formalism.FrobeniusOrbits.HostHyp q d :=
    ⟨hrow.1, hrow.2.2.2.2.1, hq8, hd16, by rw [← kronSym_of_odd _ (by omega)]; exact hrow.2.2.2.2.2.2.2.2.1⟩
  have hN : 30 ≤ 4 * R.n * q * d := by
    have : 4 * 1 * 3 * 7 ≤ 4 * R.n * q * d := by gcongr <;> omega
    omega
  have hd100 : 100 ≤ d := by
    have h1 := (hbig s R q d hs hg hR hrow).1.2
    have h2 := R.rank_add_five_le
    have h3 := R.m_add_three_le_k
    have h4 := R.two_le_m
    have hr : 6 ≤ R.r := by unfold Ranks.r; omega
    have ht : 11 ≤ R.t := by omega
    have h5 : 4 * 11 * 6 ≤ 4 * R.t * R.r := by gcongr
    omega
  have hmod := modRow_of_rowq (pairWin_self s) hn hd100 hrow
  obtain ⟨p, p', q0, hp, hp', hq0, hpp, hq0p, hq0p', mp, mp', mq0, lp, lp', lq0⟩ := hAux _ hN
  have hmono : ((4 * R.n * q * d : ℕ) : ℝ) ^ C8 ≤ ((4 * R.n * q * d : ℕ) : ℝ) ^ max C8 4 :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ 4 * R.n * q * d)) (le_max_left _ _)
  have kp := lp.trans hmono
  have kp' := lp'.trans hmono
  have kq0 := lq0.trans hmono
  push_cast at lp lp' lq0
  obtain ⟨g, hgi, hg01, hdisj⟩ := hG s R _ d hs hd hR hmod
  obtain ⟨T, t1, t2, t3, t4, t5, t6⟩ := hT s R hs hxe hR ho4
  have hlt' := hlt s R q d hs hh hrow
  have m15 : ∀ a : ℕ, a % (15 * (4 * R.n * q * d)) = 1 → a % 15 = 1 ∧ a % (4 * R.n * q * d) = 1 := fun a h =>
    mod_of_mod_lcm (by omega) (mod_lcm_of_mod_mul (by omega) h)
  have hodd : ∀ l ∈ ({g 0, g 1, p, p', q0} : Finset ℕ), l % 2 = 1 := by
    have o1 : ∀ a : ℕ, a % (4 * R.n * q * d) = 1 → a % 2 = 1 := fun a h => by
      rw [← Nat.mod_mod_of_dvd a (⟨2 * R.n * q * d, by ring⟩ : 2 ∣ 4 * R.n * q * d), h]
    have o2 : ∀ i, g i % 2 = 1 := fun i => by
      have h1 : p < g i := by exact_mod_cast (lp.trans_lt hlt').trans_le (hgi i).2.1
      have h2 := hp.two_le
      exact ((hgi i).1.eq_two_or_odd).resolve_left (by omega)
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl
    exacts [o2 0, o2 1, o1 _ (m15 _ mp).2, o1 _ (m15 _ mp').2, o1 _ mq0]
  obtain ⟨H0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := exists_host R q d ⌊s.x ^ (s.ez / 5)⌋₊ hyp
    (hbig s R q d hs hg hR hrow).1 (hbig s R q d hs hg hR hrow).2 h2e hinj
    (by rw [ho1, one_pow]; exact Nat.one_le_two_pow)
    (fun l hl h2 hle => by
      rw [← kronSym_of_odd _ (fun h => h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).1 h).symm)]
      refine hrow.2.2.2.2.2.2.2.2.2.1 l hl (((Nat.le_floor_iff ?_).1 hle).trans
        ((pairWin_self s).rpow_ez_le (by norm_num)))
      have := s.one_lt_alt
      positivity)
    g p p' q0 (fun i => (hgi i).1) hg01 hp hp' hpp ⟨(m15 p mp).1, (m15 p' mp').1⟩
    (fun i => ⟨fun h => by have := (hgi i).2.1; rw [← h] at this; linarith,
      fun h => by have := (hgi i).2.1; rw [← h] at this; linarith⟩)
    hodd T (Lwv s) t6 t1 t2 CT2
  subst e1 e2 e4 e5 e6 e9 e11
  have hQS : H0.QS = 4 * R.n := by
    rw [e12, show R.n = 2 ^ R.e from hord]; ring
  have hQR : (H0.QS : ℝ) = 4 * R.n := by exact_mod_cast hQS
  rw [← hQS] at hN hgi m15 mp mp' mq0 kp kp' kq0
  push_cast at kp kp' kq0
  obtain ⟨TT, tt1, tt2, hbad, hsh⟩ := hTops s R H0 hs hc hR hJ ho4 e3.ge
  have hnorm := fun i => GlobalTheory.T.norm_one_prime_elements R H0 (H0.QS * H0.q * H0.d) (H0.g i) (by omega) (hgi i).2.2.2
  have hgm : ∀ i, H0.g i % (H0.QS * H0.q * H0.d) = 1 := fun i =>
    (hnorm i).2.trans (Nat.mod_eq_of_lt (by omega))
  have hsplit := GlobalTheory.HostSplit.split_of_one_mod R H0
  have hpr : PairRow s.x s.eps H0 := by
    rw [pairRow_iff_rowq, hQS, Nat.mul_div_cancel_left _ (by norm_num)]
    exact hrow
  have hbH : BoxH { H0 with TT := TT } s.x s.eps := UpperTheory.box_bound_for_host R _ _ _ hinj e12 hbox
  have hcond : Real.log ((H0.QS : ℝ) * H0.q * H0.d) ≤ 3 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
    have := hmod.2.2.2.2.2
    rw [← hQS] at this
    push_cast at this
    exact this
  have h4 : (4 : ℝ) ≤ max C8 4 := le_max_right _ _
  refine ⟨{ H0 with TT := TT }, q0, rfl, rfl, hQS, rfl,
    ⟨⟨⟨s.x, pairWin_self s, hpr⟩, ⟨tt1, tt2⟩, t4, ⟨kp, kp'⟩, fun i => ⟨(hgi i).2.1, (hgi i).2.2.1⟩, e10, e8, e3.ge,
      hJ.trans h4, ho4.trans h4, hQR.trans_le (mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _))⟩,
    ⟨fun i => ?_, hgm, ⟨?_, ?_⟩, fun l hl => ?_⟩, ?_, ?_, hqd, ⟨s.x, pairWin_self s, hpr, hbox, hbH⟩, ?_,
    hThin s R _ hs hb hR ho4 hQR.le hcond hbH.realBox, hbad, hdisj,
    fun i => (hnorm i).1, ⟨mod_lcm_of_mod_mul H0.condN_pos mp, mod_lcm_of_mod_mul H0.condN_pos mp'⟩,
    ⟨hq0, mq0, kq0, hq0p, hq0p'⟩, e7⟩, hsh⟩
  · obtain ⟨π, h1, h2, -⟩ := (hnorm i).1
    exact ⟨π, h1, h2⟩
  · exact (GlobalTheory.HostSplit.ncard_placesOver H0.E hp).symm.trans (hsplit _ hp (m15 _ mp).2).1
  · exact (GlobalTheory.HostSplit.ncard_placesOver H0.E hp').symm.trans (hsplit _ hp' (m15 _ mp').2).1
  · have hl' : l ∈ H0.levelPrimes := hl
    rw [e7] at hl'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
    rcases hl' with rfl | rfl | rfl | rfl | rfl
    · exact (hsplit _ (hgi 0).1 (hgm 0)).2
    · exact (hsplit _ (hgi 1).1 (hgm 1)).2
    · exact (hsplit _ hp (m15 _ mp).2).2
    · exact (hsplit _ hp' (m15 _ mp').2).2
    · exact (hsplit _ hq0 mq0).2
  · rw [← e10] at t3
    exact t3
  · rw [← e10] at t5
    exact t5
  · refine (abs_dlogH_le { H0 with TT := TT } hqd).trans ?_
    rw [hs]
    exact hlog s.x hf

theorem hostEx : QDChoice → ThinChoice → NormPrimes → SmallPrimeOne → TopsChoice → HostEx := by
  intro hQD hThin hNP hSP hTops
  refine ⟨2, by norm_num, fun eps he he' => ?_⟩
  obtain ⟨C5, xa, hC5, hQD⟩ := hQD eps he he'
  obtain ⟨CT2, C8, c6, Cb, xb, hC8, hc6, hCb, h⟩ := exists_hostGood hThin hNP hSP hTops eps C5 he he' hC5
  obtain ⟨xc, hRk⟩ := exists_ranks_cyclic_frame eps he he'
  refine ⟨CT2, C8, C5, c6, Cb, max xa (max xb xc), hC8, hC5, hc6, hCb, Scales.univ 2 1 le_rfl, fun s hs hx hS => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨R, hR, h2e, hφ⟩ := hRk s hs hx.2.2
  obtain ⟨q, d, hrow, hqd, hbox⟩ := hQD s.x hx.1 R.n R.ord_pos (hs ▸ hR.1.2)
  rw [← hs] at hrow hqd hbox
  obtain ⟨H, q0, -, -, -, h1, h2, -⟩ := h s R q d hs hx.2.1 (by rw [Scales.mem_univ.1 hS]; norm_num) hR h2e hφ hrow hqd hbox
  exact ⟨R, H, q0, hR, h1, h2, trivial⟩

end GlobalTheory.EX.HostExist
end

section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_existence_of_choices : QDChoice → ThinChoice → NormPrimes → SmallPrimeOne → TopsChoice → HostEx := by
  first | exact @GlobalTheory.EX.HostExist.hostEx | exact GlobalTheory.EX.HostExist.hostEx | (intros; apply GlobalTheory.EX.HostExist.hostEx <;> assumption)
end
