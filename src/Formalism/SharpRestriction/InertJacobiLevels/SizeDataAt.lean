import Formalism.SharpRestriction.InertJacobiLevels.RayPrimes

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField

section Norm

variable {R : Ranks} (H : Host R)

theorem conj_bE : H.conj (H.sqd) = - H.sqd := by
  have h1 := H.gal_sqd H.conj
  have h2 : H.gal H.conj = R.cc := H.galE_conjE
  rw [h2] at h1
  simpa [Formalism.HC.Frame.cc, c0] using h1

theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem bE_integral : IsIntegral ℤ (H.sqd) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (H.d : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  simp only [eq_intCast, Int.cast_natCast]
  linear_combination bE_sq H

def bO : 𝓞 H.E := ⟨H.sqd, bE_integral H⟩

theorem tnorm_of (x y : ℤ) (T M : ℕ) (hT : (T : ℤ) = (1 + M * x) ^ 2 + H.d * (M * y) ^ 2)
    (hM : M = H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2) : TNorm H T := by
  have hbc : ((bO H : 𝓞 H.E) : H.E) = H.sqd := rfl
  have hco : (((1 + (M : 𝓞 H.E) * ((x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H) : 𝓞 H.E)) : H.E) =
      1 + (M : H.E) * ((x : H.E) + (y : H.E) * H.sqd) := by
    rw [← hbc]; push_cast; rfl
  refine ⟨1 + (M : 𝓞 H.E) * ((x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H), ?_, ?_, ?_⟩
  · rw [hco]
    have hb : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ _
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) (add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) hb)))
  · rw [hco]
    have hT' : (T : H.E) = (1 + M * x) ^ 2 + H.d * (M * y) ^ 2 := by exact_mod_cast congrArg (Int.cast : ℤ → H.E) hT
    simp only [map_add, map_mul, map_one, map_natCast, map_intCast, conj_bE]
    rw [hT']
    linear_combination (-(M : H.E) ^ 2 * (y : H.E) ^ 2) * bE_sq H
  · rw [← hM, Ideal.mem_span_singleton]
    exact ⟨(x : 𝓞 H.E) + (y : 𝓞 H.E) * bO H, by ring⟩

end Norm

theorem exists_strictHenselian_absolutely_closed_local_ring (h : RayPrimes) {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1)) (N : ℕ) :
    ∃ T : ℕ, N < T ∧ T.Prime ∧ ∀ (u0 : (Rt s).A) (T' Lw : ℕ), TNorm (hostOf A u0 T' Lw) T := by
  have hM : 0 < 2 ^ (2 + 2) * A.q * A.d * (A.g0 * A.g1) ^ 2 := by
    have := A.hyp.1.pos; have := A.hyp.2.1.pos; have := A.first_prime_isPrime.pos; have := A.second_prime_isPrime.pos
    positivity
  obtain ⟨x, y, T, hN, hp, hT⟩ := h A.d _ N A.hyp.2.1 hM
  exact ⟨T, hN, hp, fun u0 T' Lw => tnorm_of (hostOf A u0 T' Lw) x y T _ hT rfl⟩

theorem scale_w''_bounds (sc : Scale) (n : ℕ) (hn : 1 ≤ n) : 0 ≤ sc.w'' n ∧ sc.w'' n ≤ sc.b := by
  have hx : 0 < sc.x := by linarith [sc.one_lt_alt]
  have hb : 0 < sc.b := Real.exp_pos _
  have hX : 1 ≤ sc.X' := Real.one_le_exp (by positivity)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : sc.w'' n = sc.b / (n * sc.X') := by
    simp only [Scale.w'', Scale.b', Scale.a]
    field_simp
  rw [e]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have h1 : (1 : ℝ) ≤ n * sc.X' := one_le_mul_of_one_le_of_one_le hn' hX
  nlinarith

def sizeDataOfAjZero (D : D7) (sc : Scale)
    (hTT : D.host.TT = ∅)
    (hAj : ∀ j w, D.what₂.Aj j w = 0)
    (hTu : ∀ u, sc.b ^ ((D.R.m : ℝ) / 2) ≤ ((D.mem u).A.T : ℝ))
    (hb : ∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ sc.b ^ 2)
    (hsplit : ⌊sc.x ^ (sc.ez / 5)⌋₊ ≤ D.host.splitBound)
    (ho : (D.R.o : ℝ) ≤ sc.x ^ (sc.eps / 100))
    (hQS : (D.host.QS : ℝ) ≤ 4 * D.R.n * sc.x ^ (sc.eps / 100))
    (j0 : ℕ) (hj0 : Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0)
    (hLw : 10 * j0 + 20 ≤ D.host.Lw)
    (η Cc : ℝ) (hη : 0 < η)
    (hthick : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ,
      (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
      sc.b ≤ wj D j τ ∧ wj D j τ ≤ sc.b + η + 1)
    (hthin : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) →
      sc.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ sc.w'' D.R.n + η)
    (hcg : ∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
      (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧
      (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ Cc * ((D.R.k : ℝ) * (4 * (D.s.Del : ℝ))))
    (hcv : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
      (((D.hc τ).v i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (hcu : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k →
      0 ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (hbe : ∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η)
    (hSc : 0 < (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)))
    (Ct : ℝ) (htw : 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ sc.x ^ Ct)
    (CGam : ℝ) (hCG : 0 < CGam)
    (hGam : ∀ u, Real.log (D.mem u).A.GamP = CGam * (D.R.m : ℝ) ^ 5 * D.R.f * sc.L)
    (LaG : ℝ) (hT2 : D.host.T2.card = 1) : SizeData₂ D where
  sc := sc
  aT := fun _ => 0
  aT_win := fun t => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  bT := fun _ => 0
  bT_ge := fun t => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  top_u := fun _ t _ _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  top_b := fun _ t _ _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  supp := ∅
  gain := fun _ _ => 0
  F := fun _ _ => 0
  E := fun _ _ _ => 0
  tau := fun _ => 0
  io := fun _ => 0
  gain_supp := fun _ _ _ => rfl
  F_supp := fun _ _ _ => rfl
  E_supp := fun _ _ _ _ => rfl
  tau_supp := fun _ _ => rfl
  io_supp := fun _ _ => rfl
  gain_g := fun _ _ _ => rfl
  b_le := hb
  untwisted := fun w _ j _ _ => ⟨hAj j w, rfl⟩
  not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
  drop := ∅
  drop_alt := fun _ => Set.notMem_empty _
  F_conj := fun _ _ => rfl
  F_above := by intros; rfl
  j0 := j0
  logFiveDepth_le := hj0
  weightLength_ge_depth := hLw
  logDerivativeAtOne := dlogL D 1
  logDerivative_at_one_eq := rfl
  split_tie := hsplit
  o_tie := ho
  QS_tie := hQS
  NuLat := fun _ => ⊤
  de2 := (D.host.T2.card : ℝ) / D.R.n
  thickDensity_pos := by
    have : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.toFrame.ord_pos
    rw [hT2]; positivity
  thickDensity_le_one := by
    have : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.toFrame.ord_pos
    rw [hT2, div_le_one (by linarith)]; simpa using this
  typeDensity_eq_card_div := rfl
  LaG := LaG
  Sc := (D.R.k : ℝ) * (4 * (D.s.Del : ℝ))
  etaSz := η
  Cc := Cc
  win_thick := hthick
  win_top := fun _ _ _ _ t _ => ((Finset.eq_empty_iff_forall_notMem.mp hTT) t.1 t.2).elim
  win_thin := hthin
  cloud_gap := hcg
  cloud_v := hcv
  cloud_u := hcu
  be_close := hbe
  Sc_pos := hSc
  Sc_eq := rfl
  etaSz_pos := hη
  TTw := fun _ => Finset.univ
  TTw_full := fun _ _ => rfl
  Ct := Ct
  t_win := htw
  CGam := CGam
  CGam_pos := hCG
  Gam_eq := hGam
  wPart := fun _ _ _ _ => 1
  wPart_ge := fun _ _ _ _ => le_rfl
  lenMN := fun _ _ => 0

theorem exists_odd (L : ℝ) (hL : 20 < L) : ∃ s : ℕ, L ≤ ((2 * s + 15 : ℕ) : ℝ) ∧ ((2 * s + 15 : ℕ) : ℝ) < L + 2 := by
  refine ⟨⌈(L - 15) / 2⌉₊, ?_, ?_⟩
  · have h := Nat.le_ceil ((L - 15) / 2)
    push_cast
    linarith
  · have h := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ (L - 15) / 2)
    push_cast
    linarith


end Formalism.MainNotions.Inhab

end
