import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestRawTail1Of
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LatticeCountingFormula
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.OtherStart

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem liftSubst_one_X {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O] (w : O) (r : ℕ)
    {ι : Type} {k : ℕ} (LL : LiftLetters ι) (v : ι × Fin k) :
    liftSubst p f O w r LL (1 : Matrix (Fin k) (Fin k) (WF p f)) (X v) =
      C (algebraMap O (KK O) (dW O w LL r v.1 v.2)) * X v := by
  unfold liftSubst
  rw [MvPolynomial.aeval_X, sigMat_one, inv_one]
  by_cases hv : LL.vec v.1 <;> simp [hv, Matrix.one_apply, dW] <;> split_ifs <;> simp_all

theorem liftSubst_one_hh {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (x : X.TT × Bool) (b : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
        (MvPolynomial.X (x, b)) =
      (if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then
        C (algebraMap O (KK O) w) * MvPolynomial.X (x, b) else MvPolynomial.X (x, b)) := by
  rw [liftSubst_one_X]
  have hd : dW O w (hhLetters X.TT) 1 x b =
      if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then w else 1 := rfl
  rw [hd]
  split_ifs <;> simp

private theorem liftSubst_X_true_zero_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), (0 : Fin (X.m + 1)))) = MvPolynomial.X ((y, true), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_true_succ_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), c.succ)) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, true), c.succ) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_zero_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), (0 : Fin (X.m + 1)))) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, false), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_succ_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), c.succ)) = MvPolynomial.X ((y, false), c.succ) := by
  rw [liftSubst_one_hh]
  simp

theorem key3One_S {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kSkey O X j i) =
      w • (MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0) +
        w ^ (X.p ^ (segDists X.TT j).get i - 1) • (∑ c : Fin X.m,
          MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
            MvPolynomial.X ((topOdd X j i, false), c.succ) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kSkey
  rw [map_sum, Fin.sum_univ_succ]
  simp only [map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X, liftSubst_X_false_zero_eq_C_mul_X, liftSubst_X_false_succ_eq_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  have hsum : ∑ c : Fin X.m, (C (algebraMap O (KK O) w) * MvPolynomial.X ((topStart X j, true), c.succ)) ^
      (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) =
      C (algebraMap O (KK O) w) ^ (q' + 1) * ∑ c : Fin X.m,
        MvPolynomial.X ((topStart X j, true), c.succ) ^ (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsum]
  ring

theorem key_lift_identity_lower {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kWkey O X j i c.succ) =
      w • (MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
        w ^ (X.p ^ (segDists X.TT j).get i - 1) •
          (MvPolynomial.X ((topOdd X j i, true), 0) *
            MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kWkey
  simp only [map_sub, map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  ring

theorem loc4One {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (locC O X c.succ) =
      ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
        w ^ (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1)) •
          (∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1) : RHH O X) := by
  unfold locC
  simp only [map_sub, map_prod, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, map_pow, map_pow,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _

def CoarseMultiplicityOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)),
      ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
        InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 ∧
        ∀ c : Fin X.m, InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c.succ) 1

def LocalOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0) 1

theorem third_key_of_order (h : CoarseMultiplicityOrderBound) : CoarseMultiplicityBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD j i
  exact ⟨fun g hg => h X O S hSq hD j i g hg, key3One_S S.w j i, fun c => key_lift_identity_lower S.w j i c⟩

theorem local_fourth_of_order (h : LocalOrderBound) : LocalBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD hn
  exact ⟨fun j0 g hg hr => h X O S hSq hD hn j0 g hg hr, fun c => loc4One S.w c⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem key_pow_dvd {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime) (w : A) (hw : w ^ 2 = (p : A)) (k e : ℕ)
    (u v : Fin (k + 1) → A) (M N' N : Fin (k + 1) → Fin (k + 1) → A)
    (hMN : ∀ b a, ∃ T, M b a ^ (p ^ e) = N' b a + p * T)
    (hinv : ∀ b b', ∑ a, N' b a * N a b' = if b = b' then 1 else 0)
    (hu : ∀ b, b ≠ 0 → w ∣ u b) (hv0 : w ∣ v 0) :
    w ∣ ∑ a, (∑ b, u b * M b a) ^ (p ^ e) * (∑ b', v b' * N a b') := by

  apply (Ideal.Quotient.eq_zero_iff_dvd w _).mp
  set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ
  have hw0 : φ w = 0 := (Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl
  have hp0 : φ (p : A) = 0 := by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]
  have hu0 : ∀ b, b ≠ 0 → φ (u b) = 0 := fun b hb => (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hu b hb)
  have hv0' : φ (v 0) = 0 := (Ideal.Quotient.eq_zero_iff_dvd w _).mpr hv0
  have hrow : ∀ a, φ (∑ b, u b * M b a) = φ (u 0) * φ (M 0 a) := by
    intro a
    have hz : ∀ i : Fin k, φ (u i.succ) = 0 := fun i => hu0 _ (Fin.succ_ne_zero _)
    rw [map_sum, Fin.sum_univ_succ, map_mul]
    simp [hz]
  have hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a) := by
    intro a
    obtain ⟨T, hT⟩ := hMN 0 a
    rw [← map_pow, hT, map_add, map_mul, hp0, zero_mul, add_zero]
  have hδ : ∀ b', ∑ a, φ (N' 0 a) * φ (N a b') = if (0 : Fin (k + 1)) = b' then 1 else 0 := by
    intro b'
    have h := congrArg φ (hinv 0 b')
    rw [map_sum] at h
    simp_rw [map_mul] at h
    rw [h]
    split_ifs <;> simp
  rw [map_sum]
  simp_rw [map_mul, map_pow, hrow, mul_pow, hpow, map_sum, map_mul]
  have e : ∑ a, φ (u 0) ^ (p ^ e) * φ (N' 0 a) * ∑ b', φ (v b') * φ (N a b') =
      φ (u 0) ^ (p ^ e) * ∑ b', φ (v b') * ∑ a, φ (N' 0 a) * φ (N a b') := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e]
  simp_rw [hδ]
  simp [hv0']

theorem sigPow_mod' (p f : ℕ) [Fact p.Prime] (s : ℤ) : sigPow p f s = sigPow p f (s % (f : ℤ)) := by
  unfold sigPow
  rw [Int.emod_emod]

theorem segPos_val (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    (((segPos X.TT j i).val : ℕ) : ℤ) = (((segStart X.TT j).val : ℤ) + ((segDists X.TT j).get i : ℤ)) % (X.n' : ℤ) := by
  simp only [segPos, posAdd]
  push_cast
  rfl

theorem kS_ord (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hsq : S.SqP) (hD : D1num X)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 := by
  classical
  have hp : X.p.Prime := hD.1
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  set d := (segDists X.TT j).get i with hd
  set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0
  set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1
  let xs : X.TT × Bool := (topStart X j, true)
  let y : X.TT × Bool := (topOdd X j i, false)
  let A := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O
  let u : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)
  let v : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 y b) * MvPolynomial.X (y, b)
  let M : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))
  let N' : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))
  let N : Fin (X.m + 1) → Fin (X.m + 1) → A := fun a b => C (psiO X.p X.n' O s1 (g a b))

  have hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) =
      MvPolynomial.map (algebraMap O (KK O)) (∑ a, (∑ b, u b * M b a) ^ (X.p ^ d) * (∑ b', v b' * N a b')) := by
    unfold kSkey
    simp only [map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs a rfl,
      liftSubst_X_cov X.p X.n' O S.w (hhLetters X.TT) 1 g y a rfl]
    simp only [u, v, M, N, map_sum, map_mul, map_C, map_X, sigMat_apply]
    rfl

  have hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T := by
    intro b a
    obtain ⟨τ, hτ⟩ := frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)
    have e1 : (s0 + d - s0).toNat = d := by omega
    rw [e1] at hτ
    have e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1 := by
      rw [sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]
      congr 1
      simp only [hs0, hs1, topStart, topOdd]
      rw [segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [e2] at hτ
    refine ⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩
    have := congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast] at this
    simp only [M, N', psiO, RingHom.comp_apply]
    linear_combination this

  have hinv : ∀ b b', ∑ a, N' b a * N a b' = if b = b' then 1 else 0 := by
    intro b b'
    have h1 : ∑ a, N' b a * N a b' = C (psiO X.p X.n' O s1 ((g⁻¹ * g) b b')) := by
      simp only [N', N, ← map_mul, ← map_sum, Matrix.mul_apply]
    rw [h1, Matrix.nonsing_inv_mul g hg, Matrix.one_apply]
    split_ifs <;> simp
  have hw : (C S.w : A) ^ 2 = (X.p : A) := by rw [← map_pow, hsq, map_natCast]
  have hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 xs b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, xs, this]
    exact ⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩
  have hv0 : (C S.w : A) ∣ v 0 := by
    have : dW O S.w (hhLetters X.TT) 1 y (0 : Fin (X.m + 1)) = S.w := by simp [dW, hhLetters, y]
    exact ⟨MvPolynomial.X (y, 0), by simp only [v, this]⟩
  obtain ⟨Q, hQ⟩ := key_pow_dvd X.p hp (C S.w : A) hw X.m d u v M N' N hMN hinv hu hv0
  unfold InWjRg
  rw [hlift, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

theorem key_minor_dvd {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime) (w : A) (hw : w ^ 2 = (p : A)) (k e : ℕ)
    (u u' : Fin (k + 1) → A) (M N' : Fin (k + 1) → Fin (k + 1) → A)
    (hMN : ∀ b a, ∃ T, M b a ^ (p ^ e) = N' b a + p * T)
    (hu : ∀ b, b ≠ 0 → w ∣ u b) (hu' : ∀ b, b ≠ 0 → w ∣ u' b) (c : Fin (k + 1)) :
    w ∣ (∑ b, u' b * N' b c) * (∑ b, u b * M b 0) ^ (p ^ e) - (∑ b, u' b * N' b 0) * (∑ b, u b * M b c) ^ (p ^ e) := by

  apply (Ideal.Quotient.eq_zero_iff_dvd w _).mp
  set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ
  have hw0 : φ w = 0 := (Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl
  have hp0 : φ (p : A) = 0 := by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]
  have hrow : ∀ (x : Fin (k + 1) → A) (Q : Fin (k + 1) → Fin (k + 1) → A), (∀ b, b ≠ 0 → w ∣ x b) →
      ∀ a, φ (∑ b, x b * Q b a) = φ (x 0) * φ (Q 0 a) := by
    intro x Q hx a
    have hz : ∀ i : Fin k, φ (x i.succ) = 0 := fun i =>
      (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hx _ (Fin.succ_ne_zero _))
    rw [map_sum, Fin.sum_univ_succ, map_mul]
    simp [hz]
  have hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a) := by
    intro a
    obtain ⟨T, hT⟩ := hMN 0 a
    rw [← map_pow, hT, map_add, map_mul, hp0, zero_mul, add_zero]
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, hrow u' N' hu' c, hrow u M hu 0, hrow u' N' hu' 0,
    hrow u M hu c, mul_pow, mul_pow, hpow 0, hpow c]
  ring

theorem kW_ord (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hsq : S.SqP) (hD : D1num X)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (c : Fin (X.m + 1)) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c) 1 := by
  classical
  have hp : X.p.Prime := hD.1
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  set d := (segDists X.TT j).get i with hd
  set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0
  set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1
  let xs : X.TT × Bool := (topStart X j, true)
  let z : X.TT × Bool := (topOdd X j i, true)
  let A := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O
  let u : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)
  let u' : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 z b) * MvPolynomial.X (z, b)
  let M : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))
  let N' : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))
  have hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c) =
      MvPolynomial.map (algebraMap O (KK O)) ((∑ b, u' b * N' b c) * (∑ b, u b * M b 0) ^ (X.p ^ d) -
        (∑ b, u' b * N' b 0) * (∑ b, u b * M b c) ^ (X.p ^ d)) := by
    unfold kWkey
    simp only [map_sub, map_mul, map_pow]
    rw [liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z c rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs 0 rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z 0 rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs c rfl]
    simp only [u, u', M, N', map_sum, map_mul, map_C, map_X, sigMat_apply]
    rfl
  have hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T := by
    intro b a
    obtain ⟨τ, hτ⟩ := frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)
    have e1 : (s0 + d - s0).toNat = d := by omega
    rw [e1] at hτ
    have e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1 := by
      rw [sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]
      congr 1
      simp only [hs0, hs1, topStart, topOdd]
      rw [segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [e2] at hτ
    refine ⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩
    have := congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast] at this
    simp only [M, N', psiO, RingHom.comp_apply]
    linear_combination this
  have hw : (C S.w : A) ^ 2 = (X.p : A) := by rw [← map_pow, hsq, map_natCast]
  have hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 xs b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, xs, this]
    exact ⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩
  have hu' : ∀ b, b ≠ 0 → (C S.w : A) ∣ u' b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 z b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, z, this]
    exact ⟨MvPolynomial.X (z, b), by simp only [u', this]⟩
  obtain ⟨Q, hQ⟩ := key_minor_dvd X.p hp (C S.w : A) hw X.m d u u' M N' hMN hu hu' c
  unfold InWjRg
  rw [hlift, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

theorem key3Ord : CoarseMultiplicityOrderBound := by
  intro X _ O _ _ _ _ S hsq hD j i g hg
  exact ⟨kS_ord X O S hsq hD j i g hg, fun c => kW_ord X O S hsq hD j i g hg c.succ⟩


end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  ∑ b : Fin (X.m + 1), C (dW O w (hhLetters X.TT) 1 (topStart X j, true) b) * MvPolynomial.X ((topStart X j, true), b) *
    C (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ b a))

def locExpr (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j0 : Fin (numSeg X.TT)) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O :=
  xvL X O w g j0 0 * ∏ c : Fin X.m, (∏ j : Fin (numSeg X.TT), xvL X O w g j 0 ^ (X.p ^ segG X.TT j - 1) -
    ∏ j : Fin (numSeg X.TT), xvL X O w g j c.succ ^ (X.p ^ segG X.TT j - 1))

theorem liftSubst_start (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (MvPolynomial.X ((topStart X j, true), a)) =
      MvPolynomial.map (algebraMap O (KK O)) (xvL X O w g j a) := by
  rw [liftSubst_X_vec X.p X.n' O w (hhLetters X.TT) 1 g hg (topStart X j, true) a rfl]
  simp only [xvL, map_sum, map_mul, map_C, map_X, sigMat_apply]
  rfl

theorem locR_lift (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (j0 : Fin (numSeg X.TT)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) g (locR O X j0) =
      MvPolynomial.map (algebraMap O (KK O)) (locExpr X O w g j0) := by
  unfold locR locC locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, liftSubst_start X O w g hg]

def LocalDivisibilityBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      (C S.w : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O) ∣ locExpr X O S.w g j0

theorem loc4Ord_of (h : LocalDivisibilityBound) : LocalOrderBound := by
  intro X _ O _ _ _ _ S hS hD h2 j0 g hg hpl
  obtain ⟨Q, hQ⟩ := h X O S hS hD h2 j0 g hg hpl
  unfold InWjRg
  rw [locR_lift X O S.w g hg j0, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def psiRes (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    O ⧸ Ideal.span {w} :=
  Ideal.Quotient.mk (Ideal.span {w}) (psiO X.p X.n' O ((topStart X j : X.TT).val.val : ℤ) (g⁻¹ 0 a))

def LocalResidueBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      psiRes X O S.w g j0 0 = 0 ∨ ∃ c : Fin X.m,
        ∏ j : Fin (numSeg X.TT), psiRes X O S.w g j 0 ^ (X.p ^ segG X.TT j - 1) =
          ∏ j : Fin (numSeg X.TT), psiRes X O S.w g j c.succ ^ (X.p ^ segG X.TT j - 1)

theorem map_xvL (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (j : Fin (numSeg X.TT)) (a : Fin (X.m + 1)) :
    map (Ideal.Quotient.mk (Ideal.span {w})) (xvL X O w g j a) =
      C (psiRes X O w g j a) * MvPolynomial.X ((topStart X j, true), 0) := by
  have hw0 : Ideal.Quotient.mk (Ideal.span {w}) w = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w)
  unfold xvL psiRes
  rw [map_sum, Finset.sum_eq_single 0]
  · simp [Formalism.MainNotions.LemmaBAlt.dW, Formalism.MainNotions.ColumnSystems.hhLetters]
    try ring
  · intro b _ hb
    have hb1 : 1 ≤ b.val := Nat.one_le_iff_ne_zero.mpr (fun h => hb (Fin.ext h))
    simp [Formalism.MainNotions.LemmaBAlt.dW, Formalism.MainNotions.ColumnSystems.hhLetters, hb1, hw0]
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem loc4Div_of (h : LocalResidueBound) : LocalDivisibilityBound := by
  intro X _ O _ _ _ _ S hS hD hn j0 g hg hne
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero (Ideal.Quotient.mk (Ideal.span {S.w})) S.w
    (fun x => by rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton])]
  unfold locExpr
  simp only [map_mul, map_prod, map_sub, map_pow, map_xvL]
  rcases h X O S hS hD hn j0 g hg hne with h0 | ⟨c, hc⟩
  · rw [h0]
    simp
  · apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [hc, sub_self]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

def psiRes0 (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (a : Fin (X.m + 1)) : O ⧸ Ideal.span {w} :=
  Ideal.Quotient.mk (Ideal.span {w}) (psiO X.p X.n' O 0 (g⁻¹ 0 a))

def ResPowAt : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (a : Fin (X.m + 1)),
      (∀ j : Fin (numSeg X.TT), psiRes X O S.w g j a = psiRes0 X O S.w g a ^ (X.p ^ (segStart X.TT j).val)) ∧
      psiRes0 X O S.w g a ^ (X.p ^ X.n') = psiRes0 X O S.w g a

def ResTelAt : Prop :=
  ∀ (X : Loc) (K : Type) [Field K] (y : K), D1num X → 2 ≤ numSeg X.TT → y ≠ 0 → y ^ (X.p ^ X.n') = y →
    ∏ j : Fin (numSeg X.TT), (y ^ (X.p ^ (segStart X.TT j).val)) ^ (X.p ^ segG X.TT j - 1) = 1

def ResLineAt : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 → psiRes0 X O S.w g 0 ≠ 0 →
      ∃ c : Fin X.m, psiRes0 X O S.w g c.succ ≠ 0

theorem loc4Res_of (hP : ResPowAt) (hT : ResTelAt) (hL : ResLineAt) : LocalResidueBound := by
  intro X _ O _ _ _ _ S hS hD hseg j0 g hg hrat
  haveI : (Ideal.span {S.w}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer S.w).mp S.w_irr]
    exact IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ Ideal.span {S.w}) := Ideal.Quotient.field _
  by_cases h0 : psiRes0 X O S.w g 0 = 0
  · left
    rw [(hP X O S hS hD g 0).1 j0, h0, zero_pow (pow_ne_zero _ (Fact.out : X.p.Prime).ne_zero)]
  · right
    obtain ⟨c, hc⟩ := hL X O S hS hD g hg hrat h0
    refine ⟨c, ?_⟩
    have e0 := (hP X O S hS hD g 0).1
    have ec := (hP X O S hS hD g c.succ).1
    simp only [e0, ec]
    exact (hT X _ _ hD hseg h0 (hP X O S hS hD g 0).2).trans
      (hT X _ _ hD hseg hc (hP X O S hS hD g c.succ).2).symm

theorem resPowAt : ResPowAt := by
  intro X _ O _ _ _ _ S hS hD g a
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  have hF := frobCong (p := X.p) (f := X.n') hf
  have hp0 : Ideal.Quotient.mk (Ideal.span {S.w}) (X.p : O) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, ← (show S.w ^ 2 = (X.p : O) from hS), pow_two]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have key : ∀ (s s' : ℤ), s ≤ s' → ∀ β : WF X.p X.n',
      Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O (sigPow X.p X.n' s β)) ^ (X.p ^ (s' - s).toNat) =
        Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O (sigPow X.p X.n' s' β)) := by
    intro s s' hs β
    obtain ⟨τ, hτ⟩ := hF s s' hs β
    have h1 := congrArg (fun z => Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O z)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast, hp0, zero_mul] at h1
    exact sub_eq_zero.1 h1
  constructor
  · intro j
    have := key 0 ((segStart X.TT j).val : ℤ) (by positivity) (g⁻¹ 0 a)
    simp only [sub_zero, Int.toNat_natCast] at this
    exact this.symm
  · have := key 0 (X.n' : ℤ) (by positivity) (g⁻¹ 0 a)
    simp only [sub_zero, Int.toNat_natCast] at this
    unfold psiRes0
    have e : sigPow X.p X.n' (X.n' : ℤ) = sigPow X.p X.n' 0 := by
      rw [sigPow_mod' X.p X.n' (X.n' : ℤ), Int.emod_self]
    show Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O (sigPow X.p X.n' 0 (g⁻¹ 0 a))) ^ (X.p ^ X.n') =
      Ideal.Quotient.mk (Ideal.span {S.w}) (algebraMap (WF X.p X.n') O (sigPow X.p X.n' 0 (g⁻¹ 0 a)))
    rw [this, e]

theorem resTelAt : ResTelAt := by
  intro X K _ y hD h2 hy hq
  have hn : 0 < X.n' := by have := hD.2.2.1; omega
  have hper : ∀ s, y ^ (X.p ^ (s + X.n')) = y ^ (X.p ^ s) := by
    intro s
    rw [pow_add, pow_mul, ← pow_mul, mul_comm, pow_mul, hq]
  have hmod : ∀ s, y ^ (X.p ^ s) = y ^ (X.p ^ (s % X.n')) := by
    intro s
    conv_lhs => rw [← Nat.mod_add_div s X.n']
    induction s / X.n' with
    | zero => simp
    | succ t ih =>
      rw [Nat.mul_succ, ← add_assoc, hper, ih]
  have hnext : ∀ j : Fin (numSeg X.TT), ((segStart X.TT j).val + segG X.TT j) % X.n' = (segNext X.TT j).val := by
    intro j
    obtain ⟨e1, _⟩ := segG_eq X.TT h2 j
    rw [e1]
    unfold cdist
    have h1 := (segStart X.TT j).isLt
    have h2' := (segNext X.TT j).isLt
    rw [Nat.add_mod_mod]
    have : (segStart X.TT j).val + ((segNext X.TT j).val + X.n' - (segStart X.TT j).val) = (segNext X.TT j).val + X.n' := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt h2']
  set A : Fin (numSeg X.TT) → K := fun j => y ^ (X.p ^ (segStart X.TT j).val) with hA
  have hA0 : ∀ j, A j ≠ 0 := fun j => pow_ne_zero _ hy
  have hP0 : (∏ j, A j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hA0 j
  have hpow : ∀ j, A j ^ (X.p ^ segG X.TT j - 1) * A j = A (rot (numSeg X.TT) j) := by
    intro j
    have hge : 1 ≤ X.p ^ segG X.TT j := Nat.one_le_pow _ _ hD.1.pos
    rw [← pow_succ, Nat.sub_add_cancel hge]
    show (y ^ (X.p ^ (segStart X.TT j).val)) ^ (X.p ^ segG X.TT j) = y ^ (X.p ^ (segStart X.TT (rot _ j)).val)
    rw [← pow_mul, ← pow_add, hmod, hnext j, next_eq]
  have hprod : (∏ j, A j ^ (X.p ^ segG X.TT j - 1)) * ∏ j, A j = ∏ j, A j := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun j _ => hpow j]
    exact (rot_bij (numSeg X.TT)).prod_comp A
  exact mul_right_cancel₀ hP0 (by rw [hprod, one_mul])

theorem loc4Res_of_line (hL : ResLineAt) : LocalResidueBound :=
  loc4Res_of resPowAt resTelAt hL

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem psiRes0_ne {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
    (a : Fin (X.m + 1)) (h : WittVector.constantCoeff (g⁻¹ 0 a) ≠ 0) : psiRes0 X O S.w g a ≠ 0 := by
  intro h0
  unfold psiRes0 at h0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
  have hu : IsUnit (g⁻¹ 0 a) := WittVector.isUnit_of_coeff_zero_ne_zero _ h
  have hu' : IsUnit (psiO X.p X.n' O 0 (g⁻¹ 0 a)) := hu.map _
  exact S.w_irr.not_isUnit (isUnit_of_dvd_unit h0 hu')

theorem resLineAt : ResLineAt := by
  intro X _ O _ _ _ _ S _ _ g _ hne h0
  by_contra hall
  push_neg at hall
  apply hne
  have hcc : ∀ c : Fin X.m, WittVector.constantCoeff (g⁻¹ 0 c.succ) = 0 := by
    intro c
    by_contra hc
    exact psiRes0_ne S g c.succ hc (hall c)
  have hv0 : WittVector.constantCoeff (g⁻¹ 0 0) ≠ 0 := by
    intro hz
    apply h0
    unfold psiRes0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    by_cases hx : g⁻¹ 0 0 = 0
    · rw [hx, map_zero]
      exact dvd_zero _
    · obtain ⟨m, b, hb, hab⟩ := WittVector.exists_eq_pow_p_mul (g⁻¹ 0 0) hx
      have hm : m ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hab
        exact hb (hab ▸ hz)
      rw [hab, map_mul, map_pow, map_natCast]
      have hwp : S.w ∣ (X.p : O) := by
        have h1 := S.p_mem
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer S.w).mp S.w_irr,
          Ideal.mem_span_singleton] at h1
        exact h1
      exact Dvd.dvd.mul_right (dvd_pow hwp hm) _
  have hset : ∀ h : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'),
      ratPlane X.p X.n' 1 h =
        Submodule.span (GaloisField X.p X.n') {fun c => WittVector.constantCoeff (h⁻¹ 0 c)} := by
    intro h
    unfold ratPlane
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi0 : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [hi0]
    · rintro rfl
      exact ⟨0, by simp, rfl⟩
  rw [hset g, hset 1, inv_one]
  have hv : (fun c => WittVector.constantCoeff (g⁻¹ 0 c)) = WittVector.constantCoeff (g⁻¹ 0 0) •
      (fun c => WittVector.constantCoeff ((1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) 0 c)) := by
    funext c
    refine Fin.cases ?_ (fun c' => ?_) c
    · simp
    · simp [hcc c', Matrix.one_apply_ne (Fin.succ_ne_zero c').symm]
  rw [hv, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hv0)]

theorem loc4Res : LocalResidueBound := loc4Res_of_line resLineAt

end Formalism.MainNotions.ColumnSystems.Pf
end
end
