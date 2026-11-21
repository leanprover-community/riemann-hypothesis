import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEvenCubicalValuesNotMemMaximalIdealPowStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TPos

open Finset

theorem lagrange_decomp : ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ), (∀ i j, A i j = A j i) →
    (∀ v : Fin r → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (A i j : ℚ) * v j) →
    ∃ N : ℕ, 0 < N ∧ ∃ (k : ℕ) (n : Fin k → ℕ) (m : Fin k → Fin r → ℤ),
      ∀ i j, (N : ℤ) * A i j = ∑ l, (n l : ℤ) * m l i * m l j := by
  intro r
  induction r with
  | zero => intro A _ _; exact ⟨1, one_pos, 0, Fin.elim0, Fin.elim0, fun i => i.elim0⟩
  | succ r ih =>
    intro A hs hp
    have ha : 0 < A 0 0 := by
      have h := hp (fun i => if i = 0 then 1 else 0) (by
        intro h; have := congrFun h 0; simp at this)
      simpa [Fin.sum_univ_succ, Fin.succ_ne_zero] using h
    set a := A 0 0 with ha_def
    set c : Fin r → ℤ := fun j => A 0 j.succ with hc
    set S : Matrix (Fin r) (Fin r) ℤ := fun i j => a * A i.succ j.succ - c i * c j with hS
    have hSs : ∀ i j, S i j = S j i := by
      intro i j; simp only [hS]; rw [hs i.succ j.succ]; ring
    have hSp : ∀ v : Fin r → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (S i j : ℚ) * v j := by
      intro v hv
      set s : ℚ := ∑ j, (c j : ℚ) * v j with hs_def
      set Q : ℚ := ∑ i, ∑ j, v i * (A i.succ j.succ : ℚ) * v j with hQ
      have haq : (0:ℚ) < a := by exact_mod_cast ha
      have h1 : ∑ i, ∑ j, v i * (S i j : ℚ) * v j = a * Q - s * s := by
        have e : ∀ i j, v i * (S i j : ℚ) * v j
            = a * (v i * (A i.succ j.succ : ℚ) * v j) - ((c i : ℚ) * v i) * ((c j : ℚ) * v j) := by
          intro i j; rw [show S i j = a * A i.succ j.succ - c i * c j from rfl]; push_cast; ring
        rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e i j, hQ, hs_def,
          Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      set u : Fin (r+1) → ℚ := Fin.cons (-s / a) v with hu
      have hu0 : u ≠ 0 := by
        intro h; apply hv; funext j; have := congrFun h j.succ; simpa [hu] using this
      have h2 : ∑ i, ∑ j, u i * (A i j : ℚ) * u j = Q - s * s / a := by
        simp only [Fin.sum_univ_succ, hu, Fin.cons_zero, Fin.cons_succ]
        have e1 : ∑ j : Fin r, -s / a * (A 0 j.succ : ℚ) * v j = -s / a * s := by
          rw [hs_def, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by simp only [hc]; ring
        have e2 : ∑ i : Fin r, (v i * (A i.succ 0 : ℚ) * (-s / a) +
            ∑ j : Fin r, v i * (A i.succ j.succ : ℚ) * v j) = -s / a * s + Q := by
          rw [Finset.sum_add_distrib, hQ, hs_def, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => by rw [hs i.succ 0]; simp only [hc]; ring
        rw [e1, e2]
        field_simp
        ring
      have h3 := hp u hu0
      rw [h2] at h3
      rw [h1]
      have : a * Q - s * s = a * (Q - s * s / a) := by field_simp
      rw [this]; exact mul_pos haq h3
    obtain ⟨N', hN', k, n, m, hm⟩ := ih S hSs hSp
    refine ⟨N' * a.toNat, Nat.mul_pos hN' (by omega), k + 1, Fin.cons N' n,
      Fin.cons (fun j => A 0 j) (fun l => Fin.cons 0 (m l)), ?_⟩
    have haN : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha.le
    intro i j
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Nat.cast_mul, haN]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [ha_def]
    · simp [ha_def]
    · simp; rw [hs i.succ 0]; ring
    · simp only [Fin.cons_succ]
      rw [← hm i j]; simp only [hS, hc]; ring

theorem zpow_fsum {G I : Type} [CommGroup G] (a : G) (s : Finset I) (f : I → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem tensor_pos : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ z : Fin r → X, z ≠ 0 → ∃ s ∈ maximalIdeal R, ((∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s := by
  intro R _ _ _ _ _ X _ _ κ hneg hcub hmax r W hW z hz
  classical
  let B : X → X → (FractionRing R)ˣ := fun a b => κ (a + b) * (κ a)⁻¹ * (κ b)⁻¹
  have h0 : κ 0 = 1 := by
    have h := hcub 0 0 0
    simp only [add_zero] at h
    exact mul_left_cancel (a := κ 0 * κ 0 * κ 0) (by rw [_root_.mul_one]; exact h)
  have hB1 : ∀ a a' b, B (a + a') b = B a b * B a' b := by
    intro a a' b
    have e : κ (a + a' + b) = κ (a + a') * κ (a + b) * κ (a' + b) * (κ a * κ a' * κ b)⁻¹ := by
      rw [← hcub a a' b]; group
    simp only [B]; rw [e]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have := (κ a).ne_zero; have := (κ a').ne_zero; have := (κ b).ne_zero
    have := (κ (a + a')).ne_zero; have := (κ (a + b)).ne_zero; have := (κ (a' + b)).ne_zero
    field_simp
  have hBs : ∀ a b, B a b = B b a := by
    intro a b; simp only [B]; rw [add_comm]; exact mul_right_comm _ _ _
  have hB0 : ∀ b, B 0 b = 1 := by intro b; simp [B, h0]
  have hBd : ∀ a, B a a = κ a ^ 2 := by
    intro a
    have h := hB1 a (-a) a
    rw [add_neg_cancel, hB0] at h
    have hm : B (-a) a = (κ a)⁻¹ * (κ a)⁻¹ := by simp [B, h0, hneg]
    rw [hm] at h
    have := eq_inv_of_mul_eq_one_left h.symm
    rw [this]; group
  let f : X → Multiplicative X →* (FractionRing R)ˣ := fun w =>
    { toFun := fun a => B (Multiplicative.toAdd a) w
      map_one' := hB0 w
      map_mul' := fun a b => hB1 _ _ _ }
  have hBsum : ∀ (c : Fin r → ℤ) (w : X), B (∑ i, c i • z i) w = ∏ i, B (z i) w ^ c i := by
    intro c w
    have e : Multiplicative.ofAdd (∑ i, c i • z i) = ∏ i, (Multiplicative.ofAdd (z i)) ^ c i := by
      simp [ofAdd_sum, ofAdd_zsmul]
    have := congrArg (f w) e
    rw [map_prod] at this
    simp only [map_zpow] at this
    exact this
  have hBn : ∀ (M : ℕ) a w, B (M • a) w = B a w ^ M := by
    intro M a w
    induction M with
    | zero => simp [hB0]
    | succ M ih => rw [succ_nsmul, hB1, ih, pow_succ]
  have hQ : ∀ c : Fin r → ℤ,
      ∏ i, ∏ j, B (z i) (z j) ^ (c i * c j) = κ (∑ i, c i • z i) ^ 2 := by
    intro c
    rw [← hBd, hBsum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hBs, hBsum, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hBs, ← zpow_mul, mul_comm]

  set A : Matrix (Fin r) (Fin r) ℤ := W + W.transpose with hA
  have hAij : ∀ i j, A i j = W i j + W j i := fun i j => rfl
  have hAs : ∀ i j, A i j = A j i := fun i j => by rw [hAij, hAij, add_comm]
  have hApos : ∀ v : Fin r → ℚ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * (A i j : ℚ) * v j := by
    intro v hv
    have hv' : (fun i => (v i : ℝ)) ≠ 0 := by
      intro h; apply hv; funext i; have := congrFun h i; simpa using this
    have h := hW.dotProduct_mulVec_pos hv'
    have e : dotProduct (star (fun i => (v i : ℝ))) ((A.map (Int.cast : ℤ → ℝ)).mulVec (fun i => (v i : ℝ)))
        = ((∑ i, ∑ j, v i * (A i j : ℚ) * v j : ℚ) : ℝ) := by
      rw [Rat.cast_sum]
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, star_trivial,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Rat.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast; ring
    rw [e] at h
    exact_mod_cast h
  obtain ⟨N, hN, k, n, m, hm⟩ := lagrange_decomp r A hAs hApos
  set x : (FractionRing R)ˣ := ∏ i, ∏ j, B (z i) (z j) ^ W i j with hx
  have hx2 : x ^ 2 = ∏ i, ∏ j, B (z i) (z j) ^ A i j := by
    have e1 : ∏ i, ∏ j, B (z i) (z j) ^ A i j
        = (∏ i, ∏ j, B (z i) (z j) ^ W i j) * ∏ i, ∏ j, B (z i) (z j) ^ W j i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [hAij, zpow_add]
    have e2 : ∏ i, ∏ j, B (z i) (z j) ^ W j i = ∏ i, ∏ j, B (z i) (z j) ^ W i j := by
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      rw [hBs]
    rw [e1, e2, pow_two]
  let y : Fin k → X := fun l => ∑ i, m l i • z i
  have hxN : x ^ (2 * N) = ∏ l, κ (y l) ^ (2 * n l) := by
    calc x ^ (2 * N) = (x ^ 2) ^ N := pow_mul x 2 N
      _ = ∏ i, ∏ j, B (z i) (z j) ^ ((N : ℤ) * A i j) := by
        rw [hx2, ← Finset.prod_pow]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm]
      _ = ∏ i, ∏ j, ∏ l, (B (z i) (z j) ^ (m l i * m l j)) ^ (n l) := by
        refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
        rw [hm, zpow_fsum]
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
      _ = ∏ i, ∏ l, ∏ j, (B (z i) (z j) ^ (m l i * m l j)) ^ (n l) :=
        Finset.prod_congr rfl fun i _ => Finset.prod_comm
      _ = ∏ l, ∏ i, ∏ j, (B (z i) (z j) ^ (m l i * m l j)) ^ (n l) := Finset.prod_comm
      _ = ∏ l, κ (y l) ^ (2 * n l) := by
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [pow_mul, show y l = ∑ i, m l i • z i from rfl, ← hQ (m l)]
        simp only [Finset.prod_pow]
  have hs : ∀ l, ∃ t : R, ((κ (y l) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ t ∧
      (y l ≠ 0 → t ∈ maximalIdeal R) := by
    intro l
    by_cases h : y l = 0
    · exact ⟨1, by rw [h, h0]; simp, fun h' => absurd h h'⟩
    · obtain ⟨t, ht, e⟩ := hmax _ h; exact ⟨t, e, fun _ => ht⟩
  choose s hs1 hs2 using hs
  have hxK : ((x : (FractionRing R)ˣ) : FractionRing R) ^ (2 * N)
      = algebraMap R _ (∏ l, s l ^ (2 * n l)) := by
    rw [← Units.val_pow_eq_pow_val, hxN, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Units.val_pow_eq_pow_val, hs1, map_pow]
  have hint : IsIntegral R ((x : (FractionRing R)ˣ) : FractionRing R) :=
    IsIntegral.of_pow (by omega : 0 < 2 * N) (hxK ▸ isIntegral_algebraMap)
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have htN : t ^ (2 * N) = ∏ l, s l ^ (2 * n l) := by
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_pow, ht, hxK]
  have hdet : A.det ≠ 0 := by
    have h := hW.det_pos
    have e : (A.map (Int.cast : ℤ → ℝ)).det = ((A.det : ℤ) : ℝ) := by
      have := (Int.castRingHom ℝ).map_det A
      exact this.symm
    rw [e] at h
    exact_mod_cast h.ne'
  have hex : ∃ l, n l ≠ 0 ∧ y l ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hrow : ∀ i, ∑ j, ((N : ℤ) * A i j) • z j = 0 := by
      intro i
      simp_rw [hm i, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      have : ∑ j, ((n l : ℤ) * m l i * m l j) • z j = ((n l : ℤ) * m l i) • y l := by
        simp only [y, Finset.smul_sum, mul_smul]
      rw [this]
      by_cases hn : n l = 0
      · simp [hn]
      · rw [hcon l hn, smul_zero]
    have hcol : ∀ q, ((N : ℤ) * A.det) • z q = 0 := by
      intro q
      have h1 : ∑ i, A.adjugate q i • ∑ j, ((N : ℤ) * A i j) • z j = 0 := by
        simp [hrow]
      rw [← h1]
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have : ∀ j, ∑ i, A.adjugate q i * ((N : ℤ) * A i j) = (N : ℤ) * (A.adjugate * A) q j := by
        intro j; rw [Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp_rw [this, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply]
      simp [Finset.sum_ite_eq, mul_comm]
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hz
    have hq' : z q ≠ 0 := hq
    have hD : (N : ℤ) * A.det ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') hdet
    have hM : ((N : ℤ) * A.det).natAbs • z q = 0 := by
      rcases Int.natAbs_eq ((N : ℤ) * A.det) with h | h
      · rw [← natCast_zsmul, ← h]; exact hcol q
      · have := hcol q; rw [h, neg_smul, neg_eq_zero, natCast_zsmul] at this; exact this
    have hk1 : κ (z q) ^ (2 * ((N : ℤ) * A.det).natAbs) = 1 := by
      rw [pow_mul, ← hBd, ← hBn, hM, hB0]
    obtain ⟨s', hs', e'⟩ := hmax _ hq'
    have h1 : s' ^ (2 * ((N : ℤ) * A.det).natAbs) = 1 := by
      apply IsFractionRing.injective R (FractionRing R)
      rw [map_pow, ← e', map_one, ← Units.val_pow_eq_pow_val, hk1, Units.val_one]
    have hpos := Int.natAbs_pos.mpr hD
    have hunit : IsUnit s' := IsUnit.of_pow_eq_one h1 (by omega)
    exact (IsLocalRing.mem_maximalIdeal _).mp hs' hunit
  obtain ⟨l0, hn0, hy0⟩ := hex
  have hprod : ∏ l, s l ^ (2 * n l) ∈ maximalIdeal R := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l0)]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (hs2 l0 hy0) _ (by omega))
  refine ⟨t, ?_, ht.symm⟩
  exact (maximalIdeal.isMaximal R).isPrime.mem_of_pow_mem (2 * N) (htN ▸ hprod)

end GlobalTheory.Mum.TPos
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.even_cubical_tensor_posDef_form_positive : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (κ : X → (FractionRing R)ˣ), (∀ a, κ (-a) = κ a) → (∀ a a' b, κ (a + a' + b) * κ a * κ a' * κ b = κ (a + a') * κ (a + b) * κ (a' + b)) → (∀ a, a ≠ 0 → ∃ s ∈ maximalIdeal R, (κ a : FractionRing R) = algebraMap R _ s) → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ z : Fin r → X, z ≠ 0 → ∃ s ∈ maximalIdeal R, ((∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s := by
  first | exact @GlobalTheory.Mum.TPos.tensor_pos | exact GlobalTheory.Mum.TPos.tensor_pos | (intros; apply GlobalTheory.Mum.TPos.tensor_pos <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU

noncomputable section

namespace GlobalTheory.Mum.TensPos

theorem exists_bilin_lift {X A Q : Type} [AddCommGroup X] [Module.Free ℤ X] [AddCommGroup A] [AddCommGroup Q] (π : A →+ Q)
    (hπ : Function.Surjective π) (f : X → Q) (hn : ∀ a, f (-a) = f a)
    (hc : ∀ a a' b, f (a + a' + b) + f a + f a' + f b = f (a + a') + f (a + b) + f (a' + b)) :
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] A, ∀ x, π (B x x) = f x := by
  have h0 : f 0 = 0 := by
    have := hc 0 0 0
    simp only [add_zero] at this
    linear_combination (norm := abel) this
  have hadd : ∀ a a' b, QuadraticMap.polar f (a + a') b = QuadraticMap.polar f a b + QuadraticMap.polar f a' b := by
    intro a a' b
    simp only [QuadraticMap.polar]
    linear_combination (norm := abel) hc a a' b
  have hsm : ∀ (n : ℤ) a b, QuadraticMap.polar f (n • a) b = n • QuadraticMap.polar f a b := fun n a b =>
    map_zsmul (AddMonoidHom.mk' (fun a => QuadraticMap.polar f a b) (fun a a' => hadd a a' b)) n a
  have hxx : ∀ x, QuadraticMap.polar f x x = f x + f x := by
    intro x
    have := hsm (-1) x x
    rw [neg_one_zsmul, neg_one_zsmul, QuadraticMap.polar, neg_add_cancel, h0, hn] at this
    linear_combination (norm := abel) this
  have hq : ∀ (n : ℤ) x, f (n • x) = (n * n) • f x := by
    intro n x
    induction n using Int.induction_on with
    | zero => simp [h0]
    | succ n ih =>
      have := hsm n x x
      rw [hxx, QuadraticMap.polar, ih] at this
      rw [add_zsmul, one_zsmul]
      linear_combination (norm := module) this
    | pred n ih =>
      have := hsm (n : ℤ) x x
      rw [neg_zsmul, hn] at ih
      rw [hxx, QuadraticMap.polar, ih] at this
      rw [show (-(n : ℤ) - 1) = -((n : ℤ) + 1) by ring, neg_zsmul, hn, add_zsmul, one_zsmul]
      linear_combination (norm := module) this
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (QuadraticMap.ofPolar (R := ℤ) f hq hadd hsm)
  let b := Module.Free.chooseBasis ℤ X
  choose s hs using hπ
  let B' : X →ₗ[ℤ] X →ₗ[ℤ] A := b.constr ℤ fun i => b.constr ℤ fun j => s (B (b i) (b j))
  have e : B'.compr₂ π.toIntLinearMap = B := LinearMap.ext_basis b b fun i j => by
    simp [B', hs]
  refine ⟨B', fun x => ?_⟩
  have e1 := congrArg (fun C => C x x) e
  have e2 := congrArg (fun C => C x) hB
  exact e1.trans e2

theorem exists_exact {X G : Type} [AddCommGroup X] [Module.Free ℤ X] [CommGroup G] (H : Subgroup G) (a : X → G)
    (hn : ∀ x, ∃ u ∈ H, a (-x) = u * a x)
    (hc : ∀ x y w, ∃ u ∈ H, a (x + y + w) * a x * a y * a w = u * (a (x + y) * a (x + w) * a (y + w))) :
    ∃ B : X →ₗ[ℤ] X →ₗ[ℤ] Additive G, ∀ x, ∃ u ∈ H, a x = u * (B x x).toMul := by
  have h1 : ∀ u ∈ H, (QuotientGroup.mk' H) u = 1 := fun u hu => (QuotientGroup.eq_one_iff u).2 hu
  obtain ⟨B, hB⟩ := exists_bilin_lift (X := X) (MonoidHom.toAdditive (QuotientGroup.mk' H)) (QuotientGroup.mk'_surjective H)
    (fun x => Additive.ofMul (QuotientGroup.mk' H (a x)))
    (fun x => by
      obtain ⟨u, hu, e⟩ := hn x
      simp only [e, map_mul, h1 u hu, _root_.one_mul])
    (fun x y w => by
      obtain ⟨u, hu, e⟩ := hc x y w
      have := congrArg (QuotientGroup.mk' H) e
      simp only [map_mul, h1 u hu, _root_.one_mul] at this
      exact congrArg Additive.ofMul this)
  refine ⟨B, fun x => ⟨a x * ((B x x).toMul)⁻¹, ?_, by rw [inv_mul_cancel_right]⟩⟩
  have : QuotientGroup.mk' H (B x x).toMul = QuotientGroup.mk' H (a x) := congrArg Additive.toMul (hB x)
  rw [← QuotientGroup.eq_one_iff]
  show QuotientGroup.mk' H _ = 1
  rw [map_mul, map_inv, this, mul_inv_cancel]

def unitsK (R : Type) [CommRing R] : Subgroup (FractionRing R)ˣ :=
  (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range

theorem mem_of_unit {R : Type} [CommRing R] (I : Ideal R) {u x : (FractionRing R)ˣ} (hu : u ∈ unitsK R)
    (hx : ∃ s ∈ I, (x : FractionRing R) = algebraMap R _ s) : ∃ s ∈ I, ((u * x : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ s := by
  obtain ⟨v, rfl⟩ := hu
  obtain ⟨s, hs, e⟩ := hx
  exact ⟨v * s, I.mul_mem_left _ hs, by rw [Units.val_mul, e, map_mul]; rfl⟩

theorem scalars (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R]
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (a : X → (FractionRing R)ˣ)
    (hn : ∀ x, ∃ u ∈ unitsK R, a (-x) = u * a x)
    (hc : ∀ x y w, ∃ u ∈ unitsK R, a (x + y + w) * a x * a y * a w = u * (a (x + y) * a (x + w) * a (y + w)))
    (hp : ∀ x, x ≠ 0 → ∃ s ∈ maximalIdeal R, (a x : FractionRing R) = algebraMap R _ s)
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (hW : ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef)
    (a' : (Fin r → X) → (FractionRing R)ˣ)
    (h' : ∀ z, ∃ u ∈ unitsK R, a' z = u * ∏ i, ∏ j, (a (z i + z j) * (a (z i))⁻¹ * (a (z j))⁻¹) ^ W i j) :
    (∀ z, z ≠ 0 → ∃ s ∈ maximalIdeal R, (a' z : FractionRing R) = algebraMap R _ s) ∧
      ∀ n : ℕ, {z | ¬ ∃ s ∈ maximalIdeal R ^ n, (a' z : FractionRing R) = algebraMap R _ s}.Finite := by
  obtain ⟨B, hB⟩ := exists_exact (unitsK R) a hn hc
  choose u hu eu using hB
  let κ : X → (FractionRing R)ˣ := fun x => (B x x).toMul
  let κ' : (Fin r → X) → (FractionRing R)ˣ := fun z => ∏ i, ∏ j, (κ (z i + z j) * (κ (z i))⁻¹ * (κ (z j))⁻¹) ^ W i j
  have eκ' : ∀ z, Additive.ofMul (κ' z) = ∑ i, ∑ j, W i j • (B (z i) (z j) + B (z j) (z i)) := by
    intro z
    simp only [κ', κ, ofMul_prod, ofMul_zpow, ofMul_mul, ofMul_inv, ofMul_toMul, map_add, LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg _ ?_
    abel
  have κn : ∀ x, κ (-x) = κ x := fun x => by simp [κ]
  have κc : ∀ x y w, κ (x + y + w) * κ x * κ y * κ w = κ (x + y) * κ (x + w) * κ (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [κ, ofMul_mul, ofMul_toMul, map_add, LinearMap.add_apply]
    abel
  have κp : ∀ x, x ≠ 0 → ∃ s ∈ maximalIdeal R, (κ x : FractionRing R) = algebraMap R _ s := fun x hx => by
    have := mem_of_unit _ ((unitsK R).inv_mem (hu x)) (hp x hx)
    rwa [eu x, inv_mul_cancel_left] at this
  have κ'n : ∀ x, κ' (-x) = κ' x := fun x => by
    apply Additive.ofMul.injective
    simp [eκ']
  have κ'c : ∀ x y w, κ' (x + y + w) * κ' x * κ' y * κ' w = κ' (x + y) * κ' (x + w) * κ' (y + w) := fun x y w => by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, eκ', ← Finset.sum_add_distrib, ← smul_add, Pi.add_apply, map_add, LinearMap.add_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congrArg _ ?_
    abel
  have κ'p := GlobalTheory.T.even_cubical_tensor_posDef_form_positive R X κ κn κc κp W hW
  have κ't := GlobalTheory.T.finite_even_cubical_values_not_mem_maximalIdeal_pow R (Fin r → X) κ' κ'n κ'c κ'p
  have ea : ∀ z, ∃ v ∈ unitsK R, a' z = v * κ' z := fun z => by
    obtain ⟨v, hv, e⟩ := h' z
    refine ⟨v * ∏ i, ∏ j, (u (z i + z j) * (u (z i))⁻¹ * (u (z j))⁻¹) ^ W i j, mul_mem hv (prod_mem fun i _ => prod_mem fun j _ =>
      zpow_mem (mul_mem (mul_mem (hu _) (inv_mem (hu _))) (inv_mem (hu _))) _), ?_⟩
    rw [e, _root_.mul_assoc, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← mul_zpow, eu (z i + z j), eu (z i), eu (z j)]
    refine congrArg (· ^ W i j) (Additive.ofMul.injective ?_)
    simp only [κ, ofMul_mul, ofMul_inv]
    abel
  refine ⟨fun z hz => ?_, fun n => (κ't n).subset fun z hz hm => hz ?_⟩
  · obtain ⟨v, hv, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hv (κ'p z hz)
  · obtain ⟨v, hv, e⟩ := ea z
    rw [e]; exact mem_of_unit _ hv hm

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

open GlobalTheory.PsiScalUnit

def unitsS (z : (TK R).left) : Subgroup ((TK R).left.presheaf.stalk z)ˣ := (unitsK R).map (Units.map (ev z).toMonoidHom)

theorem gm_mem (z : (TK R).left) {Y : Scheme.{0}} (p : Spec (CommRingCat.of R) ⟶ Y) (U : Y.Opens)
    (h : p (closedPoint R) ∈ U) (s : Γ(Y, U)ˣ) : gm (Y := (TK R).left) (jK R ≫ p) z U s ∈ unitsS z := by
  have hle : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ p ⁻¹ᵁ U := fun y _ =>
    (IsLocalRing.specializes_closedPoint y).mem_open (p ⁻¹ᵁ U).isOpen h
  obtain ⟨u, hu⟩ := ev_unit z (res hle (pullU p U s))
  refine ⟨_, ⟨u, rfl⟩, Units.ext (hu.symm.trans (congrArg Units.val ?_))⟩
  exact (gm_res _ _ hle trivial _).trans (gm_pull (jK R) p z U (hle trivial) _)

theorem exists_int (P : PolAV (Spec (CommRingCat.of R))) (z : (TK R).left) : ∃ J, Good P.L z J ∧
    ∀ p : Spec (CommRingCat.of R) ⟶ P.A.left, p ≫ P.A.hom = 𝟙 _ → p (closedPoint R) ∈ P.L.U (J (jK R ≫ p)) := by
  have : IsDominant (jK R) := DVR.isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ P.A.left => exists_chart P.isLB (p (closedPoint R))
  obtain ⟨J, hJ, e⟩ := exists_good P.L P.isLB (Z := (TK R).left) z
    (K := {p : Spec (CommRingCat.of R) ⟶ P.A.left // p ≫ P.A.hom = 𝟙 _}) (fun p => jK R ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) P.A.hom
      (a.2.trans b.2.symm) (jK R) h))
    (fun p => (IsLocalRing.specializes_closedPoint (jK R z)).mem_open (p.1 ⁻¹ᵁ P.L.U (pick p.1)).isOpen (hpk p.1))
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

theorem val_mem (P : PolAV (Spec (CommRingCat.of R))) (z : (TK R).left) {J : ((TK R).left ⟶ P.A.left) → P.L.ι}
    (hJ : ∀ p : Spec (CommRingCat.of R) ⟶ P.A.left, p ≫ P.A.hom = 𝟙 _ → p (closedPoint R) ∈ P.L.U (J (jK R ≫ p)))
    (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A) (e : ℤ)
    (t : LB.Gen (LB.LinComb P.L (K := PUnit) (fun _ => c.left) (fun _ => e))) :
    val t (toUnit (TK R)).left z J ∈ unitsS z := by
  have := gm_mem z (𝟙 _) (LB.wchart P.L (fun _ : PUnit => c.left) (fun _ => J (jK R ≫ c.left)))
    (Set.mem_iInter.2 fun _ => hJ c.left (Over.w c)) (t.s (fun _ => J (jK R ≫ c.left)))
  rw [Category.comp_id] at this
  exact this

theorem scalar_tens {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} (T : Tens D D' W)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing R)ˣ) (h : PsiScal D ga a)
    (ga' : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (K := PUnit) (fun _ => (D'.c χ).left) (fun _ => -1)))
    (a' : D'.X → (FractionRing R)ˣ) (h' : PsiScal D' ga' a') (y : D'.X) :
    ∃ u ∈ unitsK R, a' y = u * ∏ i, ∏ j, (a (T.xe y i + T.xe y j) * (a (T.xe y i))⁻¹ * (a (T.xe y j))⁻¹) ^ W i j := by
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  obtain ⟨J, hJ, iJ⟩ := exists_int D.P z
  obtain ⟨J', hJ', iJ'⟩ := exists_int D'.P z
  let E : (FractionRing R)ˣ →* ((TK R).left.presheaf.stalk z)ˣ := Units.map (ev z).toMonoidHom
  have hE : Function.Injective E := Units.map_injective (ev_inj z)
  have hψ : ∀ χ, val (D.psi χ) (𝟙 _) z J = E (a χ) * val (ga χ) (toUnit (TK R)).left z J := fun χ =>
    Units.ext (((h χ).2 (TK R) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have hψ' : val (D'.psi y) (𝟙 _) z J' = E (a' y) * val (ga' y) (toUnit (TK R)).left z J' :=
    Units.ext (((h' y).2 (TK R) (𝟙 _) z J' hJ').trans (congrArg₂ (· * ·) (ev_eq z _) rfl))
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (toUnit (TK R)).left z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
  have mρ : val D.rigK (𝟙 _) z J ∈ unitsS z := vρ ▸ val_mem D.P z iJ η[D.P.A] 1 D.rig
  have mg : ∀ χ, val (ga χ) (toUnit (TK R)).left z J ∈ unitsS z := fun χ => val_mem D.P z iJ _ _ _
  have mg' : val (ga' y) (toUnit (TK R)).left z J' ∈ unitsS z := val_mem D'.P z iJ' _ _ _
  have mτ : ∀ b c : D.X, ∃ u ∈ unitsS z, val (D.tau b c) (𝟙 _) z J = u * E (a (b + c) * (a b)⁻¹ * (a c)⁻¹) := fun b c => by
    refine ⟨_, mul_mem (mul_mem (mul_mem (mg (b + c)) (inv_mem (mg b))) (inv_mem (mg c))) (inv_mem mρ), ?_⟩
    rw [vτ, hψ, hψ, hψ, map_mul, map_mul, map_inv, map_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  choose u hu eu using mτ
  have e := T.psi y z J J' hJ hJ'
  have hφ : ∀ k, tensφ T.pr k ≫ D.P.A.hom = D'.P.A.hom := by
    rintro ⟨⟨i, j⟩, k⟩
    fin_cases k <;> exact Over.w _
  have mw : gm (D'.xK y) z _ (T.w.s (fun k => J (D'.xK y ≫ tensφ T.pr k), J' (D'.xK y))) ∈ unitsS z := by
    refine gm_mem z (D'.c y).left
      (LB.wchart D.P.L (tensφ T.pr) (fun k => J (D'.xK y ≫ tensφ T.pr k)) ⊓ D'.P.L.U (J' (D'.xK y)))
      ⟨Set.mem_iInter.2 fun k => ?_, iJ' _ (Over.w _)⟩ _
    have := iJ ((D'.c y).left ≫ tensφ T.pr k) (by rw [Category.assoc, hφ]; exact Over.w _)
    rw [← Category.assoc] at this
    exact this
  rw [hψ'] at e
  simp only [eu, mul_zpow, Finset.prod_mul_distrib] at e
  obtain ⟨v, hv, ev'⟩ := mul_mem (mul_mem (inv_mem mg') mw)
    (prod_mem fun i (_ : i ∈ Finset.univ) => prod_mem fun j (_ : j ∈ Finset.univ) => zpow_mem (hu (T.xe y i) (T.xe y j)) (W i j))
  refine ⟨v, hv, hE ?_⟩
  rw [map_mul, map_prod]
  simp only [map_prod, map_zpow]
  rw [show E v = _ from ev', eq_mul_inv_of_mul_eq e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem psi_pos_tendsto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Tens D.toPre D' W → (∀ χ : D'.X, χ ≠ 0 → D'.PsiIn χ (maximalIdeal R)) ∧ ∀ n : ℕ, {χ : D'.X | ¬ D'.PsiIn χ (maximalIdeal R ^ n)}.Finite := by
  intro R _ _ _ hR D D' r W hW T
  obtain ⟨_, -, _, -⟩ := hR
  obtain ⟨ga, a, h⟩ := exists_psiScal R D.toPre
  obtain ⟨ga', a', h'⟩ := exists_psiScal R D'
  obtain ⟨hp, ht⟩ := scalars R D.toPre.X a
    (fun x => by
      obtain ⟨u, e⟩ := even_part D.toPre ga a h D.psi_even x
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x y w => by
      obtain ⟨u, e⟩ := cub_part D.toPre ga a h D.tau_bimult x y w
      exact ⟨_, ⟨u, rfl⟩, Units.ext e⟩)
    (fun x hx => by
      obtain ⟨s, hs, e⟩ := (PsiScalIn.main_local D.toPre ga a h x _).1 (D.psi_pos x hx)
      exact ⟨s, hs, e.symm⟩)
    W hW (fun z => a' (T.xe.symm z))
    (fun z => by simpa only [AddEquiv.apply_symm_apply] using scalar_tens T ga a h ga' a' h' (T.xe.symm z))
  refine ⟨fun χ hχ => ?_, fun n => ((ht n).preimage T.xe.injective.injOn).subset fun χ hχ hm => hχ ?_⟩
  · obtain ⟨s, hs, e⟩ := hp (T.xe χ) (fun h0 => hχ (T.xe.map_eq_zero_iff.1 h0))
    rw [AddEquiv.symm_apply_apply] at e
    exact (PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩
  · obtain ⟨s, hs, e⟩ := hm
    rw [AddEquiv.symm_apply_apply] at e
    exact (PsiScalIn.main_local D' ga' a' h' χ _).2 ⟨s, hs, e.symm⟩

end GlobalTheory.Mum.TensPos
end
end
