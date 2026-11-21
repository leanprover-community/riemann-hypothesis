import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPower
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
import GroundTheory.PAdicHodge.SemilinearResidue
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangXRoot

section
section
namespace GlobalTheory.PMonE

theorem glOnto_zero_and_glCount_zero : GLOnto 0 ∧ GLCount 0 := by
  constructor
  · intro F _ _ _ _ p _ _ m _ _ e D he _ M hM b hb
    obtain ⟨x, hx, -⟩ := existsUnique_integral_gsum_eq F p m e D he M
      (fun i j => by simp [hM.top]) (fun n hn i j => hM.small n (by omega) i j) b hb
    exact ⟨x, hx⟩
  · intro F _ _ _ _ p _ _ m _ _ e D he _ M hM _
    obtain ⟨y, hy, huniq⟩ := existsUnique_integral_gsum_eq F p m e D he M
      (fun i j => by simp [hM.top]) (fun n hn i j => hM.small n (by omega) i j) 0 (fun i => by simp)
    rw [Nat.mul_zero, pow_zero, Nat.card_eq_one_iff_exists]
    exact ⟨⟨y, hy⟩, fun z => Subtype.ext (huniq z.1 z.2)⟩

end GlobalTheory.PMonE
end

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero : GLOnto 0 ∧ GLCount 0 := by
  atlas_forward_decl GlobalTheory.PMonE.glOnto_zero_and_glCount_zero
end

section
section
noncomputable section

namespace GlobalTheory.PMonE.LangOnto

open Polynomial Finset GlobalTheory.PMonE

def backPoly {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) (j : ℕ) : k[X] :=
  Nat.rec X (fun j P => P ^ q - C (c (n - j)) * X) j

theorem backPoly_zero {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) : backPoly q n c 0 = X := rfl

theorem backPoly_succ {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) (j : ℕ) :
    backPoly q n c (j + 1) = backPoly q n c j ^ q - C (c (n - j)) * X := rfl

theorem backPoly_natDegree {k : Type*} [Field k] {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (c : ℕ → k) :
    ∀ j, 1 ≤ (backPoly q n c j).natDegree := by
  intro j
  induction j with
  | zero => simp [backPoly_zero]
  | succ j ih =>
    have h1 : (C (c (n - j)) * X : k[X]).natDegree ≤ 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      simp
    have h2 : 2 ≤ (backPoly q n c j ^ q).natDegree := by
      rw [natDegree_pow]; nlinarith
    rw [backPoly_succ, natDegree_sub_eq_left_of_natDegree_lt (by omega)]
    omega

theorem exists_sub_eq_inv {k : Type*} [Field k] [IsAlgClosed k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {q : ℕ} (hq : 2 ≤ q) (ψ : V →+ V)
    (hψ : ∀ (c : k) (x : V), ψ (c ^ q • x) = c • ψ x) (z : V) : ∃ y, y - ψ y = z := by
  obtain ⟨m, ⟨c, hrel⟩, -⟩ := GroundTheory.PAdicHodge.SemilinearResidue.exists_rel k (fun i => (⇑ψ)^[i] z)
  cases m with
  | zero => exact ⟨0, by simpa using hrel.symm⟩
  | succ n =>
    have hdeg : (backPoly q n c (n + 1) - C 1).degree ≠ 0 := by
      rw [degree_sub_C (natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1)))]
      exact (natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1))).ne'
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
    set u : ℕ → k := fun i => (backPoly q n c (n - i)).eval t with hu
    have h0 : u 0 ^ q = 1 + c 0 * t := by
      have := ht.eq_zero
      simp only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, Nat.sub_self] at this
      simp only [hu, Nat.sub_zero]
      linear_combination this
    have hn : u n = t := by simp [hu, backPoly_zero]
    have hs : ∀ i ∈ range n, u (i + 1) ^ q = u i + c (i + 1) * t := by
      intro i hi
      have hi' : i < n := mem_range.mp hi
      have e1 : n - i = (n - (i + 1)) + 1 := by omega
      have e2 : n - (n - (i + 1)) = i + 1 := by omega
      simp only [hu]
      rw [e1]
      simp only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, e2]
      ring
    have hit : ∀ i, ψ ((⇑ψ)^[i] z) = (⇑ψ)^[i + 1] z := fun i =>
      (Function.iterate_succ_apply' _ _ _).symm
    refine ⟨∑ i ∈ range (n + 1), u i ^ q • (⇑ψ)^[i] z, ?_⟩
    rw [map_sum]
    simp_rw [hψ, hit]
    have hA : ∑ i ∈ range n, u (i + 1) ^ q • (⇑ψ)^[i + 1] z
        = ∑ i ∈ range n, (u i + c (i + 1) * t) • (⇑ψ)^[i + 1] z :=
      sum_congr rfl (fun i hi => by rw [hs i hi])
    rw [sum_range_succ (fun i => u i • (⇑ψ)^[i + 1] z), hn, hrel, smul_sum, sum_range_succ' _ n,
      sum_range_succ' (fun i => t • c i • (⇑ψ)^[i] z) n, hA, h0]
    simp only [Function.iterate_zero, id, smul_smul, add_smul, sum_add_distrib, one_smul, mul_comm t]
    abel

theorem exists_sol {F : Type*} [Field F] [IsAlgClosed F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] {m : Type*}
    [Fintype m] {e : ℕ} (he : 0 < e) (A : Matrix m m F) (b : m → F) :
    ∃ x : m → F, ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  have : ExpChar F p := ExpChar.prime hp.out
  have hq : 2 ≤ p ^ e := GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he
  let r : F ≃+* F := (iterateFrobeniusEquiv F p e).symm
  have hr : ∀ a : F, r a ^ p ^ e = a := fun a => by
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv F p e).apply_symm_apply a
  have hr' : ∀ a : F, r (a ^ p ^ e) = a := fun a => by
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv F p e).symm_apply_apply a
  let ψ : (m → F) →+ (m → F) := AddMonoidHom.mk' (fun y => A.mulVec (fun i => r (y i))) (fun y y' => by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp)
  have hψ : ∀ (c : F) (x : m → F), ψ (c ^ p ^ e • x) = c • ψ x := by
    intro c x
    change A.mulVec _ = c • A.mulVec _
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hr']
  obtain ⟨y, hy⟩ := exists_sub_eq_inv hq ψ hψ b
  refine ⟨fun i => r (y i), fun i => ?_⟩
  rw [hr, ← hy]
  rfl

theorem lang_onto : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F,
    (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b →
      ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  intro F _ _ _ p _ _ m _ _ e he A hA b hb
  obtain ⟨x, hx⟩ := exists_sol p he A b
  refine ⟨x, ?_, hx⟩
  have hq : 2 ≤ p ^ e := GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he
  intro i₀
  by_contra hlt
  push Not at hlt
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun j => ‖x j‖) ⟨i₀, mem_univ _⟩
  have hR : 1 < ‖x i‖ := hlt.trans_le (hi i₀ (mem_univ _))
  have h1 : ‖A.mulVec x i‖ ≤ ‖x i‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun j _ => ?_)
    rw [norm_mul]
    calc ‖A i j‖ * ‖x j‖ ≤ 1 * ‖x j‖ := mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
      _ ≤ ‖x i‖ := by rw [one_mul]; exact hi j (mem_univ _)
  have h2 : x i ^ p ^ e = b i + A.mulVec x i := by rw [← hx i]; ring
  have h3 : ‖x i‖ ^ p ^ e ≤ ‖x i‖ := by
    rw [← norm_pow, h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hb i).trans hR.le) h1)
  have h4 : ‖x i‖ ^ 1 < ‖x i‖ ^ p ^ e := pow_lt_pow_right₀ hR (by omega)
  rw [pow_one] at h4
  linarith

end GlobalTheory.PMonE.LangOnto

end
end

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_solution_frobenius_sub_mulVec_eq : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b → ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  atlas_forward_decl GlobalTheory.PMonE.LangOnto.lang_onto
end

section
section
noncomputable section

namespace GlobalTheory.PMonE

open Polynomial

theorem langCount_card_fixed (F : Type) [Field F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (e : ℕ) (he : 0 < e) : Nat.card {c : F // c ^ p ^ e = c} = p ^ e := by
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  have hsep : (X ^ p ^ e - X : F[X]).Separable := galois_poly_separable p (p ^ e) (dvd_pow_self p he.ne')
  have hdeg : (X ^ p ^ e - X : F[X]).natDegree = p ^ e := FiniteField.X_pow_card_sub_X_natDegree_eq F hq
  have hne : (X ^ p ^ e - X : F[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hq
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := F) hsep (IsAlgClosed.splits_domain _)
  rw [hdeg] at hcard
  have h2 : Nat.card ((X ^ p ^ e - X : F[X]).rootSet F) = p ^ e := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)).trans h2
  rw [Polynomial.mem_rootSet_of_ne hne]
  simp [sub_eq_zero]

theorem langCount_integral {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (q : ℕ) (hq : 1 < q) (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (x : m → F)
    (hx : ∀ i, x i ^ q = A.mulVec x i) : Integral x := by
  by_contra hcon
  simp only [Integral, not_forall, not_le] at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖x j‖) ⟨i₀, Finset.mem_univ _⟩
  have hgt : 1 < ‖x i‖ := lt_of_lt_of_le hi₀ (hi i₀ (Finset.mem_univ _))
  have hle : ‖x i‖ ^ q ≤ ‖x i‖ := by
    rw [← norm_pow, hx i]
    simp only [Matrix.mulVec, dotProduct]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j _
    rw [norm_mul]
    calc ‖A i j‖ * ‖x j‖ ≤ 1 * ‖x i‖ :=
          mul_le_mul (hA i j) (hi j (Finset.mem_univ _)) (norm_nonneg _) zero_le_one
      _ = ‖x i‖ := one_mul _
  have hlt : ‖x i‖ < ‖x i‖ ^ q := lt_self_pow₀ hgt hq
  linarith

theorem langCount_card_semilinear (F : Type) [Field F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (e : ℕ) (he : 0 < e) {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : V →+ V)
    (hΦ : ∀ (a : F) (v : V), Φ (a • v) = a ^ p ^ e • Φ v) (hinj : Function.Injective Φ) :
    Nat.card {v : V // Φ v = v} = (p ^ e) ^ Module.finrank F V := by
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  obtain ⟨b, hb⟩ := LangIsogenyConstruction.lang_basis (p ^ e) hq Φ hΦ hinj
  have hkey : ∀ v, b.equivFun (Φ v) = fun i => b.equivFun v i ^ p ^ e := by
    intro v
    have hv : Φ v = b.equivFun.symm (fun i => b.equivFun v i ^ p ^ e) := by
      conv_lhs => rw [← b.sum_equivFun v]
      rw [map_sum, Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΦ, hb]
    rw [hv, LinearEquiv.apply_symm_apply]
  have e1 : {v : V // Φ v = v} ≃
      {c : Fin (Module.finrank F V) → F // ∀ i, c i ^ p ^ e = c i} :=
    b.equivFun.toEquiv.subtypeEquiv fun v => by
      constructor
      · intro h i
        have := congrFun (hkey v) i
        rw [h] at this
        exact this.symm
      · intro h
        apply b.equivFun.injective
        rw [hkey v]
        funext i
        exact h i
  rw [Nat.card_congr (e1.trans (Equiv.subtypePiEquivPi (p := fun _ c => c ^ p ^ e = c))), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _),
    Fintype.card_fin, langCount_card_fixed F p e he]

theorem langCount : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e →
    ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → A.det ≠ 0 →
    (∀ x : m → F, (∀ i, x i ^ p ^ e = A.mulVec x i) → Integral x) ∧
    Nat.card {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} = (p ^ e) ^ Fintype.card m := by
  intro F _ _ _ p _ _ m _ _ e he A hA hdet
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  refine ⟨fun x hx => langCount_integral (p ^ e) hq A hA x hx, ?_⟩
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  let Φ : (m → F) →+ (m → F) := AddMonoidHom.mk' (fun x => A⁻¹.mulVec (fun i => x i ^ p ^ e)) (by
    intro a b
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp only [Pi.add_apply]
    rw [add_pow_char_pow])
  have hΦ : ∀ (c : F) (v : m → F), Φ (c • v) = c ^ p ^ e • Φ v := by
    intro c v
    show A⁻¹.mulVec (fun i => (c • v) i ^ p ^ e) = c ^ p ^ e • A⁻¹.mulVec (fun i => v i ^ p ^ e)
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [mul_pow]
  have hfix : ∀ x : m → F, Φ x = x ↔ ∀ i, x i ^ p ^ e = A.mulVec x i := by
    intro x
    change A⁻¹.mulVec (fun i => x i ^ p ^ e) = x ↔ _
    constructor
    · intro h i
      have h2 := congrArg A.mulVec h
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec] at h2
      exact congrFun h2 i
    · intro h
      have h2 : (fun i => x i ^ p ^ e) = A.mulVec x := funext h
      rw [h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
  have hinj : Function.Injective Φ := by
    intro x y hxy
    change A⁻¹.mulVec (fun i => x i ^ p ^ e) = A⁻¹.mulVec (fun i => y i ^ p ^ e) at hxy
    have h2 := congrArg A.mulVec hxy
    simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec] at h2
    funext i
    have h3 := congrFun h2 i
    rw [← iterateFrobenius_def, ← iterateFrobenius_def] at h3
    exact (iterateFrobenius F p e).injective h3
  have hc := langCount_card_semilinear F p e he Φ hΦ hinj
  rw [Module.finrank_fintype_fun_eq_card] at hc
  rw [← hc]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hfix x).symm)

end GlobalTheory.PMonE

end
end

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lang_count_frobenius_eq_mulVec_solutions : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → A.det ≠ 0 → (∀ x : m → F, (∀ i, x i ^ p ^ e = A.mulVec x i) → Integral x) ∧ Nat.card {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} = (p ^ e) ^ Fintype.card m := by
  atlas_forward_decl GlobalTheory.PMonE.langCount
end

section
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

section Prep

variable {F : Type} [NormedField F] {m : Type} [Fintype m]

def PrepBd (c : ℝ) (X : Matrix m m F) : Prop := ∀ i j, ‖X i j‖ ≤ c

noncomputable def prepV (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (k : ℕ) : ℕ → Matrix m m F :=
  Nat.rec (motive := fun _ => ℕ → Matrix m m F) (fun _ => 0)
    (fun _ V n => M (n + 1) + V (n + 1) * A.map (fun a => a ^ q ^ (n + 1))) k

theorem prepV_zero (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (n : ℕ) : prepV q M A 0 n = 0 := rfl

theorem prepV_succ (q : ℕ) (M : ℕ → Matrix m m F) (A : Matrix m m F) (k n : ℕ) :
    prepV q M A (k + 1) n = M (n + 1) + prepV q M A k (n + 1) * A.map (fun a => a ^ q ^ (n + 1)) := rfl

variable [IsUltrametricDist F]

omit [Fintype m] in
theorem PrepBd.add {c : ℝ} {X Y : Matrix m m F} (hX : PrepBd c X) (hY : PrepBd c Y) : PrepBd c (X + Y) :=
  fun i j => (IsUltrametricDist.norm_add_le_max (X i j) (Y i j)).trans (max_le (hX i j) (hY i j))

omit [Fintype m] [IsUltrametricDist F] in
theorem PrepBd.neg {c : ℝ} {X : Matrix m m F} (hX : PrepBd c X) : PrepBd c (-X) :=
  fun i j => by simpa using hX i j

omit [Fintype m] [IsUltrametricDist F] in
theorem PrepBd.mono {c d : ℝ} {X : Matrix m m F} (hX : PrepBd c X) (h : c ≤ d) : PrepBd d X :=
  fun i j => (hX i j).trans h

theorem PrepBd.mul {c d : ℝ} {X Y : Matrix m m F} (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : PrepBd c X) (hY : PrepBd d Y) :
    PrepBd (c * d) (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hX i k) (hY k j) (norm_nonneg _) hc

omit [Fintype m] [IsUltrametricDist F] in
theorem PrepBd.map_pow {X : Matrix m m F} (hX : PrepBd 1 X) (N : ℕ) : PrepBd 1 (X.map (fun a => a ^ N)) := by
  intro i j
  rw [Matrix.map_apply, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hX i j)

theorem prepV_bd {q D : ℕ} {M : ℕ → Matrix m m F} {δ : ℝ} (hδ : 0 ≤ δ)
    (hM : ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n)) {A : Matrix m m F} (hA : PrepBd 1 A) :
    ∀ k n, 1 ≤ n → n + k ≤ D → PrepBd δ (prepV q M A k n) := by
  intro k
  induction k with
  | zero => intro n _ _ i j; simpa [prepV_zero] using hδ
  | succ k ih =>
    intro n hn hk
    rw [prepV_succ]
    refine (hM _ (by omega) (by omega)).add ?_
    simpa using PrepBd.mul hδ zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)

omit [Fintype m] in
theorem PrepBd.map_pow_sub (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) {A B : Matrix m m F} {ε : ℝ}
    (hA : PrepBd 1 A) (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    PrepBd ε (A.map (fun a => a ^ (p ^ e) ^ n) - B.map (fun a => a ^ (p ^ e) ^ n)) := by
  intro i j
  have h1 : ‖A i j - B i j‖ ≤ 1 := by
    have := (hA.add hB.neg) i j
    simpa [sub_eq_add_neg] using this
  have h2 : ‖A i j - B i j‖ ≤ ε := h i j
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← pow_mul, ← sub_pow_char_pow, norm_pow]
  exact (pow_le_of_le_one (norm_nonneg _) h1 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).trans h2

theorem prepV_sub_bd (p : ℕ) [Fact p.Prime] [CharP F p] {e D : ℕ} {M : ℕ → Matrix m m F} {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (hM : ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n)) {A B : Matrix m m F} (hA : PrepBd 1 A)
    (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    ∀ k n, 1 ≤ n → n + k ≤ D → PrepBd (δ * ε) (prepV (p ^ e) M A k n - prepV (p ^ e) M B k n) := by
  intro k
  induction k with
  | zero => intro n _ _ i j; simpa [prepV_zero] using mul_nonneg hδ hε
  | succ k ih =>
    intro n hn hk
    rw [prepV_succ, prepV_succ]
    have e1 : M (n + 1) + prepV (p ^ e) M A k (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) -
        (M (n + 1) + prepV (p ^ e) M B k (n + 1) * B.map (fun a => a ^ (p ^ e) ^ (n + 1))) =
        (prepV (p ^ e) M A k (n + 1) - prepV (p ^ e) M B k (n + 1)) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)) +
        prepV (p ^ e) M B k (n + 1) *
          (A.map (fun a => a ^ (p ^ e) ^ (n + 1)) - B.map (fun a => a ^ (p ^ e) ^ (n + 1))) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]; abel
    rw [e1]
    refine PrepBd.add ?_ ?_
    · simpa using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (ih (n + 1) (by omega) (by omega)) (hA.map_pow _)
    · exact PrepBd.mul hδ hε (prepV_bd hδ hM hB k (n + 1) (by omega) (by omega))
        (PrepBd.map_pow_sub p e _ hA hB h)

theorem prep_fixed [CompleteSpace F] {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1) (M0 : Matrix m m F) (h0 : PrepBd 1 M0)
    (W : Matrix m m F → Matrix m m F) (hW : ∀ A, PrepBd 1 A → PrepBd δ (W A))
    (hW2 : ∀ A B ε, 0 ≤ ε → PrepBd 1 A → PrepBd 1 B → PrepBd ε (A - B) → PrepBd (δ * ε) (W A - W B)) :
    ∃ A, PrepBd 1 A ∧ A = -M0 - W A * A := by
  let s : Set (m → m → F) := {A | ∀ i j, ‖A i j‖ ≤ 1}
  let f : (m → m → F) → (m → m → F) := fun A => fun i j => (-M0 - W (Matrix.of A) * (Matrix.of A)) i j
  have hs : IsClosed s := by
    simp only [s, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have hf : Set.MapsTo f s s := by
    intro A hA
    have hA' : PrepBd 1 (Matrix.of A) := hA
    have : PrepBd 1 (-M0 - W (Matrix.of A) * (Matrix.of A)) := by
      rw [sub_eq_add_neg]
      refine h0.neg.add (PrepBd.neg ?_)
      exact (PrepBd.mul hδ zero_le_one (hW _ hA') hA').mono (by simpa using hδ1.le)
    exact this
  have hc : ContractingWith ⟨δ, hδ⟩ (hf.restrict f s s) := by
    refine ⟨hδ1, LipschitzWith.of_dist_le_mul fun A B => ?_⟩
    have hA' : PrepBd 1 (Matrix.of A.1) := A.2
    have hB' : PrepBd 1 (Matrix.of B.1) := B.2
    have hε : 0 ≤ dist A B := dist_nonneg
    have hAB : PrepBd (dist A B) (Matrix.of A.1 - Matrix.of B.1) := by
      intro i j
      rw [Matrix.sub_apply, Matrix.of_apply, Matrix.of_apply, ← dist_eq_norm, Subtype.dist_eq]
      exact (dist_le_pi_dist _ _ j).trans (dist_le_pi_dist A.1 B.1 i)
    have key : PrepBd (δ * dist A B) ((-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) -
        (-M0 - W (Matrix.of B.1) * (Matrix.of B.1))) := by
      have e1 : (-M0 - W (Matrix.of A.1) * (Matrix.of A.1)) - (-M0 - W (Matrix.of B.1) * (Matrix.of B.1)) =
          -((W (Matrix.of A.1) - W (Matrix.of B.1)) * (Matrix.of A.1) +
            W (Matrix.of B.1) * (Matrix.of A.1 - Matrix.of B.1)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub]; abel
      rw [e1]
      refine PrepBd.neg (PrepBd.add ?_ ?_)
      · simpa using PrepBd.mul (mul_nonneg hδ hε) zero_le_one (hW2 _ _ _ hε hA' hB' hAB) hA'
      · exact PrepBd.mul hδ hε (hW _ hB') hAB
    change dist (f A.1) (f B.1) ≤ δ * dist A B
    refine (dist_pi_le_iff (mul_nonneg hδ hε)).2 fun i => (dist_pi_le_iff (mul_nonneg hδ hε)).2 fun j => ?_
    rw [dist_eq_norm]
    exact key i j
  obtain ⟨y, hy, hfix, -⟩ := hc.exists_fixedPoint' hs.isComplete hf (x := 0) (by intro i j; simp) (edist_ne_top _ _)
  refine ⟨Matrix.of y, hy, ?_⟩
  ext i j
  exact (congrFun (congrFun hfix i) j).symm

omit [IsUltrametricDist F] in
theorem prep_pow_sub_mulVec (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) (A : Matrix m m F) (x : m → F) :
    (fun i => (x i ^ p ^ e - A.mulVec x i) ^ (p ^ e) ^ n) =
      (fun i => x i ^ (p ^ e) ^ (n + 1)) - (A.map (fun a => a ^ (p ^ e) ^ n)).mulVec (fun i => x i ^ (p ^ e) ^ n) := by
  funext i
  have hq : (p ^ e) ^ n = p ^ (e * n) := (pow_mul p e n).symm
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [pow_succ' (p ^ e) n, pow_mul (x i), hq, sub_pow_char_pow, sum_pow_char_pow]
  simp only [mul_pow]

omit [IsUltrametricDist F] in
theorem prep_identity (p : ℕ) [Fact p.Prime] [CharP F p] (e D : ℕ) (M U : ℕ → Matrix m m F) (A : Matrix m m F)
    (hD : U D = 0) (hU : ∀ n, n < D → U n = M (n + 1) + U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1)))
    (h0 : M 0 = -(U 0 * A)) (x : m → F) :
    gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  unfold gsum
  simp only [prep_pow_sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, sum_sub_distrib]
  rw [sum_range_succ', sum_range_succ, sum_range_succ', hD, h0]
  have : ∑ n ∈ range D, (U n).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) =
      ∑ n ∈ range D, (M (n + 1)).mulVec (fun i => x i ^ (p ^ e) ^ (n + 1)) +
      ∑ n ∈ range D, (U (n + 1) * A.map (fun a => a ^ (p ^ e) ^ (n + 1))).mulVec
        (fun i => x i ^ (p ^ e) ^ (n + 1)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [← Matrix.add_mulVec, ← hU n (mem_range.1 hn)]
  rw [this]
  have hA : A.map (fun a => a ^ (p ^ e) ^ 0) = A := by ext i j; simp
  rw [hA, Matrix.neg_mulVec, Matrix.zero_mulVec]
  abel

end Prep

theorem preparation : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → 1 ≤ D →
    ∀ M : ℕ → Matrix m m F, Normal 1 M → ∃ (A : Matrix m m F) (U : ℕ → Matrix m m F), (∀ i j, ‖A i j‖ ≤ 1) ∧
      (∀ i j, ‖(U 0 - 1) i j‖ < 1) ∧ (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) ∧ M 0 = -(U 0 * A) ∧
      ∀ x : m → F, gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  intro F _ _ _ p _ _ m _ _ e D _ hD M hM
  obtain ⟨δ, hδ, hδ1, hMδ⟩ : ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧ ∀ n, 2 ≤ n → n ≤ D → PrepBd δ (M n) := by
    let S : Finset (ℕ × m × m) := Icc 2 D ×ˢ univ
    refine ⟨((S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊ : NNReal) : ℝ), NNReal.coe_nonneg _, ?_, ?_⟩
    · have : (S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊) < 1 := by
        rw [Finset.sup_lt_iff (by simp)]
        intro t ht
        have h2 : 2 ≤ t.1 := (mem_Icc.1 (mem_product.1 ht).1).1
        exact_mod_cast hM.small t.1 (by omega) t.2.1 t.2.2
      exact_mod_cast this
    · intro n h2 hn i j
      have : ‖M n i j‖₊ ≤ S.sup fun t => ‖M t.1 t.2.1 t.2.2‖₊ :=
        Finset.le_sup (f := fun t : ℕ × m × m => ‖M t.1 t.2.1 t.2.2‖₊) (b := (n, i, j))
          (mem_product.2 ⟨mem_Icc.2 ⟨h2, hn⟩, mem_univ _⟩)
      exact_mod_cast this
  obtain ⟨k, rfl⟩ : ∃ k, D = k + 1 := ⟨D - 1, by omega⟩
  have hW : ∀ A : Matrix m m F, PrepBd 1 A →
      PrepBd δ (prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)) := fun A hA => by
    have := PrepBd.mul hδ zero_le_one (prepV_bd (q := p ^ e) hδ hMδ hA k 1 le_rfl (by omega))
      (hA.map_pow ((p ^ e) ^ 1))
    rwa [mul_one] at this
  obtain ⟨A, hA, hfix⟩ := prep_fixed hδ hδ1 (M 0) (hM.int 0)
    (fun A => prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1)) hW (by
      intro A B ε hε hA hB h
      have e1 : prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1) -
          prepV (p ^ e) M B k 1 * B.map (fun a => a ^ (p ^ e) ^ 1) =
          (prepV (p ^ e) M A k 1 - prepV (p ^ e) M B k 1) * A.map (fun a => a ^ (p ^ e) ^ 1) +
          prepV (p ^ e) M B k 1 * (A.map (fun a => a ^ (p ^ e) ^ 1) - B.map (fun a => a ^ (p ^ e) ^ 1)) := by
        rw [Matrix.sub_mul, Matrix.mul_sub]; abel
      rw [e1]
      refine PrepBd.add ?_ ?_
      · have := PrepBd.mul (mul_nonneg hδ hε) zero_le_one
          (prepV_sub_bd p (e := e) hδ hε hMδ hA hB h k 1 le_rfl (by omega)) (hA.map_pow ((p ^ e) ^ 1))
        rwa [mul_one] at this
      · exact PrepBd.mul hδ hε (prepV_bd hδ hMδ hB k 1 le_rfl (by omega)) (PrepBd.map_pow_sub p e _ hA hB h))
  have hU0 : prepV (p ^ e) M A (k + 1 - 0) 0 = 1 + prepV (p ^ e) M A k 1 * A.map (fun a => a ^ (p ^ e) ^ 1) := by
    rw [Nat.sub_zero, prepV_succ, zero_add, hM.top]
  have h0 : M 0 = -(prepV (p ^ e) M A (k + 1 - 0) 0 * A) := by
    rw [hU0, Matrix.add_mul, Matrix.one_mul]
    have := eq_sub_iff_add_eq.1 hfix
    rw [this, neg_neg]
  refine ⟨A, fun n => prepV (p ^ e) M A (k + 1 - n) n, hA, ?_, ?_, h0, ?_⟩
  · intro i j
    beta_reduce
    rw [hU0, add_sub_cancel_left]
    exact (hW A hA i j).trans_lt hδ1
  · intro n hn i j
    beta_reduce
    by_cases h : n ≤ k + 1
    · exact (prepV_bd hδ hMδ hA _ n hn (by omega) i j).trans_lt hδ1
    · have : k + 1 - n = 0 := by omega
      simp [this, prepV_zero]
  · refine prep_identity p e (k + 1) M _ A (by simp [prepV_zero]) (fun n hn => ?_) h0
    have : k + 1 - n = (k + 1 - (n + 1)) + 1 := by omega
    beta_reduce
    rw [this, prepV_succ]

end GlobalTheory.PMonE

end
end

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystem_preparation_normalForm_one : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → 1 ≤ D → ∀ M : ℕ → Matrix m m F, Normal 1 M → ∃ (A : Matrix m m F) (U : ℕ → Matrix m m F), (∀ i j, ‖A i j‖ ≤ 1) ∧ (∀ i j, ‖(U 0 - 1) i j‖ < 1) ∧ (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) ∧ M 0 = -(U 0 * A) ∧ ∀ x : m → F, gsum (p ^ e) D M x = gsum (p ^ e) D U (fun i => x i ^ p ^ e - A.mulVec x i) := by
  atlas_forward_decl GlobalTheory.PMonE.preparation
end

section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → ∀ U : ℕ → Matrix m m F, (∀ i j, ‖(U 0 - 1) i j‖ < 1) → (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) → ∀ b : m → F, Integral b → ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by
  first | exact @GlobalTheory.PMonE.existsUnique_integral_gsum_eq | exact GlobalTheory.PMonE.existsUnique_integral_gsum_eq | (intros; apply GlobalTheory.PMonE.existsUnique_integral_gsum_eq <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset

theorem norm_mulVec_le_one_of_integral_matrix {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (x : m → F) (hx : Integral x) (i : m) :
    ‖A.mulVec x i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hA i j) (norm_nonneg _) (hx j)

theorem integralNormVector_pow_sub_mulVec {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (q : ℕ) (x : m → F) (hx : Integral x) :
    Integral (fun i => x i ^ q - A.mulVec x i) := by
  intro i
  have h1 : ‖x i ^ q‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx i)
  have h2 := norm_mulVec_le_one_of_integral_matrix A hA x hx i
  calc ‖x i ^ q - A.mulVec x i‖ = ‖x i ^ q + -A.mulVec x i‖ := by rw [sub_eq_add_neg]
    _ ≤ max ‖x i ^ q‖ ‖-A.mulVec x i‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := by rw [norm_neg]; exact max_le h1 h2

theorem additiveSystemFrobeniusPowerSum_zero {F : Type} [NormedField F] {m : Type} [Fintype m] (q D : ℕ) (hq : 0 < q)
    (U : ℕ → Matrix m m F) : gsum q D U (fun _ => 0) = 0 := by
  unfold gsum
  refine Finset.sum_eq_zero (fun n _ => ?_)
  have : (fun _ : m => (0 : F) ^ q ^ n) = 0 := by
    funext i; simp [zero_pow (pow_pos hq n).ne']
  rw [this, Matrix.mulVec_zero]

theorem gl1 : GLOnto 1 ∧ GLCount 1 := by
  constructor
  · intro F _ _ _ _ p _ _ m _ _ e D he hD M hM b hb
    obtain ⟨A, U, hA, hU0, hUn, -, hfac⟩ := GlobalTheory.T.additiveSystem_preparation_normalForm_one F p m e D he hD M hM
    obtain ⟨y, ⟨hy, hyb⟩, -⟩ := GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq F p m e D he U hU0 hUn b hb
    obtain ⟨x, hx, hxy⟩ := GlobalTheory.T.exists_integral_solution_frobenius_sub_mulVec_eq F p m e he A hA y hy
    refine ⟨x, hx, ?_⟩
    rw [hfac]
    have : (fun i => x i ^ p ^ e - A.mulVec x i) = y := funext hxy
    rw [this, hyb]
  · intro F _ _ _ _ p _ _ m _ _ e D he hD M hM hdet
    obtain ⟨A, U, hA, hU0, hUn, hM0, hfac⟩ := GlobalTheory.T.additiveSystem_preparation_normalForm_one F p m e D he hD M hM
    have hAdet : A.det ≠ 0 := by
      intro h
      apply hdet
      rw [hM0, Matrix.det_neg, Matrix.det_mul, h, mul_zero, mul_zero]
    obtain ⟨hInt, hcard⟩ := GlobalTheory.T.lang_count_frobenius_eq_mulVec_solutions F p m e he A hA hAdet
    have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
    obtain ⟨z, -, hz⟩ := GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq F p m e D he U hU0 hUn 0 (fun i => by simp)
    have key : ∀ x : m → F, Integral x →
        (gsum (p ^ e) D M x = 0 ↔ ∀ i, x i ^ p ^ e = A.mulVec x i) := by
      intro x hx
      rw [hfac]
      constructor
      · intro h0
        have h1 := hz _ ⟨integralNormVector_pow_sub_mulVec A hA (p ^ e) x hx, h0⟩
        have h2 := hz (fun _ => 0) ⟨fun i => by simp, additiveSystemFrobeniusPowerSum_zero _ D hq U⟩
        intro i
        have := congrFun (h1.trans h2.symm) i
        exact sub_eq_zero.mp this
      · intro h
        have : (fun i => x i ^ p ^ e - A.mulVec x i) = fun _ => 0 := funext fun i => by rw [h i, sub_self]
        rw [this]
        exact additiveSystemFrobeniusPowerSum_zero _ D hq U
    have eqv : {x : m → F // Integral x ∧ gsum (p ^ e) D M x = 0} ≃
        {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} :=
      { toFun := fun x => ⟨x.1, (key x.1 x.2.1).mp x.2.2⟩
        invFun := fun x => ⟨x.1, hInt x.1 x.2, (key x.1 (hInt x.1 x.2)).mpr x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [Nat.card_congr eqv, hcard, mul_one]

end GlobalTheory.PMonE

end
end

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_orderOne : GLOnto 1 ∧ GLCount 1 := by
  atlas_forward_decl GlobalTheory.PMonE.gl1
end

section
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset Matrix

section Lower

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

def lowerOrder (N : ℕ) (M : ℕ → Matrix m m F) (n : ℕ) : Matrix (m ⊕ m) (m ⊕ m) F :=
  fromBlocks (if n = N then 1 else 0) (if n + 1 = N then -1 else 0) (if n = 0 then M 0 else 0) (M (n + 1))

omit [Fintype m] in
theorem norm_one_apply_le (i j : m) : ‖(1 : Matrix m m F) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

omit [Fintype m] in
theorem lowerOrder_normal {N : ℕ} (hN : 1 ≤ N) {M : ℕ → Matrix m m F} (hM : Normal (N + 1) M) :
    Normal N (lowerOrder N M) where
  int n i j := by
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · split_ifs
      · exact norm_one_apply_le i j
      · simp
    · split_ifs
      · rw [Matrix.neg_apply, norm_neg]
        exact norm_one_apply_le i j
      · simp
    · split_ifs
      · exact hM.int 0 i j
      · simp
    · exact hM.int (n + 1) i j
  top := by
    have h1 : N + 1 ≠ N := by omega
    have h2 : N ≠ 0 := by omega
    simp [lowerOrder, h1, h2, hM.top]
  small n hn i j := by
    have h1 : n ≠ N := by omega
    have h2 : n + 1 ≠ N := by omega
    have h3 : n ≠ 0 := by omega
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, if_neg h1, if_neg h2, if_neg h3,
        Matrix.zero_apply, norm_zero, zero_lt_one]
    exact hM.small (n + 1) (by omega) i j

theorem gsum_lowerOrder_inl (q : ℕ) {K D : ℕ} (hD : K + 1 ≤ D) (M : ℕ → Matrix m m F) (z : m ⊕ m → F) (i : m) :
    gsum q D (lowerOrder (K + 1) M) z (Sum.inl i) = z (Sum.inl i) ^ q ^ (K + 1) - z (Sum.inr i) ^ q ^ K := by

  have h : ∀ n, (lowerOrder (K + 1) M n).mulVec (fun k => z k ^ q ^ n) (Sum.inl i) =
      (if n = K + 1 then z (Sum.inl i) ^ q ^ (K + 1) else 0) +
        (if n = K then -z (Sum.inr i) ^ q ^ K else 0) := by
    intro n
    simp only [lowerOrder, Matrix.fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, Function.comp_def]
    by_cases h1 : n = K + 1
    · subst h1
      simp
    · by_cases h2 : n = K
      · subst h2
        simp [Matrix.neg_mulVec]
      · have h3 : n ≠ K := h2
        simp [h1, h3]
  simp only [gsum, Finset.sum_apply, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos (by omega), if_pos (by omega), sub_eq_add_neg]

theorem gsum_lowerOrder_inr (q : ℕ) (N D : ℕ) (M : ℕ → Matrix m m F) (z : m ⊕ m → F)
    (hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ q) (i : m) :
    gsum q D (lowerOrder N M) z (Sum.inr i) = gsum q (D + 1) M (fun j => z (Sum.inl j)) i := by

  have h : ∀ n, (lowerOrder N M n).mulVec (fun k => z k ^ q ^ n) (Sum.inr i) =
      (if n = 0 then (M 0).mulVec (fun j => z (Sum.inl j) ^ q ^ 0) i else 0) +
        (M (n + 1)).mulVec (fun j => z (Sum.inl j) ^ q ^ (n + 1)) i := by
    intro n
    simp only [lowerOrder, Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, Function.comp_def, hz]
    congr 1
    · split_ifs with h0
      · subst h0
        rfl
      · simp
    · congr 2
      funext j
      rw [← pow_mul, ← pow_succ']
  simp only [gsum, Finset.sum_apply, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [Finset.sum_range_succ' _ (D + 1), if_pos (by omega), add_comm]

end Lower

theorem glOnto_succ (K : ℕ) (H : GLOnto (K + 1)) : GLOnto (K + 2) := by
  intro F _ _ _ _ p _ _ m _ _ e D he hD M hM b hb
  obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩

  obtain ⟨z, hzI, hzs⟩ := H F p (m ⊕ m) e D he (by omega) (lowerOrder (K + 1) M)
    (lowerOrder_normal (by omega) hM) (Sum.elim 0 b) (by
      intro k
      rcases k with k | k
      · simp
      · exact hb k)

  have hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ p ^ e := by
    intro i
    have h0 := congrFun hzs (Sum.inl i)
    rw [gsum_lowerOrder_inl (p ^ e) (by omega)] at h0
    simp only [Sum.elim_inl, Pi.zero_apply] at h0
    have hqK : (p ^ e) ^ K = p ^ (e * K) := (pow_mul p e K).symm
    have h1 : (z (Sum.inl i) ^ p ^ e - z (Sum.inr i)) ^ p ^ (e * K) = 0 := by
      rw [sub_pow_char_pow, ← hqK, ← pow_mul, ← pow_succ']
      exact h0
    exact (sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp h1)).symm
  refine ⟨fun j => z (Sum.inl j), fun j => hzI (Sum.inl j), ?_⟩
  funext i
  rw [← gsum_lowerOrder_inr (p ^ e) (K + 1) D M z hz i, hzs]
  rfl

theorem glOnto_of_one : ∀ N : ℕ, 1 ≤ N → GLOnto 1 → GLOnto N := by
  intro N hN H
  induction N, hN using Nat.le_induction with
  | base => exact H
  | succ n hn ih =>
    obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨n - 1, by omega⟩
    exact glOnto_succ K ih

end GlobalTheory.PMonE

end
end

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one : ∀ N : ℕ, 1 ≤ N → GLOnto 1 → GLOnto N := by
  atlas_forward_decl GlobalTheory.PMonE.glOnto_of_one
end

section
section
noncomputable section

namespace GlobalTheory.PMonE.LinCount

open Finset GlobalTheory.PMonE

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

def lin (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) : Matrix (Fin (K + 1) × m) (Fin (K + 1) × m) F :=
  fun r c =>
    if r.1 = Fin.last K then
      (if k = 0 then M c.1 r.2 c.2 else if c.1 = Fin.last K then M (k + K) r.2 c.2 else 0)
    else
      (if k = 0 then (if (c.1 : ℕ) = r.1 + 1 ∧ r.2 = c.2 then -1 else 0)
        else if k = 1 then (if r = c then 1 else 0) else 0)

theorem lin_normal (K : ℕ) (M : ℕ → Matrix m m F) (h : Normal (K + 1) M) : Normal 1 (lin K M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n r c
    unfold lin
    split_ifs <;> first | exact h.int _ _ _ | simp
  · ext ⟨i, a⟩ ⟨j, b⟩
    have h1 : M (1 + K) = 1 := by rw [add_comm]; exact h.top
    by_cases hi : i = Fin.last K
    · subst hi
      by_cases hj : j = Fin.last K
      · subst hj
        simp [lin, h1, Matrix.one_apply]
      · simp [lin, hj, Matrix.one_apply, Ne.symm hj]
    · simp [lin, hi, Matrix.one_apply]
  · intro n hn r c
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp only [lin, h0, h1, if_false]
    split_ifs
    · exact h.small _ (by omega) _ _
    · simp
    · simp

theorem lin_zero_cast (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M 0).mulVec Y (i.castSucc, a) = - Y (i.succ, a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (i.succ, a)]
  · simp [lin, (Fin.castSucc_lt_last i).ne]
  · rintro ⟨j, b⟩ _ hne
    have : ¬ ((j : ℕ) = i + 1 ∧ a = b) := by
      rintro ⟨h1, rfl⟩
      exact hne (by congr 1; exact Fin.ext (by simpa using h1))
    simp [lin, (Fin.castSucc_lt_last i).ne, this]
  · simp

theorem lin_one_cast (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M 1).mulVec Y (i.castSucc, a) = Y (i.castSucc, a) := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]

theorem lin_two_cast (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M (k + 1 + 1)).mulVec Y (i.castSucc, a) = 0 := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]

theorem lin_zero_last (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M 0).mulVec Y (Fin.last K, a) = ∑ j : Fin (K + 1), (M j).mulVec (fun b => Y (j, b)) a := by
  simp [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]

theorem lin_succ_last (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M (k + 1)).mulVec Y (Fin.last K, a) = (M (k + 1 + K)).mulVec (fun b => Y (Fin.last K, b)) a := by
  simp only [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last K)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem lin_det (K : ℕ) (M : ℕ → Matrix m m F) (h : (M 0).det ≠ 0) : (lin K M 0).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hs : ∀ (i : Fin K) (a : m), v (i.succ, a) = 0 := by
    intro i a
    have := congrFun hv0 (i.castSucc, a)
    rw [lin_zero_cast] at this
    simpa using this
  have hz : (M 0).mulVec (fun b => v (0, b)) = 0 := by
    funext a
    have := congrFun hv0 (Fin.last K, a)
    rw [lin_zero_last, Fin.sum_univ_succ] at this
    simpa [hs, Matrix.mulVec, dotProduct] using this
  have h00 : (fun b => v (0, b)) = 0 := by
    by_contra hne
    exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hz⟩)
  apply hv
  funext ⟨j, b⟩
  refine Fin.cases ?_ (fun i => ?_) j
  · exact congrFun h00 b
  · exact hs i b

theorem gsum_lin_cast (q K E : ℕ) (M : ℕ → Matrix m m F) (X : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    gsum q (E + 1) (lin K M) X (i.castSucc, a) = X (i.castSucc, a) ^ q - X (i.succ, a) := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [lin_two_cast, zero_add, lin_one_cast, lin_zero_cast]
  simp [sub_eq_add_neg]

theorem gsum_lin_last (q K E : ℕ) (M : ℕ → Matrix m m F) (x : m → F) (a : m) :
    gsum q E (lin K M) (fun r => x r.2 ^ q ^ (r.1 : ℕ)) (Fin.last K, a) = gsum q (K + E) M x a := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', show K + E + 1 = (K + 1) + E by ring, Finset.sum_range_add, add_comm]
  congr 1
  · rw [lin_zero_last, Finset.sum_range]
    simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [lin_succ_last, show k + 1 + K = K + 1 + k by ring]
    congr 1
    funext b
    simp only [Fin.val_last]
    rw [← pow_mul, ← pow_add, show K + (k + 1) = K + 1 + k by ring]

theorem card_lin (q K E : ℕ) (M : ℕ → Matrix m m F) :
    Nat.card {x : m → F // Integral x ∧ gsum q (K + (E + 1)) M x = 0} =
      Nat.card {X : Fin (K + 1) × m → F // Integral X ∧ gsum q (E + 1) (lin K M) X = 0} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨fun r => x.1 r.2 ^ q ^ (r.1 : ℕ), ?_, ?_⟩) ⟨?_, ?_⟩)
  · intro r
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (x.2.1 _)
  · funext ⟨j, a⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [gsum_lin_last, x.2.2]; rfl
    · rw [gsum_lin_cast]
      simp [pow_succ, pow_mul]
  · intro x y hxy
    ext a
    have := congrFun (congrArg Subtype.val hxy) (0, a)
    simpa using this
  · rintro ⟨X, hX, hX0⟩
    have key : X = fun r => X (0, r.2) ^ q ^ (r.1 : ℕ) := by
      funext ⟨j, a⟩
      induction j using Fin.induction with
      | zero => simp
      | succ i ih =>
        have := congrFun hX0 (i.castSucc, a)
        rw [gsum_lin_cast, Pi.zero_apply, sub_eq_zero] at this
        rw [← this, ih]
        simp [pow_succ, pow_mul]
    refine ⟨⟨fun a => X (0, a), fun a => hX _, ?_⟩, Subtype.ext key.symm⟩
    funext a
    rw [← gsum_lin_last, ← key, hX0]; rfl

theorem glCount_of_one : ∀ N : ℕ, 1 ≤ N → GLCount 1 → GLCount N := by
  intro N hN h1 F _ _ _ _ p _ _ m _ _ e D he hD M hM hdet
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  obtain ⟨E, rfl⟩ : ∃ E, D = K + (E + 1) := ⟨D - K - 1, by omega⟩
  rw [card_lin, h1 F p (Fin (K + 1) × m) e (E + 1) he (by omega) (lin K M) (lin_normal K M hM) (lin_det K M hdet)]
  simp [mul_comm]

end GlobalTheory.PMonE.LinCount

end
end

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one : ∀ N : ℕ, 1 ≤ N → GLCount 1 → GLCount N := by
  atlas_forward_decl GlobalTheory.PMonE.LinCount.glCount_of_one
end

section
section
open GlobalTheory.PMonE

namespace GlobalTheory

theorem PMonE.generalLemma_allOrders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero
  · exact ⟨GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.1, GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.2⟩

end GlobalTheory
end

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_all_orders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  atlas_forward_decl GlobalTheory.PMonE.generalLemma_allOrders
end
