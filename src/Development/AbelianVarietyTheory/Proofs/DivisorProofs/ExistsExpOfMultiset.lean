import Mathlib
import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.UnitTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterAbsoluteValuePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterRamifiedFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeEigenvalueLeCardCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  first | exact @GlobalTheory.TjCount.tj_cosets_finite_card_le | exact GlobalTheory.TjCount.tj_cosets_finite_card_le | (intros; apply GlobalTheory.TjCount.tj_cosets_finite_card_le <;> assumption)
end

section
section
open NumberField IsDedekindDomain

namespace GlobalTheory.LFun

theorem tn_single (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (ϖ : w.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E w ϖ) :
    ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w n), ∃ g,
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  classical
  intro x hx
  have h0 : ϖ ≠ 0 := Formalism.UG.P.tjcosets_ne_zero w ϖ hϖ
  set g := Formalism.UG.P.tjcosets_dG n n ϖ h0 with hg
  have hdiag : Formalism.UG.diagJ n ϖ n = ϖ • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    unfold Formalism.UG.diagJ
    ext i j
    by_cases h : i = j
    · subst h; simp [i.2]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hcomm : ∀ a : GL (Fin n) (w.adicCompletion E), g * a = a * g := fun a => by
    ext : 1
    rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val, hdiag]
    simp
  have hT : Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n = Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL w n) g := by
    unfold Formalism.UG.Tj Formalism.UG.dosetInd
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b, hb, Units.ext (by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]; exact e)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]⟩
  refine ⟨g, ?_⟩
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx (R := {g})]
  · simp
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
    refine ⟨g, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have : g⁻¹ * (a * g * b) = a * b := by
      rw [← hcomm a]; group
    rw [this]
    exact (GlobalTheory.LFun.KGL w n).mul_mem ha hb

end GlobalTheory.LFun
end

open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w n), ∃ g, GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  atlas_forward_decl GlobalTheory.LFun.tn_single
end

section
namespace GlobalTheory.ElementarySymmetricNormBound

open Polynomial

theorem sum_esymm_eq_zero (s : Multiset ℂ) (x : ℂ) (hx : x ∈ s) :
    ∑ j ∈ Finset.range (Multiset.card s + 1),
      (-1) ^ j * (s.esymm j * x ^ (Multiset.card s - j)) = 0 := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_finset_sum] at h
  simp only [Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_one] at h
  rw [← h]
  exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨x, hx, sub_self x⟩)

theorem norm_le_of_esymm (s : Multiset ℂ) (M : ℝ) (hM : 1 ≤ M)
    (h : ∀ j, 1 ≤ j → j ≤ Multiset.card s → ‖s.esymm j‖ ≤ M) (x : ℂ) (hx : x ∈ s) :
    ‖x‖ ≤ (Multiset.card s : ℝ) * M := by
  have hn1 : 1 ≤ Multiset.card s := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hx⟩
  by_cases hx1 : ‖x‖ ≤ 1
  · calc ‖x‖ ≤ 1 := hx1
      _ ≤ M := hM
      _ ≤ (Multiset.card s : ℝ) * M :=
          le_mul_of_one_le_left (by linarith) (by exact_mod_cast hn1)
  push_neg at hx1
  have h0 := sum_esymm_eq_zero s x hx
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm]
  rw [Finset.sum_range_succ'] at h0
  simp only [pow_zero, he0, one_mul, Nat.sub_zero] at h0
  have hxn : x ^ Multiset.card s = -∑ i ∈ Finset.range (Multiset.card s),
      (-1) ^ (i + 1) * (s.esymm (i + 1) * x ^ (Multiset.card s - (i + 1))) :=
    eq_neg_of_add_eq_zero_right h0
  have hbound : ‖x‖ ^ Multiset.card s ≤
      (Multiset.card s : ℝ) * M * ‖x‖ ^ (Multiset.card s - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    calc _ ≤ ∑ i ∈ Finset.range (Multiset.card s),
          ‖(-1 : ℂ) ^ (i + 1) * (s.esymm (i + 1) * x ^ (Multiset.card s - (i + 1)))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (Multiset.card s), M * ‖x‖ ^ (Multiset.card s - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          exact mul_le_mul (h (i + 1) (by omega) (by omega)) (pow_le_pow_right₀ hx1.le (by omega))
            (pow_nonneg (norm_nonneg _) _) (by linarith)
      _ = (Multiset.card s : ℝ) * M * ‖x‖ ^ (Multiset.card s - 1) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hpos : 0 < ‖x‖ ^ (Multiset.card s - 1) := pow_pos (by linarith) _
  have hsplit : ‖x‖ ^ Multiset.card s = ‖x‖ * ‖x‖ ^ (Multiset.card s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit] at hbound
  exact le_of_mul_le_mul_right hbound hpos

theorem norm_unit_le_of_esymm :
    ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), Multiset.card B = n → (1 : ℝ) ≤ M →
      (∀ (j : ℕ), (1 : ℕ) ≤ j → j ≤ n →
        ‖Multiset.esymm (Multiset.map (fun (b : ℂˣ) ↦ (↑b : ℂ)) B) j‖ ≤ M) →
      ∀ b ∈ B, ‖(↑b : ℂ)‖ ≤ (↑n : ℝ) * M := by
  intro n B M hcard hM h b hb
  have hb' := norm_le_of_esymm (B.map (fun b : ℂˣ => (b : ℂ))) M hM
    (fun j hj1 hj2 => by
      rw [Multiset.card_map, hcard] at hj2
      exact h j hj1 hj2) (b : ℂ) (Multiset.mem_map_of_mem _ hb)
  rwa [Multiset.card_map, hcard] at hb'

end GlobalTheory.ElementarySymmetricNormBound
end

section
section
namespace GlobalTheory

open Polynomial in

theorem cauchy_roots_bound : ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), B.card = n → 1 ≤ M →
    (∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ M) →
    ∀ b ∈ B, ‖(b : ℂ)‖ ≤ n * M := by
  first
  | exact @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm
  | exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm
  | (apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)
  | (intros; apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm ..)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_root_le_card_mul_bound_of_esymm_norm_le : ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), B.card = n → 1 ≤ M → (∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ M) → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ n * M := by
  atlas_forward_decl GlobalTheory.cauchy_roots_bound
end

section
namespace GlobalTheory

theorem norm_inv_le_pow_card_of_norm_prod_eq_one :
    ∀ (B : Multiset ℂˣ) (M : ℝ), 1 ≤ M → (∀ b ∈ B, ‖(b : ℂ)‖ ≤ M) →
      ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 → ∀ b ∈ B, ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ M ^ B.card := by
  intro B M hM hB hprod b hb
  have aux : ∀ C : Multiset ℂˣ, (∀ c ∈ C, ‖(c : ℂ)‖ ≤ M) →
      ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ ≤ M ^ C.card := by
    intro C
    induction C using Multiset.induction_on with
    | empty => intro _; simp
    | cons a C ih =>
      intro hC
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, norm_mul,
        mul_comm (M ^ _)]
      exact mul_le_mul (hC a (Multiset.mem_cons_self a C))
        (ih fun c hc => hC c (Multiset.mem_cons_of_mem hc)) (norm_nonneg _) (by linarith)
  obtain ⟨C, rfl⟩ := Multiset.exists_cons_of_mem hb
  have hC : ∀ c ∈ C, ‖(c : ℂ)‖ ≤ M := fun c hc => hB c (Multiset.mem_cons_of_mem hc)
  rw [Multiset.map_cons, Multiset.prod_cons, norm_mul] at hprod
  have hinv : ‖((b⁻¹ : ℂˣ) : ℂ)‖ = ‖(C.map fun c : ℂˣ => (c : ℂ)).prod‖ := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact (eq_inv_of_mul_eq_one_right hprod).symm
  rw [hinv, Multiset.card_cons]
  exact (aux C hC).trans (pow_le_pow_right₀ hM (Nat.le_succ _))

end GlobalTheory

alias _root_.GlobalTheory.T.norm_inv_le_pow_card_of_norm_prod_eq_one' := _root_.GlobalTheory.norm_inv_le_pow_card_of_norm_prod_eq_one
end

section
noncomputable section

open NumberField IsDedekindDomain UpperTheory.V
open Formalism.L2.Host

namespace GlobalTheory.HenQ

theorem local_bound (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (h1 : ∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) (h2 : ∀ x, x ≠ 0 → 0 < (Bf x x).re)
    (h3 : ∀ g x y, Bf (ρ g x) (ρ g y) = Bf x y) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w ρ B) :
    ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Formalism.UG.qV E w : ℝ) ^ (n * n + n)) ∧
      ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ ((Formalism.UG.qV E w : ℝ) ^ (n * n + n)) ^ n := by
  obtain ⟨x, hx0, hxK, hcard, hT⟩ := hB.exists_vec
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  set q := Formalism.UG.qV E w with hqdef
  have hq2 : 2 ≤ q := GlobalTheory.LFun.one_lt_absNorm w
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)

  have he : ∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ (q : ℝ) ^ (n * n) := by
    intro j _ hjn
    obtain ⟨hfin, hc⟩ := GlobalTheory.T.heckeTj_cosets_finite_card_le E w n ϖ hϖ j hjn
    have hh : ∀ g, ‖Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j g‖ ≤ 1 := fun g => by
      unfold Formalism.UG.Tj
      exact (norm_indicator_le_norm_self _ _).trans (by simp)
    have k1 := GlobalTheory.T.norm_heckeEigenvalue_le_card_cosets _ (GlobalTheory.LFun.KGL w n) V ρ Bf h1 h2 h3 _ x _ hh hfin hx0 (hT ϖ hϖ j hjn)
    have k2 : ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ ‖GlobalTheory.LFun.satEig q n B j‖ := by
      unfold GlobalTheory.LFun.satEig
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      refine le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow hq1 ?_)
      have : (((j : ℂ) * ((n : ℂ) - j)) / 2).re = (j : ℝ) * ((n : ℝ) - j) / 2 := by simp
      rw [this]
      have : (j : ℝ) ≤ n := by exact_mod_cast hjn
      positivity
    refine k2.trans (k1.trans ?_)
    refine le_trans ((Nat.cast_le (α := ℝ)).2 hc) ?_
    push_cast
    exact pow_le_pow_right₀ hq1 (Nat.mul_le_mul_left n hjn)
  have hnq : (n : ℝ) ≤ (q : ℝ) ^ n := by
    have : n < 2 ^ n := Nat.lt_two_pow_self
    have h2n : (2 : ℝ) ^ n ≤ (q : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq2) n
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast this.le
    linarith
  have hup : ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (q : ℝ) ^ (n * n + n) := by
    intro b hb
    refine (GlobalTheory.T.norm_root_le_card_mul_bound_of_esymm_norm_le n B _ hcard (one_le_pow₀ hq1) he b hb).trans ?_
    rw [pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_left hnq (by positivity)
  refine fun b hb => ⟨hup b hb, ?_⟩

  obtain ⟨g, hg⟩ := GlobalTheory.T.heckeTn_scalar_uniformiser_single_translation E w n V ρ ϖ hϖ x hxK
  have hn := hT ϖ hϖ n le_rfl
  have hsat : GlobalTheory.LFun.satEig q n B n = (B.map fun b : ℂˣ => (b : ℂ)).prod := by
    unfold GlobalTheory.LFun.satEig
    simp only [sub_self, mul_zero, zero_div, Complex.cpow_zero, one_mul]
    have : (B.map fun b : ℂˣ => (b : ℂ)).card = n := by rw [Multiset.card_map, hcard]
    rw [← this, Multiset.esymm, Multiset.powersetCard_self]
    simp
  rw [hg, hsat] at hn
  have hp : ‖(B.map fun b : ℂˣ => (b : ℂ)).prod‖ = 1 := by
    set c := (B.map fun b : ℂˣ => (b : ℂ)).prod
    have e := h3 g x x
    rw [hn, map_smul, map_smulₛₗ, LinearMap.smul_apply] at e
    have hx : Bf x x ≠ 0 := fun h0 => by simpa [h0] using h2 x hx0
    simp only [smul_eq_mul] at e
    have e2 : starRingEnd ℂ c * c = 1 := by
      refine mul_right_cancel₀ hx ?_
      rw [one_mul]
      nth_rewrite 2 [← e]
      ring
    have e3 : ‖c‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      have : (Complex.normSq c : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact e2
      exact_mod_cast this
    nlinarith [norm_nonneg c]
  have := GlobalTheory.T.norm_inv_le_pow_card_of_norm_prod_eq_one' B _ (one_le_pow₀ hq1) hup hp b hb
  rwa [hcard] at this

end GlobalTheory.HenQ
end
end
