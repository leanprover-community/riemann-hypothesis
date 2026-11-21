import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexFixedElementApproximation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.axLemma_padicComplex_fixed_element_approximation : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (y : ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ‖Per.σC g y - y‖ ≤ r) → ∃ z : Om l, (∀ g ∈ H, g z = z) ∧ ‖y - (z : ℂ_[l])‖ ≤ c * r := by
  first | exact @GlobalTheory.AxLemma.ax_lemma_complete | exact GlobalTheory.AxLemma.ax_lemma_complete | (intros; apply GlobalTheory.AxLemma.ax_lemma_complete <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory

theorem padicInt_exists_pow_sub_norm_le_of_exact_level (l : ℕ) [Fact l.Prime] (u v : ℤ_[l]) (m : ℕ)
    (hm : 1 ≤ m) (hu : ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ m)
    (hv : ‖v - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m) :
    ∃ i : ℕ, ‖u ^ i - v‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (m + 1) := by
  have key : ∀ (x : ℤ_[l]) (n : ℕ), ‖x‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ n ↔ ((l : ℕ) : ℤ_[l]) ^ n ∣ x := by
    intro x n
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_p,
      zpow_neg, zpow_natCast, inv_pow]
  have hl0 : ‖((l : ℕ) : ℤ_[l])‖ ^ m ≠ 0 := by
    apply pow_ne_zero
    rw [norm_ne_zero_iff]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  obtain ⟨a, ha⟩ := (key _ _).1 hu.le
  obtain ⟨b, hb⟩ := (key _ _).1 hv
  have ha1 : ‖a‖ = 1 := by
    rw [ha, norm_mul, norm_pow] at hu
    exact mul_left_cancel₀ hl0 (by rw [hu, mul_one])
  obtain ⟨a', ha'⟩ := (PadicInt.isUnit_iff.2 ha1).exists_right_inv
  refine ⟨(a' * b).appr 1, (key _ _).2 ?_⟩
  set i := (a' * b).appr 1 with hi
  have hc := PadicInt.appr_spec 1 (a' * b)
  rw [Ideal.mem_span_singleton, pow_one, ← hi] at hc
  obtain ⟨c, hc⟩ := hc
  have hu' : u = 1 + ((l : ℕ) : ℤ_[l]) ^ m * a := by rw [← ha]; ring
  have hv' : v = 1 + ((l : ℕ) : ℤ_[l]) ^ m * b := by rw [← hb]; ring
  have hpow : ∀ (x : ℤ_[l]) (n : ℕ), ∃ d, (1 + x) ^ n = 1 + n * x + x ^ 2 * d := by
    intro x n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨d, hd⟩ := ih
      exact ⟨d + n + x * d, by rw [pow_succ, hd]; push_cast; ring⟩
  obtain ⟨d, hd⟩ := hpow (((l : ℕ) : ℤ_[l]) ^ m * a) i
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine ⟨-(a * c) + ((l : ℕ) : ℤ_[l]) ^ k * a ^ 2 * d, ?_⟩
  have hi' : (i : ℤ_[l]) = a' * b - ((l : ℕ) : ℤ_[l]) * c := by rw [← hc]; ring
  rw [hu', hd, hv', hi']
  linear_combination (((l : ℕ) : ℤ_[l]) ^ (1 + k) * b) * ha'

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_exists_pow_sub_norm_le_of_exact_level' : ∀ (l : ℕ) [Fact l.Prime] (u v : ℤ_[l]) (m : ℕ), 1 ≤ m → ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ m → ‖v - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m → ∃ i : ℕ, ‖u ^ i - v‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (m + 1) := by
  atlas_forward_decl GlobalTheory.padicInt_exists_pow_sub_norm_le_of_exact_level
end

section
namespace GlobalTheory.PadicLte

theorem norm_pow_prime_sub_one (l : ℕ) [Fact l.Prime] (u : ℤ_[l])
    (h : ‖u - 1‖ < ‖((l : ℕ) : ℤ_[l])‖) :
    ‖u ^ l - 1‖ = ‖u - 1‖ * ‖((l : ℕ) : ℤ_[l])‖ := by
  have hl1 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
    intro i
    rw [← mul_geom_sum, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
  have hsum : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, (u ^ i - 1)‖ ≤ ‖u - 1‖ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      exact (PadicInt.nonarchimedean _ _).trans (max_le ih (hpow m))
  have hsplit : ∑ i ∈ Finset.range l, u ^ i
      = ((l : ℕ) : ℤ_[l]) + ∑ i ∈ Finset.range l, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hgeom : ‖∑ i ∈ Finset.range l, u ^ i‖ = ‖((l : ℕ) : ℤ_[l])‖ := by
    rw [hsplit, PadicInt.norm_add_eq_max_of_ne]
    · exact max_eq_left ((hsum l).trans h.le)
    · exact ((hsum l).trans_lt h).ne'
  rw [← mul_geom_sum, norm_mul, hgeom]

theorem norm_pow_prime_pow_sub_one (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (k : ℕ) (hk : 2 ≤ k)
    (hu : ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k) (n : ℕ) :
    ‖u ^ l ^ n - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := by
  have hl1 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : 0 ≤ ‖((l : ℕ) : ℤ_[l])‖ := norm_nonneg _
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    have hlt : ‖u ^ l ^ n - 1‖ < ‖((l : ℕ) : ℤ_[l])‖ := by
      rw [ih]
      calc ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ 2 :=
            pow_le_pow_of_le_one hl0 hl1.le (by omega)
        _ < ‖((l : ℕ) : ℤ_[l])‖ ^ 1 := by
            have hpos : 0 < ‖((l : ℕ) : ℤ_[l])‖ := by
              rw [PadicInt.norm_p]
              exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
            exact pow_lt_pow_right_of_lt_one₀ hpos hl1 (by norm_num)
        _ = ‖((l : ℕ) : ℤ_[l])‖ := pow_one _
    rw [pow_succ, pow_mul, norm_pow_prime_sub_one l _ hlt, ih, ← pow_succ, ← add_assoc]

end GlobalTheory.PadicLte
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one : ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (k : ℕ), 2 ≤ k → ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∀ n : ℕ, ‖u ^ l ^ n - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := by
  atlas_forward_decl GlobalTheory.PadicLte.norm_pow_prime_pow_sub_one
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory

theorem units_map_toZModPow_eq_one_iff (l : ℕ) [Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) :
    Units.map (PadicInt.toZModPow (p := l) m).toMonoidHom u = 1 ↔
      ‖(u : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m := by
  rw [PadicInt.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg,
    PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_one, sub_eq_zero, Units.ext_iff]
  simp

theorem congruence_chain_of_character {G : Type*} [Group G] (l : ℕ) [Fact l.Prime]
    (η : G →* ℤ_[l]ˣ) (γ : G) (k : ℕ) (hk : 2 ≤ k)
    (hγ : ‖(η γ : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k) :
    ∃ H : ℕ → Subgroup G,
      (∀ n g, g ∈ H n ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)) ∧
      (∀ n, (H n).Normal) ∧ (∀ n, (H n).index ≠ 0) ∧ (∀ n, (H n).index ≤ l ^ (k + n)) ∧
      (∀ n, γ ^ l ^ n ∈ H n) ∧
      ∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  let φ : ∀ n : ℕ, G →* (ZMod (l ^ (k + n)))ˣ := fun n =>
    (Units.map (PadicInt.toZModPow (p := l) (k + n)).toMonoidHom).comp η
  have hmem : ∀ n g, g ∈ (φ n).ker ↔
      ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := fun n g => by
    rw [MonoidHom.mem_ker]
    exact units_map_toZModPow_eq_one_iff l (k + n) (η g)
  have hlte : ∀ n, ‖(η (γ ^ l ^ n) : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n) := fun n => by
    rw [map_pow, Units.val_pow_eq_pow_val]
    exact GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one l _ k hk hγ n
  refine ⟨fun n => (φ n).ker, hmem, fun n => inferInstance, fun n => ?_, fun n => ?_,
    fun n => ?_, fun n h hh => ?_⟩
  · have : NeZero (l ^ (k + n)) := ⟨pow_ne_zero _ hl⟩
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  · have : NeZero (l ^ (k + n)) := ⟨pow_ne_zero _ hl⟩
    rw [Subgroup.index_ker]
    calc Nat.card (φ n).range ≤ Nat.card (ZMod (l ^ (k + n))) :=
          Nat.card_le_card_of_injective (fun x => ((x : (ZMod (l ^ (k + n)))ˣ) : ZMod (l ^ (k + n))))
            (fun x y hxy => Subtype.ext (Units.ext hxy))
      _ = l ^ (k + n) := Nat.card_zmod _
  · exact (hmem n _).2 (hlte n).le
  · obtain ⟨i, hi⟩ := GlobalTheory.T.padicInt_exists_pow_sub_norm_le_of_exact_level' l (η (γ ^ l ^ n) : ℤ_[l]) (η h : ℤ_[l]) (k + n) (by omega)
      (hlte n) ((hmem n h).1 hh)
    refine ⟨i, (hmem (n + 1) _).2 ?_⟩
    set w : ℤ_[l]ˣ := η ((γ ^ l ^ n) ^ i) with hw
    have hwv : (w : ℤ_[l]) = (η (γ ^ l ^ n) : ℤ_[l]) ^ i := by
      rw [hw, map_pow η (γ ^ l ^ n) i, Units.val_pow_eq_pow_val]
    have key : ((η (((γ ^ l ^ n) ^ i)⁻¹ * h) : ℤ_[l]ˣ) : ℤ_[l]) - 1 =
        -((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * ((w : ℤ_[l]) - (η h : ℤ_[l])) := by
      rw [map_mul, map_inv, ← hw, Units.val_mul, mul_sub, neg_mul, neg_mul, Units.inv_mul]
      ring
    rw [key, norm_mul, norm_neg, hwv]
    calc _ ≤ 1 * ‖(η (γ ^ l ^ n) : ℤ_[l]) ^ i - (η h : ℤ_[l])‖ :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hi

theorem galois_congruence_chain : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (γ : GQ l) (k : ℕ), 2 ≤ k → ‖(η γ : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∃ H : ℕ → Subgroup (GQ l), (∀ n g, g ∈ H n ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)) ∧ (∀ n, (H n).Normal) ∧ (∀ n, (H n).index ≠ 0) ∧ (∀ n, (H n).index ≤ l ^ (k + n)) ∧ (∀ n, γ ^ l ^ n ∈ H n) ∧ ∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1) :=
  fun l _ η γ k hk hγ => congruence_chain_of_character l η γ k hk hγ

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_subgroup_filtration_index_bounded : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (γ : GQ l) (k : ℕ), 2 ≤ k → ‖(η γ : ℤ_[l]) - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k → ∃ H : ℕ → Subgroup (GQ l), (∀ n g, g ∈ H n ↔ ‖(η g : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (k + n)) ∧ (∀ n, (H n).Normal) ∧ (∀ n, (H n).index ≠ 0) ∧ (∀ n, (H n).index ≤ l ^ (k + n)) ∧ (∀ n, γ ^ l ^ n ∈ H n) ∧ ∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1) := by
  atlas_forward_decl GlobalTheory.galois_congruence_chain
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem tate_eigenvector_estimate : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l) (u : ℚ_[l]) (y : ℂ_[l]) (z : Om l) (N : ℕ) (e δ : ℝ), Per.σC γ y = algebraMap ℚ_[l] ℂ_[l] u * y → ‖u‖ = 1 → (γ ^ N) z = z → ‖y - (z : ℂ_[l])‖ ≤ e → ‖∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)‖ ≤ δ * ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ → 0 ≤ δ → ‖u ^ N - 1‖ * ‖y‖ ≤ max (‖u - 1‖ * e) (δ * e) := by
  intro l _ γ u y z N e δ hy hu hz he hT hδ
  have hca : ∀ c : ℚ_[l], ((algebraMap ℚ_[l] (Om l) c : Om l) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] c :=
    fun _ => rfl
  have hn : ∀ c : ℚ_[l], ‖algebraMap ℚ_[l] ℂ_[l] c‖ = ‖c‖ := fun c => by
    rw [← hca, PadicComplex.norm_extends, norm_algebraMap']
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  set U : ℂ_[l] := algebraMap ℚ_[l] ℂ_[l] u with hU
  have hv : ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ ≤ e := by
    rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul,
      hca, ← GlobalTheory.RingBasics.σC_coe]
    have h1 : Per.σC γ (z : ℂ_[l]) - U * (z : ℂ_[l])
        = U * (y - (z : ℂ_[l])) + -Per.σC γ (y - (z : ℂ_[l])) := by
      rw [map_sub, hy]; ring
    rw [← hU, h1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, hU, hn, hu, one_mul]; exact he
    · rw [norm_neg, GlobalTheory.RingBasics.norm_σC]; exact he
  have hpow : ∀ i : ℕ, Per.σC (γ ^ i) y = U ^ i * y := by
    intro i
    induction i with
    | zero => simp [GlobalTheory.RingBasics.σC_one]
    | succ i ih =>
      rw [pow_succ, GlobalTheory.RingBasics.σC_mul, hy, map_mul, hU, TateTwist.σC_algebraMap, ← hU, ih]
      ring
  have htel : ∑ i ∈ Finset.range N, (γ ^ i) (γ z) = ∑ i ∈ Finset.range N, (γ ^ i) z := by
    have h := Finset.sum_range_sub (fun i => (γ ^ i) z) N
    rw [Finset.sum_sub_distrib] at h
    simp only [hz, pow_zero, AlgEquiv.one_apply, sub_self, pow_succ, AlgEquiv.mul_apply] at h
    exact sub_eq_zero.1 h
  have hTv : ∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)
      = algebraMap ℚ_[l] (Om l) (1 - u) * ∑ i ∈ Finset.range N, (γ ^ i) z := by
    simp only [map_sub, map_mul, AlgEquiv.commutes, Finset.sum_sub_distrib, htel, map_one,
      ← Finset.mul_sum]
    ring
  set S : Om l := ∑ i ∈ Finset.range N, (γ ^ i) z with hS
  have hSc : (S : ℂ_[l]) = ∑ i ∈ Finset.range N, Per.σC (γ ^ i) (z : ℂ_[l]) := by
    simp only [GlobalTheory.RingBasics.σC_coe]
    exact map_sum (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l]) _ _
  have hB : ‖(U - 1) * (S : ℂ_[l])‖ ≤ δ * e := by
    have h2 : (U - 1) * (S : ℂ_[l]) = -((algebraMap ℚ_[l] (Om l) (1 - u) * S : Om l) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_mul, hca, map_sub, map_one, ← hU]; ring
    rw [h2, norm_neg, PadicComplex.norm_extends, ← hTv]
    exact hT.trans (mul_le_mul_of_nonneg_left hv hδ)
  have hA : ‖∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))‖ ≤ e :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg he0 fun i _ => by
      rw [GlobalTheory.RingBasics.norm_σC]; exact he
  have hmain : algebraMap ℚ_[l] ℂ_[l] (u ^ N - 1) * y
      = (U - 1) * (∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))) + (U - 1) * (S : ℂ_[l]) := by
    rw [hSc, ← mul_add, ← Finset.sum_add_distrib]
    simp only [map_sub, sub_add_cancel, hpow, map_pow, map_one, ← hU]
    rw [← Finset.sum_mul, ← mul_assoc, mul_geom_sum]
  rw [← hn, ← norm_mul, hmain]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ hB)
  have h3 : ‖U - 1‖ = ‖u - 1‖ := by rw [← hn, map_sub, map_one]
  rw [norm_mul, h3]
  exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)

end GlobalTheory.InertiaEigenvalues
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_estimate_galois_eigenvector_cLTate : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l) (u : ℚ_[l]) (y : ℂ_[l]) (z : Om l) (N : ℕ) (e δ : ℝ), Per.σC γ y = algebraMap ℚ_[l] ℂ_[l] u * y → ‖u‖ = 1 → (γ ^ N) z = z → ‖y - (z : ℂ_[l])‖ ≤ e → ‖∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)‖ ≤ δ * ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ → 0 ≤ δ → ‖u ^ N - 1‖ * ‖y‖ ≤ max (‖u - 1‖ * e) (δ * e) := by
  atlas_forward_decl GlobalTheory.InertiaEigenvalues.tate_eigenvector_estimate
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem norm_pow_index_le_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup (GQ l)), H.index ≠ 0 → ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖x‖ < 1 → ‖x‖ ^ H.index ≤ ‖((l : ℕ) : Om l)‖ := by
  intro l _ H hidx x hx hx1
  have hfin : Fintype (GQ l ⧸ H) := Subgroup.fintypeOfIndexNeZero hidx
  have fout : ∀ g : GQ l, (g : GQ l ⧸ H).out x = g x := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, AlgEquiv.mul_apply, hx h h.2]
  have hfix : ∀ g : GQ l, g (∏ q : GQ l ⧸ H, q.out x) = ∏ q : GQ l ⧸ H, q.out x := fun g => by
    rw [map_prod, ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ H => q.out x]
    refine Finset.prod_congr rfl fun q _ => ?_
    have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ H) := by
      rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    rw [e, fout, AlgEquiv.mul_apply]
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have hn : ‖c‖ = ‖x‖ ^ H.index := by
    rw [← norm_algebraMap' (Om l) c, hc, norm_prod]
    refine (Finset.prod_congr rfl fun q _ => GlobalTheory.RingBasics.norm_gal (Quotient.out q) x).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
    rfl
  have hc1 : ‖c‖ < 1 := hn ▸ pow_lt_one₀ (norm_nonneg x) hx1 hidx
  have h2 : ‖c‖ ≤ (l : ℝ) ^ (-1 : ℤ) := by
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simpa using hc1
  rw [← hn, ← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]
  simpa using h2

end GlobalTheory.Per
end

section
noncomputable section
namespace GlobalTheory.WildMove
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws
open scoped Formalism.Per

private theorem charP_closedBallSubring_quotient_openBallIdeal {l : ℕ} [hl : Fact l.Prime] :
    CharP (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸ GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) l := by
  have hM := GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal (PadicAlgCl l)
  have : (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)).IsPrime := hM.isPrime
  refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
  have e : ((l : PadicAlgCl l)) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := (map_natCast _ l).symm
  push_cast
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem exists_norm_pow_prime_pow_sub_lt_one {l : ℕ} [hl : Fact l.Prime] (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) :
    ∃ f : ℕ, 0 < f ∧ ‖a ^ (l ^ f) - a‖ < 1 := by
  classical
  have : NeZero l := ⟨hl.out.ne_zero⟩
  set O := GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) with hO
  set M := GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l) with hM
  have : M.IsMaximal := GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal _
  let : Field (O ⧸ M) := Ideal.Quotient.field M
  have : CharP (O ⧸ M) l := charP_closedBallSubring_quotient_openBallIdeal
  let : Algebra (ZMod l) (O ⧸ M) := ZMod.algebra _ l

  have hcoef : ∀ c : ℚ_[l], ‖c‖ ≤ 1 → ∀ h : algebraMap ℚ_[l] (PadicAlgCl l) c ∈ O,
      Ideal.Quotient.mk M ⟨_, h⟩ ∈ Set.range (algebraMap (ZMod l) (O ⧸ M)) := by
    intro c hc h
    have key : ∀ x : ℤ_[l], ∃ n : ℕ, ‖(x : ℚ_[l]) - n‖ < 1 := by
      intro x
      obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := x)
      rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def, PadicInt.coe_sub,
        PadicInt.coe_natCast] at hn
      exact ⟨n, hn⟩
    obtain ⟨n, hn'⟩ := key ⟨c, hc⟩
    refine ⟨(n : ZMod l), ?_⟩
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
    have e : ((n : PadicAlgCl l)) = algebraMap ℚ_[l] (PadicAlgCl l) (n : ℚ_[l]) := (map_natCast _ n).symm
    push_cast
    rw [e, ← map_sub, PadicAlgCl.norm_extends, norm_sub_rev]
    exact hn'

  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  set P := minpoly ℚ_[l] a with hP
  have hPm : P.Monic := minpoly.monic hint
  have hPc : ∀ n, ‖P.coeff n‖ ≤ 1 := by
    have h1 : spectralValue P ≤ 1 := by
      rw [← PadicAlgCl.spectralNorm_eq] at ha
      exact ha
    exact (spectralValue_le_one_iff hPm).1 h1
  set Pm := P.map (algebraMap ℚ_[l] (PadicAlgCl l)) with hPm'
  have hPmO : ∀ n, Pm.coeff n ∈ O := by
    intro n
    rw [Polynomial.coeff_map, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring, PadicAlgCl.norm_extends]
    exact hPc n
  have hsub : (↑Pm.coeffs : Set (PadicAlgCl l)) ⊆ O := by
    intro x hx
    obtain ⟨n, -, hn⟩ := Polynomial.mem_coeffs_iff.1 hx
    rw [hn]
    exact hPmO n
  set Q := Pm.toSubring O hsub with hQ
  set Qb := Q.map (Ideal.Quotient.mk M) with hQb
  have hQm : Qb.Monic := ((Polynomial.monic_toSubring _ _ _).2 (hPm.map _)).map _
  have hlift : Qb ∈ Polynomial.lifts (algebraMap (ZMod l) (O ⧸ M)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hQb, Polynomial.coeff_map]
    have e : Q.coeff n = ⟨algebraMap ℚ_[l] (PadicAlgCl l) (P.coeff n), by
        rw [← Polynomial.coeff_map]; exact hPmO n⟩ := by
      apply Subtype.ext
      rw [hQ, Polynomial.coeff_toSubring]
      exact Polynomial.coeff_map _ _
    rw [e]
    exact hcoef _ (hPc n) _
  set a' : O := ⟨a, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring.2 ha⟩ with ha'
  have hQa : Q.eval a' = 0 := by
    apply Subtype.ext
    show O.subtype (Q.eval a') = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hQ, Polynomial.map_toSubring]
    show Pm.eval a = 0
    rw [hPm', Polynomial.eval_map, ← Polynomial.aeval_def, hP, minpoly.aeval]
  have hroot : Qb.eval (Ideal.Quotient.mk M a') = 0 := by
    rw [hQb, Polynomial.eval_map, Polynomial.eval₂_at_apply, hQa, map_zero]
  obtain ⟨R, hRmap, -, hRmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hQm
  have hab : IsIntegral (ZMod l) (Ideal.Quotient.mk M a') :=
    ⟨R, hRmon, by rw [← Polynomial.eval_map, hRmap]; exact hroot⟩

  have := IntermediateField.adjoin.finiteDimensional hab
  have : Finite (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) :=
    Module.finite_of_finite (ZMod l)
  let : Fintype (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) =
      l ^ Module.finrank (ZMod l) (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) := by
    rw [Module.card_eq_pow_finrank (K := ZMod l), ZMod.card]
  have hx := FiniteField.pow_card (⟨Ideal.Quotient.mk M a', IntermediateField.mem_adjoin_simple_self _ _⟩ :
    IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})
  rw [hcard] at hx
  have hx' := congrArg Subtype.val hx
  simp only [SubmonoidClass.coe_pow] at hx'
  refine ⟨Module.finrank (ZMod l) (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank (ZMod l)
        (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})) with h0 | h0
    · have h1 := Fintype.one_lt_card (α := IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})
      rw [hcard, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h0
  · have h2 : Ideal.Quotient.mk M (a' ^ (l ^ Module.finrank (ZMod l)
        (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})) - a') = 0 := by
      rw [map_sub, map_pow, hx', sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal] at h2
    simpa [ha'] using h2

private theorem exists_teichmuller_root_norm_sub_lt_one {l : ℕ} [hl : Fact l.Prime] (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) :
    ∃ ζ : PadicAlgCl l, (ζ = 0 ∨ ∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) ∧ ‖a - ζ‖ < 1 := by
  classical
  obtain ⟨f, hf, hlt⟩ := exists_norm_pow_prime_pow_sub_lt_one a ha
  have hl1 : 1 < l := hl.out.one_lt
  have hq1 : 1 < l ^ f := Nat.one_lt_pow hf.ne' hl1
  set q := l ^ f with hq
  set P : Polynomial (PadicAlgCl l) := Polynomial.X ^ q - Polynomial.X with hP
  have hPm : P.Monic := Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq1)
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm
    IsAlgClosed.card_roots_eq_natDegree
  have heval : a ^ q - a = (P.roots.map fun r => a - r).prod := by
    have h := congrArg (Polynomial.eval a) hprod
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at h
    simpa [hP, Function.comp_def] using h.symm
  by_contra hcon
  push_neg at hcon
  have hge : ∀ r ∈ P.roots, 1 ≤ ‖a - r‖ := by
    intro r hr
    have hr' : r ^ q = r := by
      have h := Polynomial.isRoot_of_mem_roots hr
      simp only [Polynomial.IsRoot, hP, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at h
      exact sub_eq_zero.1 h
    by_cases h0 : r = 0
    · exact hcon r (Or.inl h0)
    · refine hcon r (Or.inr ⟨q - 1, by omega, ?_, ?_⟩)
      · intro hd
        have h2 : l ∣ q - 1 + 1 := by rw [Nat.sub_add_cancel hq1.le, hq]; exact dvd_pow_self l hf.ne'
        have h3 : l ∣ 1 := (Nat.dvd_add_right hd).1 h2
        exact hl1.ne' (Nat.dvd_one.1 h3)
      · have h4 : r ^ (q - 1) * r = 1 * r := by
          rw [← pow_succ, Nat.sub_add_cancel hq1.le, one_mul, hr']
        exact mul_right_cancel₀ h0 h4
  have key : ∀ s : Multiset (PadicAlgCl l), (∀ r ∈ s, 1 ≤ ‖a - r‖) →
      1 ≤ ‖(s.map fun r => a - r).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons r s ih =>
      intro h
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact one_le_mul_of_one_le_of_one_le (h r (Multiset.mem_cons.2 (Or.inl rfl)))
        (ih fun x hx => h x (Multiset.mem_cons.2 (Or.inr hx)))
  have h5 := key _ hge
  rw [← heval] at h5
  exact absurd hlt (not_lt.2 h5)

private theorem norm_apply_sub_lt_one_of_fixes_prime_to_l_roots {l : ℕ} [hl : Fact l.Prime] (γ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (hγ : ∀ ζ : PadicAlgCl l, (∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) → γ ζ = ζ)
    (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) : ‖γ a - a‖ < 1 := by
  obtain ⟨ζ, hζ, hlt⟩ := exists_teichmuller_root_norm_sub_lt_one a ha
  have hfix : γ ζ = ζ := by
    rcases hζ with h0 | h1
    · rw [h0, map_zero]
    · exact hγ ζ h1
  have e : γ a - a = γ (a - ζ) + -(a - ζ) := by rw [map_sub, hfix]; ring
  have hn : ‖γ (a - ζ)‖ = ‖a - ζ‖ := (spectralNorm_eq_of_equiv γ (a - ζ)).symm
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt ?_
  rw [hn, norm_neg, max_self]
  exact hlt

private theorem apply_root_eq_of_mem_fixingSubgroup_Kur {l : ℕ} [hl : Fact l.Prime] (γ : GQ l) (hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup) :
    ∀ ζ : PadicAlgCl l, (∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) → γ ζ = ζ := by
  intro ζ hζ
  have hmem : ζ ∈ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    exact IntermediateField.subset_adjoin _ _ hζ
  exact hγ ⟨ζ, hmem⟩

theorem norm_sub_lt (l : ℕ) [hl : Fact l.Prime] (γ : GQ l) (hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup)
    (n : ℕ) (x : Om l) (hx : x ≠ 0) (h : (γ ^ l ^ n) x = x) : ‖γ x - x‖ < ‖x‖ := by
  have hn : ∀ (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (y : PadicAlgCl l), ‖g y‖ = ‖y‖ :=
    fun g y => (spectralNorm_eq_of_equiv g y).symm
  have hfix := apply_root_eq_of_mem_fixingSubgroup_Kur γ hγ
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hγx : γ x ≠ 0 := by
    intro h0
    apply hx
    rw [← norm_eq_zero, ← hn γ x, h0, norm_zero]
  set u : Om l := γ x / x with hu'
  have hu : ‖u‖ = 1 := by rw [hu', norm_div, hn, div_self hx0]
  have hind : ∀ k : ℕ, ‖(γ ^ k) x / x - u ^ k‖ < 1 := by
    intro k
    induction k with
    | zero => simp [div_self hx]
    | succ k ih =>
      have hvk : ‖(γ ^ k) x / x‖ = 1 := by rw [norm_div, hn, div_self hx0]
      have e : (γ ^ (k + 1)) x / x - u ^ (k + 1) =
          ((γ ((γ ^ k) x / x) - (γ ^ k) x / x) + ((γ ^ k) x / x - u ^ k)) * u := by
        rw [show γ ^ (k + 1) = γ * γ ^ k from pow_succ' γ k, AlgEquiv.mul_apply, pow_succ u k, map_div₀, hu']
        field_simp
        ring
      rw [e, norm_mul, hu, mul_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (norm_apply_sub_lt_one_of_fixes_prime_to_l_roots γ hfix _ hvk.le) ih)
  have hq : ‖u ^ (l ^ n) - 1‖ < 1 := by
    have h1 := hind (l ^ n)
    rw [h, div_self hx, norm_sub_rev] at h1
    exact h1
  have hM : (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)).IsMaximal :=
    GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal _
  let : Field (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸ GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) :=
    Ideal.Quotient.field _
  have : CharP (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸
    GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) l := charP_closedBallSubring_quotient_openBallIdeal
  set u' : GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) :=
    ⟨u, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring.2 hu.le⟩ with hu''
  have h1 : (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) u') ^ (l ^ n) = 1 := by
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l))),
      Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
    simpa [hu''] using hq
  have h2 : (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) u' - 1) ^ (l ^ n) = 0 := by
    rw [sub_pow_char_pow, h1, one_pow, sub_self]
  have h3 := pow_eq_zero_iff (pow_ne_zero n hl.out.ne_zero) |>.1 h2
  rw [sub_eq_zero, ← map_one (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l))),
    Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal] at h3
  have h4 : ‖u - 1‖ < 1 := by simpa [hu''] using h3
  have e : γ x - x = x * (u - 1) := by
    rw [mul_sub, mul_one, hu', mul_div_assoc', mul_comm x (γ x), mul_div_assoc, div_self hx, mul_one]
  rw [e, norm_mul]
  exact mul_lt_of_lt_one_right (norm_pos_iff.2 hx) h4

end GlobalTheory.WildMove
end
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaMove

theorem fixed_apply {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal) (σ : GQ l)
    {x : Om l} (hx : ∀ g ∈ H, g x = x) : ∀ g ∈ H, g (σ x) = σ x := by
  intro g hg
  have h := hx _ (hH.conj_mem' g hg σ)
  have h2 : σ ((σ⁻¹ * g * σ) x) = g (σ x) := by
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  rw [← h2, h]

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem norm_natCast_le_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one _ _

theorem norm_pow_sub_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : Subgroup (GQ l)), H.Normal → H.index ≠ 0 → ∀ m n : ℕ, H.index ≤ l ^ m → γ ^ l ^ n ∈ H → ∀ j ≤ m, ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖(γ ^ l ^ j) x - x‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (m - j)) * ‖x‖ := by
  intro l hl γ hγ H hH hi m n hm hn j
  have hτ0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have hτ1 := norm_natCast_le_one l
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hτpos : 0 < ‖((l : ℕ) : Om l)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hl0
  induction j with
  | zero =>
    intro _ x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hlt := GlobalTheory.WildMove.norm_sub_lt l γ hγ n x hx0 (hx _ hn)
    set z : Om l := (γ x - x) / x with hz
    have hzfix : ∀ g ∈ H, g z = z := by
      intro g hg
      rw [hz, map_div₀, map_sub, fixed_apply hH γ hx g hg, hx g hg]
    have hzn : ‖z‖ = ‖γ x - x‖ / ‖x‖ := norm_div _ _
    have hz1 : ‖z‖ < 1 := by rw [hzn, div_lt_one hxpos]; exact hlt
    have hv := GlobalTheory.Per.norm_pow_index_le_of_fixed l H hi z hzfix hz1
    have h1 : ‖z‖ ^ (l ^ m) ≤ ‖((l : ℕ) : Om l)‖ :=
      (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hm).trans hv
    have h2 : ‖z‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ m) := by
      have h3 := Real.rpow_le_rpow (by positivity) h1
        (show (0 : ℝ) ≤ ((l ^ m : ℕ) : ℝ)⁻¹ by positivity)
      rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ hl0)] at h3
      rw [one_div]
      exact_mod_cast h3
    rw [hzn, div_le_iff₀ hxpos] at h2
    simpa using h2
  | succ j ih =>
    intro hj x hx
    have ih' := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
    have hk' : m - (j + 1) = k := by omega
    rw [hk] at ih'
    rw [hk']
    set s : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hs
    have hs0 : 0 ≤ s := Real.rpow_nonneg hτ0 _
    have hs1 : s ≤ 1 := Real.rpow_le_one hτ0 hτ1 (by positivity)
    have h := (GlobalTheory.MemLoc.norm_geom_sum_galois_le l (γ ^ l ^ j) (fixedAdd H) s hs0 hs1
      (fun y hy => fixed_apply hH _ hy) (fun y hy => ih' y hy) x hx).2
    rw [← pow_mul, ← pow_succ] at h
    have hsl : s ^ l = ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ k) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hτ0]
      congr 1
      field_simp
      ring
    have hτs : ‖((l : ℕ) : Om l)‖ ≤ s ^ (l - 1) := by
      have h1 : s ^ l ≤ s ^ (l - 1) := pow_le_pow_of_le_one hs0 hs1 (by omega)
      refine le_trans ?_ h1
      rw [hsl]
      have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.pos
      have h2 : (1 : ℝ) / (l : ℝ) ^ k ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ hl1
      have h3 := Real.rpow_le_rpow_of_exponent_ge hτpos hτ1 h2
      rwa [Real.rpow_one] at h3
    rw [max_eq_left hτs, ← pow_succ, Nat.sub_add_cancel hl.out.pos, hsl] at h
    exact h

end GlobalTheory.InertiaMove
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_inertia_pow_prime_pow_sub_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : Subgroup (GQ l)), H.Normal → H.index ≠ 0 → ∀ m n : ℕ, H.index ≤ l ^ m → γ ^ l ^ n ∈ H → ∀ j ≤ m, ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖(γ ^ l ^ j) x - x‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (m - j)) * ‖x‖ := by
  atlas_forward_decl GlobalTheory.InertiaMove.norm_pow_sub_le
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ), 0 ≤ s → s ≤ 1 → (∀ x ∈ S, σ x ∈ S) → (∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) → ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧ ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  first | exact @GlobalTheory.MemLoc.norm_geom_sum_galois_le | exact GlobalTheory.MemLoc.norm_geom_sum_galois_le | (intros; apply GlobalTheory.MemLoc.norm_geom_sum_galois_le <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PartialTraceGain

theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ i ∈ Finset.range (a * b), f i = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i + a * j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ, add_comm (a * b) i]

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ < 1 := by
  have h : ((l : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem apply_mem_fixedAdd {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal)
    (σ : GQ l) {x : Om l} (hx : x ∈ fixedAdd H) : σ x ∈ fixedAdd H := by
  intro g hg
  have h1 := hx _ (hH.conj_mem' g hg σ)
  have h2 : g * σ = σ * (σ⁻¹ * g * σ) := by group
  calc g (σ x) = (g * σ) x := rfl
    _ = σ ((σ⁻¹ * g * σ) x) := by rw [h2]; rfl
    _ = σ x := by rw [h1]

theorem apply_sum_pow {l : ℕ} [Fact l.Prime] (σ : GQ l) (m : ℕ) {x : Om l}
    (hx : (σ ^ m) x = x) :
    σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ j) x := by
  have h1 : σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ (j + 1)) x := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ']; rfl
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) x) m
  rw [Finset.sum_range_succ, hx] at h2
  rw [h1]
  simpa using h2.symm

theorem pow_apply_of_fixed {l : ℕ} [Fact l.Prime] (σ : GQ l) {y : Om l} (hy : σ y = y) (i : ℕ) :
    (σ ^ i) y = y := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ]
    change (σ ^ i) (σ y) = y
    rw [hy, ih]

theorem norm_sum_pow_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : ℕ → Subgroup (GQ l)) (k : ℕ), (∀ n, (H n).Normal) → (∀ n, (H n).index ≠ 0) → (∀ n, (H n).index ≤ l ^ (k + n)) → (∀ n, γ ^ l ^ n ∈ H n) → (∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1)) → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Om l), (∀ g ∈ H n, g x = x) → ‖∑ i ∈ Finset.range (l ^ n), (γ ^ i) x‖ ≤ ρ ^ n * ‖x‖ := by
  intro l hl γ hγ H k hN hI hIle hpow hgen
  have hp : l.Prime := hl.out
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hp.one_le
  have ha0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have ha1 := norm_natCast_lt_one l
  have hpk : (1 : ℝ) ≤ (l : ℝ) ^ (k + 1) := one_le_pow₀ hl1
  have he0 : (0 : ℝ) < (1 : ℝ) / (l : ℝ) ^ (k + 1) := by positivity
  have he1 : (1 : ℝ) / (l : ℝ) ^ (k + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hpk
  set ρ : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg ha0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one ha0 ha1 he0
  have haρ : ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    have := Real.rpow_le_rpow_of_exponent_ge' ha0 ha1.le he0.le he1
    rwa [Real.rpow_one] at this
  have hmax : max (ρ ^ (l - 1)) ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    refine max_le ?_ haρ
    have h2 := hp.two_le
    exact pow_le_of_le_one hρ0 hρ1.le (by omega)
  refine ⟨ρ, hρ0, hρ1, fun n => ?_⟩
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    set σ : GQ l := γ ^ l ^ n with hσ
    have hσl : σ ^ l = γ ^ l ^ (n + 1) := by rw [hσ, ← pow_mul, ← pow_succ]
    have hxS : x ∈ fixedAdd (H (n + 1)) := hx
    set y : Om l := ∑ j ∈ Finset.range l, (σ ^ j) x with hy
    have hyS : y ∈ fixedAdd (H (n + 1)) :=
      sum_mem fun j _ => apply_mem_fixedAdd (hN _) _ hxS
    have hσy : σ y = y := apply_sum_pow σ l (by rw [hσl]; exact hx _ (hpow _))
    have hyH : ∀ g ∈ H n, g y = y := by
      intro g hg
      obtain ⟨i, hi⟩ := hgen n g hg
      have h1 := hyS _ hi
      have h2 : g = σ ^ i * ((σ ^ i)⁻¹ * g) := by group
      calc g y = (σ ^ i) (((σ ^ i)⁻¹ * g) y) := by
            conv_lhs => rw [h2]
            rfl
        _ = y := by rw [h1, pow_apply_of_fixed σ hσy]
    have hmove : ∀ z ∈ fixedAdd (H (n + 1)), ‖σ z - z‖ ≤ ρ * ‖z‖ := by
      intro z hz
      have := GlobalTheory.T.norm_inertia_pow_prime_pow_sub_le l γ hγ (H (n + 1)) (hN _) (hI _) (k + (n + 1)) (n + 1) (hIle _)
        (hpow _) n (by omega) z hz
      rwa [show k + (n + 1) - n = k + 1 by omega] at this
    have hyn : ‖y‖ ≤ ρ * ‖x‖ :=
      (GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le l σ (fixedAdd (H (n + 1))) ρ hρ0 hρ1.le
        (fun z hz => apply_mem_fixedAdd (hN _) σ hz) hmove x hxS).1.trans
        (mul_le_mul_of_nonneg_right hmax (norm_nonneg _))
    have hsum : ∑ i ∈ Finset.range (l ^ (n + 1)), (γ ^ i) x
        = ∑ i ∈ Finset.range (l ^ n), (γ ^ i) y := by
      rw [pow_succ, sum_range_mul_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hy, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add, pow_mul]; rfl
    rw [hsum]
    calc _ ≤ ρ ^ n * ‖y‖ := ih y hyH
      _ ≤ ρ ^ n * (ρ * ‖x‖) := mul_le_mul_of_nonneg_left hyn (pow_nonneg hρ0 _)
      _ = ρ ^ (n + 1) * ‖x‖ := by ring

end GlobalTheory.PartialTraceGain
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_inertia_partialTrace_geometric_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : ℕ → Subgroup (GQ l)) (k : ℕ), (∀ n, (H n).Normal) → (∀ n, (H n).index ≠ 0) → (∀ n, (H n).index ≤ l ^ (k + n)) → (∀ n, γ ^ l ^ n ∈ H n) → (∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1)) → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Om l), (∀ g ∈ H n, g x = x) → ‖∑ i ∈ Finset.range (l ^ n), (γ ^ i) x‖ ≤ ρ ^ n * ‖x‖ := by
  atlas_forward_decl GlobalTheory.PartialTraceGain.norm_sum_pow_le
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.TateEigen

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_pos : 0 < ‖((l : ℕ) : ℤ_[l])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem norm_l_lt_one : ‖((l : ℕ) : ℤ_[l])‖ < 1 := by
  rw [PadicInt.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem exists_pow_near_one (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ u : ℤ_[l]ˣ, ‖((u ^ N : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ k := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨Nat.card (ZMod (l ^ k))ˣ, Nat.card_pos, fun u => ?_⟩
  have h : (Units.map (PadicInt.toZModPow (p := l) k).toMonoidHom u) ^ Nat.card (ZMod (l ^ k))ˣ = 1 :=
    pow_card_eq_one'
  have h2 : ((u ^ Nat.card (ZMod (l ^ k))ˣ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
      RingHom.ker (PadicInt.toZModPow (p := l) k) := by
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
    rw [← map_pow] at h
    exact congrArg Units.val h
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨w, hw⟩ := h2
  rw [hw, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one w)

theorem exists_norm_eq_pow (x : ℤ_[l]) (hx : x ≠ 0) : ∃ k : ℕ, ‖x‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ k := by
  refine ⟨x.valuation, ?_⟩
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [norm_mul, PadicInt.norm_units, one_mul, norm_pow]

theorem finite_on_inertia : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (y : ℂ_[l]), y ≠ 0 →
    (∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y) →
    ∃ N : ℕ, 0 < N ∧ ∀ γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup, η γ ^ N = 1 := by
  intro l _ η y hy hη
  obtain ⟨c, hc, hax⟩ := GlobalTheory.T.axLemma_padicComplex_fixed_element_approximation l
  have hτ0 := norm_l_pos (l := l)
  have hτ1 := norm_l_lt_one (l := l)
  set τ := ‖((l : ℕ) : ℤ_[l])‖ with hτ
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc) hτ1
  obtain ⟨N, hN, hNu⟩ := exists_pow_near_one (l := l) (k₁ + 2)
  refine ⟨N, hN, fun γ₀ hγ₀ => ?_⟩
  by_contra hne
  set γ := γ₀ ^ N with hγdef
  have hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := pow_mem hγ₀ N
  have hηγ : η γ = η γ₀ ^ N := map_pow _ _ _
  have hne' : (η γ : ℤ_[l]) - 1 ≠ 0 := by
    intro h
    apply hne
    rw [← hηγ]
    exact Units.ext (sub_eq_zero.1 h)
  obtain ⟨k, hk⟩ := exists_norm_eq_pow _ hne'
  have hkk : k₁ + 2 ≤ k := by
    have := hNu (η γ₀)
    rw [← hηγ, hk] at this
    exact (pow_le_pow_iff_right_of_lt_one₀ hτ0 hτ1).1 this
  have hk2 : 2 ≤ k := by omega
  obtain ⟨H, hmem, hnorm, hidx, hidx', hpow, hgen⟩ := GlobalTheory.T.exists_normal_subgroup_filtration_index_bounded l η γ k hk2 hk
  obtain ⟨ρ, hρ0, hρ1, hgain⟩ := GlobalTheory.T.norm_inertia_partialTrace_geometric_le l γ hγ H k hnorm hidx hidx' hpow hgen
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc) hρ1
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hr : 0 < τ ^ (k + n) * ‖y‖ := by positivity
  obtain ⟨z, hz, hyz⟩ := hax (H n) y (τ ^ (k + n) * ‖y‖) hr (by
    intro g hg
    have e : Per.σC g y - y = algebraMap ℚ_[l] ℂ_[l] ((((η g : ℤ_[l]) - 1 : ℤ_[l])) : ℚ_[l]) * y := by
      rw [hη g, PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]; ring
    rw [e, norm_mul, norm_algebraMap']
    exact mul_le_mul_of_nonneg_right ((hmem n g).1 hg) hy0.le)
  have hv : ∀ g ∈ H n, g (γ z - algebraMap ℚ_[l] (Om l) ((η γ : ℤ_[l]) : ℚ_[l]) * z) =
      γ z - algebraMap ℚ_[l] (Om l) ((η γ : ℤ_[l]) : ℚ_[l]) * z := by
    intro g hg
    have h1 := hz _ ((hnorm n).conj_mem' g hg γ)
    have h2 : g (γ z) = γ z := by
      have := congrArg γ h1
      simpa [mul_assoc] using this
    rw [map_sub, map_mul, h2, hz g hg, AlgEquiv.commutes]
  have hest := GlobalTheory.T.tate_estimate_galois_eigenvector_cLTate l γ ((η γ : ℤ_[l]) : ℚ_[l]) y z (l ^ n) (c * (τ ^ (k + n) * ‖y‖)) (ρ ^ n)
    (hη γ) (PadicInt.norm_units (η γ)) (hz _ (hpow n)) hyz (hgain n _ hv) (by positivity)
  have hlte := GlobalTheory.T.norm_pow_prime_pow_sub_one_of_norm_sub_one l (η γ : ℤ_[l]) k hk2 hk n
  have e1 : ‖((η γ : ℤ_[l]) : ℚ_[l]) ^ l ^ n - 1‖ = τ ^ (k + n) := by
    rw [hτ, ← hlte, PadicInt.norm_def]; push_cast; rfl
  have e2 : ‖((η γ : ℤ_[l]) : ℚ_[l]) - 1‖ = τ ^ k := by
    rw [hτ, ← hk, PadicInt.norm_def]; push_cast; rfl
  rw [e1, e2] at hest
  have hk' : τ ^ k < c⁻¹ := lt_of_le_of_lt (pow_le_pow_of_le_one hτ0.le hτ1.le (by omega)) hk₁
  have key : ∀ a : ℝ, a < c⁻¹ → a * (c * (τ ^ (k + n) * ‖y‖)) < τ ^ (k + n) * ‖y‖ := by
    intro a ha
    have : a * c < 1 := by
      have := mul_lt_mul_of_pos_right ha hc
      rwa [inv_mul_cancel₀ hc.ne'] at this
    rw [← mul_assoc]
    exact mul_lt_of_lt_one_left hr this
  exact absurd hest (not_le.2 (max_lt (key _ hk') (key _ hn)))

end GlobalTheory.TateEigen
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_character_finite_on_inertia_of_eigenvector : ∀ (l : ℕ) [Fact l.Prime] (η : GQ l →* ℤ_[l]ˣ) (y : ℂ_[l]), y ≠ 0 → (∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y) → ∃ N : ℕ, 0 < N ∧ ∀ γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup, η γ ^ N = 1 := by
  atlas_forward_decl GlobalTheory.TateEigen.finite_on_inertia
end
