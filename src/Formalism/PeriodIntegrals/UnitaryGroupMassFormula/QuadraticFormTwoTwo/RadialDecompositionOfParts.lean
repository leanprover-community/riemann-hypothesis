import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.CbStrictMonoOfAnti
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.GANormSqStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.InLieW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticFormTwoTwo.AdUnitBLie

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem gb_entry {i j : Fin (2 * r + k + 1)} (hj : r ≤ j.val) (hj' : j.val ≤ r + k) :
    Hpk k r i j = if i = j then (if j.val = r + k then -1 else 1) else 0 := by
  simp only [Hpk]
  by_cases h : i = j
  · subst h
    have h1 : ¬ (i.val < r ∧ i.val + i.val = 2 * r + k) := by omega
    rw [if_neg h1, if_neg h1, if_pos ⟨hj, hj', rfl⟩, if_pos rfl]
  · have h1 : ¬ (i.val < r ∧ i.val + j.val = 2 * r + k) := by omega
    have h2 : ¬ (j.val < r ∧ i.val + j.val = 2 * r + k) := by omega
    have h3 : ¬ (r ≤ i.val ∧ i.val ≤ r + k ∧ i = j) := fun hh => h hh.2.2
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h]

theorem gb_mulVec {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    Hpk k r *ᵥ v = fun i => (if i.val = r + k then -1 else 1) * v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [gb_entry hi.1 hi.2, if_pos rfl]
    · rw [hv i (by omega)]; ring
  · intro b _ hb
    by_cases hb' : r ≤ b.val ∧ b.val ≤ r + k
    · rw [gb_entry hb'.1 hb'.2, if_neg (Ne.symm hb)]; ring
    · rw [hv b (by omega)]; ring
  · intro h; exact absurd (Finset.mem_univ i) h

theorem gb_herm {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ i, star (w i) * ((if i.val = r + k then -1 else 1) * v i) := by
  unfold herm
  rw [gb_mulVec hv]
  simp only [dotProduct, Pi.star_apply]

theorem gb_symm {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  rw [gb_herm hv, gb_herm hw, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp only [star_mul', star_star, star_neg, star_one] <;> ring

theorem gb_add_left (v v' w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (v + v') w = herm (Hpk k r) v w + herm (Hpk k r) v' w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

theorem gb_smul_left (c : ℂ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (c • v) w = c * herm (Hpk k r) v w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem gb_sub_left (v v' w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (v - v') w = herm (Hpk k r) v w - herm (Hpk k r) v' w := by
  simp only [herm, Matrix.mulVec_sub, dotProduct_sub]

theorem gb_smul_right (c : ℂ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (c • w) = star c * herm (Hpk k r) v w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem gb_sub_right (v w w' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (w - w') = herm (Hpk k r) v w - herm (Hpk k r) v w' := by
  simp only [herm, star_sub, sub_dotProduct]

theorem gb_wb_smul {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (c : ℂ) : inWb k r (c • v) := by
  intro i hi
  simp [hv i hi]

theorem gb_wb_sub {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w) : inWb k r (v - w) := by
  intro i hi
  simp [hv i hi, hw i hi]


theorem gb_pos {z v : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hv : inWb k r v)
    (hvz : herm (Hpk k r) v z = 0) (hv0 : v ≠ 0) : 0 < (herm (Hpk k r) v v).re := by
  classical
  obtain ⟨t, htv⟩ : ∃ t : Fin (2 * r + k + 1), t.val = r + k := ⟨⟨r + k, by omega⟩, rfl⟩
  have key : ∀ a b : Fin (2 * r + k + 1) → ℂ, inWb k r a →
      herm (Hpk k r) a b = -(star (b t) * a t) + ∑ i ∈ Finset.univ.erase t, star (b i) * a i := by
    intro a b ha
    rw [gb_herm ha, ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    congr 1
    · rw [if_pos htv]; ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i.val ≠ r + k := fun h => Finset.ne_of_mem_erase hi (Fin.ext (by rw [htv]; exact h))
      rw [if_neg hne]; ring
  have nsq : ∀ x : ℂ, (star x * x).re = ‖x‖ ^ 2 := by
    intro x
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have hre : ∀ a : Fin (2 * r + k + 1) → ℂ, inWb k r a →
      (herm (Hpk k r) a a).re = (∑ i ∈ Finset.univ.erase t, ‖a i‖ ^ 2) - ‖a t‖ ^ 2 := by
    intro a ha
    rw [key a a ha, Complex.add_re, Complex.neg_re, nsq, Complex.re_sum]
    simp only [nsq]
    ring
  have hzz : (∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2) < ‖z t‖ ^ 2 := by
    have h1 := hre z hz
    unfold Tz at hT
    linarith
  have hvz' : ∑ i ∈ Finset.univ.erase t, star (z i) * v i = star (z t) * v t := by
    have h1 := key v z hv
    rw [hvz] at h1
    linear_combination -h1
  have cs1 : ‖z t‖ * ‖v t‖ ≤ ∑ i ∈ Finset.univ.erase t, ‖z i‖ * ‖v i‖ := by
    have e : ‖z t‖ * ‖v t‖ = ‖∑ i ∈ Finset.univ.erase t, star (z i) * v i‖ := by
      rw [hvz', norm_mul, norm_star]
    rw [e]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, norm_star]
  have cs2 : (∑ i ∈ Finset.univ.erase t, ‖z i‖ * ‖v i‖) ^ 2 ≤
      (∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2) * ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hS0 : 0 ≤ ‖z t‖ * ‖v t‖ := by positivity
  have hab : (‖z t‖ * ‖v t‖) ^ 2 ≤
      (∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2) * ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 := by
    nlinarith [mul_le_mul cs1 cs1 hS0 (hS0.trans cs1)]
  have hNz : 0 ≤ ∑ i ∈ Finset.univ.erase t, ‖z i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hNv : 0 ≤ ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  rw [hre v hv]
  by_contra hneg
  push_neg at hneg
  have hle : (∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2) ≤ ‖v t‖ ^ 2 := by linarith
  have hb : ‖v t‖ ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg hNz (sub_nonneg.2 hle), sq_nonneg ‖v t‖]
  have hvt : v t = 0 := by
    have h2 : ‖v t‖ ^ 2 = 0 := le_antisymm hb (sq_nonneg _)
    simpa using h2
  have hNv0 : ∑ i ∈ Finset.univ.erase t, ‖v i‖ ^ 2 = 0 := by linarith
  have hvE : ∀ i ∈ Finset.univ.erase t, v i = 0 := by
    intro i hi
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 hNv0 i hi
    simpa using h3
  apply hv0
  funext i
  by_cases hi : i = t
  · subst hi; simpa using hvt
  · simpa using hvE i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)

theorem gb_normalize {b v : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hT : 0 < Tz k r b) (hv : inWb k r v)
    (hvb : herm (Hpk k r) v b = 0) (hv0 : v ≠ 0) : ∃ s : ℂ, herm (Hpk k r) (s • v) (s • v) = 1 := by
  have hp := gb_pos hb hT hv hvb hv0
  have him : (herm (Hpk k r) v v).im = 0 := by
    have h := congrArg Complex.im (gb_symm hv hv)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  set q := (herm (Hpk k r) v v).re with hq
  have hvv : herm (Hpk k r) v v = (q : ℂ) := Complex.ext (by simp [hq]) (by simp [him])
  refine ⟨(((Real.sqrt q)⁻¹ : ℝ) : ℂ), ?_⟩
  rw [gb_smul_left, gb_smul_right, hvv]
  have hst : star (((Real.sqrt q)⁻¹ : ℝ) : ℂ) = (((Real.sqrt q)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hst]
  have hne : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hr : ((Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) : ℝ) = 1 := by
    field_simp
    linarith [Real.mul_self_sqrt hp.le, Real.sq_sqrt hp.le]
  exact_mod_cast hr

def gbL (c : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun v := herm (Hpk k r) v c
  map_add' v w := gb_add_left v w c
  map_smul' a v := by simp only [gb_smul_left, smul_eq_mul, RingHom.id_apply]

theorem gb_perp {m : ℕ} (hm : m + 2 < k + 1) (cs : Fin m → Fin (2 * r + k + 1) → ℂ)
    (a b : Fin (2 * r + k + 1) → ℂ) :
    ∃ v, v ≠ 0 ∧ inWb k r v ∧ herm (Hpk k r) v a = 0 ∧ herm (Hpk k r) v b = 0 ∧
      ∀ j, herm (Hpk k r) v (cs j) = 0 := by
  classical
  obtain ⟨c, hca, hcb, hcs⟩ : ∃ c : Fin (m + 2) → Fin (2 * r + k + 1) → ℂ,
      c 0 = a ∧ c (Fin.succ 0) = b ∧ ∀ j : Fin m, c j.succ.succ = cs j :=
    ⟨Fin.cons a (Fin.cons b cs), by simp, by simp, fun j => by simp⟩
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ),
      ∀ x, emb x = Function.extend (wI k r) x 0 :=
    ⟨Function.ExtendByZero.linearMap ℂ (wI k r), fun x => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (m + 2) → ℂ),
      ∀ x j, L x j = herm (Hpk k r) (emb x) (c j) :=
    ⟨(LinearMap.pi fun j => gbL (c j)) ∘ₗ emb, fun x j => rfl⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  have hle : Module.finrank ℂ (LinearMap.range L) ≤ m + 2 := by
    have h1 := Submodule.finrank_le (LinearMap.range L)
    simpa using h1
  simp only [Module.finrank_fin_fun] at hrk
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker L) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hx0' : x ≠ 0 := fun h => hx0 (by subst h; rfl)
  have hL0 : ∀ j, herm (Hpk k r) (emb x) (c j) = 0 := by
    intro j
    have h1 := congrFun (LinearMap.mem_ker.1 hx) j
    rw [hL] at h1
    exact h1
  have hinj : Function.Injective (wI k r) := by
    intro p q h
    simp only [wI, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  refine ⟨emb x, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hx0'
    funext j
    have h1 := congrFun h0 (wI k r j)
    rw [hemb, hinj.extend_apply] at h1
    simpa using h1
  · intro i hi
    have hni : ¬∃ p, wI k r p = i := by
      rintro ⟨p, rfl⟩
      have := p.isLt
      simp only [wI, Fin.val_mk] at hi
      omega
    rw [hemb, Function.extend_apply' _ _ _ hni, Pi.zero_apply]
  · have h1 := hL0 0
    rwa [hca] at h1
  · have h1 := hL0 (Fin.succ 0)
    rwa [hcb] at h1
  · intro j
    have h1 := hL0 j.succ.succ
    rwa [hcs] at h1

theorem exists_frame_of_positive_vector {a b : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hT : 0 < Tz k r b) :
    ∀ m, m ≤ k - 1 → ∃ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [a, b] Bs := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨Fin.elim0, ?_⟩
    unfold IsFrameOf
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨Bs, hB⟩ := ih (by omega)
    unfold IsFrameOf at hB
    obtain ⟨hB1, hB2, hB3⟩ := hB
    obtain ⟨v, hv0, hvw, hva, hvb, hvc⟩ := gb_perp (by omega) Bs a b
    obtain ⟨s, hs⟩ := gb_normalize hb hT hvw hvb hv0
    have hsv : inWb k r (s • v) := gb_wb_smul hvw s
    have h1 : ∀ i, herm (Hpk k r) (Bs i) (s • v) = 0 := by
      intro i
      rw [gb_smul_right, gb_symm (hB1 i) hvw, hvc i, star_zero, mul_zero]
    have h2 : ∀ i, herm (Hpk k r) (s • v) (Bs i) = 0 := by
      intro i
      rw [gb_smul_left, hvc i, mul_zero]
    refine ⟨Fin.snoc Bs (s • v), ?_⟩
    unfold IsFrameOf
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact hsv
      · rw [Fin.snoc_castSucc]; exact hB1 j
    · intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
      · rw [Fin.snoc_last, if_pos rfl]; exact hs
      · rw [Fin.snoc_last, Fin.snoc_castSucc, h2, if_neg (Fin.castSucc_lt_last j').ne']
      · rw [Fin.snoc_last, Fin.snoc_castSucc, h1, if_neg (Fin.castSucc_lt_last i').ne]
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, hB2]
        by_cases h : i' = j' <;> simp [h]
    · intro i w hw
      have hw' := hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw'
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]
        rcases hw' with rfl | rfl
        · rw [gb_smul_left, hva, mul_zero]
        · rw [gb_smul_left, hvb, mul_zero]
      · rw [Fin.snoc_castSucc]; exact hB3 j w hw

theorem exists_frame {a b : Fin (2 * r + k + 1) → ℂ} (ha : inWb k r a) (hb : inWb k r b) (hT : 0 < Tz k r b) :
    ∃ Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [a, b] Bs := exists_frame_of_positive_vector hb hT (k - 1) le_rfl

theorem exists_unit {z a : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ha : inWb k r a)
    (hind : ∀ c : ℂ, a ≠ c • z) :
    ∃ e : Fin (2 * r + k + 1) → ℂ, inWb k r e ∧ herm (Hpk k r) e z = 0 ∧ herm (Hpk k r) e e = 1 ∧
      ∀ v, herm (Hpk k r) v a = 0 → herm (Hpk k r) v z = 0 → herm (Hpk k r) v e = 0 := by
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    intro h
    unfold Tz at hT
    rw [h] at hT
    simp at hT
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = herm (Hpk k r) a z / herm (Hpk k r) z z := ⟨_, rfl⟩
  have hwb : inWb k r (a - c • z) := gb_wb_sub ha (gb_wb_smul hz c)
  have hwz : herm (Hpk k r) (a - c • z) z = 0 := by
    rw [gb_sub_left, gb_smul_left, hc]
    simp [hzz]
  have hw0 : a - c • z ≠ 0 := by
    intro h
    exact hind c (sub_eq_zero.1 h)
  obtain ⟨s, hs⟩ := gb_normalize hz hT hwb hwz hw0
  refine ⟨s • (a - c • z), gb_wb_smul hwb s, ?_, hs, ?_⟩
  · rw [gb_smul_left, hwz, mul_zero]
  · intro v hva hvz
    rw [gb_smul_right, gb_sub_right, gb_smul_right, hva, hvz]
    ring

theorem geom_package {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    (hT' : 0 < Tz k r z') {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hGG : GGl k r z z' g ≠ 0) :
    ∃ (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (e' e : Fin (2 * r + k + 1) → ℂ),
      IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs ∧
      inWb k r e' ∧ herm (Hpk k r) e' z' = 0 ∧ herm (Hpk k r) e' e' = 1 ∧ IsFrameOf k r [z', e'] Bs ∧
      inWb k r e ∧ herm (Hpk k r) e z = 0 ∧ herm (Hpk k r) e e = 1 ∧
      IsFrameOf k r [z, e] (fun a => g *ᵥ Bs a) := by
  have hgi := glev_inWb hg hz
  have hgi' := glev_inWb hg hz'
  obtain ⟨hnp1, hnp2⟩ := not_prop_of_GG hz hz' hg hGG
  obtain ⟨_, hu2⟩ := glev_unit hg
  obtain ⟨Bs, hB⟩ := exists_frame hgi.2 hz' hT'
  obtain ⟨e', he'w, he'z, he'e, he'v⟩ := exists_unit hz' hT' hgi.2 hnp1
  obtain ⟨e, hew, hez, hee, hev⟩ := exists_unit hz hT hgi'.1 hnp2
  have hB' := hB
  unfold IsFrameOf at hB'
  obtain ⟨hB1, hB2, hB3⟩ := hB'
  have hBa : ∀ a, herm (Hpk k r) (Bs a) (g⁻¹ *ᵥ z) = 0 := fun a => hB3 a _ (by simp)
  have hBb : ∀ a, herm (Hpk k r) (Bs a) z' = 0 := fun a => hB3 a _ (by simp)
  have hgz : g *ᵥ (g⁻¹ *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hu2, Matrix.one_mulVec]
  have hgB : ∀ a, herm (Hpk k r) (g *ᵥ Bs a) z = 0 := by
    intro a
    have h1 := glev_herm hg (Bs a) (g⁻¹ *ᵥ z)
    rw [hgz] at h1
    rw [h1]
    exact hBa a
  refine ⟨Bs, e', e, hB, he'w, he'z, he'e, ?_, hew, hez, hee, ?_⟩
  · unfold IsFrameOf
    refine ⟨hB1, hB2, ?_⟩
    intro a v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with h | h
    · rw [h]; exact hBb a
    · rw [h]; exact he'v (Bs a) (hBa a) (hBb a)
  · unfold IsFrameOf
    refine ⟨fun a => (glev_inWb hg (hB1 a)).1, fun a b => ?_, ?_⟩
    · show herm (Hpk k r) (g *ᵥ Bs a) (g *ᵥ Bs b) = if a = b then 1 else 0
      rw [glev_herm hg]
      exact hB2 a b
    · intro a v hv
      show herm (Hpk k r) (g *ᵥ Bs a) v = 0
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with h | h
      · rw [h]; exact hgB a
      · rw [h]
        apply hev
        · rw [glev_herm hg]; exact hBb a
        · exact hgB a

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section SlopeTestRemainingChoices

variable {k r : ℕ}

theorem ffa_hpk_esI_row (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem ffa_herm_esI (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) x (bvec (esI k r a)) = x (eI k r a) := by
  have hs : star (bvec (esI k r a)) = bvec (esI k r a) := by
    funext j
    by_cases h : j = esI k r a <;> simp [bvec, h]
  unfold herm
  rw [hs]
  simp [bvec, mulVec, dotProduct, Pi.single_apply, ffa_hpk_esI_row]

theorem ffa_herm_UH {n : Mx k r} (hn : n ∈ UH (Hpk k r)) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (n *ᵥ x) (n *ᵥ y) = herm (Hpk k r) x y := by
  have hn' : nᴴ * Hpk k r * n = Hpk k r := hn
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hn']

private theorem hpk_eI_apply (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem herm_bvec_eI_quadratic_form_two_two (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) x (bvec (eI k r a)) = x (esI k r a) := by
  have hs : star (bvec (eI k r a)) = bvec (eI k r a) := by
    funext j
    by_cases h : j = eI k r a <;> simp [bvec, h]
  unfold herm
  rw [hs]
  simp [bvec, mulVec, dotProduct, Pi.single_apply, hpk_eI_apply]

theorem ffa_nlev_fix {n : Mx k r} (hn : n ∈ Nlev k r (Fin.last r)) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : n *ᵥ w = w := by
  rcases hn with ⟨⟨hU, -, h3⟩, -, hG⟩
  have hlast : ∀ a : Fin r, a.val < (Fin.last r).val := fun a => by simp
  funext i
  have hi := i.isLt
  by_cases hlo : i.val < r
  · have hi' : i = eI k r ⟨i.val, hlo⟩ := Fin.ext (by simp [eI])
    rw [hi', ← ffa_herm_esI (n *ᵥ w), ← ffa_herm_esI w]
    conv_lhs => rw [← (hG ⟨i.val, hlo⟩ (hlast _)).2]
    exact ffa_herm_UH hU w _
  by_cases hhi : r + k < i.val
  · have hb : 2 * r + k - i.val < r := by omega
    have hi' : i = esI k r ⟨2 * r + k - i.val, hb⟩ := Fin.ext (by simp [esI]; omega)
    rw [hi', ← herm_bvec_eI_quadratic_form_two_two (n *ᵥ w), ← herm_bvec_eI_quadratic_form_two_two w]
    conv_lhs => rw [← (hG ⟨2 * r + k - i.val, hb⟩ (hlast _)).1]
    exact ffa_herm_UH hU w _
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [h3 i i (by omega) (by omega) (by omega), if_pos rfl, one_mul]
  · intro j _ hji
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [h3 i j hj.1 hj.2 (by omega), if_neg (Ne.symm hji), zero_mul]
    · rw [hw j (by omega), mul_zero]
  · simp

theorem ffa_fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  unfold fvec
  rw [dif_neg (by simp)]

theorem ffa_zeta_left {z z' : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UH (Hpk k r)) (hz : h *ᵥ z = z)
    (g : Mx k r) : zetaL k r z z' (Fin.last r) (h * g) = zetaL k r z z' (Fin.last r) g := by
  unfold zetaL
  simp only [ffa_fvec_last]
  rw [← mulVec_mulVec, ← ffa_herm_UH hh (g *ᵥ z') z, hz]

theorem ffa_zeta_right {z z' : Fin (2 * r + k + 1) → ℂ} {h' : Mx k r} (hz' : h' *ᵥ z' = z')
    (g : Mx k r) : zetaL k r z z' (Fin.last r) (g * h') = zetaL k r z z' (Fin.last r) g := by
  unfold zetaL
  simp only [ffa_fvec_last]
  rw [← mulVec_mulVec, hz']

theorem ffa_GG_left {z z' : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UH (Hpk k r)) (hz : h *ᵥ z = z)
    (g : Mx k r) : GGl k r z z' (h * g) = GGl k r z z' g := by
  unfold GGl
  rw [ffa_zeta_left hh hz]

theorem ffa_GG_right {z z' : Fin (2 * r + k + 1) → ℂ} {h' : Mx k r} (hz' : h' *ᵥ z' = z')
    (g : Mx k r) : GGl k r z z' (g * h') = GGl k r z z' g := by
  unfold GGl
  rw [ffa_zeta_right hz']

def ffaZetaLin (z z' : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℝ] ℂ where
  toFun x := herm (Hpk k r) (x *ᵥ z') z
  map_add' x y := by simp [herm, add_mulVec, mulVec_add, dotProduct_add]
  map_smul' c x := by
    simp only [herm, RingHom.id_apply]
    rw [smul_mulVec, mulVec_smul, dotProduct_smul]

theorem ffa_GG_contDiff (z z' : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ ∞ (fun x : Mx k r => (GGl k r z z' x : ℂ)) := by
  have hζ : ContDiff ℝ ∞ (fun x : Mx k r => zetaL k r z z' (Fin.last r) x) := by
    have h1 := (LinearMap.toContinuousLinearMap (ffaZetaLin z z')).contDiff (n := ∞)
    convert h1 using 1
    funext x
    simp only [zetaL, ffa_fvec_last]
    rfl
  have hc : ContDiff ℝ ∞ (fun x : Mx k r => Complex.conjCLE (zetaL k r z z' (Fin.last r) x)) :=
    Complex.conjCLE.contDiff.comp hζ
  have he : (fun x : Mx k r => (GGl k r z z' x : ℂ)) = fun x =>
      zetaL k r z z' (Fin.last r) x * Complex.conjCLE (zetaL k r z z' (Fin.last r) x) -
        (Tz k r z : ℂ) * (Tz k r z' : ℂ) := by
    funext x
    simp [GGl, Complex.mul_conj]
  rw [he]
  exact (hζ.mul hc).sub contDiff_const

end SlopeTestRemainingChoices

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}

theorem ff_zero : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ FFl k r z z' π π' (Fin.last r) D := by
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq]
  refine ⟨fun g₀ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const,
    fun _ _ _ => rfl⟩, fun _ _ _ _ => (smul_zero _).symm, fun _ _ _ _ => (smul_zero _).symm,
    fun _ _ _ _ _ _ => ?_⟩
  simp

theorem ff_add {J₁ J₂ : Mx k r → (Wq →L[ℂ] Wp)} (h₁ : J₁ ∈ FFl k r z z' π π' (Fin.last r) D)
    (h₂ : J₂ ∈ FFl k r z z' π π' (Fin.last r) D) : (fun x => J₁ x + J₂ x) ∈ FFl k r z z' π π' (Fin.last r) D := by
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq] at h₁ h₂ ⊢
  obtain ⟨s₁, l₁, r₁, e₁⟩ := h₁
  obtain ⟨s₂, l₂, r₂, e₂⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U₁, F₁, o₁, m₁, c₁, q₁⟩ := s₁ g₀ hg₀
    obtain ⟨U₂, F₂, o₂, m₂, c₂, q₂⟩ := s₂ g₀ hg₀
    refine ⟨U₁ ∩ U₂, fun x => F₁ x + F₂ x, o₁.inter o₂, ⟨m₁, m₂⟩,
      (c₁.mono Set.inter_subset_left).add (c₂.mono Set.inter_subset_right), fun g hg hgl => ?_⟩
    rw [q₁ g hg.1 hgl, q₂ g hg.2 hgl]
  · intro g hg n hn
    rw [l₁ g hg n hn, l₂ g hg n hn, smul_add]
  · intro g hg n hn
    rw [r₁ g hg n hn, r₂ g hg n hn, smul_add]
  · intro g hg h hh h' hh'
    rw [e₁ g hg h hh h' hh', e₂ g hg h hh h' hh', ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]

theorem ff_smul {J : Mx k r → (Wq →L[ℂ] Wp)} (h : J ∈ FFl k r z z' π π' (Fin.last r) D) (c : ℂ) :
    (fun x => c • J x) ∈ FFl k r z z' π π' (Fin.last r) D := by
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq] at h ⊢
  obtain ⟨s, l, rr, e⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, o, m, cd, q⟩ := s g₀ hg₀
    exact ⟨U, fun x => c • F x, o, m, cd.const_smul c, fun g hg hgl => by rw [q g hg hgl]⟩
  · intro g hg n hn
    rw [l g hg n hn, smul_comm]
  · intro g hg n hn
    rw [rr g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    rw [e g hg h hh h' hh', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

theorem ff_GGinv (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D)
    (hGG : ∀ g ∈ D, GGl k r z z' g ≠ 0) {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) :
    (fun x => ((GGl k r z z' x : ℂ))⁻¹ • J x) ∈ FFl k r z z' π π' (Fin.last r) D := by
  have hcd := ffa_GG_contDiff (k := k) (r := r) z z'
  simp only [FFl, SmoothLev, LeftEq, RightEq, Set.mem_ofPred_eq] at hJ ⊢
  obtain ⟨s, l, rr, e⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, o, m, cd, q⟩ := s g₀ hg₀
    have ho : IsOpen {x : Mx k r | (GGl k r z z' x : ℂ) ≠ 0} :=
      isOpen_ne_fun hcd.continuous continuous_const
    refine ⟨U ∩ {x : Mx k r | (GGl k r z z' x : ℂ) ≠ 0}, fun x => ((GGl k r z z' x : ℂ))⁻¹ • F x,
      o.inter ho, ⟨m, Complex.ofReal_ne_zero.mpr (hGG g₀ hg₀.2)⟩, ?_, fun g hg hgl => by rw [q g hg.1 hgl]⟩
    exact ((hcd.contDiffOn.mono Set.inter_subset_left).inv (fun x hx => hx.2)).smul
      (cd.mono Set.inter_subset_left)
  · intro g hg n hn
    have hnz : n *ᵥ z = z := ffa_nlev_fix hn hz
    rw [l g hg n hn, ffa_GG_left hn.1.1 hnz, smul_comm]
  · intro g hg n hn
    have hnz : n *ᵥ z' = z' := ffa_nlev_fix hn hz'
    rw [rr g hg n hn, ffa_GG_right hnz, smul_comm]
  · intro g hg h hh h' hh'
    rw [e g hg h hh h' hh', ffa_GG_right hh'.2.2, ffa_GG_left hh.1 hh.2.2,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

theorem top_level_pointwise_identity (hCap : CapelliIdentityEntry) (hRTA : RightTypeAction) [FiniteDimensional ℂ Wq]
    (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D)
    (hπ'r : IsCRepOn (UWset k r z') π') (hπ'c : ContinuousOn π' (UWset k r z'))
    {F : Mx k r → (Wq →L[ℂ] Wp)} (hF : F ∈ FFl k r z z' π π' (Fin.last r) D)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hGG : GGl k r z z' g ≠ 0)
    (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (hBs : IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs) (Y : ℂ) (v : Wq) :
    tL k r z z' (Fin.last r) Y 1 1 F g v = (GGl k r z z' g : ℂ) • F g (capRep k r π' Bs (Y + ((k : ℂ) - 2) / 2) v) := by
  have hBs' : IsFrameOf k r [z'] Bs :=
    ⟨hBs.1, hBs.2.1, fun a w hw => hBs.2.2 a w (List.mem_cons_of_mem _ hw)⟩
  rw [hCap _ k r z z' D F hz hz' hD.1 hF.1 g hg hGG Bs hBs Y, _root_.smul_apply,
    hRTA Wp Wq k r (k - 1) z z' π π' D hz hz' hD hπ'r hπ'c F hF g hg Bs hBs']

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section SpecAux

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {X : Type*}

theorem spec_sum_mem {β : Type*} (𝓕 : Set (X → (Wq →L[ℂ] Wp)))
    (h0 : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ 𝓕)
    (hadd : ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (fun x => F₁ x + F₂ x) ∈ 𝓕)
    (f : β → X → (Wq →L[ℂ] Wp)) (s : Finset β) (hf : ∀ i ∈ s, f i ∈ 𝓕) :
    (fun x => ∑ i ∈ s, f i x) ∈ 𝓕 := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    have e : (fun x => ∑ i ∈ (∅ : Finset β), f i x) = fun _ => (0 : Wq →L[ℂ] Wp) := by
      funext x; simp
    rw [e]; exact h0
  · intro a s ha ih hf
    have e : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
      funext x; rw [Finset.sum_insert ha]
    rw [e]
    exact hadd _ (hf a (Finset.mem_insert_self a s)) _
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem spec_iter {ι : Type*} (𝓕 : Set (X → (Wq →L[ℂ] Wp))) (G : Set X)
    (T : ℂ → (X → (Wq →L[ℂ] Wp)) → X → (Wq →L[ℂ] Wp)) (c : X → ℂ) (hc : ∀ g ∈ G, c g ≠ 0)
    (Y₀ : ℂ) (hA : ∀ F ∈ 𝓕, (fun x => (c x)⁻¹ • T Y₀ F x) ∈ 𝓕)
    (lam : ι → ℂ → ℂ) (S : X → ι → Submodule ℂ Wq)
    (heig : ∀ F ∈ 𝓕, ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ, ∀ Y, T Y F g v = (c g * lam σ Y) • F g v)
    (J : X → (Wq →L[ℂ] Wp)) (hJ : J ∈ 𝓕) (n : ℕ) :
    ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J ∈ 𝓕) ∧
      ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ,
        ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J) g v = (lam σ Y₀) ^ n • J g v := by
  induction n with
  | zero => exact ⟨hJ, fun g _ σ v _ => by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply']
      exact hA _ h1
    · intro g hg σ v hv
      rw [Function.iterate_succ_apply']
      simp only [ContinuousLinearMap.smul_apply]
      rw [heig _ h1 g hg σ v hv Y₀, h2 g hg σ v hv]
      simp only [smul_smul]
      congr 1
      have hcg := hc g hg
      rw [pow_succ]
      field_simp

end SpecAux

theorem spec_abstract {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {X ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝓕 : Set (X → (Wq →L[ℂ] Wp))) (G : Set X)
    (h0 : (fun _ => (0 : Wq →L[ℂ] Wp)) ∈ 𝓕)
    (hadd : ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, (fun x => F₁ x + F₂ x) ∈ 𝓕)
    (hsmul : ∀ F ∈ 𝓕, ∀ c : ℂ, (fun x => c • F x) ∈ 𝓕)
    (T : ℂ → (X → (Wq →L[ℂ] Wp)) → X → (Wq →L[ℂ] Wp)) (c : X → ℂ) (hc : ∀ g ∈ G, c g ≠ 0)
    (Y₀ : ℂ) (hA : ∀ F ∈ 𝓕, (fun x => (c x)⁻¹ • T Y₀ F x) ∈ 𝓕)
    (lam : ι → ℂ → ℂ) (hinj : Function.Injective (fun σ => lam σ Y₀))
    (S : X → ι → Submodule ℂ Wq) (hS : ∀ g ∈ G, DirectSum.IsInternal (S g))
    (heig : ∀ F ∈ 𝓕, ∀ g ∈ G, ∀ σ, ∀ v ∈ S g σ, ∀ Y, T Y F g v = (c g * lam σ Y) • F g v)
    (J : X → (Wq →L[ℂ] Wp)) (hJ : J ∈ 𝓕) :
    ∃ dec : ι → X → (Wq →L[ℂ] Wp), (∀ σ, dec σ ∈ 𝓕) ∧ (∀ g ∈ G, J g = ∑ σ, dec σ g) ∧
      (∀ σ Y, ∀ g ∈ G, T Y (dec σ) g = (c g * lam σ Y) • dec σ g) ∧
      ∀ g ∈ G, ∀ σ v, ∃ w ∈ S g σ, dec σ g v = J g w := by
  classical
  have hinjOn : Set.InjOn (fun σ => lam σ Y₀) (Finset.univ : Finset ι) := fun a _ b _ h => hinj h
  have hit := spec_iter 𝓕 G T c hc Y₀ hA lam S heig J hJ
  obtain ⟨dec, hdec⟩ : ∃ dec : ι → X → (Wq →L[ℂ] Wp), ∀ σ x, dec σ x =
      ∑ n ∈ Finset.range ((Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).natDegree + 1),
        (Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).coeff n •
          ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J) x := ⟨_, fun _ _ => rfl⟩
  have hmem : ∀ σ, dec σ ∈ 𝓕 := by
    intro σ
    have hfun : dec σ = fun x => ∑ n ∈ Finset.range
        ((Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).natDegree + 1),
        (fun n x => (Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).coeff n •
          ((fun F x => (c x)⁻¹ • T Y₀ F x)^[n] J) x) n x := funext (hdec σ)
    rw [hfun]
    exact spec_sum_mem 𝓕 h0 hadd _ _ fun n _ => hsmul _ (hit n).1 _
  have hkey : ∀ σ, ∀ g ∈ G, ∀ τ, ∀ v ∈ S g τ, dec σ g v = if σ = τ then J g v else 0 := by
    intro σ g hg τ v hv
    have h1 : dec σ g v =
        ((Lagrange.basis Finset.univ (fun σ => lam σ Y₀) σ).eval (lam τ Y₀)) • J g v := by
      rw [hdec, Polynomial.eval_eq_sum_range, Finset.sum_smul, _root_.sum_apply]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [_root_.smul_apply, (hit n).2 g hg τ v hv, smul_smul]
    rw [h1]
    split_ifs with hστ
    · subst hστ
      have he := Lagrange.eval_basis_self hinjOn (Finset.mem_univ σ)
      rw [he, one_smul]
    · have he := Lagrange.eval_basis_of_ne (v := fun σ => lam σ Y₀) hστ (Finset.mem_univ τ)
      rw [he, zero_smul]
  have htop : ∀ g ∈ G, ∀ v : Wq, v ∈ ⨆ i, S g i := fun g hg v => by
    rw [(hS g hg).submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine ⟨dec, hmem, ?_, ?_, ?_⟩
  · intro g hg
    ext v
    rw [_root_.sum_apply]
    refine Submodule.iSup_induction (S g) (motive := fun v => J g v = ∑ σ, dec σ g v)
      (htop g hg v) ?_ ?_ ?_
    · intro τ w hw
      simp only [hkey _ g hg τ w hw, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp
    · intro x y hx hy
      simp only [map_add, hx, hy, Finset.sum_add_distrib]
  · intro σ Y g hg
    ext v
    rw [_root_.smul_apply]
    refine Submodule.iSup_induction (S g)
      (motive := fun v => T Y (dec σ) g v = (c g * lam σ Y) • dec σ g v) (htop g hg v) ?_ ?_ ?_
    · intro τ w hw
      rw [heig (dec σ) (hmem σ) g hg τ w hw Y, hkey σ g hg τ w hw]
      split_ifs with hστ
      · rw [hστ]
      · rw [smul_zero, smul_zero]
    · simp
    · intro x y hx hy
      rw [map_add, map_add, hx, hy, smul_add]
  · intro g hg σ v
    refine Submodule.iSup_induction (S g)
      (motive := fun v => ∃ w ∈ S g σ, dec σ g v = J g w) (htop g hg v) ?_ ?_ ?_
    · intro τ w hw
      by_cases hστ : σ = τ
      · subst hστ
        exact ⟨w, hw, by rw [hkey σ g hg σ w hw, if_pos rfl]⟩
      · exact ⟨0, zero_mem _, by rw [hkey σ g hg τ w hw, if_neg hστ, map_zero]⟩
    · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
    · rintro x y ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩
      exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, map_add, h₁, h₂]⟩

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

section
open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Group

variable {k r : ℕ}

theorem sv_one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z := by
  simp [UWset, UH]

theorem sv_exp_uw {z : Fin (2 * r + k + 1) → ℂ} {X : Mx k r} (hX : inLieW k r z X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UWset k r z :=
  ⟨B5.exp_mem hX.1 t, fun a => ⟨Qx2.exp_fix (hX.2.2 a).1 t, Qx2.exp_fix (hX.2.2 a).2 t⟩, Qx2.exp_fix hX.2.1 t⟩

theorem sv_uw_glev {z : Fin (2 * r + k + 1) → ℂ} {h g : Mx k r} (hh : h ∈ UWset k r z)
    (hg : g ∈ Glev k r (Fin.last r)) : h * g ∈ Glev k r (Fin.last r) := by
  simp only [UWset, Glev, UH, Set.mem_setOf_eq] at hh hg ⊢
  obtain ⟨hh1, hh2, -⟩ := hh
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_mul]
    calc gᴴ * hᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hh1, hg1]
  · rw [← Matrix.mulVec_mulVec, (hg2 a ha).1, (hh2 a).1]
  · rw [← Matrix.mulVec_mulVec, (hg2 a ha).2, (hh2 a).2]

theorem sv_one_nlev (i : Fin (r + 1)) : (1 : Mx k r) ∈ Nlev k r i :=
  ⟨(nSubgroup k r).1, WeylGroupFacts.uh_one, fun _ _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩⟩

theorem sv_uw_slev {z : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (i : Fin (r + 1)) :
    h ∈ Slev k r z i := by
  show ∃ h' ∈ UWset k r z, ∃ m ∈ Nlev k r i, h = h' * m
  exact ⟨h, hh, 1, sv_one_nlev i, (mul_one h).symm⟩

end Group

section SmoothJ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}

theorem J_smoothVec (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' (Fin.last r) D) (hπ'1 : π' 1 = 1)
    {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) (v : Wq) : J g v ∈ SmVec k r z π := by
  intro h hh X hX
  have h1' : (1 : Mx k r) ∈ UWset k r z' := sv_one_uw z'
  have he : ∀ t : ℝ, π (h * NormedSpace.exp ((t : ℂ) • X)) (J g v) =
      J (h * NormedSpace.exp ((t : ℂ) • X) * g) v := by
    intro t
    have hm := hJ.2.2.2 g hg _ (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) 1 h1'
    rw [Matrix.mul_one] at hm
    rw [hm]
    simp [hπ'1]
  have hfun : (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) (J g v)) =
      fun t : ℝ => J (h * NormedSpace.exp ((t : ℂ) • X) * g) v := funext he
  rw [hfun]
  have hhg : h * g ∈ Glev k r (Fin.last r) ∩ D := by
    refine ⟨sv_uw_glev hh hg.1, ?_⟩
    have := hD.2 g hg h (sv_uw_slev hh _) 1 (sv_uw_slev h1' _)
    simpa using this
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hJ.1 (h * g) hhg
  have hd : DifferentiableAt ℝ F (h * g) :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hc : HasDerivAt (fun t : ℝ => h * NormedSpace.exp ((t : ℂ) • X) * g)
      (mulRightRealCLM g (h * NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X)) 0 :=
    (mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (B5.curve_hasDerivAt h X 0)
  have hc0 : h * g = h * NormedSpace.exp (((0 : ℝ) : ℂ) • X) * g := by
    simp [NormedSpace.exp_zero]
  have hFc : DifferentiableAt ℝ (fun t : ℝ => F (h * NormedSpace.exp ((t : ℂ) • X) * g)) 0 :=
    (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).differentiableAt
  have hFv : DifferentiableAt ℝ (fun t : ℝ => F (h * NormedSpace.exp ((t : ℂ) • X) * g) v) 0 :=
    ((ContinuousLinearMap.apply ℂ Wp v).restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hFc
  refine hFv.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, h * NormedSpace.exp ((t : ℂ) • X) * g ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by rw [← hc0]; exact hU.mem_nhds hgU)
  filter_upwards [hmem] with t ht
  rw [hFe _ ht (sv_uw_glev (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) hg.1)]

end SmoothJ

section Conj

variable {k r : ℕ}

theorem sv_lie_conj {z : Fin (2 * r + k + 1) → ℂ} {X h₀ : Mx k r} (hX : inLieW k r z X)
    (hh₀ : h₀ ∈ UWset k r z) : inLieW k r z (h₀⁻¹ * X * h₀) := by
  have hu := WeylGroupFacts.isUnit_of_uh hh₀.1
  have hi1 : h₀ * h₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hU : h₀ᴴ * Hpk k r * h₀ = Hpk k r := hh₀.1
  have A : (h₀⁻¹)ᴴ * Hpk k r = Hpk k r * h₀ := by
    calc (h₀⁻¹)ᴴ * Hpk k r = (h₀⁻¹)ᴴ * (h₀ᴴ * Hpk k r * h₀) := by rw [hU]
      _ = (h₀ * h₀⁻¹)ᴴ * Hpk k r * h₀ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * h₀ := by rw [hi1, conjTranspose_one, Matrix.one_mul]
  have B : Hpk k r * h₀⁻¹ = h₀ᴴ * Hpk k r := by
    calc Hpk k r * h₀⁻¹ = h₀ᴴ * Hpk k r * h₀ * h₀⁻¹ := by rw [hU]
      _ = h₀ᴴ * Hpk k r := by rw [Matrix.mul_assoc, hi1, Matrix.mul_one]
  refine ⟨?_, ?_, fun a => ⟨?_, ?_⟩⟩
  · calc (h₀⁻¹ * X * h₀)ᴴ * Hpk k r + Hpk k r * (h₀⁻¹ * X * h₀)
        = h₀ᴴ * (Xᴴ * ((h₀⁻¹)ᴴ * Hpk k r)) + (Hpk k r * h₀⁻¹) * X * h₀ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = h₀ᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * h₀ := by
          rw [A, B]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hX.1]; simp
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh₀.2.2, hX.2.1, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hh₀.2.1 a).1, (hX.2.2 a).1, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hh₀.2.1 a).2, (hX.2.2 a).2, Matrix.mulVec_zero]

theorem sv_exp_conj {z : Fin (2 * r + k + 1) → ℂ} {X h h₀ : Mx k r} (hh₀ : h₀ ∈ UWset k r z) (t : ℝ) :
    h * NormedSpace.exp ((t : ℂ) • X) * h₀ = h * h₀ * NormedSpace.exp ((t : ℂ) • (h₀⁻¹ * X * h₀)) := by
  have hu := WeylGroupFacts.isUnit_of_uh hh₀.1
  have hu' : IsUnit h₀ := (Matrix.isUnit_iff_isUnit_det _).2 hu
  have hi1 : h₀ * h₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (t : ℂ) • (h₀⁻¹ * X * h₀) = h₀⁻¹ * ((t : ℂ) • X) * h₀ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.exp_conj' _ _ hu']
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc h h₀ h₀⁻¹, hi1, Matrix.mul_one]

end Conj

section Lin

variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}

def svSub (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) : Submodule ℂ Wp where
  carrier := SmVec k r z π
  zero_mem' := by
    intro h _ X _
    simp only [map_zero]
    exact differentiableAt_const _
  add_mem' := by
    intro x y hx hy h hh X hX
    simp only [map_add]
    exact (hx h hh X hX).add (hy h hh X hX)
  smul_mem' := by
    intro c x hx h hh X hX
    simp only [map_smul]
    exact (hx h hh X hX).const_smul c

theorem sv_stable (hrep : IsCRepOn (UWset k r z) π) {h₀ : Mx k r} (hh₀ : h₀ ∈ UWset k r z) {x : Wp}
    (hx : x ∈ SmVec k r z π) : π h₀ x ∈ SmVec k r z π := by
  intro h hh X hX
  have e : (fun t : ℝ => π (h * NormedSpace.exp ((t : ℂ) • X)) (π h₀ x)) =
      fun t : ℝ => π (h * h₀ * NormedSpace.exp ((t : ℂ) • (h₀⁻¹ * X * h₀))) x := by
    funext t
    rw [← sv_exp_conj hh₀ t, hrep.2 _ (WeylGroupFacts.uw_mul hh (sv_exp_uw hX t)) _ hh₀]
    rfl
  rw [e]
  exact hx (h * h₀) (WeylGroupFacts.uw_mul hh hh₀) _ (sv_lie_conj hX hh₀)

theorem sv_all {u : ℕ → ℝ} (hπ : IsType k r z π u) {x₀ : Wp} (hx₀ : x₀ ≠ 0) (hsm : x₀ ∈ SmVec k r z π)
    (v : Wp) : v ∈ SmVec k r z π := by
  rcases hπ.2.2.2.2.1 (svSub k r z π) (fun h hh v hv => sv_stable hπ.2.1 hh hv) with h0 | htop
  · have hm : x₀ ∈ svSub k r z π := hsm
    rw [h0] at hm
    exact absurd ((Submodule.mem_bot ℂ).1 hm) hx₀
  · have hm : v ∈ svSub k r z π := by rw [htop]; exact Submodule.mem_top
    exact hm

theorem sv_dRep_diff (hall : ∀ v : Wp, v ∈ SmVec k r z π) {X : Mx k r} (hX : inLieW k r z X) (v : Wp) :
    DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) 0 := by
  have := hall v 1 (sv_one_uw z) X hX
  simpa only [Matrix.one_mul] using this

theorem sv_dRep_lin (hall : ∀ v : Wp, v ∈ SmVec k r z π) {X : Mx k r} (hX : inLieW k r z X) :
    IsLinearMap ℂ (dRep π X) := by
  constructor
  · intro x y
    unfold dRep
    simp only [map_add]
    exact deriv_add (sv_dRep_diff hall hX x) (sv_dRep_diff hall hX y)
  · intro c x
    unfold dRep
    simp only [map_smul]
    exact deriv_const_smul c (sv_dRep_diff hall hX x)

theorem sv_ecRep_lin (hall : ∀ v : Wp, v ∈ SmVec k r z π) {Z : Mx k r}
    (h1 : inLieW k r z (hpart1 (Hpk k r) Z)) (h2 : inLieW k r z (hpart2 (Hpk k r) Z)) :
    IsLinearMap ℂ (EcRep (Hpk k r) π Z) := by
  have l1 := sv_dRep_lin hall h1
  have l2 := sv_dRep_lin hall h2
  constructor
  · intro x y
    unfold EcRep
    rw [l1.map_add, l2.map_add, smul_add]
    abel
  · intro c x
    unfold EcRep
    rw [l1.map_smul, l2.map_smul, smul_add, smul_comm Complex.I c]

end Lin

section Frame

variable {k r : ℕ}

theorem sv_herm_bvec (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec p) w = ∑ i, star (w i) * Hpk k r i p := by
  simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem sv_herm_out {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) {p : Fin (2 * r + k + 1)}
    (hp : p.val < r ∨ r + k < p.val) : herm (Hpk k r) (bvec p) w = 0 := by
  rw [sv_herm_bvec]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hw i hi, star_zero, zero_mul]
  · have h0 : Hpk k r i p = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, mul_zero]

theorem sv_herm_swap (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  have hsym : ∀ i j, Hpk k r i j = Hpk k r j i := by
    intro i j
    simp only [Hpk, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hreal : ∀ i j, star (Hpk k r i j) = Hpk k r i j := by
    intro i j
    simp only [Hpk]
    split_ifs <;> simp
  simp only [herm, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hreal]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsym]
  ring

theorem sv_unitB_mulVec {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    (v : Fin (2 * r + k + 1) → ℂ) : unitB (Hpk k r) Bs a b *ᵥ v = herm (Hpk k r) v (Bs b) • Bs a := by
  ext p
  simp only [Matrix.mulVec, dotProduct, unitB, Matrix.of_apply, sv_herm_bvec, Pi.smul_apply, smul_eq_mul]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.star_apply]
  ring

theorem sv_unitB_adj {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    (v : Fin (2 * r + k + 1) → ℂ) :
    (unitB (Hpk k r) Bs a b)ᴴ *ᵥ (Hpk k r *ᵥ v) =
      herm (Hpk k r) v (Bs a) • fun p => star (herm (Hpk k r) (bvec p) (Bs b)) := by
  ext p
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, unitB, Matrix.of_apply, star_mul',
    Pi.smul_apply, smul_eq_mul]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply]
  ring

theorem sv_unitB_kill {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    {v : Fin (2 * r + k + 1) → ℂ} (ha : herm (Hpk k r) v (Bs a) = 0) (hb : herm (Hpk k r) v (Bs b) = 0) :
    hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 ∧ hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b) *ᵥ v = 0 := by
  have e1 : unitB (Hpk k r) Bs a b *ᵥ v = 0 := by rw [sv_unitB_mulVec, hb, zero_smul]
  have e2 : (Hpk k r * (unitB (Hpk k r) Bs a b)ᴴ * Hpk k r) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sv_unitB_adj, ha, zero_smul, Matrix.mulVec_zero]
  unfold hpart1 hpart2
  rw [Qx2.hpk_inv, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec, e1, e2]
  simp only [sub_self, add_zero, smul_zero, and_self]

theorem sv_unitB_lie {z : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hBs : IsFrameOf k r [z] Bs) (a b : Fin m) :
    inLieW k r z (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      inLieW k r z (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b)) := by
  have hzB : ∀ x, herm (Hpk k r) z (Bs x) = 0 := fun x => by
    rw [sv_herm_swap, hBs.2.2 x z (List.mem_singleton_self z), star_zero]
  have heB : ∀ (c : Fin r) x, herm (Hpk k r) (bvec (eI k r c)) (Bs x) = 0 := fun c x =>
    sv_herm_out (hBs.1 x) (Or.inl (by simp [eI]))
  have hesB : ∀ (c : Fin r) x, herm (Hpk k r) (bvec (esI k r c)) (Bs x) = 0 := fun c x =>
    sv_herm_out (hBs.1 x) (Or.inr (by have := c.isLt; simp only [esI]; omega))
  have kz := sv_unitB_kill Bs a b (hzB a) (hzB b)
  have ke := fun c => sv_unitB_kill Bs a b (heB c a) (heB c b)
  have kes := fun c => sv_unitB_kill Bs a b (hesB c a) (hesB c b)
  exact ⟨⟨Qx2.hpart1_lie _, kz.1, fun c => ⟨(ke c).1, (kes c).1⟩⟩,
    ⟨Qx2.hpart2_lie _, kz.2, fun c => ⟨(ke c).2, (kes c).2⟩⟩⟩

end Frame

section QM

theorem sv_foldr_lin {X : Type*} [AddCommGroup X] [Module ℂ X] (L : List (X → X))
    (hL : ∀ T ∈ L, IsLinearMap ℂ T) : IsLinearMap ℂ (fun x => L.foldr (fun T h => T h) x) := by
  induction L with
  | nil => exact ⟨fun x y => rfl, fun c x => rfl⟩
  | cons T L ih =>
    have hT := hL T (by simp)
    have ih' := ih (fun S hS => hL S (by simp [hS]))
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · have e1 := ih'.map_add x y
      have e2 := hT.map_add (List.foldr (fun T h => T h) x L) (List.foldr (fun T h => T h) y L)
      try simp only at e1
      simp only [List.foldr_cons, e1, e2]
    · have e1 := ih'.map_smul c x
      have e2 := hT.map_smul c (List.foldr (fun T h => T h) x L)
      try simp only at e1
      simp only [List.foldr_cons, e1, e2]

theorem sv_qmF_lin {X : Type*} [AddCommGroup X] [Module ℂ X] {n t : ℕ} (Eop : Fin n → Fin n → X → X)
    (hE : ∀ a b, IsLinearMap ℂ (Eop a b)) (a b : Fin t → Fin n) (u : ℂ) : IsLinearMap ℂ (qmF Eop a b u) := by
  have hfac : ∀ σ : Equiv.Perm (Fin t), IsLinearMap ℂ (fun x : X =>
      (List.ofFn fun k : Fin t => fun y : X =>
        (if a (σ k) = b k then (u - ((k : ℕ) : ℂ)) • y else 0) + Eop (a (σ k)) (b k) y).foldr
        (fun T h => T h) x) := by
    intro σ
    apply sv_foldr_lin
    intro T hT
    rw [List.mem_ofFn] at hT
    obtain ⟨j, rfl⟩ := hT
    have hl := hE (a (σ j)) (b j)
    constructor
    · intro x y
      split_ifs <;> simp only [hl.map_add, smul_add] <;> abel
    · intro c x
      split_ifs <;> simp only [hl.map_smul, smul_add, zero_add, smul_comm c]
  constructor
  · intro x y
    unfold qmF
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← smul_add]
    exact congrArg _ ((hfac σ).map_add x y)
  · intro c x
    unfold qmF
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm c]
    exact congrArg _ ((hfac σ).map_smul c x)

end QM

section Cap

variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
  {π : Mx k r → (Wp →L[ℂ] Wp)}

theorem capRep_linear {u : ℕ → ℝ} (hπ : IsType k r z π u) {x₀ : Wp} (hx₀ : x₀ ≠ 0) (hsm : x₀ ∈ SmVec k r z π)
    {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (hBs : IsFrameOf k r [z] Bs) (w : ℂ) :
    IsLinearMap ℂ (capRep k r π Bs w) := by
  have hall := sv_all hπ hx₀ hsm
  unfold capRep
  exact sv_qmF_lin _ (fun a b => sv_ecRep_lin hall (sv_unitB_lie hBs a b).1 (sv_unitB_lie hBs a b).2) id id w

end Cap

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem linearMap_coeAddMonoidHom_eq_mapRange_smul {ι : Type*} [DecidableEq ι] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (S : ι → Submodule ℂ W) (L : W →ₗ[ℂ] W) (a : ι → ℂ) (hL : ∀ i, ∀ y ∈ S i, L y = a i • y)
    (f : DirectSum ι (fun i => S i)) :
    L (DirectSum.coeAddMonoidHom S f) = DirectSum.coeAddMonoidHom S
      (DFinsupp.mapRange.addMonoidHom (fun i => DistribSMul.toAddMonoidHom (S i) (a i)) f) := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [DirectSum.coeAddMonoidHom_of, hL i y y.2]
    change _ = DirectSum.coeAddMonoidHom S
      (DFinsupp.mapRange _ (fun j => map_zero _) (DFinsupp.single (β := fun j => S j) i y))
    rw [DFinsupp.mapRange_single]
    change _ = DirectSum.coeAddMonoidHom S (DirectSum.of (fun j => S j) i _)
    rw [DirectSum.coeAddMonoidHom_of]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]

theorem vanish_match (hBr : Branching) {P : M.Par} (hP : P.OK) {Wp : Type} [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    (hz : inWb P.k P.r z) (hT : 0 < Tz P.k P.r z) (hπ : IsType P.k P.r z π P.u)
    {e : Fin (2 * P.r + P.k + 1) → ℂ} (he : inWb P.k P.r e) (hez : herm (Hpk P.k P.r) e z = 0)
    (hee : herm (Hpk P.k P.r) e e = 1) (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (hBs : IsFrameOf P.k P.r [z, e] Bs) (hlin : ∀ w : ℂ, IsLinearMap ℂ (capRep P.k P.r π Bs w))
    {x : Wp} (hx : x ≠ 0) (μ : ℂ → ℂ) (hμ : ∀ w : ℂ, capRep P.k P.r π Bs w x = μ (w - ((P.k : ℂ) - 2) / 2) • x) :
    ∃ ρ : M.Ty (Pq P), ∀ Y : ℂ, μ Y = M.xC (Pq P) ρ Y := by
  obtain ⟨S, hS, -, hcap⟩ := hBr Wp (Pq P) (Pq_OK hP) rfl z e π hz hT hπ he hez hee
  obtain ⟨d, hd⟩ := hS.2 x
  obtain ⟨ρ, hρ⟩ : ∃ ρ, d ρ ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by rw [← hd, show d = 0 from DFinsupp.ext h, map_zero])
  refine ⟨ρ, fun Y => ?_⟩
  have hw : Y + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Y := add_sub_cancel_right _ _
  have h1 := linearMap_coeAddMonoidHom_eq_mapRange_smul S (IsLinearMap.mk' _ (hlin (Y + ((P.k : ℂ) - 2) / 2)))
    (fun σ => M.xC (Pq P) σ Y)
    (fun σ y hy => (hcap Bs hBs σ _ y hy).trans (congrArg (fun t => M.xC (Pq P) σ t • y) hw)) d
  have h2 := linearMap_coeAddMonoidHom_eq_mapRange_smul S (μ Y • LinearMap.id) (fun _ => μ Y) (fun _ _ _ => rfl) d
  have h3 : (DFinsupp.mapRange.addMonoidHom fun i =>
        DistribSMul.toAddMonoidHom (S i) (M.xC (Pq P) i Y)) d =
      (DFinsupp.mapRange.addMonoidHom fun i => DistribSMul.toAddMonoidHom (S i) (μ Y)) d :=
    hS.1 (by
      rw [← h1, ← h2, hd]
      simpa [hw] using hμ (Y + ((P.k : ℂ) - 2) / 2))
  have h4 := congrArg (fun f => f ρ) h3
  simp only [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_apply,
    DistribSMul.toAddMonoidHom_apply] at h4
  exact (smul_left_injective ℂ hρ h4).symm

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frame_sub {k r m : ℕ} {vs vs' : List (Fin (2 * r + k + 1) → ℂ)} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r vs Bs) (hs : ∀ v ∈ vs', v ∈ vs) : IsFrameOf k r vs' Bs :=
  ⟨h.1, h.2.1, fun a v hv => h.2.2 a v (hs v hv)⟩

theorem radial_decomposition_of_parts' : RadialDecompositionOfParts := by
  intro _hC2 _hCC hCap hRTA hBr hTP
  intro Wp Wq _ _ _ _ _ _ P z z' π π' D hPl hD hGGD J hJ
  obtain ⟨hP, hz, hz', hTz, hTz', hπ, hπ'⟩ := hPl
  have hT : 0 < Tz P.k P.r z := by rw [hTz]; exact hP.T_pos
  have hT' : 0 < Tz P.k P.r z' := by rw [hTz']; exact hP.T'_pos
  obtain ⟨Y₀, hY₀⟩ := exists_sep hP
  obtain ⟨f, hfi, hfx, hfr⟩ := comb_match hP
  have hloc : ∀ g : Mx P.k P.r, ∃ (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
      (e : Fin (2 * P.r + P.k + 1) → ℂ) (S : M.Ty (Pp P) → Submodule ℂ Wq),
      g ∈ Glev P.k P.r (Fin.last P.r) ∩ D →
      IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Bs ∧ inWb P.k P.r e ∧ herm (Hpk P.k P.r) e z = 0 ∧
      herm (Hpk P.k P.r) e e = 1 ∧ IsFrameOf P.k P.r [z, e] (fun a => g *ᵥ Bs a) ∧ DirectSum.IsInternal S ∧
      ∀ σ, ∀ v ∈ S σ, ∀ w : ℂ, capRep P.k P.r π' Bs w v = M.xC (Pp P) σ (w - ((P.k : ℂ) - 2) / 2) • v := by
    intro g
    by_cases hg : g ∈ Glev P.k P.r (Fin.last P.r) ∩ D
    · obtain ⟨Bs, e', e, hB1, he', he'z, he'e, hB2, he, hez, hee, hB3⟩ :=
        geom_package hz hz' hT hT' hg.1 (hGGD g hg.2)
      obtain ⟨S, hSi, -, hSe⟩ := hBr Wq (Pp P) (Pp_OK hP) rfl z' e' π' hz' hT' hπ' he' he'z he'e
      exact ⟨Bs, e, S, fun _ => ⟨hB1, he, hez, hee, hB3, hSi, fun σ v hv w => hSe Bs hB2 σ w v hv⟩⟩
    · exact ⟨fun _ _ => 0, 0, fun _ => ⊥, fun h => absurd h hg⟩
  choose Bs e S hBS using hloc
  obtain ⟨dec, hdecF, hsum, heigd, hcomp⟩ := spec_abstract (FFl P.k P.r z z' π π' (Fin.last P.r) D)
    (Glev P.k P.r (Fin.last P.r) ∩ D) ff_zero (fun F₁ h₁ F₂ h₂ => ff_add h₁ h₂) (fun F h c => ff_smul h c)
    (fun Y F => tL P.k P.r z z' (Fin.last P.r) Y 1 1 F) (fun x => (GGl P.k P.r z z' x : ℂ))
    (fun g hg => by exact_mod_cast hGGD g hg.2) Y₀
    (fun F hF => ff_GGinv hz hz' hD hGGD (hTP Wp Wq P.k P.r z z' π π' (Fin.last P.r) D Y₀ 1 1 hz hz' hD F hF))
    (fun σ Y => M.xC (Pp P) σ Y) hY₀ S (fun g hg => (hBS g hg).2.2.2.2.2.1)
    (by
      intro F hF g hg σ v hv Y
      have hc : Y + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Y := by ring
      rw [top_level_pointwise_identity hCap hRTA hz hz' hD hπ'.2.1 hπ'.2.2.1 hF hg (hGGD g hg.2) (Bs g) (hBS g hg).1 Y v,
        (hBS g hg).2.2.2.2.2.2 σ v hv _, hc, ContinuousLinearMap.map_smul, smul_smul])
    J hJ
  have hvan : ∀ σ, σ ∉ Set.range f → ∀ g ∈ Glev P.k P.r (Fin.last P.r) ∩ D, dec σ g = 0 := by
    intro σ hσ g hg
    ext v
    obtain ⟨w, hw, hdw⟩ := hcomp g hg σ v
    rw [hdw, _root_.zero_apply]
    by_contra hne
    obtain ⟨hB1, he, hez, hee, hB3, -, hSe⟩ := hBS g hg
    have hsm := J_smoothVec hz hz' hD hπ'.2.1.1 hJ hg w
    have hlin : ∀ W : ℂ, IsLinearMap ℂ (capRep P.k P.r π (fun a => g *ᵥ Bs g a) W) := fun W =>
      capRep_linear hπ hne hsm (fun a => g *ᵥ Bs g a) (frame_sub hB3 (by simp)) W
    have hμ : ∀ W : ℂ, capRep P.k P.r π (fun a => g *ᵥ Bs g a) W (J g w) =
        M.xC (Pp P) σ (W - ((P.k : ℂ) - 2) / 2) • J g w := by
      intro W
      rw [← left_ad hz hz' hD hπ'.2.1.1 hJ hg (Bs g) (frame_sub hB1 (by simp)) W w,
        hRTA Wp Wq P.k P.r (P.k - 1) z z' π π' D hz hz' hD hπ'.2.1 hπ'.2.2.1 J hJ g hg (Bs g)
          (frame_sub hB1 (by simp)) W w,
        hSe σ w hw W, ContinuousLinearMap.map_smul]
    obtain ⟨ρ, hρ⟩ := vanish_match hBr hP hz hT hπ he hez hee _ hB3 hlin hne _ hμ
    exact hσ (hfr σ ρ hρ)
  refine ⟨fun ρ => dec (f ρ), fun ρ => hdecF (f ρ), ?_, ?_⟩
  · intro g hg
    have h1 : ∑ σ ∈ Finset.univ.image f, dec σ g = ∑ σ, dec σ g :=
      Finset.sum_subset (Finset.subset_univ _) (fun σ _ hσ => hvan σ
        (fun ⟨ρ, hρ⟩ => hσ (hρ ▸ Finset.mem_image_of_mem f (Finset.mem_univ ρ))) g hg)
    rw [hsum g hg, ← h1, Finset.sum_image (fun a _ b _ h => hfi h)]
  · intro ρ Y g hg
    have h := heigd (f ρ) Y g hg
    rw [h, hfx ρ Y]

end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end
