import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair.Model

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}


theorem isAdj_sumOp (S S' : Pair k n → Finset (Pair k n)) (w w' : Pair k n → Pair k n → ℂ)
    (hS : ∀ P Q, Q ∈ S P ↔ P ∈ S' Q) (hw : ∀ P Q, Q ∈ S P → w P Q = (starRingEnd ℂ) (w' Q P)) :
    IsAdj (sumOp S w) (sumOp S' w') := by
  classical
  intro φ φ' h h'
  unfold cntIp
  rw [finsum_eq_sum_of_support_subset (s := h'.toFinset) _ (fun P hP => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, map_eq_zero] at hP
      simpa using hP.2),
    finsum_eq_sum_of_support_subset (s := h.toFinset) _ (fun P hP => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hP
      simpa using hP.1)]
  have e1 : ∀ P, sumOp S w φ P = ∑ Q ∈ h.toFinset, if Q ∈ S P then w P Q * φ Q else 0 := fun P => by
    rw [sumOp_apply, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm
    have : φ Q = 0 := by simpa [hQ] using hQ'
    simp [this]
  have e2 : ∀ Q, sumOp S' w' φ' Q = ∑ P ∈ h'.toFinset, if P ∈ S' Q then w' Q P * φ' P else 0 := fun P => by
    rw [sumOp_apply, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm
    have : φ' Q = 0 := by simpa [hQ] using hQ'
    simp [this]
  simp only [e1, e2, Finset.sum_mul, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun P _ => ?_
  by_cases hQ : Q ∈ S P
  · rw [if_pos hQ, if_pos ((hS P Q).1 hQ), hw P Q hQ, map_mul]
    ring
  · rw [if_neg hQ, if_neg (fun h => hQ ((hS P Q).2 h))]
    simp



variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem sum_withLat_dia {A : Type*} [AddCommMonoid A] (c : 𝓀[k]ˣ) (L : Submodule 𝒪[k] (n → k)) (F : Pair k n → A) :
    ∑ P ∈ withLat L, F (c • P) = ∑ P ∈ withLat L, F P :=
  Finset.sum_equiv (MulAction.toPerm c) (fun P => by simp) fun _ _ => rfl

theorem FF_dia (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (c : 𝓀[k]ˣ) (φ : Form k n M) :
    FF q χ (dia c φ) = dia c (FF q χ φ) := by
  ext P₁
  simp only [FF_apply, dia_apply, Pair.dia_ker]
  rw [← sum_withLat_dia c _ fun P => χ (cross q (c • P₁) P) • φ P]
  refine Finset.sum_congr rfl fun P hP => ?_
  have h := mem_withLat.1 hP
  rw [cross_dia_left q (P := c • P) h, cross_dia_right q h, Units.inv_mul_cancel_left]

theorem sum_char {V : Type*} [AddCommGroup V] [Module 𝓀[k] V] [Fintype V] {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1)
    (g : Module.Dual 𝓀[k] V) [Decidable (g = 0)] : ∑ x, χ (g x) = if g = 0 then (Fintype.card V : ℂ) else 0 := by
  split_ifs with hg
  · simp [hg]
  · refine (AddChar.sum_eq_zero_iff_ne_zero (ψ := χ.compAddMonoidHom g.toAddMonoidHom)).2 fun h => hχ ?_
    ext a
    obtain ⟨x, rfl⟩ := LinearMap.surjective hg a
    exact DFunLike.congr_fun h x

theorem FFStar_FF [Fintype n] (q : Unif k) {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1) (φ : Form k n M) :
    FFStar q χ (FF q χ φ) = (SplitWeil.resCard k ^ Fintype.card n : ℂ) • φ - tr φ := by
  classical
  ext P
  obtain ⟨L, hL, f, rfl⟩ : ∃ (L : Submodule 𝒪[k] (n → k)) (_ : L.IsLattice k) (f : _), P = ofDual L f :=
    ⟨P.lat, P.isLat, _, P.ofDual_red.symm⟩
  letI := Fintype.ofFinite (Red L)
  letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
  have hc : (Fintype.card (Red L) : ℂ) = SplitWeil.resCard k ^ Fintype.card n := by
    rw [← Nat.card_eq_fintype_card, Red.card_eq]; push_cast; rfl
  simp only [FFStar_ofDual, FF_up, Finset.smul_sum, smul_smul, Pi.sub_apply, Pi.smul_apply, tr_apply, ofDual_lat,
    sum_withLat]
  rw [Finset.sum_comm]
  have key : ∀ g : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0},
      ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) * χ (g.1 x.1) =
        (if g = f then (Fintype.card (Red L) : ℂ) else 0) - 1 := fun g => by
    have h1 := sum_char hχ (g.1 - f.1)
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0] at h1
    simp only [map_zero, AddChar.map_zero_eq_one, sub_eq_zero, Subtype.val_inj] at h1
    rw [← h1, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul, LinearMap.sub_apply, neg_add_eq_sub]
  simp only [← Finset.sum_smul, key, sub_smul, one_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hc]

theorem sum_stable_eq_zero {φ : Form k n M} (h : φ ∈ Mram k n M) (s : Finset (Pair k n))
    (hs : ∀ (c : 𝓀[k]ˣ) P, c • P ∈ s ↔ P ∈ s) : ∑ P ∈ s, φ P = 0 := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have h1 : ∑ P ∈ s, ∑ c : 𝓀[k]ˣ, φ (c • P) = 0 := Finset.sum_eq_zero fun P _ => (mem_Mram φ).1 h P
  rw [Finset.sum_comm] at h1
  have h2 : ∀ c : 𝓀[k]ˣ, ∑ P ∈ s, φ (c • P) = ∑ P ∈ s, φ P := fun c =>
    Finset.sum_equiv (MulAction.toPerm c) (fun P => (hs c P).symm) fun _ _ => rfl
  simp only [h2, Finset.sum_const, Finset.card_univ] at h1
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left (by exact_mod_cast Fintype.card_ne_zero)

theorem tr_eq_zero {φ : Form k n M} (h : φ ∈ Mram k n M) : tr φ = 0 ∧ tr' φ = 0 :=
  ⟨funext fun P => (tr_apply φ P).trans (sum_stable_eq_zero h _ (by simp)),
    funext fun P => (tr'_apply φ P).trans (sum_stable_eq_zero h _ (by simp))⟩

theorem FF_eq_D_Gs (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FF q χ φ = D q (Gs χ φ) := by
  classical
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ext P₁
  rw [FF_apply, D_apply, ← Finset.sum_filter_add_sum_filter_not _ (fun P => cross q P₁ P = 0)]
  have h0 : ∑ P ∈ withLat P₁.ker with cross q P₁ P = 0, χ (cross q P₁ P) • φ P = 0 := by
    rw [Finset.sum_congr rfl (g := φ) fun P hP => by simp [(Finset.mem_filter.1 hP).2]]
    refine sum_stable_eq_zero h _ fun c P => ?_
    simp only [Finset.mem_filter, mem_withLat, Pair.dia_lat]
    exact and_congr_right fun hP => by simp [cross_dia_right q hP]
  rw [h0, zero_add]
  simp only [Gs_apply]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun z _ => z.2 • z.1) ?_ ?_ ?_ ?_
  · rintro ⟨P, c⟩ hz
    simp only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz
    simp [hz.1, cross_dia_right q hz.1, hz.2]
  · rintro ⟨P, c⟩ hz ⟨P', c'⟩ hz' e
    simp only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz hz' e
    have := congrArg (cross q P₁) e
    rw [cross_dia_right q hz.1, cross_dia_right q hz'.1, hz.2, hz'.2, mul_one, mul_one, Units.val_inj] at this
    subst this
    rw [MulAction.injective c e]
  · intro P hP
    simp only [Finset.mem_filter, mem_withLat] at hP
    refine ⟨((Units.mk0 _ hP.2)⁻¹ • P, Units.mk0 _ hP.2), ?_, smul_inv_smul _ _⟩
    simp [hP.1, cross_dia_right q hP.1, hP.2]
  · rintro ⟨P, c⟩ hz
    simp only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz
    simp [cross_dia_right q hz.1, hz.2]

theorem FF_ne_zero [Fintype n] (q : Unif k) {χ : AddChar 𝓀[k] ℂ} (hχ : χ ≠ 1) {φ : Form k n M}
    (h : φ ∈ Mram k n M) (h0 : FF q χ φ = 0) : φ = 0 := by
  have := FFStar_FF q hχ φ
  rw [h0, map_zero, (tr_eq_zero h).1, sub_zero] at this
  refine (smul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ ?_)
  exact_mod_cast (Nat.card_pos (α := 𝓀[k])).ne'






instance factThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩


end GlobalTheory.LatPair.Model
