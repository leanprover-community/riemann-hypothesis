import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransportStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTermsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumMapPowerSeriesMkFinsum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour

section
open PowerSeries

namespace GlobalTheory.PowerSeriesCompositionMap

variable {O O₁ K : Type} [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁]

noncomputable def comp {ι : Type} (b : Module.Basis ι O O₁) (j : ι) : PowerSeries O₁ →+ PowerSeries O where
  toFun f := PowerSeries.mk fun n => b.repr (coeff n f) j
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

lemma coeff_comp {ι : Type} (b : Module.Basis ι O O₁) (j : ι) (f : PowerSeries O₁) (n : ℕ) :
    coeff n (comp b j f) = b.repr (coeff n f) j := by
  simp [comp]

lemma decomp {ι : Type} [Fintype ι] (b : Module.Basis ι O O₁) (f : PowerSeries O₁) :
    f = ∑ j, C (b j) * map (algebraMap O O₁) (comp b j f) := by
  ext n
  rw [map_sum]
  simp only [coeff_C_mul, coeff_map, coeff_comp]
  conv_lhs => rw [← b.sum_repr (coeff n f)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, mul_comm]

lemma comp_C_mul_map {ι : Type} (b : Module.Basis ι O O₁) (j : ι) (a : O₁) (g : PowerSeries O) :
    comp b j (C a * map (algebraMap O O₁) g) = C (b.repr a j) * g := by
  ext n
  rw [coeff_comp, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm, ← Algebra.smul_def, map_smul]
  simp [mul_comm]

variable {ι : Type} [Fintype ι] (b : Module.Basis ι O O₁) (i : PowerSeries O →+* K) (io : O₁ →+* K)

noncomputable def ext : PowerSeries O₁ →+ K :=
  ∑ j, (AddMonoidHom.mulLeft (io (b j))).comp ((i : PowerSeries O →+ K).comp (comp b j))

lemma ext_apply (f : PowerSeries O₁) : ext b i io f = ∑ j, io (b j) * i (comp b j f) := by
  simp [ext, AddMonoidHom.finset_sum_apply]

variable {b i io}

lemma ext_C_mul_map (h : ∀ a : O, io (algebraMap O O₁ a) = i (C a)) (a : O₁) (g : PowerSeries O) :
    ext b i io (C a * map (algebraMap O O₁) g) = io a * i g := by
  rw [ext_apply]
  simp only [comp_C_mul_map, map_mul, ← h, ← mul_assoc, ← Finset.sum_mul]
  congr 1
  conv_rhs => rw [← b.sum_repr a, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, map_mul, mul_comm]

lemma ext_mul (h : ∀ a : O, io (algebraMap O O₁ a) = i (C a)) (f g : PowerSeries O₁) :
    ext b i io (f * g) = ext b i io f * ext b i io g := by
  conv_lhs => rw [decomp b f, decomp b g, Finset.sum_mul_sum, map_sum]
  conv_rhs => rw [decomp b f, decomp b g, map_sum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : C (b j) * map (algebraMap O O₁) (comp b j f) * (C (b k) * map (algebraMap O O₁) (comp b k g))
      = C (b j * b k) * map (algebraMap O O₁) (comp b j f * comp b k g) := by
    rw [map_mul, map_mul]; ring
  rw [e, ext_C_mul_map h, ext_C_mul_map h, ext_C_mul_map h, map_mul, map_mul]
  ring

theorem main (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁]
    [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K)
    (h : ∀ a : O, io (algebraMap O O₁ a) = i (C a)) :
    ∃ Φ : PowerSeries O₁ →+* K, (∀ a : O₁, Φ (C a) = io a) ∧ Φ X = i X ∧
      ∀ f : PowerSeries O₁, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  let b := Module.Free.chooseBasis O O₁
  have hC : ∀ a : O₁, ext b i io (C a) = io a := fun a => by
    simpa using ext_C_mul_map (b := b) h a 1
  let Φ : PowerSeries O₁ →+* K :=
    { ext b i io with
      map_one' := by simpa using hC 1
      map_mul' := ext_mul h }
  refine ⟨Φ, hC, ?_, fun f => ?_⟩
  · show ext b i io X = i X
    simpa using ext_C_mul_map (b := b) h 1 X
  · show ext b i io f ∈ _
    rw [ext_apply]
    refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inr ⟨_, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)

example : ∀ (O O₁ K : Type) [inst : CommRing O] [inst_1 : CommRing O₁] [inst_2 : CommRing K] [inst_3 : Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K), (∀ (a : O), (io : O₁ → K) ((Algebra.algebraMap O O₁ : O → O₁) a) = (i : PowerSeries O → K) ((PowerSeries.C : O → PowerSeries O) a)) → ∃ (Φ : PowerSeries O₁ →+* K), (∀ (a : O₁), (Φ : PowerSeries O₁ → K) ((PowerSeries.C : O₁ → PowerSeries O₁) a) = (io : O₁ → K) a) ∧ (Φ : PowerSeries O₁ → K) PowerSeries.X = (i : PowerSeries O → K) PowerSeries.X ∧ ∀ (f : PowerSeries O₁), (Φ : PowerSeries O₁ → K) f ∈ Subring.closure (Set.range (⇑i : PowerSeries O → K) ∪ Set.range (⇑io : O₁ → K)) := main
end GlobalTheory.PowerSeriesCompositionMap
end

section
section
open TensorProduct

namespace GlobalTheory

theorem powerSeries_extend_finite_free (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K]
    [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K)
    (io : O₁ →+* K) (h : ∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) :
    ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧
      Φ PowerSeries.X = i PowerSeries.X ∧
      ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  first
  | exact @_root_.GlobalTheory.PowerSeriesCompositionMap.main
  | exact _root_.GlobalTheory.PowerSeriesCompositionMap.main
  | (apply _root_.GlobalTheory.PowerSeriesCompositionMap.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerSeriesCompositionMap.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerSeriesCompositionMap.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerSeriesCompositionMap.main ..)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free : ∀ (O O₁ K : Type) [CommRing O] [CommRing O₁] [CommRing K] [Algebra O O₁] [Module.Free O O₁] [Module.Finite O O₁] (i : PowerSeries O →+* K) (io : O₁ →+* K), (∀ a, io (algebraMap O O₁ a) = i (PowerSeries.C a)) → ∃ Φ : PowerSeries O₁ →+* K, (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = i PowerSeries.X ∧ ∀ f, Φ f ∈ Subring.closure (Set.range i ∪ Set.range io) := by
  atlas_forward_decl GlobalTheory.powerSeries_extend_finite_free
end

section
section
open PowerSeries

namespace GlobalTheory

namespace SeriesRoot

variable {O : Type*} [CommRing O]

noncomputable def residuePart (k l : ℕ) : PowerSeries O →+ PowerSeries O where
  toFun f := PowerSeries.mk fun n => coeff (k * n + l) f
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

theorem coeff_residuePart (k l n : ℕ) (f : PowerSeries O) :
    coeff n (residuePart k l f) = coeff (k * n + l) f := by
  simp [residuePart]

theorem coeff_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j : ℕ} (hj : j < k) (g : PowerSeries O)
    (m : ℕ) :
    coeff m (X ^ j * expand k hk g) = if m % k = j then coeff (m / k) g else 0 := by
  rw [coeff_X_pow_mul', coeff_expand]
  by_cases h : m % k = j
  · have hm : m = k * (m / k) + j := by rw [← h]; exact (Nat.div_add_mod m k).symm
    have h1 : j ≤ m := by omega
    have h2 : m - j = k * (m / k) := by omega
    rw [if_pos h1, if_pos h, h2, if_pos (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)]
  · rw [if_neg h]
    split_ifs with h1 h2
    · exfalso
      obtain ⟨c, hc⟩ := h2
      apply h
      have : m = j + k * c := by omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    · rfl
    · rfl

theorem sum_residuePart {k : ℕ} (hk : k ≠ 0) (f : PowerSeries O) :
    ∑ l ∈ Finset.range k, X ^ l * expand k hk (residuePart k l f) = f := by
  ext m
  rw [map_sum, Finset.sum_congr rfl
    (fun l hl => coeff_X_pow_mul_expand hk (Finset.mem_range.1 hl) _ m), Finset.sum_ite_eq,
    if_pos (Finset.mem_range.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero hk))), coeff_residuePart,
    Nat.div_add_mod]

theorem residuePart_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j l : ℕ} (hj : j < k) (hl : l < k)
    (g : PowerSeries O) :
    residuePart k l (X ^ j * expand k hk g) = if l = j then g else 0 := by
  ext n
  rw [coeff_residuePart, coeff_X_pow_mul_expand hk hj, Nat.mul_add_mod, Nat.mod_eq_of_lt hl,
    Nat.mul_add_div (Nat.pos_of_ne_zero hk), Nat.div_eq_of_lt hl, add_zero]
  split_ifs <;> simp

variable {K : Type*} [CommRing K]

noncomputable def extendAdd (φ : PowerSeries O →+* K) (k : ℕ) (t : K) : PowerSeries O →+ K where
  toFun f := ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f)
  map_zero' := by simp
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]

theorem extendAdd_apply (φ : PowerSeries O →+* K) (k : ℕ) (t : K) (f : PowerSeries O) :
    extendAdd φ k t f = ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f) := rfl

theorem extendAdd_X_pow_mul_expand_of_lt (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) (t : K)
    {j : ℕ} (hj : j < k) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  rw [extendAdd_apply, Finset.sum_eq_single j]
  · rw [residuePart_X_pow_mul_expand hk hj hj, if_pos rfl]
  · intro l hl hlj
    rw [residuePart_X_pow_mul_expand hk hj (Finset.mem_range.1 hl), if_neg hlj, map_zero,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

theorem extendAdd_X_pow_mul_expand (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (j : ℕ) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  have h : (X : PowerSeries O) ^ j * expand k hk g =
      X ^ (j % k) * expand k hk (X ^ (j / k) * g) := by
    rw [map_mul, map_pow, expand_X, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]
  rw [h, extendAdd_X_pow_mul_expand_of_lt φ hk t (Nat.mod_lt _ (Nat.pos_of_ne_zero hk)),
    map_mul, map_pow, ← ht, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]

theorem extendAdd_mul (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (f g : PowerSeries O) :
    extendAdd φ k t (f * g) = extendAdd φ k t f * extendAdd φ k t g := by
  conv_lhs => rw [← sum_residuePart hk f, ← sum_residuePart hk g]
  rw [extendAdd_apply φ k t f, extendAdd_apply φ k t g, Finset.sum_mul_sum, Finset.sum_mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm, ← pow_add, ← map_mul, extendAdd_X_pow_mul_expand φ hk ht, map_mul,
    pow_add]
  ring

noncomputable def extendHom (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : PowerSeries O →+* K where
  toFun := extendAdd φ k t
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by simpa using extendAdd_X_pow_mul_expand φ hk ht 0 1
  map_mul' := extendAdd_mul φ hk ht

theorem extendHom_expand (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (g : PowerSeries O) : extendHom φ hk ht (expand k hk g) = φ g := by
  have := extendAdd_X_pow_mul_expand φ hk ht 0 g
  rw [pow_zero, pow_zero, one_mul, one_mul] at this
  exact this

theorem extendHom_X (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : extendHom φ hk ht X = t := by
  have := extendAdd_X_pow_mul_expand φ hk ht 1 1
  rw [pow_one, pow_one, map_one, map_one, mul_one, mul_one] at this
  exact this

end SeriesRoot

theorem exists_ringHom_powerSeries_root :
    ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k →
      t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K,
        (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧
          ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  intro O K _ _ φ k t hk ht
  refine ⟨SeriesRoot.extendHom φ hk.ne' ht, fun a => ?_, SeriesRoot.extendHom_X φ hk.ne' ht,
    fun f => ?_⟩
  · rw [← SeriesRoot.extendHom_expand φ hk.ne' ht (PowerSeries.C a), expand_C]
  · change ∑ l ∈ Finset.range k, t ^ l * φ (SeriesRoot.residuePart k l f) ∈ _
    refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ (Subring.pow_mem _ ?_ l) ?_
    · exact Subring.subset_closure (Or.inr rfl)
    · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_powerSeries_root' : ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k → t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K, (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  atlas_forward_decl GlobalTheory.exists_ringHom_powerSeries_root
end

section
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

theorem hasSum_zpow_of_form_le {O C X : Type} [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (φ : PowerSeries O →+* C) (h1 : ∀ f, ‖φ f‖ ≤ 1) (hX : ‖φ PowerSeries.X‖ < 1) (u : Cˣ)
    (hu : (u : C) = φ PowerSeries.X) (B : LinearMap.BilinForm ℤ X) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (y : X) {m : ℕ} (hm : m ≠ 0) {D : ℤ} (hD : 0 < D) (E : X → ℤ)
    (hE : ∀ χ, B (y + m • χ) (y + m • χ) ≤ D * E χ) (a : X → O) :
    HasSum (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ)))
      (φ (PowerSeries.mk fun n => ∑ᶠ (χ : X) (_ : E χ = n), a χ)) := by
  classical
  have hB0 : ∀ x, 0 ≤ B x x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hp x hx).le
  have hE0 : ∀ χ, 0 ≤ E χ := by
    intro χ
    have h := hE χ
    have h' := hB0 (y + m • χ)
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hinj : Function.Injective (fun χ : X => y + m • χ) := by
    intro a b h
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa using h
    exact smul_right_injective X (Int.natCast_ne_zero.mpr hm) h'
  have hQ := GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef hs hp
  have hfin : ∀ n : ℕ, {χ | (E χ).toNat = n}.Finite := by
    intro n
    refine (Set.Finite.preimage (fun _ _ _ _ h => hinj h)
      (GlobalTheory.ClassMin.finite_sublevel hQ ((D * n : ℤ) : ℝ))).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq] at hχ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]
    have h := hE χ
    have h0 := hE0 χ
    have h2 := hB0 (y + m • χ)
    have hEn : E χ = n := by omega
    rw [hEn] at h
    have h3 : (B (y + m • χ) (y + m • χ) : ℝ) ≤ ((D * n : ℤ) : ℝ) := by exact_mod_cast h
    have h4 : (0 : ℝ) ≤ B (y + m • χ) (y + m • χ) := by exact_mod_cast h2
    linarith
  have h := GlobalTheory.hasSum_map_powerSeries_mk_finsum O C X φ h1 hX (fun χ => (E χ).toNat) hfin a
  have hf : (fun χ => ((u ^ E χ : Cˣ) : C) * φ (PowerSeries.C (a χ))) =
      fun χ => φ (PowerSeries.C (a χ)) * φ PowerSeries.X ^ (E χ).toNat := by
    funext χ
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (hE0 χ)
    rw [hk]
    simp [hu, mul_comm]
  have hg : (fun n : ℕ => ∑ᶠ (χ : X) (_ : E χ = n), a χ) =
      fun n : ℕ => ∑ᶠ (χ : X) (_ : (E χ).toNat = n), a χ := by
    funext n
    refine finsum_congr fun χ => ?_
    have h0 := hE0 χ
    have hiff : (E χ = n) = ((E χ).toNat = n) := propext (by omega)
    rw [hiff]
  rw [hf, hg]
  exact h

theorem form_le_exponent {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k)
    {j : ℕ} (hj : j ∣ k) (hj0 : j ≠ 0) (x z : N.X) (s : ℤ) (hs : (m : ℤ) ^ 2 * β.be z z ≤ s) :
    β.be x x ≤ 4 * (m : ℤ) ^ 2 * (β.be x x / (2 * m ^ 2) + β.be z x / j + s) := by
  have hB0 : ∀ y, 0 ≤ β.be y y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (β.pos y hy).le
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hk : k = 0 := by simpa using hm
    have h0 : β.be x x = 0 := by
      have h := β.dvd x x
      simpa [hk] using h
    simp [h0]
  · have hmk : (2 * (m : ℤ) ^ 2) ∣ 2 * (k : ℤ) := mul_dvd_mul_left 2 (by exact_mod_cast hm)
    have hjk : (j : ℤ) ∣ 2 * (k : ℤ) := dvd_mul_of_dvd_right (by exact_mod_cast hj) 2
    obtain ⟨q, hq⟩ := dvd_trans hmk (β.dvd x x)
    obtain ⟨c, hc⟩ := dvd_trans hjk (β.dvd z x)
    have hm2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
    have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
    have hq' : β.be x x / (2 * m ^ 2) = q := by
      rw [hq]
      exact Int.mul_ediv_cancel_left q hm2.ne'
    have hc' : β.be z x / j = c := by
      rw [hc]
      exact Int.mul_ediv_cancel_left c (by omega)
    rw [hq', hc']
    have hexp := hB0 ((j : ℤ) • x + (2 * (m : ℤ) ^ 2) • z)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hexp
    rw [β.symm x z, hc] at hexp
    have ha := hB0 z
    have hs0 : 0 ≤ s := le_trans (mul_nonneg (by positivity) ha) hs
    have hjj : (0 : ℤ) ≤ (j : ℤ) ^ 2 - 1 := by nlinarith
    have h5 : 0 ≤ 4 * (m : ℤ) ^ 2 * (((j : ℤ) ^ 2 - 1) * s + (s - (m : ℤ) ^ 2 * β.be z z)) :=
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg hjj hs0) (by linarith))
    have key : 0 ≤ (j : ℤ) ^ 2 * (β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s) := by
      nlinarith [hexp, h5]
    have hX : 0 ≤ β.be x x + 4 * (m : ℤ) ^ 2 * c + 4 * (m : ℤ) ^ 2 * s := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_pos_of_neg (by positivity : (0 : ℤ) < (j : ℤ) ^ 2) hneg
      linarith
    nlinarith [hX, hq]

theorem twist_tx_ev_eq_map_arc : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 hX u hu N₀ N I k β₀ β hβ m hm hmo p₀ p hp1 hp2
  have hm0 : m ≠ 0 := hmo.pos.ne'
  have hT := (GlobalTheory.T.hom_transport_alt O C (φ.comp PowerSeries.C) N₀ N I).2.2.2.2 m hmo p₀ p hp1 hp2
  have hpt : ∀ χ₀ : N₀.X, p.1.1.toAdd + m • I.e χ₀ = I.e (p₀.1.1.toAdd + m • χ₀) := by
    intro χ₀
    rw [hp1, map_add, map_nsmul]
  have hdiv2 : ∀ x y, (2 * (m : ℤ) ^ 2) ∣ β₀.be x y := fun x y =>
    dvd_trans (mul_dvd_mul_left 2 (by exact_mod_cast hm)) (β₀.dvd x y)
  have hD2 : (0 : ℤ) < 2 * (m : ℤ) ^ 2 := by positivity
  constructor
  · have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0 hD2
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2))
      (fun χ => (Int.mul_ediv_cancel' (hdiv2 _ _)).ge) (fun χ => N₀.txT m p₀ χ)
    have key : ∀ χ₀, (N.twist β u).txT m (N.twQ β u hm p) (I.e χ₀) =
        (I.lam : C) * (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2)) :
          Cˣ) : C) * φ (PowerSeries.C (N₀.txT m p₀ χ₀))) := by
      intro χ₀
      rw [(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).1, hpt, hβ, (hT χ₀).1, RingHom.comp_apply]
      ring
    show ∑' χ, (N.twist β u).txT m (N.twQ β u hm p) χ = _
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f ((I.lam : C) * φ (N₀.arcTx β₀.be m p₀))) (funext key)).mpr
      (hsum.mul_left (I.lam : C))
  · intro j hj q₀ q hj0 hq1 hq2 s hs
    have hsum := hasSum_zpow_of_form_le φ h1 hX u hu β₀.be β₀.symm β₀.pos p₀.1.1.toAdd hm0
      (D := 4 * (m : ℤ) ^ 2) (by positivity)
      (fun χ => β₀.be (p₀.1.1.toAdd + m • χ) (p₀.1.1.toAdd + m • χ) / (2 * m ^ 2) +
        β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ) / j + s)
      (fun χ => form_le_exponent β₀ hm hj hj0 _ _ (s : ℤ) hs) (fun χ => N₀.evT m p₀ q₀.1.2 χ)
    have key : ∀ χ₀, (u : C) ^ s * (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 (I.e χ₀) =
        ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
          (((u ^ (β₀.be (p₀.1.1.toAdd + m • χ₀) (p₀.1.1.toAdd + m • χ₀) / (2 * m ^ 2) +
            β₀.be q₀.1.1.toAdd (p₀.1.1.toAdd + m • χ₀) / j + s) : Cˣ) : C) *
            φ (PowerSeries.C (N₀.evT m p₀ q₀.1.2 χ₀))) := by
      intro χ₀
      rw [(GlobalTheory.T.twist_terms_alt C N k β u m hm hmo p (I.e χ₀)).2.1 j hj q hj0, hpt, hq1, hβ, hβ,
        (hT χ₀).2 q₀.1.2 q.1.2 hq2, RingHom.comp_apply]
      simp only [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
      ring
    show (u : C) ^ s * ∑' χ, (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = _
    rw [← tsum_mul_left]
    refine HasSum.tsum_eq ((I.e.toEquiv.hasSum_iff).mp ?_)
    exact (congrArg (fun f => HasSum f (((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C) *
      φ (N₀.arcEv β₀.be m p₀ q₀ s))) (funext key)).mpr
      (hsum.mul_left ((I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) : C))

end GlobalTheory.Ex
end

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_tx_ev_eq_map_arc_alt : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (u : Cˣ), (u : C) = φ PowerSeries.X → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (β₀ : N₀.Form k) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = β₀.be y z) → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p₀ : N₀.QT (m ^ 2)) (p : N.QT (m ^ 2)), p.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p.1.2 → (N.twist β u).tx m (N.twQ β u hm p) = I.lam * φ (N₀.arcTx β₀.be m p₀) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q₀ : N₀.QT j) (q : N.QT j), j ≠ 0 → q.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q.1.2 → ∀ s : ℕ, (m : ℤ) ^ 2 * β₀.be q₀.1.1.toAdd q₀.1.1.toAdd ≤ s → (u : C) ^ s * (N.twist β u).ev m (N.twQ β u hm p) (N.twQ β u hj q).1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv β₀.be m p₀ q₀ s) := by
  atlas_forward_decl GlobalTheory.Ex.twist_tx_ev_eq_map_arc
end

section
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.RootSum

def scaleForm {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) : N.Form n where
  be := (n : ℤ) • β.be
  symm y z := congrArg ((n : ℤ) * ·) (β.symm y z)
  pos y hy := mul_pos (Int.natCast_pos.2 hn) (β.pos y hy)
  dvd y z := by
    obtain ⟨a, ha⟩ := β.dvd y z
    exact ⟨k * a, by change (n : ℤ) * β.be y z = _; rw [ha]; ring⟩

def pullForm {O O' : Type} [CommRing O] [CommRing O'] {N₀ : NumD O} {N : NumD O'} {k : ℕ} (β : N.Form k)
    (e : N₀.X ≃+ N.X) (be₀ : LinearMap.BilinForm ℤ N₀.X) (h : ∀ y z, β.be (e y) (e z) = be₀ y z) : N₀.Form k where
  be := be₀
  symm y z := by rw [← h, ← h, β.symm]
  pos y hy := by rw [← h]; exact β.pos _ (fun h0 => hy (e.map_eq_zero_iff.1 h0))
  dvd y z := h y z ▸ β.dvd _ _

def idHom {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u : Oˣ)
    (h : t ^ n = u) : NumD.Hom (RingHom.id O) (N.twist (scaleForm β n hn) t) (N.twist β u) where
  φ := MonoidHom.id _
  h _ := 1
  h_one := rfl
  θ_eq _ _ _ := by simp only [mul_one]; rfl
  σ_eq _ := by simp only [mul_one]; rfl
  lam := 1
  th_eq _ := by simp only [mul_one, Units.val_one, one_mul]; rfl
  e := AddEquiv.refl N.X
  c_eq _ := rfl
  ψ_eq (χ : N.X) := by
    rw [mul_one]
    change N.ψ χ * u ^ (β.be χ χ / 2) = N.ψ χ * t ^ ((n : ℤ) * β.be χ χ / 2)
    rw [Int.mul_ediv_assoc _ ((Dvd.intro _ rfl : (2 : ℤ) ∣ 2 * k).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, h]

theorem idHom_rel {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u r : Oˣ)
    (h : t ^ n = u) {i : ℕ} (a : ℕ) (hi : i * a = n) (hd : i ∣ n) (hr : t ^ a = r) (p₁ : N.QT i)
    (p : (N.twist β u).QT i) (hp : TwRel β u r p₁ p) :
    p.1.1.toAdd = (idHom β n hn t u h).e (N.twQ (scaleForm β n hn) t hd p₁).1.1.toAdd ∧
      (idHom β n hn t u h).Rel (N.twQ (scaleForm β n hn) t hd p₁).1.2 p.1.2 := by
  refine ⟨congrArg Multiplicative.toAdd hp.1, hp.2.1, fun (χ : N.X) => ?_⟩
  change p.1.2.s χ * 1 = p₁.1.2.s χ * t ^ ((n : ℤ) * β.be p₁.1.1.toAdd χ / i) * 1 * 1
  have hi0 : (i : ℤ) ≠ 0 := by
    rintro h0
    rw [Int.natCast_eq_zero.1 h0, zero_mul] at hi
    omega
  rw [hp.2.2, ← hi, Nat.cast_mul, mul_assoc (i : ℤ), Int.mul_ediv_cancel_left _ hi0, zpow_mul, zpow_natCast, hr,
    mul_one, mul_one]

theorem twist_tx_ev_eq_map_arc_root : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (t u rm rj : Cˣ) (m j : ℕ), Odd m → 0 < j → (t : C) = φ PowerSeries.X → t ^ j = rm → t ^ (m ^ 2) = rj → rm ^ (m ^ 2) = u → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (be₀ : LinearMap.BilinForm ℤ N₀.X) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = be₀ y z) → ∀ (p₀ : N₀.QT (m ^ 2)) (p₁ : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2)), p₁.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p₁.1.2 → TwRel β u rm p₁ p → (N.twist β u).tx m p = I.lam * φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀) ∧ ∀ (q₀ : N₀.QT j) (q₁ : N.QT j) (q : (N.twist β u).QT j), q₁.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q₁.1.2 → TwRel β u rj q₁ q → ∀ s : ℕ, (m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd) ≤ s → (t : C) ^ s * (N.twist β u).ev m p q.1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 h2 t u rm rj m j hm hj ht hrm hrj hu N₀ N I k be₀ β hβ p₀ p₁ p hp1 hp2 hp
  have hn : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  have htu : t ^ (m ^ 2 * j) = u := by rw [mul_comm, pow_mul, hrm, hu]
  have hd : m ^ 2 ∣ m ^ 2 * j := Dvd.intro _ rfl
  have key := GlobalTheory.T.twist_tx_ev_eq_map_arc_alt O C φ h1 h2 t ht N₀ N I (m ^ 2 * j) (scaleForm (pullForm β I.e be₀ hβ) _ hn)
    (scaleForm β _ hn) (fun y z => congrArg (((m ^ 2 * j : ℕ) : ℤ) * ·) (hβ y z)) m hd hm p₀ p₁ hp1 hp2
  have hr := idHom_rel β _ hn t u rm htu j rfl hd hrm p₁ p hp
  have tr := (NumD.hom_transport C C _ _ _ (idHom β _ hn t u htu)).2.2.2.2 m hm _ p hr.1 hr.2
  refine ⟨Eq.trans (tsum_congr fun χ => ?_) key.1, fun q₀ q₁ q hq1 hq2 hq s hs => ?_⟩
  · exact (tr χ).1.trans (one_mul _)
  · have hd' : j ∣ m ^ 2 * j := Dvd.intro_left _ rfl
    have hr' := idHom_rel β _ hn t u rj htu (m ^ 2) (mul_comm _ _) hd' hrj q₁ q hq
    refine Eq.trans (congrArg _ (tsum_congr fun χ => ?_)) (key.2 j hd' q₀ q₁ hj.ne' hq1 hq2 s hs)
    refine ((tr χ).2 _ _ hr'.2).trans ?_
    change ((1 * 1 ^ (m ^ 2) : Cˣ) : C) * _ = _
    rw [one_pow, mul_one, Units.val_one, one_mul]
    rfl

end GlobalTheory.Ex.RootSum
end
end

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_tx_ev_eq_map_arc_root_alt : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (t u rm rj : Cˣ) (m j : ℕ), Odd m → 0 < j → (t : C) = φ PowerSeries.X → t ^ j = rm → t ^ (m ^ 2) = rj → rm ^ (m ^ 2) = u → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (be₀ : LinearMap.BilinForm ℤ N₀.X) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = be₀ y z) → ∀ (p₀ : N₀.QT (m ^ 2)) (p₁ : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2)), p₁.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p₁.1.2 → TwRel β u rm p₁ p → (N.twist β u).tx m p = I.lam * φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀) ∧ ∀ (q₀ : N₀.QT j) (q₁ : N.QT j) (q : (N.twist β u).QT j), q₁.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q₁.1.2 → TwRel β u rj q₁ q → ∀ s : ℕ, (m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd) ≤ s → (t : C) ^ s * (N.twist β u).ev m p q.1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀ q₀ s) := by
  atlas_forward_decl GlobalTheory.Ex.RootSum.twist_tx_ev_eq_map_arc_root
end

section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ArcSeries

section Comp
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}

def homComp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x)) :
    NumD.Hom k N N'' :=
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  { φ := I'.φ.comp I.φ
    h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
    h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
    θ_eq x y u := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.θ_eq x y u)
      have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    σ_eq x := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.σ_eq x)
      have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
      apply Additive.ofMul.injective
      simp only [e, map_mul, map_inv, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
      linear_combination (norm := abel) a + b
    lam := I'.lam * Units.map g.toMonoidHom I.lam
    th_eq x := by
      rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq, hk]
      simp only [Units.val_mul, map_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      ring
    e := I.e.trans I'.e
    c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
    ψ_eq χ := by
      have a := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (I.ψ_eq χ)
      have b := congrArg Additive.ofMul (I'.ψ_eq (I.e χ))
      apply Additive.ofMul.injective
      simp only [e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq] at a b ⊢
      linear_combination (norm := abel) a + b }

theorem homComp_rel (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') (k : O →+* O'') (hk : ∀ x, k x = g (f x))
    {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b) (h' : I'.Rel b c) : (homComp I I' k hk).Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have e : ∀ x : Oˣ, Units.map k.toMonoidHom x = Units.map g.toMonoidHom (Units.map f.toMonoidHom x) :=
    fun x => Units.ext (hk x)
  have p := congrArg (fun t => Additive.ofMul (Units.map g.toMonoidHom t)) (h.2 χ)
  have q := congrArg Additive.ofMul (h'.2 (I.e χ))
  apply Additive.ofMul.injective
  simp only [homComp, e, map_mul, ofMul_mul, AddEquiv.trans_apply, I.c_eq, h.1] at p q ⊢
  linear_combination (norm := abel) p + q
end Comp

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]; exact Iff.rfl⟩

theorem mem_of_isIntegral {R K : Type} [CommRing R] [Field K] [Algebra R K] (S : ValuationSubring K)
    (h : ∀ r, algebraMap R K r ∈ S) {x : K} (hx : IsIntegral R x) : x ∈ S := by
  have : IsIntegral S x := hx.map_of_comp_eq ((algebraMap R K).codRestrict S h) (RingHom.id K) rfl
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact y.2

theorem exists_map {O O₁ K : Type} [CommRing O] [CommRing O₁] [Field K] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (io : O₁ →+* K)
    (hio : ∀ a, io (algebraMap O O₁ a) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {k : ℕ} (hk : 0 < k) {t : K}
    (ht : t ^ k = algebraMap (PowerSeries O) K PowerSeries.X) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (Φ : PowerSeries O₁ →+* K), Module.Finite (PowerSeries O) R₁ ∧
      (∀ a, Φ (PowerSeries.C a) = io a) ∧ Φ PowerSeries.X = t ∧ ∀ f, Φ f ∈ R₁ := by
  obtain ⟨Φ₁, h1, h2, h3⟩ := GlobalTheory.T.exists_powerSeries_ringHom_extending_finite_free O O₁ K (algebraMap _ K) io hio
  obtain ⟨Φ, h4, h5, h6⟩ := GlobalTheory.T.exists_ringHom_powerSeries_root' O₁ K Φ₁ k t hk (ht.trans h2.symm)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := O₁)
  refine ⟨Algebra.adjoin _ (io '' s ∪ {t}), Φ, Algebra.finite_adjoin_of_finite_of_isIntegral
    ((s.finite_toSet.image _).union (Set.finite_singleton _)) ?_, fun a => (h4 a).trans (h1 a), h5, fun f => ?_⟩
  · rintro x (⟨a, -, rfl⟩ | rfl)
    · exact (Algebra.IsIntegral.isIntegral (R := O) a).map_of_comp_eq PowerSeries.C io (RingHom.ext fun a => (hio a).symm)
    · exact IsIntegral.of_pow hk (ht ▸ isIntegral_algebraMap)
  · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h6 f)
    rintro x (⟨g, rfl⟩ | rfl)
    · refine (Subring.closure_le (t := (Algebra.adjoin _ (io '' s ∪ {t})).toSubring)).2 ?_ (h3 g)
      rintro x (⟨g, rfl⟩ | ⟨a, rfl⟩)
      · exact Subalgebra.algebraMap_mem _ g
      · have ha : a ∈ Submodule.span O (s : Set O₁) := hs ▸ Submodule.mem_top
        change io a ∈ Algebra.adjoin (PowerSeries O) (io '' s ∪ {t})
        induction ha using Submodule.span_induction with
        | mem x hx => exact Algebra.subset_adjoin (.inl ⟨x, hx, rfl⟩)
        | zero => rw [map_zero]; exact zero_mem _
        | add x y _ _ a b => rw [map_add]; exact add_mem a b
        | smul c x _ a => rw [Algebra.smul_def, map_mul, hio]; exact mul_mem (Subalgebra.algebraMap_mem _ _) a
    · exact Algebra.subset_adjoin (.inr rfl)

def Sums {R K F : Type} [CommRing R] [Field K] [Field F] [Algebra R K] (X : R) (io : F →+* K) (N : NumD F)
    (be : LinearMap.BilinForm ℤ N.X) (m j : ℕ) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j) (t : Kˣ)
    (v w : La → K) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (gam : K →+* C),
    (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) → ‖gam (algebraMap R K X)‖ < 1 →
    ∀ (N' : NumD C) (I : NumD.Hom (gam.comp io) N N') (k : ℕ) (β : N'.Form k), I.lam = 1 →
    (∀ y z, β.be (I.e y) (I.e z) = be y z) → ∀ u rm rj : Cˣ, (u : C) = gam (algebraMap R K X) →
    (rm : C) = gam (t ^ j : Kˣ) → (rj : C) = gam (t ^ m ^ 2 : Kˣ) →
    ∀ (q' : La → N'.QT (m ^ 2)) (p : La → (N'.twist β u).QT (m ^ 2)),
    (∀ x, (q' x).1.1.toAdd = I.e (q x).1.1.toAdd ∧ I.Rel (q x).1.2 (q' x).1.2) → (∀ x, TwRel β u rm (q' x) (p x)) →
    (∀ x, gam (v x) = (N'.twist β u).tx m (p x)) ∧
    ∀ (qz' : N'.QT j) (pz : (N'.twist β u).QT j), qz'.1.1.toAdd = I.e qz.1.1.toAdd → I.Rel qz.1.2 qz'.1.2 →
      TwRel β u rj qz' pz → ∃ s : Cˣ, ∀ x, gam (w x) = s * (N'.twist β u).ev m (p x) pz.1.2

theorem exists_sums {O O₁ K F : Type} [CommRing O] [CommRing O₁] [Field K] [Field F] [Algebra O O₁] [Module.Free O O₁]
    [Module.Finite O O₁] [Algebra (PowerSeries O) K] (f : O₁ →+* F) (io : F →+* K)
    (hio : ∀ a, io (f (algebraMap O O₁ a)) = algebraMap (PowerSeries O) K (PowerSeries.C a)) {N : NumD F}
    (be : LinearMap.BilinForm ℤ N.X) {m j : ℕ} (hm : Odd m) (hj : 0 < j) {La : Type} (q : La → N.QT (m ^ 2)) (qz : N.QT j)
    (t : Kˣ) (ht : (t : K) ^ (m ^ 2 * j) = algebraMap (PowerSeries O) K PowerSeries.X) {N₀ : NumD O₁}
    (I₀ : NumD.Hom f N₀ N) (hl : I₀.lam = 1)
    (hq : ∀ x, ∃ p₀ : N₀.QT (m ^ 2), (q x).1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 (q x).1.2)
    (hz : ∃ p₀ : N₀.QT j, qz.1.1.toAdd = I₀.e p₀.1.1.toAdd ∧ I₀.Rel p₀.1.2 qz.1.2) :
    ∃ (R₁ : Subalgebra (PowerSeries O) K) (v w : La → K), Module.Finite (PowerSeries O) R₁ ∧ (∀ x, v x ∈ R₁) ∧
      Sums (PowerSeries.X : PowerSeries O) io N be m j q qz t v w := by
  have hk : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  obtain ⟨R₁, Φ, hR, h1, h2, h3⟩ := exists_map (io.comp f) hio hk ht
  choose p₀ hp hp' using hq
  obtain ⟨q₀, hz, hz'⟩ := hz
  let be₀ : LinearMap.BilinForm ℤ N₀.X := be.comp I₀.e.toAddMonoidHom.toIntLinearMap I₀.e.toAddMonoidHom.toIntLinearMap
  let s : ℕ := ((m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd)).toNat
  refine ⟨R₁, fun x => Φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x)),
    fun x => Φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m (p₀ x) q₀ s), hR, fun x => h3 _, ?_⟩
  intro C _ _ _ gam g1 g2 N' I k β hI hβ u rm rj hu hrm hrj q' p hq' hp''
  obtain ⟨S, hS⟩ := exists_ball C
  have n1 : ∀ g, ‖(gam.comp Φ) g‖ ≤ 1 := fun g => (hS _).1 (mem_of_isIntegral (S.comap gam)
    (fun r => (hS _).2 (g1 r)) ((Algebra.IsIntegral.isIntegral (⟨_, h3 g⟩ : R₁)).map R₁.val))
  have n2 : ‖(gam.comp Φ) PowerSeries.X‖ < 1 := by
    rw [← ht, map_pow, norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) hk.ne'] at g2
    rwa [RingHom.comp_apply, h2]
  let t' : Cˣ := Units.map gam.toMonoidHom t
  let J := homComp I₀ I ((gam.comp Φ).comp PowerSeries.C) fun x => congrArg gam (h1 x)
  have hJ : J.lam = 1 := by
    change I.lam * Units.map _ I₀.lam = 1
    rw [hI, hl, map_one, mul_one]
  have e1 : t' ^ j = rm := Units.ext (by rw [hrm, ← map_pow]; rfl)
  have key := fun x => GlobalTheory.T.twist_tx_ev_eq_map_arc_root_alt O₁ C (gam.comp Φ) n1 n2 t' u rm rj m j hm hj (congrArg gam h2.symm) e1
    (Units.ext (by rw [hrj, ← map_pow]; rfl))
    (Units.ext (by rw [hu, ← e1, ← pow_mul, mul_comm j, ← ht, ← map_pow, map_pow gam]; simp [t']))
    N₀ N' J k be₀ β (fun y z => hβ _ _) (p₀ x) (q' x) (p x) ((hq' x).1.trans (congrArg I.e (hp x)))
    (homComp_rel _ _ _ _ (hp' x) (hq' x).2) (hp'' x)
  refine ⟨fun x => ?_, fun qz' pz a b c => ⟨(J.lam * J.h q₀.1.2.b ^ (m ^ 2))⁻¹ * t' ^ s, fun x => ?_⟩⟩
  · rw [(key x).1, hJ, Units.val_one, one_mul]; rfl
  · have := (key x).2 q₀ qz' pz (a.trans (congrArg I.e hz)) (homComp_rel _ _ _ _ hz' b) c s (Int.self_le_toNat _)
    rw [Units.val_mul, mul_assoc, Units.val_pow_eq_pow_val, this, Units.inv_mul_cancel_left]; rfl

end GlobalTheory.ArcSeries
end
end
