import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticesIdempotentPositionBounded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullLatticeSandwichBetweenIntegralElements

section
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.Desc

theorem dvr_dvd_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a y : O}
    (ha : a ∈ IsLocalRing.maximalIdeal O) (hy : y ≠ 0) : ∃ k : ℕ, y ∣ a ^ k := by
  have hyt : IsDiscreteValuationRing.addVal O y ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hyt
  have ha1 : 1 ≤ IsDiscreteValuationRing.addVal O a := by
    rw [ENat.one_le_iff_ne_zero, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    exact ha
  refine ⟨n, IsDiscreteValuationRing.addVal_le_iff_dvd.1 ?_⟩
  rw [IsDiscreteValuationRing.addVal_pow, ← hn]
  calc ((n : ℕ∞)) = n • (1 : ℕ∞) := by simp
    _ ≤ n • IsDiscreteValuationRing.addVal O a := nsmul_le_nsmul_right ha1 n

theorem smul_pow_integral (K : UQ) (B : InvAlg K) (a : K.O) (ha : K.Small a) (x : B.A) :
    ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by
  have hxE : IsIntegral K.E x := Algebra.IsIntegral.isIntegral x
  obtain ⟨⟨m, hm⟩, hmx⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors K.O) x hxE
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨k, w, hw⟩ := dvr_dvd_pow ha.2.1 hm0
  refine ⟨k, ?_⟩
  have hsm : (m • x : B.A) = (⟨m, hm⟩ : nonZeroDivisors K.O) • x := rfl
  have : (al K a ^ k) • x = algebraMap K.O B.A w * (m • x) := by
    rw [← map_pow, algebraMap_smul, hw, mul_comm, mul_smul, Algebra.smul_def]
  rw [this]
  exact isIntegral_algebraMap.mul (hsm ▸ hmx)

end GlobalTheory.UnitLemma.Desc
end

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isIntegral_smallElement_pow_smul : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ x : B.A, ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by
  atlas_forward_decl GlobalTheory.UnitLemma.Desc.smul_pow_integral
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem idem_mul_aeval_idem_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (w : A) (p : R[X]) :
    f * aeval (f * w) p = f * aeval w p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, mul_add, mul_add, hp, hq]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, mul_pow]
    calc f * (algebraMap R A a * (f ^ n * w ^ n)) = algebraMap R A a * ((f * f ^ n) * w ^ n) := by ring
      _ = algebraMap R A a * (f * w ^ n) := by rw [← pow_succ', hf.pow_succ_eq]
      _ = f * (algebraMap R A a * w ^ n) := by ring

theorem isIntegral_idem_mul_of_quot {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {f : A}
    (hf : IsIdempotentElem f) (w : A)
    (h : IsIntegral R (Ideal.Quotient.mk (Ideal.span {1 - f}) w)) : IsIntegral R (f * w) := by
  obtain ⟨q, hq, hqw⟩ := h
  have h0 : aeval w q ∈ Ideal.span {1 - f} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← hqw, ← aeval_def]
    exact (aeval_algHom_apply (Ideal.Quotient.mkₐ R (Ideal.span {1 - f})) w q).symm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 h0
  have h1 : f * aeval w q = 0 := by
    rw [hc, ← mul_assoc, mul_sub, mul_one, hf.eq, sub_self, zero_mul]
  refine ⟨X * q, monic_X.mul hq, ?_⟩
  rw [← aeval_def, map_mul, aeval_X, mul_assoc, mul_left_comm, idem_mul_aeval_idem_mul hf w q, h1, mul_zero]

theorem isIntegral_or_isIntegral_of_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f →
    (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f → IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := by
  intro K B f y z hf hinv hyz
  by_cases hf0 : f = 0
  · left; rw [hf0, zero_mul]; exact isIntegral_zero
  set I : Ideal B.A := Ideal.span {1 - f} with hI
  have hmk : ∀ a b : B.A, Ideal.Quotient.mk I a = Ideal.Quotient.mk I b ↔ ∃ c, a - b = (1 - f) * c := by
    intro a b
    rw [Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
    rfl
  have hf1 : Ideal.Quotient.mk I f = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), hmk]
    exact ⟨-1, by ring⟩
  have hfm : ∀ a : B.A, Ideal.Quotient.mk I (f * a) = Ideal.Quotient.mk I a := by
    intro a; rw [map_mul, hf1, one_mul]
  have hfield : IsField (B.A ⧸ I) := by
    refine ⟨⟨0, 1, fun h => hf0 ?_⟩, mul_comm, ?_⟩
    · obtain ⟨c, hc⟩ := (hmk 0 1).1 h
      have := congrArg (f * ·) hc
      simp only [mul_sub, mul_zero, mul_one, zero_sub] at this
      rw [← mul_assoc, mul_sub, mul_one, hf.eq, sub_self, zero_mul] at this
      simpa using this
    · intro a ha
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hfx : f * x ≠ 0 := by
        intro h0
        apply ha
        rw [← hfm x, h0, map_zero]
      obtain ⟨v, hv⟩ := hinv x hfx
      refine ⟨Ideal.Quotient.mk I v, ?_⟩
      rw [← map_mul, ← hfm (x * v), ← mul_assoc, hv, hf1]
  haveI : I.IsMaximal := Ideal.Quotient.maximal_of_isField I hfield
  letI : Field (B.A ⧸ I) := Ideal.Quotient.field I
  haveI : CharZero K.O :=
    ⟨fun m n h => Nat.cast_injective (R := K.E) (by simpa using congrArg (algebraMap K.O K.E) h)⟩
  let e : FractionRing K.O ≃ₐ[K.O] K.E := IsLocalization.algEquiv (nonZeroDivisors K.O) (FractionRing K.O) K.E
  letI : Algebra (FractionRing K.O) (B.A ⧸ I) :=
    ((algebraMap K.E (B.A ⧸ I)).comp (e : FractionRing K.O →+* K.E)).toAlgebra
  haveI : IsScalarTower K.O (FractionRing K.O) (B.A ⧸ I) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    change _ = algebraMap K.E (B.A ⧸ I) (e (algebraMap K.O (FractionRing K.O) x))
    rw [AlgEquiv.commutes]
    first
      | exact IsScalarTower.algebraMap_apply K.O K.E (B.A ⧸ I) x
      | rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsIntegral (FractionRing K.O) (B.A ⧸ I) := by
    refine ⟨fun x => ?_⟩
    have hx : IsIntegral K.E x := Algebra.IsIntegral.isIntegral x
    have := IsIntegral.map_of_comp_eq (e.symm : K.E →+* FractionRing K.O) (RingHom.id (B.A ⧸ I)) ?_ hx
    · simpa using this
    · ext t
      change algebraMap K.E (B.A ⧸ I) (e (e.symm t)) = _
      simp
  have hinv' : Ideal.Quotient.mk I (f * z) = (Ideal.Quotient.mk I (f * y))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← hfm, show f * (f * z * (f * y)) = f * y * z * f * f by ring, hyz, hf.eq, hf.eq, hf1]
  rcases GlobalTheory.LN.isIntegral_or_isIntegral_inv K.O (B.A ⧸ I) (Ideal.Quotient.mk I (f * y)) with h | h
  · left
    have := isIntegral_idem_mul_of_quot hf (f * y) h
    rwa [← mul_assoc, hf.eq] at this
  · right
    rw [← hinv'] at h
    have := isIntegral_idem_mul_of_quot hf (f * z) h
    rwa [← mul_assoc, hf.eq] at this

end GlobalTheory.UnitLemma.Desc
end
end

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_isIntegral_inv_in_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f → (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f → IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := by
  atlas_forward_decl GlobalTheory.UnitLemma.Desc.isIntegral_or_isIntegral_of_fieldFactor
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem span_adjoin_gen_eq_top {K : UQ} (B : InvAlg K) (hP : B.P.Separable) :
    Submodule.span K.E ((Subalgebra.toSubmodule (Algebra.adjoin K.O {B.g}) : Submodule K.O B.A) : Set B.A) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨f, rfl⟩ := Sandwich.exists_aeval B hP x
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  show B.g ^ i ∈ Algebra.adjoin K.O {B.g}
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) i

theorem pow_smul_mem_adjoin_gen : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a →
    ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by
  intro K B a hP ha
  obtain ⟨m, hm⟩ := Sandwich.integral_sub B hP a ha.2.1 _ (span_adjoin_gen_eq_top B hP)
  refine ⟨m, fun r hr => ?_⟩
  have h := hm m le_rfl r hr
  have e : (al K a ^ m) • r = algebraMap K.O B.A a ^ m * r := by
    rw [Algebra.smul_def, al, ← map_pow, ← map_pow, ← IsScalarTower.algebraMap_apply]
  rw [e]
  exact h

end GlobalTheory.UnitLemma.Desc
end
end

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a → ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by
  atlas_forward_decl GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen
end

section
section
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial

theorem exists_isIntegral_pow_smul : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ x : B.A,
    ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := GlobalTheory.T.exists_isIntegral_smallElement_pow_smul

theorem isIntegral_or_of_fieldFactor : ∀ (K : UQ) (B : InvAlg K) (f y z : B.A), IsIdempotentElem f →
    (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) → f * y * z = f →
    IsIntegral K.O (f * y) ∨ IsIntegral K.O (f * z) := GlobalTheory.T.isIntegral_or_isIntegral_inv_in_fieldFactor

theorem exists_pow_smul_mem_adjoin_g : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a →
    ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable

variable {K : UQ} (B : InvAlg K)

theorem al_ne (a : K.O) (ha : K.Small a) : al K a ≠ 0 := by
  intro h
  exact ha.1 ((IsFractionRing.injective K.O K.E) (by simpa using h))

theorem isIntegral_sigma {r : B.A} (hr : IsIntegral K.O r) : IsIntegral K.O (B.σ r) := by
  obtain ⟨q, hq, h0⟩ := hr
  have hsub : ∀ x : K.O, K.c (algebraMap K.O K.E x) ∈ (algebraMap K.O K.E).range := fun x => by
    obtain ⟨y, hy⟩ := K.c_int x; exact ⟨y, hy.symm⟩
  let ψ : K.O ≃+* (algebraMap K.O K.E).range :=
    RingEquiv.ofBijective (algebraMap K.O K.E).rangeRestrict
      ⟨fun x y h => IsFractionRing.injective K.O K.E (congrArg Subtype.val h), (algebraMap K.O K.E).rangeRestrict_surjective⟩
  let cO : K.O →+* K.O := ψ.symm.toRingHom.comp
    (((K.c : K.E →+* K.E).comp (algebraMap K.O K.E)).codRestrict _ hsub)
  have hcO : ∀ x, algebraMap K.O K.E (cO x) = K.c (algebraMap K.O K.E x) := fun x => by
    have := ψ.apply_symm_apply ⟨K.c (algebraMap K.O K.E x), hsub x⟩
    exact congrArg Subtype.val this
  have hcomp : (algebraMap K.O B.A).comp cO = (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A) := by
    ext x
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, IsScalarTower.algebraMap_apply K.O K.E B.A x, B.σ_alg, hcO]
  refine ⟨q.map cO, hq.map cO, ?_⟩
  rw [eval₂_map, hcomp]
  have := hom_eval₂ q (algebraMap K.O B.A) (B.σ : B.A →+* B.A) r
  rw [h0, map_zero] at this
  exact this.symm

theorem sigma_smul (c : K.E) (x : B.A) : B.σ (c • x) = K.c c • B.σ x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, B.σ_alg]

theorem isIntegral_idem {f : B.A} (hf : IsIdempotentElem f) : IsIntegral K.O f :=
  ⟨X ^ 2 - X, by
    have : (X ^ 2 - X : K.O[X]) = X ^ 2 - C 1 * X ^ 1 := by simp
    rw [this]; exact monic_X_pow_sub (by simp), by simp [sq, hf.eq]⟩

theorem isIntegral_pow_smul (a : K.O) (n : ℕ) {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O ((al K a ^ n) • x) := by
  have : (al K a ^ n) • x = algebraMap K.O B.A (a ^ n) * x := by
    simp only [al, Algebra.smul_def, IsScalarTower.algebraMap_apply K.O K.E B.A, map_pow]
  rw [this]; exact isIntegral_algebraMap.mul hx

theorem not_isIntegral_inv_smul (a : K.O) (ha : K.Small a) {f : B.A} (hf : IsIdempotentElem f)
    (hf0 : f ≠ 0) : ¬ IsIntegral K.O ((al K a ^ (-1 : ℤ)) • f) := by
  intro h
  let I : Ideal B.A := Ideal.span {1 - f}
  have hI : I ≠ ⊤ := by
    intro hT
    have : (1 : B.A) ∈ I := hT ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 this
    apply hf0
    calc f = f * (c * (1 - f)) := by rw [hc, mul_one]
      _ = c * (f - f * f) := by ring
      _ = 0 := by rw [hf.eq, sub_self, mul_zero]
  haveI : Nontrivial (B.A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have hmk : Ideal.Quotient.mk I f = 1 := by
    rw [← map_one (Ideal.Quotient.mk I), eq_comm, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have h2 : IsIntegral K.O (algebraMap K.E (B.A ⧸ I) (al K a ^ (-1 : ℤ))) := by
    have := h.map (Ideal.Quotient.mkₐ K.O I)
    rwa [Ideal.Quotient.mkₐ_eq_mk, Algebra.smul_def, map_mul, hmk, mul_one,
      Ideal.Quotient.mk_algebraMap] at this
  have h3 : IsIntegral K.O (al K a ^ (-1 : ℤ)) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom K.O K.E (B.A ⧸ I))
      (algebraMap K.E (B.A ⧸ I)).injective).1 h2
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have hne := al_ne a ha
  have h4 : algebraMap K.O K.E (a * t) = algebraMap K.O K.E 1 := by
    rw [map_mul, ht, map_one, zpow_neg_one]; exact mul_inv_cancel₀ hne
  have h5 : a * t = 1 := IsFractionRing.injective K.O K.E h4
  exact (IsLocalRing.mem_maximalIdeal a).1 ha.2.1 (⟨⟨a, t, h5, by rw [mul_comm]; exact h5⟩, rfl⟩)

theorem smul_mem_of_adjoin (M : Submodule K.O B.A) (hM : ∀ y ∈ M, B.g * y ∈ M) {s : B.A}
    (hs : s ∈ Algebra.adjoin K.O {B.g}) : ∀ m ∈ M, s * m ∈ M := by
  let T : Subalgebra K.O B.A :=
    { carrier := {s | ∀ m ∈ M, s * m ∈ M}
      mul_mem' := fun {x y} hx hy m hm => by rw [mul_assoc]; exact hx _ (hy m hm)
      one_mem' := fun m hm => by rw [one_mul]; exact hm
      add_mem' := fun {x y} hx hy m hm => by rw [add_mul]; exact M.add_mem (hx m hm) (hy m hm)
      zero_mem' := fun m hm => by rw [zero_mul]; exact M.zero_mem
      algebraMap_mem' := fun c m hm => by rw [← Algebra.smul_def]; exact M.smul_mem c hm }
  have : Algebra.adjoin K.O {B.g} ≤ T := Algebra.adjoin_le (by
    intro x hx; rw [Set.mem_singleton_iff.1 hx]; exact hM)
  exact this hs

theorem exists_pos : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι)
    (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S →
    ∃ N : ℕ, ∀ M ∈ B.Lin, ∃ p : ι → ℤ, Pos B a e N M p := by
  intro K B ι _ e π S a hP ha hF
  obtain ⟨N0, hN0⟩ := exists_pow_smul_mem_adjoin_g K B a hP ha
  refine ⟨N0 + 1, fun M hM => ?_⟩
  set t := al K a with ht_def
  have ht : t ≠ 0 := al_ne a ha
  have hct : K.c t = t := ha.2.2
  have hRM : ∀ r : B.A, IsIntegral K.O r → ∀ m ∈ M, (t ^ N0) • (r * m) ∈ M := fun r hr m hm => by
    rw [← smul_mul_assoc]; exact smul_mem_of_adjoin B M hM.2.1 (hN0 r hr) m hm
  have core : ∀ f : B.A, IsIdempotentElem f → (∀ w, f * w ≠ 0 → ∃ v, f * w * v = f) →
      ∀ (q : ℤ) (m : B.A), m ∈ M → ¬ IsIntegral K.O ((t ^ (-q)) • (f * m)) →
      ∀ r : B.A, IsIntegral K.O r → (t ^ (q + N0)) • (f * r) ∈ M := by
    intro f hf hfld q m hm hni r hr
    have hy0 : f * ((t ^ (-q)) • m) ≠ 0 := by
      intro h0; apply hni; rw [← mul_smul_comm, h0]; exact isIntegral_zero
    obtain ⟨z, hz⟩ := hfld _ hy0
    have hfz : IsIntegral K.O (f * z) := by
      rcases isIntegral_or_of_fieldFactor K B f ((t ^ (-q)) • m) z hf hfld hz with h | h
      · exact (hni (by rwa [mul_smul_comm] at h)).elim
      · exact h
    have key : (t ^ (q + N0)) • (f * r) = (t ^ N0) • ((r * (f * z)) * m) := by
      have e1 : f * r = (t ^ (-q)) • ((r * (f * z)) * m) := by
        calc f * r = r * (f * ((t ^ (-q)) • m) * z) := by rw [hz]; ring
          _ = _ := by simp only [Algebra.smul_def]; ring
      rw [e1, smul_smul, ← zpow_add₀ ht, show q + N0 + -q = (N0 : ℤ) by ring, zpow_natCast]
    rw [key]; exact hRM _ (hr.mul hfz) m hm
  have hpos : ∀ i, ∃ pi : ℤ, (∀ r : B.A, IsIntegral K.O r → (t ^ (pi + ↑(N0 + 1))) • (e i * r) ∈ M) ∧
      ∀ m ∈ M, IsIntegral K.O ((t ^ (-pi)) • (e i * m)) := by
    intro i
    obtain ⟨f, hf, hf0, hfld, hS, hnS⟩ := hF.1.2 i
    have hfe : f * e i = f := by
      by_cases hi : i ∈ S
      · rw [(hS hi).1, hf.eq]
      · rw [(hnS hi).2, mul_add, hf.eq, (hnS hi).1, add_zero]
    let P : Set ℤ := {p | ∀ m ∈ M, IsIntegral K.O ((t ^ (-p)) • (e i * m))}
    have hne : P.Nonempty := by
      obtain ⟨s, hs⟩ := hM.1.1
      choose k hk using fun x : B.A => exists_isIntegral_pow_smul K B a ha (e i * x)
      refine ⟨-((s.sup k : ℕ) : ℤ), fun m hm => ?_⟩
      rw [neg_neg, zpow_natCast]
      rw [← hs] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        have hle : k x ≤ s.sup k := Finset.le_sup hx
        rw [← Nat.sub_add_cancel hle, pow_add, ← smul_smul]
        exact isIntegral_pow_smul B a _ (hk x)
      | zero => rw [mul_zero, smul_zero]; exact isIntegral_zero
      | add x y _ _ hx hy => rw [mul_add, smul_add]; exact hx.add hy
      | smul c x _ hx =>
        rw [Algebra.smul_def c x, ← mul_assoc, mul_comm (e i), mul_assoc, ← mul_smul_comm]
        exact isIntegral_algebraMap.mul hx
    have hbdd : BddAbove P := by
      have hm0 : ∃ m ∈ M, f * m ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hle : Submodule.span K.E (M : Set B.A) ≤ LinearMap.ker (LinearMap.mulLeft K.E f) := by
          rw [Submodule.span_le]; intro m hm; exact hcon m hm
        rw [hM.1.2] at hle
        have := hle (Submodule.mem_top : (1 : B.A) ∈ ⊤)
        simp at this; exact hf0 this
      obtain ⟨m0, hm0, hfm0⟩ := hm0
      obtain ⟨z, hz⟩ := hfld m0 hfm0
      obtain ⟨k, hk⟩ := exists_isIntegral_pow_smul K B a ha (f * z)
      refine ⟨k, fun p hp => ?_⟩
      by_contra hlt
      push_neg at hlt
      have h1 : IsIntegral K.O ((t ^ (-p)) • (e i * m0)) := hp m0 hm0
      have h2 : IsIntegral K.O ((t ^ (-p)) • (e i * m0) * (t ^ k • (f * z)) * f) :=
        (h1.mul hk).mul (isIntegral_idem B hf)
      have hq : e i * m0 * (f * z) * f = f := by
        calc e i * m0 * (f * z) * f = (f * e i) * m0 * z * f := by ring
          _ = f := by rw [hfe, hz, hf.eq]
      have h3 : (t ^ (-p)) • (e i * m0) * (t ^ k • (f * z)) * f = (t ^ ((k : ℤ) - p)) • f := by
        rw [sub_eq_add_neg, zpow_add₀ ht, zpow_natCast]
        simp only [Algebra.smul_def, map_mul]
        linear_combination (algebraMap K.E B.A (t ^ (-p)) * algebraMap K.E B.A (t ^ k)) * hq
      have h4 : (t ^ (-1 : ℤ)) • f = (t ^ ((p - k - 1 : ℤ).toNat)) • ((t ^ ((k : ℤ) - p)) • f) := by
        rw [smul_smul, ← zpow_natCast, ← zpow_add₀ ht, Int.toNat_of_nonneg (by omega),
          show (p - k - 1 : ℤ) + (k - p) = -1 by ring]
      exact not_isIntegral_inv_smul B a ha hf hf0 (h4 ▸ isIntegral_pow_smul B a _ (h3 ▸ h2))
    obtain ⟨pi, hmem, hnot⟩ : ∃ pi, pi ∈ P ∧ pi + 1 ∉ P :=
      ⟨sSup P, Int.csSup_mem hne hbdd, fun h => by have := le_csSup hbdd h; omega⟩
    refine ⟨pi, fun r hr => ?_, hmem⟩
    have hnot' : ¬ ∀ m ∈ M, IsIntegral K.O ((t ^ (-(pi + 1))) • (e i * m)) := hnot
    push_neg at hnot'
    obtain ⟨m, hm, hni⟩ := hnot'
    have hexp : pi + ↑(N0 + 1) = (pi + 1) + N0 := by push_cast; ring
    rw [hexp]
    by_cases hi : i ∈ S
    · rw [(hS hi).1] at hni ⊢
      exact core f hf hfld (pi + 1) m hm hni r hr
    · obtain ⟨hff, hei⟩ := hnS hi
      have Hf : ∀ r : B.A, IsIntegral K.O r → (t ^ (pi + 1 + N0)) • (f * r) ∈ M := by
        by_cases h1 : IsIntegral K.O ((t ^ (-(pi + 1))) • (f * m))
        · have h2 : ¬ IsIntegral K.O ((t ^ (-(pi + 1))) • (B.σ f * m)) := by
            intro h2; apply hni; rw [hei, add_mul, smul_add]; exact h1.add h2
          have h3 : ¬ IsIntegral K.O ((t ^ (-(pi + 1))) • (f * B.σ m)) := by
            intro h3; apply h2
            have := isIntegral_sigma B h3
            rwa [sigma_smul, map_mul, B.σ_σ, map_zpow₀, hct] at this
          exact core f hf hfld (pi + 1) (B.σ m) (hM.2.2 m hm) h3
        · exact core f hf hfld (pi + 1) m hm h1
      rw [hei, add_mul, smul_add]
      refine M.add_mem (Hf r hr) ?_
      have := hM.2.2 _ (Hf (B.σ r) (isIntegral_sigma B hr))
      rwa [sigma_smul, map_mul, B.σ_σ, map_zpow₀, hct] at this
  choose p hp using hpos
  exact ⟨p, hp⟩

end GlobalTheory.UnitLemma.Desc
end
end

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_idempotent_position_involution_stable : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∃ N : ℕ, ∀ M ∈ B.Lin, ∃ p : ι → ℤ, Pos B a e N M p := by
  atlas_forward_decl GlobalTheory.UnitLemma.Desc.exists_pos
end

section
section
noncomputable section
namespace GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Classical

theorem isIntegral_trace_of_isIntegral'
    (U L Ω : Type) [CommRing U] [Field L] [CommRing Ω] [Algebra U L] [Algebra L Ω] [Algebra U Ω]
    [IsScalarTower U L Ω] [Module.Finite L Ω] (ω : Ω) (h : IsIntegral U ω) :
    IsIntegral U (Algebra.trace L Ω ω) := by
  classical
  let b := Module.finBasis L Ω
  let A := AlgebraicClosure L
  let f : Ω →ₐ[U] Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A :=
    (((Algebra.ofId L A).mapMatrix).comp (Algebra.leftMulMatrix b)).restrictScalars U
  have hM : IsIntegral U (f ω) := h.map f
  have htr : algebraMap L A (Algebra.trace L Ω ω) = (f ω).trace := by
    rw [Algebra.trace_eq_matrix_trace b]
    simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := L) (B := A) (algebraMap L A).injective, htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (f ω).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum A (f ω) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (f ω) (p.map (algebraMap U A)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (f ω) (p.map (algebraMap U A)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix (Fin (Module.finrank L Ω)) (Fin (Module.finrank L Ω)) A) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

variable {K : UQ} (B : InvAlg K)

theorem trace_mem_of_isIntegral (x : B.A) (hx : IsIntegral K.O x) :
    Algebra.trace K.E B.A x ∈ (algebraMap K.O K.E).range :=
  IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_trace_of_isIntegral' K.O K.E B.A x hx)

theorem trace_idem_ne_zero (e : B.A) (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    Algebra.trace K.E B.A e ≠ 0 := by
  rw [Algebra.trace_apply]
  have hid : IsIdempotentElem (Algebra.lmul K.E B.A e) := by
    unfold IsIdempotentElem; ext y; simp [← mul_assoc, he.eq]
  intro h
  have := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hid).1 h
  apply h0
  have h1 := LinearMap.congr_fun this 1
  simpa using h1

theorem exists_lb (a : K.O) (ha : K.Small a) (T : K.E) (hT : T ≠ 0) :
    ∃ L : ℤ, ∀ n : ℤ, al K a ^ n * T ∈ (algebraMap K.O K.E).range → L ≤ n := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := K.O) T
  have hy0 : algebraMap K.O K.E y ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hT
  have hα : al K a ≠ 0 := by
    simpa [al] using (IsFractionRing.injective K.O K.E).ne ha.1
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal K.O)
    (IsLocalRing.maximalIdeal.isMaximal K.O).ne_top
  obtain ⟨m0, hm0⟩ : ∃ m : ℕ, x ∉ IsLocalRing.maximalIdeal K.O ^ m := by
    by_contra h
    push_neg at h
    apply hx0
    rw [← Ideal.mem_bot, ← hinf, Ideal.mem_iInf]
    exact h
  refine ⟨1 - m0, fun n hn => ?_⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat (show n ≤ 0 by omega)
  obtain ⟨o, ho⟩ := hn
  have hinv : al K a ^ (-(m : ℤ)) * al K a ^ m = 1 := by
    rw [zpow_neg, zpow_natCast]; exact inv_mul_cancel₀ (pow_ne_zero _ hα)
  have hxe : algebraMap K.O K.E x = algebraMap K.O K.E (o * y * a ^ m) := by
    rw [map_mul, map_mul, ho, map_pow]
    have e1 : al K a ^ (-(m : ℤ)) * (algebraMap K.O K.E x / algebraMap K.O K.E y) * algebraMap K.O K.E y *
        al K a ^ m = (al K a ^ (-(m : ℤ)) * al K a ^ m) * algebraMap K.O K.E x := by
      field_simp
    simp only [al] at e1 hinv ⊢
    rw [e1, hinv, one_mul]
  have hxm : x = o * y * a ^ m := IsFractionRing.injective K.O K.E hxe
  apply hm0
  have : x ∈ IsLocalRing.maximalIdeal K.O ^ m := by
    rw [hxm]; exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow ha.2.1 m)
  exact Ideal.pow_le_pow_right (by omega) this

theorem exists_int_mul (a : K.O) (ha : K.Small a) (y : B.A) :
    ∃ c : ℕ, IsIntegral K.O (al K a ^ (c : ℤ) • y) := by
  have hyE : IsIntegral K.E y := Algebra.IsIntegral.isIntegral y
  obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors K.O) (Rₘ := K.E) y hyE
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨n, u, hmu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hm0 hϖ
  have ha' : a ∈ Ideal.span {ϖ} := hϖ.maximalIdeal_eq ▸ ha.2.1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 ha'
  refine ⟨n, ?_⟩
  have hc : a ^ n = (((u⁻¹ : K.Oˣ) : K.O) * b ^ n) * m := by
    rw [hmu, ← hb, mul_pow]
    calc b ^ n * ϖ ^ n = ((u⁻¹ : K.Oˣ) : K.O) * u * (b ^ n * ϖ ^ n) := by simp
      _ = _ := by ring
  have h1 : al K a ^ (n : ℤ) • y = (((u⁻¹ : K.Oˣ) : K.O) * b ^ n) • (m • y) := by
    rw [zpow_natCast, smul_smul, ← hc]
    simp only [al, ← map_pow, algebraMap_smul]
  have h2 : (m • y) = (⟨m, hm⟩ : nonZeroDivisors K.O) • y := rfl
  rw [h1, Algebra.smul_def, h2]
  exact (isIntegral_algebraMap).mul hmi

end GlobalTheory.UnitLemma.Desc

noncomputable section
namespace GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Classical

variable {K : UQ} (B : InvAlg K)

theorem exists_ub (a : K.O) (ha : K.Small a) (e : B.A) (he : IsIdempotentElem e) (he0 : e ≠ 0)
    (y : B.A) : ∃ H : ℤ, IsUnit y → ∀ n : ℤ, IsIntegral K.O (al K a ^ (-n) • (e * y)) → n ≤ H := by
  by_cases hy : IsUnit y
  swap
  · exact ⟨0, fun h => absurd h hy⟩
  have hα : al K a ≠ 0 := by
    simpa [al] using (IsFractionRing.injective K.O K.E).ne ha.1
  obtain ⟨w, hw⟩ := hy.exists_right_inv
  obtain ⟨c, hc⟩ := exists_int_mul B a ha w
  obtain ⟨L, hL⟩ := exists_lb a ha _ (trace_idem_ne_zero B e he he0)
  refine ⟨c - L, fun _ n hn => ?_⟩
  have hi := hn.mul hc
  have heq : al K a ^ (-n) • (e * y) * (al K a ^ (c : ℤ) • w) = al K a ^ (-n + c) • e := by
    rw [smul_mul_smul_comm, mul_assoc, hw, mul_one, ← zpow_add₀ hα]
  rw [heq] at hi
  have ht := trace_mem_of_isIntegral B _ hi
  rw [map_smul, smul_eq_mul] at ht
  have := hL _ ht
  omega

theorem exists_lb' (a : K.O) (ha : K.Small a) (e : B.A) (he : IsIdempotentElem e) (he0 : e ≠ 0) (N : ℕ)
    (s : B.A) : ∃ L0 : ℤ, IsUnit s → ∀ (M : Submodule K.O B.A) (n : ℤ),
      (∀ r : B.A, IsIntegral K.O r → al K a ^ (n + N) • (e * r) ∈ M) → InDual B s M → L0 ≤ n := by
  by_cases hs : IsUnit s
  swap
  · exact ⟨0, fun h => absurd h hs⟩
  have hα : al K a ≠ 0 := by
    simpa [al] using (IsFractionRing.injective K.O K.E).ne ha.1
  obtain ⟨w, hw⟩ := hs.exists_right_inv
  obtain ⟨c, hc⟩ := exists_int_mul B a ha w
  obtain ⟨L, hL⟩ := exists_lb a ha _ (trace_idem_ne_zero B e he he0)
  refine ⟨L - N - c, fun _ M n hM hD => ?_⟩
  have hz := hD _ (hM _ hc)
  have heq : s * (al K a ^ (n + N) • (e * (al K a ^ (c : ℤ) • w))) = al K a ^ (n + N + c) • e := by
    rw [mul_smul_comm, mul_smul_comm, mul_smul_comm, smul_smul, ← zpow_add₀ hα, mul_left_comm, hw, mul_one]
  rw [heq, map_smul, smul_eq_mul] at hz
  have := hL _ hz
  omega

theorem small_card (K : UQ) : K.Small (Nat.card (IsLocalRing.ResidueField K.O) : K.O) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h' : ((Nat.card (IsLocalRing.ResidueField K.O) : ℕ) : K.E) = 0 := by
      rw [← map_natCast (algebraMap K.O K.E), h, map_zero]
    rw [Nat.cast_eq_zero] at h'
    exact (Nat.card_pos (α := IsLocalRing.ResidueField K.O)).ne' h'
  · rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    haveI := Fintype.ofFinite (IsLocalRing.ResidueField K.O)
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  · rw [map_natCast, map_natCast]

theorem finite_term_ne_zero : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι),
    B.P.Separable → IsFrame B e π S → ∀ (I I' : Finset ι), I ⊆ S → I' ⊆ S → ∀ u s : B.A, IsUnit u → IsUnit s →
    {M ∈ B.Lin | term B π I I' u s M ≠ 0}.Finite := by
  intro K B ι _ e π S hsep hF I I' hI hI' u s hu hs
  set a : K.O := (Nat.card (IsLocalRing.ResidueField K.O) : K.O)
  have ha : K.Small a := small_card K
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_lattice_idempotent_position_involution_stable K B ι e π S a hsep ha hF
  obtain ⟨C, hC⟩ := GlobalTheory.T.card_lattices_idempotent_position_bounded K B ι e π S a hsep ha hF N
  have he : ∀ i, IsIdempotentElem (e i) := fun i => hF.1.1.idem i
  have he0 : ∀ i, e i ≠ 0 := by
    intro i
    obtain ⟨f, hf, hf0, -, hS, hnS⟩ := hF.1.2 i
    by_cases hi : i ∈ S
    · rw [(hS hi).1]; exact hf0
    · obtain ⟨h1, h2⟩ := hnS hi
      intro h
      apply hf0
      have : f * e i = f := by rw [h2, mul_add, hf.eq, h1, add_zero]
      rw [h, mul_zero] at this
      exact this.symm
  have hπ : ∀ J ⊆ S, IsUnit (∏ j ∈ J, π j) := fun J hJ =>
    Finset.prod_induction _ IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one
      (fun j hj => (hF.2 j (hJ hj)).1.1)
  choose H hH using fun i y => exists_ub B a ha (e i) (he i) (he0 i) y
  choose Lo hLo using fun i t => exists_lb' B a ha (e i) (he i) (he0 i) N t
  let Ys := I.powerset.image (fun J => (∏ j ∈ J, π j) * u)
  let Ss := I'.powerset.image (fun J => (∏ j ∈ J, π j) * s)
  let P : Set (ι → ℤ) := ⋃ y ∈ (Ys : Set B.A), ⋃ t ∈ (Ss : Set B.A),
    Set.pi Set.univ (fun i => Set.Icc (Lo i t) (H i y))
  have hP : P.Finite := Set.Finite.biUnion Ys.finite_toSet fun y _ =>
    Set.Finite.biUnion Ss.finite_toSet fun t _ => Set.Finite.pi (fun i => Set.finite_Icc _ _)
  refine (hP.biUnion fun p _ => (hC p).1).subset ?_
  rintro M ⟨hML, hMt⟩
  obtain ⟨p, hp⟩ := hN M hML
  have h1 : dlt π I (indM B M) u ≠ 0 := left_ne_zero_of_mul hMt
  have h2 : dlt π I' (indD B M) s ≠ 0 := right_ne_zero_of_mul hMt
  obtain ⟨J, hJ, hJ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  obtain ⟨J', hJ', hJ0'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
  have hyM : (∏ j ∈ J, π j) * u ∈ M := by
    by_contra h; apply hJ0; simp [indM, h]
  have htD : InDual B ((∏ j ∈ J', π j) * s) M := by
    by_contra h; apply hJ0'; simp [indD, h]
  have hyU : IsUnit ((∏ j ∈ J, π j) * u) :=
    (hπ J ((Finset.mem_powerset.1 hJ).trans hI)).mul hu
  have htU : IsUnit ((∏ j ∈ J', π j) * s) :=
    (hπ J' ((Finset.mem_powerset.1 hJ').trans hI')).mul hs
  refine Set.mem_biUnion (x := p) ?_ hp
  refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hJ))
    (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hJ')) ?_)
  intro i _
  exact ⟨hLo i _ htU M (p i) (hp i).1 htD, hH i _ hyU (p i) ((hp i).2 _ hyM)⟩

end GlobalTheory.UnitLemma.Desc
end
end
end

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι), B.P.Separable → IsFrame B e π S → ∀ (I I' : Finset ι), I ⊆ S → I' ⊆ S → ∀ u s : B.A, IsUnit u → IsUnit s → {M ∈ B.Lin | term B π I I' u s M ≠ 0}.Finite := by
  atlas_forward_decl GlobalTheory.UnitLemma.Desc.finite_term_ne_zero
end
