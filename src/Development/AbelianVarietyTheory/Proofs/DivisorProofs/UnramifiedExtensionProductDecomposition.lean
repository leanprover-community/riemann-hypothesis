import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
import BuildAid.ForwardExisting

section
section
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.LKRes.ResSplit

theorem pow_sub_one_ne_zero (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r) : p ^ r - 1 ≠ 0 := by
  have h := Nat.one_lt_pow hr.ne' (Fact.out : p.Prime).one_lt
  omega

theorem Qr_eq_adjoin (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ r - 1)) (hζr : ζ ∈ Qr p r) :
    Qr p r = IntermediateField.adjoin ℚ_[p] {ζ} := by
  apply le_antisymm
  · apply UnramifiedExtensions.Kn_le (Q0 p) bot_le
    intro ξ hξ
    rw [residue_cardinality_base_field] at hξ
    have : NeZero (p ^ r - 1) := ⟨pow_sub_one_ne_zero p hr⟩
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact hζr

theorem Qr_span_pow (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r) (ζ : Qr p r)
    (hζ : IsPrimitiveRoot (ζ : PadicAlgCl p) (p ^ r - 1)) (b : Qr p r) :
    ∃ d : Fin r → ℚ_[p], b = ∑ j : Fin r, d j • ζ ^ (j : ℕ) := by
  have hQ := Qr_eq_adjoin p hr hζ ζ.2
  have hrank : Module.finrank ℚ_[p] (Qr p r) = r := by
    rw [finrank_Kn p (Q0 p) inferInstance hr, IntermediateField.finrank_bot, mul_one]
  have hint : IsIntegral ℚ_[p] (ζ : PadicAlgCl p) := Algebra.IsIntegral.isIntegral _
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = r := by
    rw [← PowerBasis.finrank pb]
    exact (congrArg (fun L : IntermediateField ℚ_[p] (PadicAlgCl p) => Module.finrank ℚ_[p] L) hQ).symm.trans hrank
  have hb : (b : PadicAlgCl p) ∈ IntermediateField.adjoin ℚ_[p] {(ζ : PadicAlgCl p)} := by
    rw [← hQ]; exact b.2
  obtain ⟨f, hf, hy⟩ := pb.exists_eq_aeval ⟨b, hb⟩
  rw [hdim] at hf
  have h1 : (b : PadicAlgCl p) = Polynomial.aeval (ζ : PadicAlgCl p) f := by
    have := congrArg Subtype.val hy
    rw [this]
    show IntermediateField.val _ (Polynomial.aeval pb.gen f) = _
    rw [← Polynomial.aeval_algHom_apply]
    rfl
  refine ⟨fun j => f.coeff j, ?_⟩
  apply Subtype.ext
  rw [h1, Polynomial.aeval_eq_sum_range' hf, Finset.sum_range]
  simp [IntermediateField.coe_sum]

theorem KQ_eq_sum_pow : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r →
    ∀ (ζ : Qr p r), IsPrimitiveRoot (ζ : PadicAlgCl p) (p ^ r - 1) →
    ∀ x : KQ p K r, ∃ c : Fin r → K, x = ∑ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) := by
  intro p _ K r hr ζ hζ x
  have key : ∀ (c : K) (z : Qr p r), inclK p K r c * inclQ p K r z = (c ⊗ₜ[ℚ_[p]] z : K ⊗[ℚ_[p]] Qr p r) := by
    intro c z
    show (c ⊗ₜ[ℚ_[p]] (1 : Qr p r) : K ⊗[ℚ_[p]] Qr p r) * ((1 : K) ⊗ₜ[ℚ_[p]] z) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h : ∀ y : K ⊗[ℚ_[p]] Qr p r, ∃ c : Fin r → K,
      y = ∑ j : Fin r, (c j ⊗ₜ[ℚ_[p]] (ζ ^ (j : ℕ)) : K ⊗[ℚ_[p]] Qr p r) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a b =>
      obtain ⟨d, hd⟩ := Qr_span_pow p hr ζ hζ b
      refine ⟨fun j => d j • a, ?_⟩
      rw [hd, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y z hy hz =>
      obtain ⟨c, hc⟩ := hy
      obtain ⟨c', hc'⟩ := hz
      refine ⟨c + c', ?_⟩
      rw [hc, hc', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, TensorProduct.add_tmul]
  obtain ⟨c, hc⟩ := h x
  refine ⟨c, ?_⟩
  have e : ∀ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) =
      (c j ⊗ₜ[ℚ_[p]] (ζ ^ (j : ℕ)) : K ⊗[ℚ_[p]] Qr p r) := by
    intro j
    rw [← map_pow, key]
  rw [Finset.sum_congr rfl fun j _ => e j]
  exact hc

end GlobalTheory.LKRes.ResSplit
end
end

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_extension_basis : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r → ∀ (ζ : Qr p r), IsPrimitiveRoot (ζ : PadicAlgCl p) (p ^ r - 1) → ∀ x : KQ p K r, ∃ c : Fin r → K, x = ∑ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) := by
  atlas_forward_decl GlobalTheory.LKRes.ResSplit.KQ_eq_sum_pow
end

section
section
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

namespace GlobalTheory.LKRes.ResSplit

theorem pow_pow_eq_of_zmod {p : ℕ} {F : Type} [CommMonoid F] {r : ℕ} {ζ : F} (hζ : ζ ^ (p ^ r - 1) = 1)
    (hp : 0 < p) {m₁ m₂ : ℕ} (h : (m₁ : ZMod r) = m₂) : ζ ^ p ^ m₁ = ζ ^ p ^ m₂ := by
  have hper : ζ ^ p ^ r = ζ := by
    have h1 : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp
    rw [show p ^ r = (p ^ r - 1) + 1 by omega, pow_succ, hζ, one_mul]
  have hmod : ∀ m, ζ ^ p ^ m = ζ ^ p ^ (m % r) := by
    intro m
    conv_lhs => rw [← Nat.mod_add_div m r]
    generalize m / r = n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, ← add_assoc, pow_add, mul_comm, pow_mul, hper, ih]
  rw [hmod m₁, hmod m₂, (ZMod.natCast_eq_natCast_iff' m₁ m₂ r).1 h]

theorem spread_main (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (f r : ℕ) (hq : qK p K = p ^ f) (hr : 0 < r)
    (ζ : PadicAlgCl p) (hζ : ζ ^ (p ^ r - 1) = 1) (c : Fin r → K) (s : ℕ) :
    ∃ i < Nat.gcd f r, ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ s) ^ (j : ℕ)‖ =
      ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)‖ := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set d := Nat.gcd f r with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right f hr
  refine ⟨s % d, Nat.mod_lt _ hd0, ?_⟩
  haveI : NeZero r := ⟨hr.ne'⟩

  set a : ℕ := ((f.gcdA r : ℤ) : ZMod r).val with ha
  have hfa : ((f : ZMod r) * (a : ZMod r)) = (d : ZMod r) := by
    rw [ha, ZMod.natCast_zmod_val]
    have h := Nat.gcd_eq_gcd_ab f r
    have h2 : ((d : ℤ) : ZMod r) = (((f : ℤ) * f.gcdA r + (r : ℤ) * f.gcdB r : ℤ) : ZMod r) := by
      rw [hd, h]
    push_cast at h2
    rw [ZMod.natCast_self, zero_mul, add_zero] at h2
    exact h2.symm
  set k := a * (s / d) with hk
  have hcong : ((s % d + f * k : ℕ) : ZMod r) = (s : ZMod r) := by
    rw [hk]
    push_cast
    rw [← mul_assoc, hfa]
    conv_rhs => rw [← Nat.mod_add_div s d]
    push_cast
    ring

  have hpN : ¬ p ∣ p ^ r - 1 := by
    intro hdvd
    have h1 : p ∣ p ^ r := dvd_pow_self p hr.ne'
    have h2 : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
    have h3 : p ∣ p ^ r - (p ^ r - 1) := Nat.dvd_sub h1 hdvd
    rw [show p ^ r - (p ^ r - 1) = 1 by omega] at h3
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
  set i := s % d
  have hζi : (ζ ^ p ^ i) ^ (p ^ r - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hφ : (frobK p K ^ k) (ζ ^ p ^ i) = ζ ^ p ^ s := by
    rw [IsFrob.pow_apply hK (isFrob_frobK hK) hpN k hζi, hq, ← pow_mul, ← pow_mul, ← pow_add]
    exact pow_pow_eq_of_zmod hζ (by omega) hcong
  set φ := frobK p K ^ k
  have hsum : φ (∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)) =
      ∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ s) ^ (j : ℕ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hφ]
    congr 1
    exact φ.commutes (c j)
  rw [← hsum, norm_GK]

end GlobalTheory.LKRes.ResSplit

theorem GlobalTheory.LKRes.ResSplit.spread : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ), qK p K = p ^ f → 0 < r → ∀ (ζ : PadicAlgCl p), ζ ^ (p ^ r - 1) = 1 → ∀ (c : Fin r → K) (s : ℕ), ∃ i < Nat.gcd f r, ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ s) ^ (j : ℕ)‖ = ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)‖ :=
  fun p _ K hK f r hq hr ζ hζ c s => GlobalTheory.LKRes.ResSplit.spread_main p K hK f r hq hr ζ hζ c s
end

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_frobenius_gcd : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ), qK p K = p ^ f → 0 < r → ∀ (ζ : PadicAlgCl p), ζ ^ (p ^ r - 1) = 1 → ∀ (c : Fin r → K) (s : ℕ), ∃ i < Nat.gcd f r, ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ s) ^ (j : ℕ)‖ = ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)‖ := by
  atlas_forward_decl GlobalTheory.LKRes.ResSplit.spread
end

section
section
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

namespace GlobalTheory.LKRes.ResSplit

open Matrix

theorem vandermonde_integral_of_roots_of_unity : ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ), ¬ p ∣ N → ∀ (w : Fin r → PadicAlgCl p), (∀ s, w s ^ N = 1) → Function.Injective w → ∀ (c : Fin r → PadicAlgCl p), (∀ s, ‖∑ j : Fin r, c j * w s ^ (j : ℕ)‖ ≤ 1) → ∀ j, ‖c j‖ ≤ 1 := by
  intro p _ N r hN w hw hinj c hc j
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero p)
  have hw1 : ∀ s, ‖w s‖ = 1 := fun s => by
    have h := congrArg norm (hw s)
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).1 h
  set S := Obar p
  let ws : Fin r → S := fun s => ⟨w s, mem_Obar_iff.2 (hw1 s).le⟩
  let ys : Fin r → S := fun s => ⟨∑ j : Fin r, c j * w s ^ (j : ℕ), mem_Obar_iff.2 (hc s)⟩
  let V' : Matrix (Fin r) (Fin r) S := Matrix.vandermonde ws
  have hmap : V'.map S.subtype = Matrix.vandermonde w := by
    ext s t; simp [V', ws, Matrix.vandermonde_apply]
  have hdet : ‖(Matrix.vandermonde w).det‖ = 1 := by
    rw [Matrix.det_vandermonde, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [norm_prod]
    refine Finset.prod_eq_one fun k hk => ?_
    have hik : i < k := Finset.mem_Ioi.1 hk
    exact norm_sub_eq_one_of_pow_eq_one p hN (hw k) (hw i) (fun h => (ne_of_lt hik) (hinj h).symm)
  have hdetS : (S.subtype V'.det) = (Matrix.vandermonde w).det := by
    rw [RingHom.map_det, ← hmap]; rfl
  have hne : (Matrix.vandermonde w).det ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet; exact zero_ne_one hdet
  have hunit : IsUnit V'.det := by
    have hmem : ((Matrix.vandermonde w).det)⁻¹ ∈ S := by
      rw [mem_Obar_iff, norm_inv, hdet, inv_one]
    refine IsUnit.of_mul_eq_one ⟨_, hmem⟩ ?_
    apply Subtype.ext
    change S.subtype V'.det * _ = 1
    rw [hdetS, mul_inv_cancel₀ hne]
  let c' : Fin r → S := V'⁻¹ *ᵥ ys
  have hc' : V' *ᵥ c' = ys := by
    simp only [c', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hV : Matrix.vandermonde w *ᵥ (fun k => (c' k : PadicAlgCl p)) = Matrix.vandermonde w *ᵥ c := by
    funext s
    have h1 := RingHom.map_mulVec S.subtype V' c' s
    rw [hc', hmap] at h1
    change _ = (vandermonde w *ᵥ ⇑S.subtype ∘ c') s at h1
    rw [show (fun k => (c' k : PadicAlgCl p)) = ⇑S.subtype ∘ c' from rfl, ← h1]
    simp only [ys, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
    simp [mul_comm]
  have hVu : IsUnit (Matrix.vandermonde w) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
  have hcc : (fun k => (c' k : PadicAlgCl p)) = c := by
    have := congrArg (fun v => (Matrix.vandermonde w)⁻¹ *ᵥ v) hV
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hVu), Matrix.one_mulVec] using this
  rw [← congrFun hcc j]
  exact mem_Obar_iff.1 (c' j).2

end GlobalTheory.LKRes.ResSplit
end

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficients_bounded_roots_unity : ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ), ¬ p ∣ N → ∀ (w : Fin r → PadicAlgCl p), (∀ s, w s ^ N = 1) → Function.Injective w → ∀ (c : Fin r → PadicAlgCl p), (∀ s, ‖∑ j : Fin r, c j * w s ^ (j : ℕ)‖ ≤ 1) → ∀ j, ‖c j‖ ≤ 1 := by
  atlas_forward_decl GlobalTheory.LKRes.ResSplit.vandermonde_integral_of_roots_of_unity
end

section
section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

namespace GlobalTheory.LKRes.ResSplit.Tau

theorem pow_eq_pow_of_modEq' {M : Type*} [Monoid M] {ζ : M} {N a b : ℕ} (hζ : ζ ^ N = 1)
    (h : a ≡ b [MOD N]) : ζ ^ a = ζ ^ b := by
  have h' : a % N = b % N := h
  rw [← Nat.mod_add_div a N, ← Nat.mod_add_div b N, pow_add, pow_add, pow_mul, pow_mul, hζ, one_pow,
    one_pow, h']

theorem pow_modEq_pow_mod (p r a : ℕ) (hp : 1 ≤ p) : p ^ a ≡ p ^ (a % r) [MOD p ^ r - 1] := by
  have h1 : p ^ r ≡ 1 [MOD p ^ r - 1] := ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp)).2 dvd_rfl).symm
  have h2 := (Nat.ModEq.pow (a / r) h1).mul_left (p ^ (a % r))
  rw [one_pow, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div] at h2
  exact h2

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem pow_fix {σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p} {x : PadicAlgCl p} (h : σ x = x) (n : ℕ) :
    (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, h]

theorem pow_apply_root' {σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p} {q N : ℕ}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ N = 1 → σ ζ = ζ ^ q) {ζ : PadicAlgCl p} (hζ : ζ ^ N = 1) (k : ℕ) :
    (σ ^ k) ζ = ζ ^ q ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : (ζ ^ q ^ n) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [pow_succ', AlgEquiv.mul_apply, ih, h _ h1, ← pow_mul, pow_succ]

theorem frob_pow_mod (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : 0 < m) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K m) (a : ℕ) : (frobK p K ^ a) x = (frobK p K ^ (a % m)) x := by
  have h := (IsFrobOn.pow_fixes_iff p K hK hm ((isFrob_frobK hK).isFrobOn m) (m * (a / m))).2
    (dvd_mul_right _ _)
  conv_lhs => rw [← Nat.mod_add_div a m, pow_add, AlgEquiv.mul_apply, h x hx]

theorem exists_tau : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ) (hq : qK p K = p ^ f), 0 < r →
    ∃ τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r),
      (∀ x, τ x = x ↔ (x : PadicAlgCl p) ∈ K) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧
      ∀ b : Qr p r, τ (incQ p K hq r b) = incQ p K hq r ((frobQ p r ^ Nat.gcd f r) b) := by
  intro p _ K hK f r hq hr
  have hp0 : 0 < p := (Nat.Prime.one_lt Fact.out).le
  have hd0 : 0 < Nat.gcd f r := Nat.gcd_pos_of_pos_right f hr
  have hm0 : 0 < r / Nat.gcd f r := Nat.div_pos (Nat.gcd_le_right (m := f) (n := r) hr) hd0
  have hrdm : r = Nat.gcd f r * (r / Nat.gcd f r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right f r)).symm
  have hfdf : f = Nat.gcd f r * (f / Nat.gcd f r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left f r)).symm
  have hcop : Nat.Coprime (f / Nat.gcd f r) (r / Nat.gcd f r) := Nat.coprime_div_gcd_div_gcd hd0
  set d := Nat.gcd f r with hd
  set m := r / d with hm
  set f' := f / d with hf'
  set k := f' ^ (Nat.totient m - 1) with hk
  have hk1 : f' * k ≡ 1 [MOD m] := by
    have ht : 0 < Nat.totient m := Nat.totient_pos.2 hm0
    have := Nat.ModEq.pow_totient hcop
    rwa [← Nat.sub_add_cancel ht, pow_succ'] at this
  have hk2 : f * k ≡ d [MOD r] := by
    have := Nat.ModEq.mul_left' d hk1
    rw [mul_one, ← mul_assoc, ← hfdf, ← hrdm] at this
    exact this
  let σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p := frobK p K ^ k
  have hσ : ∀ x ∈ Kn p K m, σ x ∈ Kn p K m := fun x hx => UnramifiedExtensions.map_mem_Kn K m σ hx
  have hσ' : ∀ x ∈ Kn p K m, σ⁻¹ x ∈ Kn p K m := fun x hx => UnramifiedExtensions.map_mem_Kn K m σ⁻¹ hx
  let τ : Kn p K m ≃+* Kn p K m :=
    { toFun := fun x => ⟨σ x, hσ x x.2⟩
      invFun := fun x => ⟨σ⁻¹ x, hσ' x x.2⟩
      left_inv := fun x => Subtype.ext (by
        show σ⁻¹ (σ (x : PadicAlgCl p)) = x
        rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply])
      right_inv := fun x => Subtype.ext (by
        show σ (σ⁻¹ (x : PadicAlgCl p)) = x
        rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply])
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : PadicAlgCl p) y)
      map_add' := fun x y => Subtype.ext (map_add σ (x : PadicAlgCl p) y) }
  have hτ : ∀ x, ((τ x : Kn p K m) : PadicAlgCl p) = σ x := fun _ => rfl
  refine ⟨τ, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_, fun b => ?_⟩
  · have h1 : σ x = x := by rw [← hτ, h]
    have h2 : (frobK p K ^ (k * f')) x = x := by rw [pow_mul]; exact pow_fix h1 f'
    have h3 : frobK p K (x : PadicAlgCl p) = x := by
      have e := frob_pow_mod hK hm0 x.2 (k * f')
      have e1 := frob_pow_mod hK hm0 x.2 1
      rw [pow_one] at e1
      have e2 : (k * f') % m = 1 % m := by rw [mul_comm]; exact hk1
      rw [e1, ← e2, ← e, h2]
    exact mem_of_frobK_fixed hK (Kn_le_Kur hm0 x.2) h3
  · exact Subtype.ext (show σ (x : PadicAlgCl p) = x from σ.commutes ⟨x, h⟩)
  · have hit : ∀ n (y : Kn p K m), (((⇑τ)^[n] y : Kn p K m) : PadicAlgCl p) = (σ ^ n) y := by
      intro n
      induction n with
      | zero => intro y; rfl
      | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
        rfl
    apply Subtype.ext
    rw [hit, ← pow_mul, frob_pow_mod hK hm0 x.2, show k * m % m = 0 by simp, pow_zero]
    rfl
  · have hN : ¬ p ∣ p ^ r - 1 := by
      intro h
      have h2 := Nat.dvd_sub (dvd_pow_self p hr.ne') h
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp0)] at h2
      exact (Nat.Prime.one_lt Fact.out).ne' (Nat.dvd_one.1 h2)
    have hpow : p ^ (f * k) ≡ p ^ d [MOD p ^ r - 1] := by
      have e := pow_modEq_pow_mod p r (f * k) hp0
      rw [show f * k % r = d % r from hk2] at e
      exact e.trans (pow_modEq_pow_mod p r d hp0).symm
    apply Subtype.ext
    rw [hτ, coe_incQ, coe_incQ, coe_frobQ_pow]
    refine UnramifiedExtensions.eqOn_Kn (Q0 p) (σ := resGK bot_le σ) (τ := frobK p (Q0 p) ^ d) (fun ζ hζ => ?_) b.2
    rw [residue_cardinality_base_field] at hζ
    rw [resGK_apply, frobenius_pow_root_of_unity p hN hζ d]
    have hfr := fun ζ' hζ' => (isFrob_iff hK (frobK p K)).1 (isFrob_frobK hK) ζ' (p ^ r - 1) hN hζ'
    show (frobK p K ^ k) ζ = _
    rw [pow_apply_root' hfr hζ k, hq, ← pow_mul]
    exact pow_eq_pow_of_modEq' hζ hpow

end GlobalTheory.LKRes.ResSplit.Tau
end
end

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_automorphism_gcd : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ) (hq : qK p K = p ^ f), 0 < r → ∃ τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r), (∀ x, τ x = x ↔ (x : PadicAlgCl p) ∈ K) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧ ∀ b : Qr p r, τ (incQ p K hq r b) = incQ p K hq r ((frobQ p r ^ Nat.gcd f r) b) := by
  atlas_forward_decl GlobalTheory.LKRes.ResSplit.Tau.exists_tau
end

section
section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKRes.ResSplit

theorem mem_intR_iff (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
    (x : Kn p K n) : x ∈ GlobalTheory.LKLoc.intR p K n ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap (Kn p K n) (PadicAlgCl p) x) ∈ Obar p ↔ _
  exact mem_Obar_iff

theorem comp_mem_intR (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {f : ℕ}
    (hq : qK p K = p ^ f) (r i : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) :
    comp p K hq r i x ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r) := by
  have h : intKQ p K r ≤ (GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)).comap (comp p K hq r i).toRingHom := by
    apply Subring.closure_le.2
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · show comp p K hq r i (inclK p K r (a : K)) ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)
      rw [mem_intR_iff p K (r / Nat.gcd f r), comp_inclK]
      exact mem_Obar_iff.1 a.2
    · show comp p K hq r i (inclQ p K r (b : Qr p r)) ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)
      rw [mem_intR_iff p K (r / Nat.gcd f r), comp_inclQ, norm_GK]
      exact mem_Obar_iff.1 b.2
  exact h hx

theorem kq_split : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ (f r : ℕ), qK p K = p ^ f → 0 < r →
    ∃ (e : KQ p K r ≃+* (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r)))
      (τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r)),
      (∀ x, (τ x = x ↔ (x : PadicAlgCl p) ∈ K)) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧
      (∀ (a : K) (i : Fin (Nat.gcd f r)), ((e (inclK p K r a) i : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a) ∧
      (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)) (h : i.val + 1 < Nat.gcd f r),
        e (sigKQ p K r x) i = e x ⟨i.val + 1, h⟩) ∧
      (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)), i.val + 1 = Nat.gcd f r → ∀ (i0 : Fin (Nat.gcd f r)),
        i0.val = 0 → e (sigKQ p K r x) i = τ (e x i0)) ∧
      (∀ x : KQ p K r, x ∈ intKQ p K r ↔ ∀ i, e x i ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)) := by
  intro p _ K hK f r hq hr
  have hp := (Fact.out : p.Prime)
  have h1r : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp.pos
  have hN : ¬ p ∣ p ^ r - 1 := by
    intro h
    have h2 : p ∣ 1 := (Nat.dvd_add_right h).1 (by rw [Nat.sub_add_cancel h1r]; exact dvd_pow_self p hr.ne')
    exact hp.not_dvd_one h2
  have hN0 : p ^ r - 1 ≠ 0 := fun h => hN (h ▸ dvd_zero p)
  obtain ⟨ζ, hζ⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hN0
  have hζmem : ζ ∈ Qr p r := UnramifiedExtensions.mem_Kn_of_pow (Q0 p) (by rw [residue_cardinality_base_field]; exact hζ.pow_eq_one)
  set ζ' : Qr p r := ⟨ζ, hζmem⟩ with hζ'
  have hfr : ∀ i : ℕ, (frobK p (Q0 p) ^ i) ζ = ζ ^ p ^ i := fun i => frobenius_pow_root_of_unity p hN hζ.pow_eq_one i

  have val : ∀ (c : Fin r → K) (i : ℕ),
      ((comp p K hq r i (∑ j : Fin r, inclK p K r (c j) * inclQ p K r ζ' ^ (j : ℕ)) : Kn p K (r / Nat.gcd f r)) :
        PadicAlgCl p) = ∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ) := by
    intro c i
    rw [map_sum, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, comp_inclK, comp_inclQ]
    rw [show ((ζ' : Qr p r) : PadicAlgCl p) = ζ from rfl, hfr]

  have key : ∀ c : Fin r → K, (∀ i < Nat.gcd f r, ‖∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ)‖ ≤ 1) →
      ∀ j, ‖(c j : PadicAlgCl p)‖ ≤ 1 := by
    intro c hc j
    refine GlobalTheory.T.coefficients_bounded_roots_unity p (p ^ r - 1) r hN (fun s => ζ ^ p ^ (s : ℕ)) ?_ ?_ (fun j => (c j : PadicAlgCl p)) ?_ j
    · intro s
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · intro s t hst
      rcases Nat.lt_or_ge r 2 with hr2 | hr2
      · apply Fin.ext
        have := s.2; have := t.2
        omega
      · have hlt : ∀ u : Fin r, p ^ (u : ℕ) < p ^ r - 1 := by
          intro u
          have h1 : p ^ (u : ℕ) ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos (by omega)
          have h2 : p ^ r = p * p ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
          have h3 : 2 ≤ p ^ (r - 1) := le_trans hp.two_le (by
            calc p = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ (r - 1) := Nat.pow_le_pow_right hp.pos (by omega))
          have h4 : 2 * p ^ (r - 1) ≤ p * p ^ (r - 1) := Nat.mul_le_mul_right _ hp.two_le
          omega
        have h5 := hζ.pow_inj (hlt s) (hlt t) hst
        exact Fin.ext (Nat.pow_right_injective hp.two_le h5)
    · intro s
      obtain ⟨i, hi, heq⟩ := GlobalTheory.T.norm_sum_frobenius_gcd p K hK f r hq hr ζ hζ.pow_eq_one c s
      rw [heq]
      exact hc i hi

  have inj : Function.Injective (eMap p K hq r) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := GlobalTheory.T.unramified_extension_basis p K r hr ζ' hζ x
    have hz : ∀ i < Nat.gcd f r, ∑ j : Fin r, (c j : PadicAlgCl p) * (ζ ^ p ^ i) ^ (j : ℕ) = 0 := by
      intro i hi
      rw [← val c i]
      have h1 := congrFun hx ⟨i, hi⟩
      rw [eMap_apply] at h1
      rw [h1]
      rfl
    have hc0 : ∀ j, c j = 0 := by
      intro j
      by_contra hcj
      have h1 := key (fun k => ((p : K)⁻¹ * (c j)⁻¹) * c k) (by
        intro i hi
        have h2 : ∑ k : Fin r, (((((p : K)⁻¹ * (c j)⁻¹) * c k : K)) : PadicAlgCl p) * (ζ ^ p ^ i) ^ (k : ℕ) =
            (((p : K)⁻¹ * (c j)⁻¹ : K) : PadicAlgCl p) *
              ∑ k : Fin r, (c k : PadicAlgCl p) * (ζ ^ p ^ i) ^ (k : ℕ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [MulMemClass.coe_mul, mul_assoc]
        rw [h2, hz i hi, mul_zero, norm_zero]
        exact zero_le_one) j
      have h3 : ((p : K)⁻¹ * (c j)⁻¹) * c j = (p : K)⁻¹ := by
        rw [mul_assoc, inv_mul_cancel₀ hcj, mul_one]
      simp only [h3] at h1
      have h5 : (((p : K)⁻¹ : K) : PadicAlgCl p) = (p : PadicAlgCl p)⁻¹ := by simp
      rw [h5, norm_inv, norm_p] at h1
      rw [inv_inv] at h1
      have h4 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      linarith
    simp [hc0]

  haveI hQf : FiniteDimensional ℚ_[p] (Qr p r) := finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI hKQf : FiniteDimensional ℚ_[p] (KQ p K r) := inferInstanceAs (FiniteDimensional ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI hLf : FiniteDimensional ℚ_[p] (Kn p K (r / Nat.gcd f r)) :=
    finiteDimensional_Kn p K hK (Nat.div_pos (Nat.gcd_le_right _ hr) (Nat.gcd_pos_of_pos_right _ hr))
  have dim : Module.finrank ℚ_[p] (KQ p K r) =
      Module.finrank ℚ_[p] (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r)) := by
    have h1 : Module.finrank ℚ_[p] (KQ p K r) = Module.finrank ℚ_[p] K * Module.finrank ℚ_[p] (Qr p r) :=
      Module.finrank_tensorProduct (R := ℚ_[p]) (S := ℚ_[p]) (M := K) (M' := Qr p r)
    rw [h1, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      finrank_Kn p K hK (Nat.div_pos (Nat.gcd_le_right _ hr) (Nat.gcd_pos_of_pos_right _ hr)),
      finrank_Kn p (Q0 p) inferInstance hr, IntermediateField.finrank_bot]
    have h2 : Nat.gcd f r * (r / Nat.gcd f r) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right f r)
    calc _ = Module.finrank ℚ_[p] K * (Nat.gcd f r * (r / Nat.gcd f r)) := by rw [h2, mul_one]
      _ = _ := by ring
  have bij : Function.Bijective (eMap p K hq r) := by
    refine ⟨inj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim (f := (eMap p K hq r).toLinearMap)).1 inj
  obtain ⟨τ, hτK, hτm, hτQ⟩ := GlobalTheory.T.exists_frobenius_automorphism_gcd p K hK f r hq hr
  let e0 := AlgEquiv.ofBijective (eMap p K hq r) bij
  have he : ∀ x i, e0 x i = comp p K hq r i x := fun x i => rfl
  have hlast : ∀ x : KQ p K r, comp p K hq r (Nat.gcd f r) x = τ (comp p K hq r 0 x) := by
    have h : ∀ y : K ⊗[ℚ_[p]] Qr p r, comp p K hq r (Nat.gcd f r) y = τ (comp p K hq r 0 y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero =>
        have z1 : comp p K hq r (Nat.gcd f r) (0 : K ⊗[ℚ_[p]] Qr p r) = 0 := map_zero _
        have z2 : comp p K hq r 0 (0 : K ⊗[ℚ_[p]] Qr p r) = 0 := map_zero _
        rw [z1, z2, map_zero]
      | tmul a b =>
        have h1 : comp p K hq r (Nat.gcd f r) (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) =
            incK p K _ a * incQ p K hq r ((frobQ p r ^ Nat.gcd f r) b) :=
          Algebra.TensorProduct.productMap_apply_tmul _ _ a b
        have h2 : comp p K hq r 0 (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) = incK p K _ a * incQ p K hq r b :=
          (Algebra.TensorProduct.productMap_apply_tmul _ _ a b).trans
            (by rw [AlgHom.comp_apply, pow_zero, AlgHom.one_apply])
        rw [h1, h2, map_mul, hτQ, (hτK _).2 (by rw [coe_incK]; exact a.2)]
      | add y z hy hz =>
        have e1 : comp p K hq r (Nat.gcd f r) (y + z) =
            comp p K hq r (Nat.gcd f r) y + comp p K hq r (Nat.gcd f r) z := map_add _ _ _
        have e2 : comp p K hq r 0 (y + z) = comp p K hq r 0 y + comp p K hq r 0 z := map_add _ _ _
        rw [e1, e2, map_add, hy, hz]
    exact h
  refine ⟨e0.toRingEquiv, τ, hτK, hτm, ?_, ?_, ?_, ?_⟩
  · intro a i
    show ((e0 (inclK p K r a) i : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a
    rw [he, comp_inclK]
  · intro x i h
    show e0 (sigKQ p K r x) i = e0 x ⟨i.val + 1, h⟩
    rw [he, he, comp_sigKQ]
  · intro x i hi i0 hi0
    show e0 (sigKQ p K r x) i = τ (e0 x i0)
    rw [he, he, comp_sigKQ, hi, hi0, hlast]
  · intro x
    show x ∈ intKQ p K r ↔ ∀ i, e0 x i ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)
    constructor
    · intro hx i
      rw [he]
      exact comp_mem_intR p K hq r i x hx
    · intro h
      obtain ⟨c, rfl⟩ := GlobalTheory.T.unramified_extension_basis p K r hr ζ' hζ x
      have hc : ∀ j, ‖(c j : PadicAlgCl p)‖ ≤ 1 := key c (fun i hi => by
        rw [← val c i, ← mem_intR_iff p K (r / Nat.gcd f r)]
        have h1 := h ⟨i, hi⟩
        rwa [he] at h1)
      have hζi : ζ' ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
        rw [mem_intR_iff p (Q0 p) r]
        exact (UnramifiedExtensions.norm_eq_one_of_pow hN0 hζ.pow_eq_one).le
      apply Subring.sum_mem
      intro j _
      apply Subring.mul_mem
      · apply Subring.subset_closure
        left
        exact ⟨⟨c j, mem_Obar_iff.2 (hc j)⟩, rfl⟩
      · apply Subring.pow_mem
        apply Subring.subset_closure
        right
        exact ⟨⟨ζ', hζi⟩, rfl⟩

end GlobalTheory.LKRes.ResSplit
end
end

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_extension_product_decomposition : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ), qK p K = p ^ f → 0 < r → ∃ (e : KQ p K r ≃+* (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r))) (τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r)), (∀ x, (τ x = x ↔ (x : PadicAlgCl p) ∈ K)) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧ (∀ (a : K) (i : Fin (Nat.gcd f r)), ((e (inclK p K r a) i : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a) ∧ (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)) (h : i.val + 1 < Nat.gcd f r), e (sigKQ p K r x) i = e x ⟨i.val + 1, h⟩) ∧ (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)), i.val + 1 = Nat.gcd f r → ∀ (i0 : Fin (Nat.gcd f r)), i0.val = 0 → e (sigKQ p K r x) i = τ (e x i0)) ∧ (∀ x : KQ p K r, x ∈ intKQ p K r ↔ ∀ i, e x i ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)) := by
  atlas_forward_decl GlobalTheory.LKRes.ResSplit.kq_split
end
