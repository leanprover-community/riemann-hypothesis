import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterInnerEqIntMulCard
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSSRepOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VirtualCharacterCosetNormOneSingleStatement

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  first | (exact @GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (exact GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (intros; apply GlobalTheory.Shin.CosetFourier.fourier_coset_sums  <;> assumption)
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem finsum_coset_pair_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ Y ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y (inl g)) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) ≠ 0 := by
  intro G Γ _ _ _ _ φ s hp hs X hX Y hY z hz hnd hcos
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, -, -, hfour⟩ := GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic G Γ φ s hgen _ hζ
  obtain ⟨h1, h2⟩ := hfour X Y
  have hvirt : ∀ a : ℕ, (fun x => Y x * (η x : ℂ) ^ a) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    intro a
    obtain ⟨hmul, -, -, -, hlin⟩ := GlobalTheory.BI.virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
    have := hmul Y hY _ (hlin (η ^ a))
    convert this using 1
    funext x; simp
  have hm : ∀ a : ℕ, ∃ m : ℤ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = m * (Nat.card (G ⋊[φ] Γ) : ℂ) :=
    fun a => GlobalTheory.BI.finsum_mul_star_virt_int _ X _ hX (hvirt a)
  choose m hm using hm
  have hN : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hl : (Nat.card Γ : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [hm, hN, hcos, hz, mul_zero] at h1 h2
  have hsum : ∑ i : Fin (Nat.card Γ), (m i.val : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ i.val = 0 := by
    have h3 : ∑ a ∈ Finset.range (Nat.card Γ), (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a * (↑(m a) * ↑(Nat.card G * Nat.card Γ))
        = (∑ a ∈ Finset.range (Nat.card Γ), (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a) * ((Nat.card G : ℂ) * Nat.card Γ) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_; push_cast; ring
    rw [h3] at h2
    rw [← Finset.sum_range (fun a => (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a)]
    have := h2.symm
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (mul_ne_zero hG hl)
  have hall := (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int hp hζ (fun i => m i.val)).1 hsum
  have hconst : ∀ a ∈ Finset.range (Nat.card Γ), m a = m 0 := by
    intro a ha
    exact hall ⟨a, Finset.mem_range.1 ha⟩ ⟨0, hp.pos⟩
  rw [Finset.sum_congr rfl (fun a ha => by rw [hconst a ha])] at h1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hz' : (z : ℂ) = (m 0 * Nat.card Γ : ℤ) := by
    push_cast at h1 ⊢
    have h4 : (Nat.card Γ : ℂ) * (Nat.card G : ℂ) * ((z : ℂ) - m 0 * Nat.card Γ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (mul_ne_zero hl hG)
    · exact sub_eq_zero.1 h
  exact hnd ⟨m 0, by rw [mul_comm]; exact_mod_cast hz'⟩

end GlobalTheory.Shin
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_semidirect_coset_pairing_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ Y ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y (inl g)) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) ≠ 0 := by
  first | (exact @GlobalTheory.Shin.finsum_coset_pair_ne_zero) | (exact GlobalTheory.Shin.finsum_coset_pair_ne_zero) | (intros; apply GlobalTheory.Shin.finsum_coset_pair_ne_zero <;> assumption)
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.CosetOrth

def twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) : Representation ℂ H V where
  toFun x := ((η x : ℂ) ^ a) • ρ x
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, Units.val_mul, mul_pow, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, mul_comm]

theorem trace_twist {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (η : H →* ℂˣ) (a : ℕ)
    (ρ : Representation ℂ H V) (x : H) :
    LinearMap.trace ℂ V (twist η a ρ x) = LinearMap.trace ℂ V (ρ x) * (η x : ℂ) ^ a := by
  show LinearMap.trace ℂ V (((η x : ℂ) ^ a) • ρ x) = _
  rw [map_smul, smul_eq_mul, mul_comm]

theorem sum_trace_mul_star_nat {H V W : Type} [Group H] [Fintype H] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H V) (σ : Representation ℂ H W) :
    ∃ k : ℕ, ∑ x, LinearMap.trace ℂ V (ρ x) * star (LinearMap.trace ℂ W (σ x)) = (Nat.card H : ℂ) * k := by
  have hne : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  haveI : Invertible (Nat.card H : ℂ) := invertibleOfNonzero hne
  have h := FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of σ) (FDRep.of ρ)
  refine ⟨Module.finrank ℂ (FDRep.of σ ⟶ FDRep.of ρ), ?_⟩
  rw [← h, mul_inv_cancel_left₀ hne]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [GlobalTheory.BadShare.ZCalc.character_inv]
  rfl

end GlobalTheory.Shin.CosetOrth

open GlobalTheory.Shin.CosetOrth in
theorem GlobalTheory.Shin.finsum_coset_mul_star_eq_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  intro G Γ _ _ _ _ φ s hp hs X Y hX hY h0
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have gen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hl0 : Nat.card Γ ≠ 0 := hp.ne_zero
  obtain ⟨η, -, -, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s gen _ (Complex.isPrimitiveRoot_exp _ hl0)
  obtain ⟨e1, e2⟩ := hF X Y
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  letI : Fintype (G ⋊[φ] Γ) := Fintype.ofFinite _
  have hm : ∀ a : ℕ, ∃ k : ℕ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = (Nat.card (G ⋊[φ] Γ) : ℂ) * k := by
    intro a
    obtain ⟨n, ρ, hρ⟩ := hX
    obtain ⟨m, σ, hσ⟩ := hY
    obtain ⟨k, hk⟩ := sum_trace_mul_star_nat ρ (twist η a σ)
    refine ⟨k, ?_⟩
    rw [finsum_eq_sum_of_fintype, ← hk]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [trace_twist, hρ x, hσ x]
    rfl
  choose k hk using hm
  have hH : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hsum : ∑ a ∈ Finset.range (Nat.card Γ), k a = 0 := by
    rw [h0, mul_zero] at e1
    simp_rw [hk] at e1
    rw [← Finset.mul_sum] at e1
    have := (mul_eq_zero.mp e1.symm).resolve_left hH
    exact_mod_cast this
  have hk0 : ∀ a ∈ Finset.range (Nat.card Γ), k a = 0 := Finset.sum_eq_zero_iff.mp hsum
  have hR : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hk a, hk0 a ha]; simp
  rw [hR] at e2
  exact (mul_eq_zero.mp e2).resolve_left (by exact_mod_cast hl0)
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_semidirect_coset_character_orth_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  first | (exact @GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (exact GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (intros; apply GlobalTheory.Shin.finsum_coset_mul_star_eq_zero <;> assumption)
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem prod_X_sub_C_dvd_pow_of_isRoot (g : ℂ[X]) :
    ∀ s : Multiset ℂ, (∀ a ∈ s, g.IsRoot a) →
      (s.map fun a => X - C a).prod ∣ g ^ Multiset.card s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact mul_dvd_mul (dvd_iff_isRoot.mpr (h a (Multiset.mem_cons_self a s)))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

theorem dvd_pow_natDegree_of_forall_isRoot (f g : ℂ[X]) (hf : f.Monic)
    (h : ∀ a ∈ f.roots, g.IsRoot a) : f ∣ g ^ f.natDegree := by
  have hc : Multiset.card f.roots = f.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have key := prod_X_sub_C_dvd_pow_of_isRoot g f.roots h
  rw [hc] at key
  have hf' := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  rw [hf.leadingCoeff, C_1, one_mul] at hf'
  rwa [hf'] at key

theorem exists_poly_pow_mul_eq_one : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B →
    ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := by
  intro n l B hl hB
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  set f := B.charpoly with hf
  have hfm : f.Monic := Matrix.charpoly_monic B
  have hB0 : aeval B f = 0 := Matrix.aeval_self_charpoly B
  have hdet : B.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det B).mp hB).ne_zero
  have hroot0 : ∀ a ∈ f.roots, a ≠ 0 := by
    intro a ha h0
    subst h0
    have h1 : f.eval 0 = 0 := (mem_roots hfm.ne_zero).mp ha
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, coeff_zero_eq_eval_zero, ← hf, h1, mul_zero]
  have hc : ∀ a : ℂ, ∃ c : ℂ, a ≠ 0 → c ^ (k + 1) * a = 1 := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun h => (h ha).elim⟩
    · obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (Nat.succ_pos k)
      exact ⟨c, fun _ => by rw [hc, inv_mul_cancel₀ ha]⟩
  choose c hc using hc
  let q : ℂ[X] := Lagrange.interpolate f.roots.toFinset id c
  have hq : ∀ a ∈ f.roots, q.eval a = c a := by
    intro a ha
    exact Lagrange.eval_interpolate_at_node (s := f.roots.toFinset) (v := id) c
      (Set.injOn_id _) (Multiset.mem_toFinset.mpr ha)
  let g : ℂ[X] := X * q ^ (k + 1) - 1
  have hg : ∀ a ∈ f.roots, g.IsRoot a := by
    intro a ha
    have := hc a (hroot0 a ha)
    simp only [g, IsRoot, eval_sub, eval_mul, eval_X, eval_pow, eval_one, hq a ha]
    rw [mul_comm, this, sub_self]
  have hdvd : f ∣ g ^ f.natDegree := dvd_pow_natDegree_of_forall_isRoot f g hfm hg
  let r : AdjoinRoot f := AdjoinRoot.root f
  let x : AdjoinRoot f := AdjoinRoot.mk f q
  let P : (AdjoinRoot f)[X] := C r * X ^ (k + 1) - 1
  have hPx : ∀ z, aeval z P = r * z ^ (k + 1) - 1 := by intro z; simp [P]
  have hmk : r * x ^ (k + 1) - 1 = AdjoinRoot.mk f g := by
    simp [r, x, g, map_sub, map_mul, map_pow, AdjoinRoot.mk_X]
  have hnil : IsNilpotent (aeval x P) := by
    refine ⟨f.natDegree, ?_⟩
    rw [hPx, hmk, ← map_pow, AdjoinRoot.mk_eq_zero]
    exact hdvd
  have hunit : IsUnit (r * x ^ (k + 1)) := by
    have := hnil.isUnit_add_one
    rwa [hPx, sub_add_cancel] at this
  have hunit' : IsUnit (r * x ^ k) := by
    rw [pow_succ, ← mul_assoc] at hunit
    exact isUnit_of_mul_isUnit_left hunit
  have hl : IsUnit ((k + 1 : ℕ) : AdjoinRoot f) := by
    have : IsUnit ((k + 1 : ℕ) : ℂ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
    simpa using this.map (algebraMap ℂ (AdjoinRoot f))
  have hder : IsUnit (aeval x (derivative P)) := by
    have h1 : aeval x (derivative P) = ((k + 1 : ℕ) : AdjoinRoot f) * (r * x ^ k) := by
      simp [P]
      ring
    rw [h1]
    exact hl.mul hunit'
  obtain ⟨y, ⟨_, hy⟩, _⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero hnil hder
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨p, ?_⟩
  have e : (AdjoinRoot.mk f p) ^ (k + 1) * r = 1 := by
    rw [mul_comm]
    rw [hPx] at hy
    exact sub_eq_zero.mp hy
  have e2 : AdjoinRoot.mk f (p ^ (k + 1) * X - 1) = 0 := by
    rw [map_sub, map_mul, map_pow, AdjoinRoot.mk_X, map_one]
    exact sub_eq_zero.mpr e
  obtain ⟨b, hb⟩ := AdjoinRoot.mk_eq_zero.mp e2
  have h2 := congrArg (aeval B) hb
  rw [map_mul, hB0, zero_mul, map_sub, map_mul, map_pow, aeval_X, map_one] at h2
  exact sub_eq_zero.mp h2

end GlobalTheory
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_pow_mul_eq_one' : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B → ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := by
  first | (exact @GlobalTheory.exists_poly_pow_mul_eq_one) | (exact GlobalTheory.exists_poly_pow_mul_eq_one) | (intros; apply GlobalTheory.exists_poly_pow_mul_eq_one  <;> assumption)
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.StableExt

theorem isSSRep_of_finite {G : Type} [Group G] [Finite G] {d : ℕ} (ρ : G →* GL (Fin d) ℂ) :
    Formalism.MainNotions.N.IsSSRep ρ := by
  haveI : (⊥ : Subgroup G).FiniteIndex := inferInstance
  apply GlobalTheory.FiniteIndexSemisimple.isSSRep_of_finiteIndex ρ (⊥ : Subgroup G)
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  refine ⟨W', fun g v hv => ?_, hW'⟩
  have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.2
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hg, map_one, Units.val_one, Matrix.one_mulVec]
  exact hv

theorem commute_aeval {n : ℕ} {M B : Matrix (Fin n) (Fin n) ℂ} (h : Commute M B) (p : ℂ[X]) :
    Commute M (aeval B p) := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun i _ => (h.pow_right i).smul_right _

theorem exists_ext : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) →
    ∃ Z : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ Z ∧ ∀ g, Z (inl g) = Y g := by
  intro G Γ _ _ _ _ φ s hs Y hY hYs
  obtain ⟨d, ρ, hρ⟩ := (GlobalTheory.BI.matrixChar_iff_isChar G Y).mpr hY
  let ρ' : G →* GL (Fin d) ℂ := ρ.comp (φ s).toMonoidHom
  obtain ⟨A, hA⟩ := GlobalTheory.TraceConj.conj_of_trace_eq G ℂ d ρ ρ' (isSSRep_of_finite ρ)
    (isSSRep_of_finite ρ') (fun g => by
      show _ = Matrix.trace ((ρ (φ s g) : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
      rw [← hρ, ← hρ, hYs])
  have hA' : ∀ g, ρ (φ s g) = A * ρ g * A⁻¹ := fun g => hA g
  have hAk : ∀ k : ℕ, ∀ g, ρ (((φ s) ^ k) g) = A ^ k * ρ g * (A ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih => intro g; rw [pow_succ', MulAut.mul_apply, hA', ih]; group
  set l := orderOf s with hl_def
  have hl : 0 < l := orderOf_pos s
  have hφl : (φ s) ^ l = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hB : ∀ g, A ^ l * ρ g = ρ g * A ^ l := by
    intro g
    have := hAk l g
    rw [hφl, MulAut.one_apply] at this
    calc A ^ l * ρ g = (A ^ l * ρ g * (A ^ l)⁻¹) * A ^ l := by group
      _ = ρ g * A ^ l := by rw [← this]
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_poly_pow_mul_eq_one' d l ((A ^ l : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) hl (Units.isUnit _)
  set Bm : Matrix (Fin d) (Fin d) ℂ := ((A ^ l : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) with hBm
  set C : Matrix (Fin d) (Fin d) ℂ := aeval Bm p with hC
  have hCA : Commute ((A : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) C := by
    apply commute_aeval
    rw [hBm, Units.val_pow_eq_pow_val]
    exact (Commute.refl _).pow_right l
  have hCρ : ∀ g, Commute ((ρ g : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) C := by
    intro g
    apply commute_aeval
    have := congrArg (fun x : GL (Fin d) ℂ => (x : Matrix (Fin d) (Fin d) ℂ)) (hB g)
    simp only [Units.val_mul] at this
    exact this.symm
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl
  have h1 : C * (C ^ (l - 1) * Bm) = 1 := by
    rw [← mul_assoc, ← pow_succ', hl1]; exact hp
  let Cu : GL (Fin d) ℂ := ⟨C, C ^ (l - 1) * Bm, h1, mul_eq_one_comm.mp h1⟩
  have hCuA : A * Cu = Cu * A := Units.ext (hCA.eq)
  have hCuρ : ∀ g, Cu * ρ g = ρ g * Cu := fun g => Units.ext ((hCρ g).eq.symm)
  have hCuB : Cu ^ l * A ^ l = 1 := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]; exact hp)
  set A' : GL (Fin d) ℂ := A * Cu with hA'def
  have hA'l : A' ^ l = 1 := by
    rw [hA'def, (show Commute A Cu from hCuA).mul_pow, ((show Commute A Cu from hCuA).pow_pow l l).eq]
    exact hCuB
  have hA's : ∀ g, ρ (φ s g) = A' * ρ g * A'⁻¹ := by
    intro g
    rw [hA', hA'def, mul_inv_rev]
    calc A * ρ g * A⁻¹ = A * (ρ g * Cu) * Cu⁻¹ * A⁻¹ := by group
      _ = A * Cu * ρ g * (Cu⁻¹ * A⁻¹) := by rw [← hCuρ g]; group
  let σ : Γ →* GL (Fin d) ℂ := monoidHomOfForallMemZpowers hs (orderOf_dvd_of_pow_eq_one hA'l)
  have hσs : σ s = A' := monoidHomOfForallMemZpowers_apply_gen hs _
  let H : Subgroup Γ :=
    { carrier := {t | ∀ g, ρ (φ t g) = σ t * ρ g * (σ t)⁻¹}
      mul_mem' := by
        intro a b ha hb g
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, MulAut.mul_apply, ha, hb, map_mul]; group
      one_mem' := by intro g; simp
      inv_mem' := by
        intro a ha g
        simp only [Set.mem_setOf_eq] at *
        have := ha ((φ a⁻¹) g)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
        rw [map_inv σ]
        calc ρ (φ a⁻¹ g) = (σ a)⁻¹ * (σ a * ρ (φ a⁻¹ g) * (σ a)⁻¹) * σ a := by group
          _ = (σ a)⁻¹ * ρ g * ((σ a)⁻¹)⁻¹ := by rw [← this]; group }
  have hsH : s ∈ H := fun g => by rw [hσs]; exact hA's g
  have hall : ∀ t, ∀ g, ρ (φ t g) = σ t * ρ g * (σ t)⁻¹ := fun t => (Subgroup.zpowers_le.mpr hsH) (hs t)
  let Λ : G ⋊[φ] Γ →* GL (Fin d) ℂ := SemidirectProduct.lift ρ σ (fun t => by
    ext g : 1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hall t g)
  refine ⟨fun x => Matrix.trace ((Λ x : GL (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ), ?_, ?_⟩
  · exact (GlobalTheory.BI.matrixChar_iff_isChar _ _).mp ⟨d, Λ, fun x => rfl⟩
  · intro g
    simp only [Λ, SemidirectProduct.lift_inl]
    exact (hρ g).symm

end GlobalTheory.StableExt
end
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semidirect_character_ext_of_stable : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∃ Z : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ Z ∧ ∀ g, Z (inl g) = Y g := by
  first | (exact @GlobalTheory.StableExt.exists_ext) | (exact GlobalTheory.StableExt.exists_ext) | (intros; apply GlobalTheory.StableExt.exists_ext <;> assumption)
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem trace_fin_eq_sum_diag (m : ℕ) (A : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    LinearMap.trace ℂ (Fin m → ℂ) A = ∑ i, A (Pi.single i 1) i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin m)), LinearMap.toMatrix_eq_toMatrix',
    Matrix.trace]
  simp [LinearMap.toMatrix'_apply]

variable {G : Type} [Group G] [Fintype G]

theorem sum_char_inv_mul_char_eq_zero_iff {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G V) (ρ : Representation ℂ G W) :
    ∑ g, σ.character g⁻¹ * ρ.character g = 0 ↔ (Representation.linHom σ ρ).invariants = ⊥ := by
  have hpos : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hpos
  have hfr := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom σ ρ)
  simp only [Representation.char_linHom] at hfr
  constructor
  · intro h
    rw [h, mul_zero] at hfr
    apply Submodule.finrank_eq_zero.mp
    exact_mod_cast hfr.symm
  · intro hb
    rw [hb, finrank_bot, Nat.cast_zero] at hfr
    exact (mul_eq_zero.mp hfr).resolve_left (inv_ne_zero hpos)

theorem comm_of_mem_invariants {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G V) (ρ : Representation ℂ G W) {p : V →ₗ[ℂ] W}
    (hp : p ∈ (Representation.linHom σ ρ).invariants) (g : G) (x : V) : p (σ g x) = ρ g (p x) := by
  have h := congrArg (fun F : V →ₗ[ℂ] W => F (σ g x)) (hp g)
  simp only [Representation.linHom_apply, LinearMap.comp_apply] at h
  rw [← h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem invariants_bot_of_quot {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G U) (ρ' : Representation ℂ G V)
    (ρ : Representation ℂ G W) (hirr : ρ'.IsIrreducible) {p : U →ₗ[ℂ] V}
    (hp : p ∈ (Representation.linHom σ ρ').invariants) (hp0 : p ≠ 0)
    (hb : (Representation.linHom σ ρ).invariants = ⊥) :
    (Representation.linHom ρ' ρ).invariants = ⊥ := by

  let S : Subrepresentation ρ' :=
    { toSubmodule := LinearMap.range p
      apply_mem_toSubmodule := by
        rintro g _ ⟨x, rfl⟩
        exact ⟨σ g x, comm_of_mem_invariants σ ρ' hp g x⟩ }
  have hrange : ∀ y : V, y ∈ LinearMap.range p := by
    rcases hirr.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hp0
      ext x
      have hx : p x ∈ S.toSubmodule := ⟨x, rfl⟩
      have hb0 : (⊥ : Subrepresentation ρ').toSubmodule = ⊥ := rfl
      rw [h, hb0] at hx
      exact (Submodule.mem_bot ℂ).mp hx
    · intro y
      have ht : (⊤ : Subrepresentation ρ').toSubmodule = ⊤ := rfl
      have : y ∈ (⊤ : Subrepresentation ρ').toSubmodule := by rw [ht]; exact Submodule.mem_top
      rw [← h] at this
      exact this
  rw [eq_bot_iff]
  intro q hq
  rw [Submodule.mem_bot]
  have hqp : q ∘ₗ p ∈ (Representation.linHom σ ρ).invariants := by
    intro g
    ext x
    simp only [Representation.linHom_apply, LinearMap.comp_apply]
    rw [← comm_of_mem_invariants ρ' ρ hq, ← comm_of_mem_invariants σ ρ' hp, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hb, Submodule.mem_bot] at hqp
  ext y
  obtain ⟨x, rfl⟩ := hrange y
  exact LinearMap.congr_fun hqp x

theorem sum_trace_smul_eq_zero {m : ℕ} (ρ₀ : Representation ℂ G (Fin m → ℂ)) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (hbot : (Representation.linHom ρ₀ ρ).invariants = ⊥)
    (B : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    ∑ g : G, LinearMap.trace ℂ (Fin m → ℂ) (B ∘ₗ ρ₀ g⁻¹) • ρ g = 0 := by
  have hsum : ∀ f : (Fin m → ℂ) →ₗ[ℂ] V, ∑ g : G, Representation.linHom ρ₀ ρ g f = 0 := by
    intro f
    have hm : ∑ g : G, Representation.linHom ρ₀ ρ g f ∈ (Representation.linHom ρ₀ ρ).invariants := by
      intro h
      rw [map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)
    rw [hbot] at hm
    exact (Submodule.mem_bot ℂ).mp hm
  ext v
  have key : ∀ i : Fin m, ∑ g : G, (B (ρ₀ g⁻¹ (Pi.single i 1))) i • ρ g v = 0 := by
    intro i
    have := congrArg (fun F : (Fin m → ℂ) →ₗ[ℂ] V => F (Pi.single i 1))
      (hsum (((LinearMap.proj i : (Fin m → ℂ) →ₗ[ℂ] ℂ) ∘ₗ B).smulRight v))
    simpa [Representation.linHom_apply, LinearMap.sum_apply] using this
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply]
  simp only [trace_fin_eq_sum_diag, Finset.sum_smul, LinearMap.comp_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun i _ => key i)

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem kills_twist_of_pair_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ]
    (φ : Γ →* MulAut G) (s : Γ), ∀ (χ : G ⋊[φ] Γ → ℂ) (Y : G → ℂ), IsChar ℂ ℂ χ →
    IsIrrChar ℂ ℂ (fun g => χ (inl g)) → IsChar ℂ ℂ Y → ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 →
    Kills (fun δ => χ (inl δ * inr s)) Y := by
  intro G Γ _ _ _ _ φ s χ Y hχ hirr hY hne V _ _ _ ρ h
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (G ⋊[φ] Γ) :=
    Finite.of_injective (fun x : G ⋊[φ] Γ => (x.left, x.right))
      (fun x y hxy => SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  obtain ⟨m, ρh, hρh⟩ := hχ
  obtain ⟨k, ρ', hρ'irr, hρ'⟩ := hirr
  obtain ⟨n, σ, hσ⟩ := hY
  have hχc : ∀ x, χ x = ρh.character x := fun x => by simpa using hρh x
  have hYc : ∀ g, Y g = σ.character g := fun g => by simpa using hσ g
  have h0c : ∀ g, χ (inl g) = ρ'.character g := fun g => by simpa using hρ' g
  have hst : ∀ g, star (Y g) = σ.character g⁻¹ := fun g => by
    rw [star_virt_eq_inv G Y (AddSubgroup.subset_closure ⟨n, σ, hσ⟩) g, hYc]
  rw [finsum_eq_sum_of_fintype] at h hne

  have hb : (Representation.linHom σ ρ).invariants = ⊥ := by
    rw [← sum_char_inv_mul_char_eq_zero_iff]
    simp only [hst] at h
    exact h

  have hne' : (Representation.linHom σ ρ').invariants ≠ ⊥ := by
    rw [Ne, ← sum_char_inv_mul_char_eq_zero_iff]
    intro h'
    apply hne
    rw [← h']
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hst, h0c, mul_comm]
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  have hb' := invariants_bot_of_quot σ ρ' ρ hρ'irr hp hp0 hb

  let ρ₀ : Representation ℂ G (Fin m → ℂ) := ρh.comp (inl : G →* G ⋊[φ] Γ)
  have hρ₀ : ∀ g, ρ₀.character g = ρ'.character g := fun g => by
    rw [← h0c, hχc]; rfl
  have hb₀ : (Representation.linHom ρ₀ ρ).invariants = ⊥ := by
    rw [← sum_char_inv_mul_char_eq_zero_iff]
    have := (sum_char_inv_mul_char_eq_zero_iff ρ' ρ).mpr hb'
    simpa only [hρ₀] using this
  have hstf : ∀ g, star (χ (inl g * inr s)) =
      LinearMap.trace ℂ (Fin m → ℂ) (ρh (inr s⁻¹) ∘ₗ ρ₀ g⁻¹) := fun g => by
    rw [star_virt_eq_inv (G ⋊[φ] Γ) χ (AddSubgroup.subset_closure ⟨m, ρh, hρh⟩), hχc, mul_inv_rev,
      ← map_inv, ← map_inv]
    simp only [Representation.character, map_mul]
    rfl
  rw [finsum_eq_sum_of_fintype]
  simp only [hstf]
  exact sum_trace_smul_eq_zero ρ₀ ρ hb₀ _

end GlobalTheory.Shin
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_restricted_character_in_isotypic_part : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), ∀ (χ : G ⋊[φ] Γ → ℂ) (Y : G → ℂ), IsChar ℂ ℂ χ → IsIrrChar ℂ ℂ (fun g => χ (inl g)) → IsChar ℂ ℂ Y → ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 → Kills (fun δ => χ (inl δ * inr s)) Y := by
  first | (exact @GlobalTheory.Shin.kills_twist_of_pair_ne_zero) | (exact GlobalTheory.Shin.kills_twist_of_pair_ne_zero) | (intros; apply GlobalTheory.Shin.kills_twist_of_pair_ne_zero  <;> assumption)
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem kills_const_mul {G : Type} [Group G] [Finite G] (c : ℂ) (f Y : G → ℂ) (h : Kills f Y) :
    Kills (fun g => c * f g) Y := by
  intro V _ _ _ ρ hY
  have hk := h V ρ hY
  have : Fintype G := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype] at hk ⊢
  have e : (fun g => star (c * f g) • ρ g) = fun g => star c • (star (f g) • ρ g) := by
    funext g; rw [star_mul', mul_smul]
  simp only []
  rw [e, ← Finset.smul_sum, hk, smul_zero]

theorem kills_of_norm_one_of_pairing_prime :
    ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime →
      s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) →
      ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∀ z : ℤ,
      ∑ᶠ g, X (inl g) * star (Y g) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) →
      Kills (fun δ => X (inl δ * inr s)) Y := by
  intro G Γ _ _ _ _ φ s hp hs X hX hn Y hY hYs z hz hl
  obtain ⟨χ, e, hχ, hχG, hXe⟩ := GlobalTheory.T.virtualCharacter_coset_normOne_single G Γ φ s hp hs X hX hn
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
    intro t
    rw [zpowers_eq_top_of_prime_card rfl hs]
    exact Subgroup.mem_top t
  obtain ⟨Z, hZ, hZY⟩ := GlobalTheory.T.exists_semidirect_character_ext_of_stable G Γ φ s hgen Y hY hYs
  have hZv : Z ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hZ
  have hXZ : ∑ᶠ g, X (inl g) * star (Z (inl g)) = z * (Nat.card G : ℂ) := by
    simp only [hZY]; exact hz
  have hc := GlobalTheory.T.finsum_semidirect_coset_pairing_ne_zero G Γ φ s hp hs X hX Z hZv z hXZ hl
  have hχc : ∑ᶠ g, χ (inl g * inr s) * star (Z (inl g * inr s)) ≠ 0 := by
    intro h0
    apply hc
    have : (fun g => X (inl g * inr s) * star (Z (inl g * inr s)))
        = fun g => e * (χ (inl g * inr s) * star (Z (inl g * inr s))) := by
      funext g; rw [hXe, mul_assoc]
    rw [this, ← mul_finsum, h0, mul_zero]
  have hχchar : IsChar ℂ ℂ χ := by
    obtain ⟨n, ρ, -, h⟩ := hχ; exact ⟨n, ρ, h⟩
  have hχY : ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 := by
    intro h0
    apply hχc
    apply GlobalTheory.T.finsum_semidirect_coset_character_orth_zero G Γ φ s hp hs χ Z hχchar hZ
    simp only [hZY]; exact h0
  have hK := GlobalTheory.T.twisted_restricted_character_in_isotypic_part G Γ φ s χ Y hχchar hχG hY hχY
  have := kills_const_mul e _ Y hK
  simpa only [hXe] using this

end GlobalTheory.Shin
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_virtualCharacter_norm_one_support : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y g) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → Kills (fun δ => X (inl δ * inr s)) Y := by
  first | (exact @GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (exact GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (intros; apply GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime  <;> assumption)
end
