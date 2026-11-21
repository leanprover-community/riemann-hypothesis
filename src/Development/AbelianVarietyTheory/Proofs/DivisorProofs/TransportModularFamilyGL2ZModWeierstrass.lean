import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModularFormLevelOneOfInvariantQExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularFormPolynomialE4E6
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VactVmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembershipStatement
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem exists_eisensteinCombination_of_isModularForm {w : ℕ} {F : ℍ → ℂ}
    (hF : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (w : ℤ) F) :
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      ∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  obtain ⟨f, hf⟩ := hF
  have hmem := _root_.ReciprocityTheory.PGsh.coe_mem_monoSpanF w f
  unfold _root_.ReciprocityTheory.PGsh.monoSpanF at hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  classical
  refine ⟨(_root_.ReciprocityTheory.PGsh.monoIdx w).image fun a => (a, _root_.ReciprocityTheory.PGsh.monoB w a),
    fun p => if hp : p.1 ∈ _root_.ReciprocityTheory.PGsh.monoIdx w then c ⟨p.1, hp⟩ else 0, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hp
    exact _root_.ReciprocityTheory.PGsh.monoIdx_wt ha
  · intro τ
    rw [Finset.sum_image (fun x _ y _ h => congrArg Prod.fst h), ← hf τ, ← hc]
    rw [Finset.sum_apply, ← Finset.sum_attach (_root_.ReciprocityTheory.PGsh.monoIdx w)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, a.2, dif_pos]
    rw [_root_.ReciprocityTheory.PGsh.coe_monoW a.2]
    rfl

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in
private theorem qConj_eisensteinCombination (g : ℂ ≃+* ℂ) {N : ℕ}
    (hN : 0 < N) {ι : Type} (s : Finset ι) (c : ι → ℂ) (u v : ι → ℕ) :
    _root_.GlobalTheory.QFam.QConj g N (fun τ => ∑ i ∈ s, c i * (E₄ τ ^ u i * E₆ τ ^ v i))
      (fun τ => ∑ i ∈ s, g (c i) * (E₄ τ ^ u i * E₆ τ ^ v i)) := by
  refine _root_.GlobalTheory.QFam.QConj.sum s fun i _ => ?_
  have h₄ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inl rfl) g
  have h₆ := _root_.GlobalTheory.QFam.eis_qConj N hN _ (Or.inr (Or.inl rfl)) g
  exact (_root_.GlobalTheory.QFam.QConj.const g N (c i)).mul hN
    ((h₄.pow hN (u i)).mul hN (h₆.pow hN (v i)))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in

theorem _root_.GlobalTheory.QFam.levelPoly_conj : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ),
    0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → _root_.GlobalTheory.QFam.QConj g N F F' →
    ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧
      (∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ∧
      ∀ τ, F' τ = ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  intro g w N F F' hN hinv hconj
  obtain ⟨a, ha, ha'⟩ := hconj
  obtain ⟨s, c, hw, hF⟩ := exists_eisensteinCombination_of_isModularForm
    (_root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N w F a hN hinv ha)
  refine ⟨s, c, hw, hF, ?_⟩
  obtain ⟨b, hb, hb'⟩ :=
    qConj_eisensteinCombination g hN s c Prod.fst Prod.snd
  have hFeq : F = fun τ => ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := funext hF
  rw [← hFeq] at hb
  have hab : a = b := ha.coeff_unique hN hb
  subst hab
  intro τ
  exact congrFun (ha'.fun_unique hb') τ

end GlobalTheory.QFam
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_eisensteinPolynomial_levelOne : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧ (∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ∧ ∀ τ, F' τ = ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  atlas_forward_decl GlobalTheory.QFam.levelPoly_conj
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isobaric_monomial_div (c x y ω : ℂ) (a b w : ℕ) (h : 4 * a + 6 * b = w) :
    c * (x ^ a * y ^ b) / ω ^ w = c * ((x / ω ^ 4) ^ a * (y / ω ^ 6) ^ b) := by
  rw [div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm, ← pow_add, h, mul_div_assoc]

theorem levelOne_value_transport : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → g (F τ₀ / ω₀ ^ w) = F' τ₁ / ω₁ ^ w := by
  intro g w N F F' τ₀ τ₁ ω₀ ω₁ hN hF hq h4 h6
  obtain ⟨s, c, hs, h0, h1⟩ := GlobalTheory.T.exists_conj_eisensteinPolynomial_levelOne g w N F F' hN hF hq
  rw [h0, h1, Finset.sum_div, Finset.sum_div, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp), isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp),
    map_mul, map_mul, map_pow, map_pow, h4, h6]

end GlobalTheory.QFam
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelOne_modularForm_value_galois_transport : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → g (F τ₀ / ω₀ ^ w) = F' τ₁ / ω₁ ^ w := by
  atlas_forward_decl GlobalTheory.QFam.levelOne_value_transport
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem sum_prod_pow_div_pow {ι S : Type} [Fintype ι] [Fintype S] (m μ : S → ℕ) (x : S → ι → ℂ)
    (ω : ℂ) :
    (∑ i, ∏ s, x s i ^ μ s) / ω ^ (∑ s, μ s * m s) = ∑ i, ∏ s, (x s i / ω ^ m s) ^ μ s := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  simp only [mul_comm]

theorem transport_power_sums : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ μ : S → ℕ, ∑ i, ∏ s, g (f s i τ₀ / ω₀ ^ m s) ^ μ s = ∑ i, ∏ s, (f' s i τ₁ / ω₁ ^ m s) ^ μ s := by
  intro g ι S _ _ act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hfam hq h4 h6 μ
  obtain ⟨-, -, -, -, hpow, -, hprod, -⟩ := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act
  obtain ⟨-, -, -, -, qpow, qfin⟩ := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure g N hN
  have hM : IsFam act (((∑ s, μ s * m s : ℕ) : ℤ)) fun i τ => ∏ s, f s i τ ^ μ s := by
    have := hprod S Finset.univ (fun s => (μ s : ℤ) * (m s : ℤ)) (fun s i τ => f s i τ ^ μ s)
      (fun s _ => hpow (m s) (f s) (μ s) (hfam s))
    push_cast
    exact this
  have hQ : QConj g N (fun τ => ∑ i, ∏ s, f s i τ ^ μ s) fun τ => ∑ i, ∏ s, f' s i τ ^ μ s :=
    (qfin ι Finset.univ (fun i τ => ∏ s, f s i τ ^ μ s) (fun i τ => ∏ s, f' s i τ ^ μ s)
      fun i _ => (qfin S Finset.univ (fun s τ => f s i τ ^ μ s) (fun s τ => f' s i τ ^ μ s)
        fun s _ => qpow _ _ (μ s) (hq s i)).2).1
  have key := GlobalTheory.T.levelOne_modularForm_value_galois_transport g (∑ s, μ s * m s) N _ _ τ₀ τ₁ ω₀ ω₁ hN
    (fun γ => (GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant ι act _ _ hact hM γ).1) hQ h4 h6
  rw [sum_prod_pow_div_pow m μ (fun s i => f s i τ₀), sum_prod_pow_div_pow m μ (fun s i => f' s i τ₁)] at key
  simpa only [map_sum, map_prod, map_pow] using key

end GlobalTheory.QFam
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_power_sums_modular_families : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ μ : S → ℕ, ∑ i, ∏ s, g (f s i τ₀ / ω₀ ^ m s) ^ μ s = ∑ i, ∏ s, (f' s i τ₁ / ω₁ ^ m s) ^ μ s := by
  atlas_forward_decl GlobalTheory.QFam.transport_power_sums
end

section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem exists_mvPolynomial_pick_point :
    ∀ (S : Type) (T : Finset (S → ℂ)) (p : S → ℂ), ∃ Q : MvPolynomial S ℂ,
      MvPolynomial.eval p Q = 1 ∧ ∀ t ∈ T, t ≠ p → MvPolynomial.eval t Q = 0 := by
  classical
  intro S T p
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a T _ ih =>
    obtain ⟨Q, hQ1, hQ0⟩ := ih
    by_cases hap : a = p
    · refine ⟨Q, hQ1, fun t ht htp => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact absurd hap htp
      · exact hQ0 t ht htp
    · obtain ⟨s, hs⟩ := Function.ne_iff.1 hap
      have hne : p s - a s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
      refine ⟨Q * (MvPolynomial.C (p s - a s)⁻¹ * (MvPolynomial.X s - MvPolynomial.C (a s))),
        ?_, fun t ht htp => ?_⟩
      · simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, hQ1, one_mul]
        exact inv_mul_cancel₀ hne
      · rcases Finset.mem_insert.1 ht with rfl | ht
        · simp
        · simp [hQ0 t ht htp]

end GlobalTheory.QFam
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem sum_eval_eq_of_sum_monomial_eq {ι S : Type} [Fintype ι] [Fintype S] (x y : ι → S → ℂ)
    (h : ∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) (Q : MvPolynomial S ℂ) :
    ∑ i, MvPolynomial.eval (x i) Q = ∑ i, MvPolynomial.eval (y i) Q := by
  simp only [MvPolynomial.eval_eq']
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, h d]

theorem exists_perm_of_sum_monomial_eq :
    ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ),
      (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) →
      ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  classical
  intro ι S _ _ x y h
  have hcard : ∀ p : S → ℂ, Fintype.card {i // x i = p} = Fintype.card {i // y i = p} := by
    intro p
    obtain ⟨Q, hQ1, hQ0⟩ := exists_mvPolynomial_pick_point S
      (Finset.univ.image x ∪ Finset.univ.image y) p
    have key : ∀ z : ι → S → ℂ, (∀ i, z i ∈ Finset.univ.image x ∪ Finset.univ.image y) →
        ∑ i, MvPolynomial.eval (z i) Q = (Fintype.card {i // z i = p} : ℂ) := by
      intro z hz
      have : ∀ i, MvPolynomial.eval (z i) Q = if z i = p then 1 else 0 := by
        intro i
        split_ifs with hi
        · rw [hi, hQ1]
        · exact hQ0 _ (hz i) hi
      simp only [this]
      rw [Finset.sum_boole, Fintype.card_subtype]
    have h1 := key x (fun i => by simp)
    have h2 := key y (fun i => by simp)
    have h3 := sum_eval_eq_of_sum_monomial_eq x y h Q
    rw [h1, h2] at h3
    exact_mod_cast h3
  refine ⟨Equiv.ofFiberEquiv (f := x) (g := y) (fun p => Fintype.equivOfCardEq (hcard p)),
    fun i => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ i).symm

end GlobalTheory.QFam
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_of_sum_monomial_eq' : ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ), (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) → ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  atlas_forward_decl GlobalTheory.QFam.exists_perm_of_sum_monomial_eq
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem exists_perm_transport_families (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S]
    (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ)
    (ω₀ ω₁ : ℂ) (hN : 0 < N) (hact : ActBij act) (hf : ∀ s, IsFam act (m s) (f s))
    (hc : ∀ s i, QConj g N (f s i) (f' s i))
    (h4 : g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4) (h6 : g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6) :
    ∃ ρ : Equiv.Perm ι, ∀ s i, g (f s i τ₀ / ω₀ ^ m s) = f' s (ρ i) τ₁ / ω₁ ^ m s := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_perm_of_sum_monomial_eq' ι S (fun i s => g (f s i τ₀ / ω₀ ^ m s))
    (fun i s => f' s i τ₁ / ω₁ ^ m s)
    (GlobalTheory.T.transport_power_sums_modular_families g ι S act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hf hc h4 h6)
  exact ⟨ρ, fun s i => congrFun (hρ i) s⟩

end GlobalTheory.QFam
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_transport_modular_families_values : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∃ ρ : Equiv.Perm ι, ∀ s i, g (f s i τ₀ / ω₀ ^ m s) = f' s (ρ i) τ₁ / ω₁ ^ m s := by
  atlas_forward_decl GlobalTheory.QFam.exists_perm_transport_families
end

section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem transport_of_separating : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N w : ℕ) (m : S → ℕ) (f f' : ι → ℍ → ℂ) (u u' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ s, IsFam act (m s) (u s)) → (∀ i, QConj g N (f i) (f' i)) → (∀ s i, QConj g N (u s i) (u' s i)) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ i i' : ι, (∀ j, (∀ s, u s j τ₀ = u s i τ₀) → f j τ₀ = f i τ₀) → (∀ s, g (u s i τ₀ / ω₀ ^ m s) = u' s i' τ₁ / ω₁ ^ m s) → g (f i τ₀ / ω₀ ^ w) = f' i' τ₁ / ω₁ ^ w := by
  intro g ι S _ _ act N w m f f' u u' τ₀ τ₁ ω₀ ω₁ hN hact hf hu hq hqu hω h4 h6 i i' hsep hi
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_perm_transport_modular_families_values g ι (Option S) act N (fun o => o.elim w m)
    (fun o => o.elim f u) (fun o => o.elim f' u') τ₀ τ₁ ω₀ ω₁ hN hact
    (by rintro (_ | s); exacts [hf, hu s])
    (by rintro (_ | s) k; exacts [hq k, hqu s k]) h4 h6
  have hj : f (ρ.symm i') τ₀ = f i τ₀ := by
    apply hsep
    intro s
    have h1 : g (u s (ρ.symm i') τ₀ / ω₀ ^ m s) = u' s (ρ (ρ.symm i')) τ₁ / ω₁ ^ m s :=
      hρ (some s) (ρ.symm i')
    rw [Equiv.apply_symm_apply, ← hi s] at h1
    have h2 := g.injective h1
    exact (div_left_inj' (pow_ne_zero _ hω)).1 h2
  have h3 : g (f (ρ.symm i') τ₀ / ω₀ ^ w) = f' (ρ (ρ.symm i')) τ₁ / ω₁ ^ w :=
    hρ none (ρ.symm i')
  rwa [Equiv.apply_symm_apply, hj] at h3

end GlobalTheory.QFam
end

section
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem wp_wpd_separate : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  intro N _ τ x y hx hy h1 h2
  obtain ⟨hsub, -, hmem, -, -⟩ := GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership N τ
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hz : tors N τ x ∉ (tauPair τ).lattice := fun h => hx ((hmem x).1 h)
  have hw : tors N τ y ∉ (tauPair τ).lattice := fun h => hy ((hmem y).1 h)
  rw [wp, wp, div_left_inj' (pow_ne_zero _ hc)] at h1
  rw [wpd, wpd, div_left_inj' (pow_ne_zero _ hc)] at h2
  rcases (Formalism.L2.Th1.F.pInjective (tauPair τ) _ _ hz hw).1 h1 with h | h
  · exact (hsub x y).1 h
  · apply (hsub x y).1
    have e : tors N τ x = -tors N τ y + ((⟨_, h⟩ : (tauPair τ).lattice) : ℂ) := by
      simp
    have h3 : (tauPair τ).derivWeierstrassP (tors N τ x) =
        -(tauPair τ).derivWeierstrassP (tors N τ y) := by
      conv_lhs => rw [e]
      rw [PeriodPair.derivWeierstrassP_add_coe, PeriodPair.derivWeierstrassP_neg]
    have h0 : (tauPair τ).derivWeierstrassP (tors N τ y) = 0 := by
      rw [h2] at h3
      linear_combination h3 / 2
    have h4 := (Formalism.L2.Th1.F.pDerivZero (tauPair τ) _ hw).1 h0
    have h5 := (tauPair τ).lattice.sub_mem h h4
    convert h5 using 1
    ring

end GlobalTheory.WpFam
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 → wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  atlas_forward_decl GlobalTheory.WpFam.wp_wpd_separate
end

section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.SepGL

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (hx : x ≠ 0) (α : GL (Fin 2) (ZMod N)) :
    vmul x α ≠ 0 := by
  intro h
  apply hx
  have h2 : (x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  unfold vmul at h
  rw [← h2, h, Matrix.zero_vecMul]

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (α β : GL (Fin 2) (ZMod N)), (∀ i : Fin 2, wp N (vmul (Pi.single i 1) α) τ = wp N (vmul (Pi.single i 1) β) τ ∧ wpd N (vmul (Pi.single i 1) α) τ = wpd N (vmul (Pi.single i 1) β) τ) → α = β := by
  intro N _ τ α β h
  rcases subsingleton_or_nontrivial (ZMod N) with hs | hs
  · exact Matrix.GeneralLinearGroup.ext fun i j => Subsingleton.elim _ _
  · have key : ∀ i : Fin 2, vmul (Pi.single i 1) α = vmul (Pi.single i 1) β := by
      intro i
      have h0 : (Pi.single i (1 : ZMod N) : Fin 2 → ZMod N) ≠ 0 := by
        intro h1
        have := congrFun h1 i
        simp at this
      exact GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq N τ _ _ (vmul_ne_zero _ h0 α) (vmul_ne_zero _ h0 β) (h i).1 (h i).2
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have := congrFun (key i) j
    simpa [vmul, Matrix.single_vecMul] using this

end GlobalTheory.WpFam.SepGL
end

section
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.WpFam

namespace GlobalTheory.WpFamGL

theorem transport_GL : ∀ (g : ℂ ≃+* ℂ) (N N' w : ℕ) [NeZero N] (a : (ZMod N)ˣ) (A : GL (Fin 2) (ZMod N)) (F F' : GL (Fin 2) (ZMod N) → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N' → N ∣ N' → ZetaAct g N a → IsFam (gact N 1) w F → (∀ α, QConj g N' (F α) (F' (α * dg a))) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → (∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3) → ∀ α, g (F α τ₀ / ω₀ ^ w) = F' (α * A) τ₁ / ω₁ ^ w := by
  classical
  intro g N N' w _ a A F F' τ₀ τ₁ ω₀ ω₁ hN' hdiv hζ hF hFF' hω₀ h4 h6 hwp α
  let e : Fin 2 → Fin 2 → ZMod N := fun i => Pi.single i 1
  let m : Fin 2 × Bool → ℕ := fun s => if s.2 then 3 else 2
  let u : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β =>
    if s.2 then wpd N (vmul (e s.1) (β * 1)) else wp N (vmul (e s.1) (β * 1))
  let u' : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β => u s (β * dg a)
  have hact : ActBij (gact N 1) := (GlobalTheory.WpFam.Act.isRAct_gact N 1).actBij
  have hu : ∀ s, IsFam (gact N 1) (m s) (u s) := by
    rintro ⟨i, _ | _⟩
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).1
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).2
  have huu' : ∀ s β, QConj g N' (u s β) (u' s β) := by
    rintro ⟨i, _ | _⟩ β
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).2.1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
  have hsep : ∀ β, (∀ s, u s β τ₀ = u s α τ₀) → F β τ₀ = F α τ₀ := by
    intro β hβ
    have : β = α := GlobalTheory.WpFam.SepGL.main N τ₀ β α fun i =>
      ⟨by simpa [u] using hβ (i, false), by simpa [u] using hβ (i, true)⟩
    rw [this]
  have hα : α * A * (dg a)⁻¹ * dg a = α * A := by group
  have hval : ∀ s, g (u s α τ₀ / ω₀ ^ m s) = u' s (α * A * (dg a)⁻¹) τ₁ / ω₁ ^ m s := by
    rintro ⟨i, _ | _⟩
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).1
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).2
  have key := GlobalTheory.QFam.transport_of_separating g (GL (Fin 2) (ZMod N)) (Fin 2 × Bool) (gact N 1) N' w
    m F (fun β => F' (β * dg a)) u u' τ₀ τ₁ ω₀ ω₁ hN' hact hF hu hFF' huu' hω₀ h4 h6 α
    (α * A * (dg a)⁻¹) hsep hval
  simpa [hα] using key

end GlobalTheory.WpFamGL
end

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_modularFamily_GL2ZMod_weierstrass : ∀ (g : ℂ ≃+* ℂ) (N N' w : ℕ) [NeZero N] (a : (ZMod N)ˣ) (A : GL (Fin 2) (ZMod N)) (F F' : GL (Fin 2) (ZMod N) → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N' → N ∣ N' → ZetaAct g N a → IsFam (gact N 1) w F → (∀ α, QConj g N' (F α) (F' (α * dg a))) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → (∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3) → ∀ α, g (F α τ₀ / ω₀ ^ w) = F' (α * A) τ₁ / ω₁ ^ w := by
  atlas_forward_decl GlobalTheory.WpFamGL.transport_GL
end
