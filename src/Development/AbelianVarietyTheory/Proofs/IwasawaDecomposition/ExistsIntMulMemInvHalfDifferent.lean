import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralHalf
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructure
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMatrixBasisLatticeUpToDenominatorNotMem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruence
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary

section
section
open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

namespace GlobalTheory.FourCopiesIso

theorem linearIndependent_of_orthogonal {K V J : Type} [Field K] [AddCommGroup V] [Module K V]
    (h : V → V →ₗ[K] K) (v : J → V) (h0 : ∀ i, h (v i) (v i) ≠ 0) (ho : ∀ i j, i ≠ j → h (v j) (v i) = 0) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s g hs j hj
  have := congrArg (h (v j)) hs
  rw [map_sum, map_zero, Finset.sum_eq_single j] at this
  · rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h0 j)
  · intro i _ hij
    rw [map_smul, ho i j hij, smul_zero]
  · intro e; exact absurd hj e

theorem nonempty_isoKG : ∀ (K E : Type) [Field K] [CharZero K] [Field E] [Algebra K E] [FiniteDimensional K E] (cj : E →+* E) (σ : K →+* K) (ι : Type) [Fintype ι], Fintype.card ι = Module.finrank K E → (∀ x, cj (algebraMap K E x) = algebraMap K E (σ x)) → (∀ y, cj (cj y) = y) → (∀ y, Algebra.trace K E (cj y) = σ (Algebra.trace K E y)) → (∀ y, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace K E (y * cj y) = (a : K)) → Nonempty (IsoKG K E cj ι) := by
  intro K E _ _ _ _ _ cj σ ι _ hcard hσ hcc htr hpos
  classical
  let h : E → E →ₗ[K] K := fun y => (Algebra.trace K E) ∘ₗ LinearMap.mulRight K (cj y)
  have hh : ∀ x y, h y x = Algebra.trace K E (x * cj y) := fun _ _ => rfl
  have hne : ∀ x, x ≠ 0 → h x x ≠ 0 := by
    intro x hx e
    obtain ⟨a, ha, h1⟩ := hpos x hx
    rw [hh, h1] at e
    exact ha.ne' (by exact_mod_cast e)
  obtain ⟨s, hs⟩ : (⊤ : Submodule K E).FG := Module.Finite.fg_top
  obtain ⟨n, v, h0, ho, hsp⟩ := GlobalTheory.FourCopies.exists_orthogonal_family h
    (fun x y e => by
      rw [hh] at e ⊢
      have := htr (x * cj y)
      rw [e, map_zero, map_mul, hcc, mul_comm] at this
      exact this)
    (fun x e => by
      by_contra hx
      exact hne x hx e) s
  have htop : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hs]; exact Submodule.span_le.2 (fun y hy => hsp y hy)
  have hli := linearIndependent_of_orthogonal h v (fun i => hne _ (h0 i)) ho
  have hn : Module.finrank K E = n := by
    simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq (hcard.trans hn)
  choose a ha hav using fun i => hpos (v i) (h0 i)
  choose A hA hA' using fun i => GlobalTheory.FourCopies.exists_similitude (a i) (ha i)
  let H : (Fin 4 → E) → (Fin 4 → E) →ₗ[K] K := fun y => ∑ k, h (y k) ∘ₗ LinearMap.proj k
  have hH : ∀ x y, H y x = ∑ k, Algebra.trace K E (x k * cj (y k)) := by
    intro x y
    simp only [H, LinearMap.sum_apply]
    rfl
  let b : Fin 4 × ι → (Fin 4 → E) := fun w k => (A (e w.2) w.1 k : E) * v (e w.2)
  have hb : ∀ w w', H (b w') (b w) = if w = w' then 1 else 0 := by
    intro w w'
    have h1 : H (b w') (b w) =
        ((∑ k, A (e w.2) w.1 k * A (e w'.2) w'.1 k : ℚ) : K) * h (v (e w'.2)) (v (e w.2)) := by
      rw [hH, hh]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← smul_eq_mul (_ * _ : K), ← map_smul, Algebra.smul_def]
      congr 1
      simp only [b, map_mul, map_ratCast]
      ring
    rw [h1]
    by_cases hi : w.2 = w'.2
    · rw [← hi, hh, hav, ← Rat.cast_mul, mul_comm, hA]
      have : w.1 = w'.1 ↔ w = w' := ⟨fun t => Prod.ext t hi, fun t => by rw [t]⟩
      simp only [this]
      split_ifs <;> simp
    · have : w ≠ w' := fun t => hi (by rw [t])
      rw [if_neg this, ho _ _ (fun t => hi (e.injective t)), mul_zero]
  have hbl : LinearIndependent K b :=
    linearIndependent_of_orthogonal H b (fun i => by rw [hb]; simp) (fun i j hij => by rw [hb, if_neg hij])
  have : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hcard]; exact Module.finrank_pos
  have hc : Fintype.card (Fin 4 × ι) = Module.finrank K (Fin 4 → E) := by
    rw [Module.finrank_pi_fintype, Fintype.card_prod, hcard]; simp
  let B := basisOfLinearIndependentOfCardEqFinrank hbl hc
  have hB : ∀ w, B w = b w := fun w => by simp [B]
  have hco : ∀ x w, H (b w) x = B.equivFun x w := by
    intro x w
    conv_lhs => rw [← B.sum_equivFun x]
    simp only [map_sum, map_smul, hB, hb, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  refine ⟨⟨B.equivFun, fun x y => ?_⟩⟩
  have hy : ∀ k, cj (y k) = ∑ w, algebraMap K E (σ (B.equivFun y w)) * cj (b w k) := by
    intro k
    conv_lhs => rw [← B.sum_equivFun y]
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, hB]
    simp only [Algebra.smul_def, map_mul, hσ]
  simp only [hσ, ← map_mul, ← map_sum]
  congr 1
  simp only [hy, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← hco x w, hH, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← smul_eq_mul (σ _), ← map_smul, Algebra.smul_def]
  congr 1
  ring

end GlobalTheory.FourCopiesIso
end

open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_isoKG_of_trace_positive : ∀ (K E : Type) [Field K] [CharZero K] [Field E] [Algebra K E] [FiniteDimensional K E] (cj : E →+* E) (σ : K →+* K) (ι : Type) [Fintype ι], Fintype.card ι = Module.finrank K E → (∀ x, cj (algebraMap K E x) = algebraMap K E (σ x)) → (∀ y, cj (cj y) = y) → (∀ y, Algebra.trace K E (cj y) = σ (Algebra.trace K E y)) → (∀ y, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace K E (y * cj y) = (a : K)) → Nonempty (IsoKG K E cj ι) := by
  atlas_forward_decl GlobalTheory.FourCopiesIso.nonempty_isoKG
end

section
section
open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

namespace GlobalTheory

theorem exists_complexLinear_extension_of_traceIsometry : ∀ (K E : Type) [Field K] [Field E] [Algebra K E] (cj : E → E) (ι : Type) [Fintype ι] (φ : E →+* ℂ) (emb : ι → E →+* ℂ), (∀ y, φ (cj y) = starRingEnd ℂ (φ y)) → (∀ τ y, emb τ (cj y) = starRingEnd ℂ (emb τ y)) → (∀ τ (x : K), emb τ (algebraMap K E x) = φ (algebraMap K E x)) → (∀ y, ∑ τ, emb τ y = φ (algebraMap K E (Algebra.trace K E y))) → ∀ γ : IsoKG K E cj ι, ∃ gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ), ∀ x : Fin 4 → E, gC (fun w => emb w.2 (x w.1)) = fun w => φ (algebraMap K E (γ.g x w)) := by
  intro K E _ _ _ cj ι _ φ emb hφ hemb hK htr γ
  classical
  let b : Fin 4 × ι → Fin 4 → E := fun w => γ.g.symm (Pi.single w 1)
  let B : Matrix (Fin 4 × ι) (Fin 4 × ι) ℂ := fun v w => emb v.2 (b w v.1)
  have hB : Bᴴ * B = 1 := by
    ext w' w
    have h := congrArg φ (γ.isom (b w) (b w'))
    simp only [b, LinearEquiv.apply_symm_apply, map_sum, map_mul, hφ, ← htr, hemb] at h
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have h2 : ∑ a, ∑ τ, Bᴴ w' (a, τ) * B (a, τ) w
        = ∑ a, ∑ τ, emb τ (b w a) * starRingEnd ℂ (emb τ (b w' a)) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun τ _ => ?_
      rw [Matrix.conjTranspose_apply, mul_comm]
      rfl
    rw [h2, ← h, Finset.sum_eq_single w]
    · by_cases hw : w' = w
      · subst hw; simp
      · simp [Matrix.one_apply_ne hw, Pi.single_eq_of_ne (Ne.symm hw)]
    · intro u _ hu
      simp [Pi.single_eq_of_ne hu]
    · simp
  have hB' : B * Bᴴ = 1 := mul_eq_one_comm.mp hB
  refine ⟨Matrix.toLin'OfInv hB' hB, fun x => ?_⟩
  have hx : x = ∑ w, γ.g x w • b w := by
    apply γ.g.injective
    simp only [b, map_sum, map_smul, LinearEquiv.apply_symm_apply]
    ext u
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : (fun w : Fin 4 × ι => emb w.2 (x w.1))
      = B *ᵥ (fun w => φ (algebraMap K E (γ.g x w))) := by
    ext v
    have := congrArg (fun y => emb v.2 (y v.1)) hx
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, map_sum, map_mul, hK] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct, B, mul_comm, hK]
  rw [hv]
  change Bᴴ *ᵥ (B *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexLinear_extension_of_traceIsometry' : ∀ (K E : Type) [Field K] [Field E] [Algebra K E] (cj : E → E) (ι : Type) [Fintype ι] (φ : E →+* ℂ) (emb : ι → E →+* ℂ), (∀ y, φ (cj y) = starRingEnd ℂ (φ y)) → (∀ τ y, emb τ (cj y) = starRingEnd ℂ (emb τ y)) → (∀ τ (x : K), emb τ (algebraMap K E x) = φ (algebraMap K E x)) → (∀ y, ∑ τ, emb τ y = φ (algebraMap K E (Algebra.trace K E y))) → ∀ γ : IsoKG K E cj ι, ∃ gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ), ∀ x : Fin 4 → E, gC (fun w => emb w.2 (x w.1)) = fun w => φ (algebraMap K E (γ.g x w)) := by
  atlas_forward_decl GlobalTheory.exists_complexLinear_extension_of_traceIsometry
end

section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_basis_lattice_up_to_denominator_notMem : ∀ (K : Type) [Field K] [NumberField K] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule (𝓞 K) (n → K)) (𝔭 : HeightOneSpectrum (𝓞 K)), L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → ∃ g : Matrix n n K, IsUnit g.det ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ x ∈ L, ∀ i, (t : K) * (g⁻¹ *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ j, (t : K) • (fun i => g i j) ∈ L := by
  first | exact @GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | exact GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem | (intros; apply GlobalTheory.LatticeLocBasis.exists_matrix_up_to_notMem <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory.UnIntApprox

open Filter Topology

theorem exists_near {K : Type} [Field K] [CharZero K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]
    (w : AbsoluteValue K ℝ) {q : K} (hq0 : q ≠ 0) (hq : star q = q⁻¹) (hw : w q < 1)
    (g : Matrix n n K) (hg : IsUnit g.det) :
    ∃ u : Matrix n n K, uᴴ * u = 1 ∧ (∀ i j, w ((g⁻¹ * u - 1) i j) ≤ 1) ∧
      ∀ i j, w ((u⁻¹ * g - 1) i j) ≤ 1 := by
  let ι := Fintype.equivFin n
  obtain ⟨u, hu, hlim⟩ := GlobalTheory.UnApprox.exists_seq (G := (1 : Matrix (Fin (Fintype.card n)) _ K))
    conjTranspose_one (by simp) (reindex ι ι g) (fun k => (1 + q ^ k)⁻¹)
  let _ : NormedField K := w.toNormedField
  have hq1 : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw
  have he : Tendsto (fun k : ℕ => (1 + q ^ k)⁻¹) atTop (𝓝 1) := by
    simpa using (hq1.const_add 1).inv₀ (by simp)
  have he' : Tendsto (fun k : ℕ => star (1 + q ^ k)⁻¹) atTop (𝓝 0) := by
    have h := hq1.mul he
    rw [zero_mul] at h
    refine h.congr fun k => ?_
    have hk : q ^ k ≠ 0 := pow_ne_zero _ hq0
    rw [star_inv₀, star_add, star_one, star_pow, hq, inv_pow]
    have : 1 + (q ^ k)⁻¹ = (q ^ k)⁻¹ * (1 + q ^ k) := by field_simp; ring
    rw [this, mul_inv, inv_inv]
  have h1 := hlim w (tendsto_iff_norm_sub_tendsto_zero.1 he) (tendsto_zero_iff_norm_tendsto_zero.1 he')
  let U : ℕ → Matrix n n K := fun k => (u k).submatrix ι ι
  have hU : Tendsto U atTop (𝓝 g) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have h3 := h1 (ι i) (ι j)
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] at h3
    exact h3
  have hinv : ContinuousAt Inv.inv g :=
    continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hg.ne_zero)
  have ha : Tendsto (fun k => g⁻¹ * U k - 1) atTop (𝓝 0) := by
    have := (hU.const_mul g⁻¹).sub_const 1
    rwa [nonsing_inv_mul _ hg, sub_self] at this
  have hb : Tendsto (fun k => (U k)⁻¹ * g - 1) atTop (𝓝 0) := by
    have := ((hinv.tendsto.comp hU).mul_const g).sub_const 1
    rwa [nonsing_inv_mul _ hg, sub_self] at this
  have key : ∀ f : ℕ → Matrix n n K, Tendsto f atTop (𝓝 0) → ∀ᶠ k in atTop, ∀ i j, w (f k i j) ≤ 1 := by
    intro f hf
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have := tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hf i) j)
    exact this.eventually_le_const one_pos
  obtain ⟨k, hk1, hk2⟩ := ((key _ ha).and (key _ hb)).exists
  refine ⟨U k, ?_, hk1, hk2⟩
  have h2 : (u k)ᴴ * u k = 1 := by
    have := hu k
    rw [Matrix.mul_one] at this
    exact mul_eq_one_comm.1 this
  show ((u k).submatrix ι ι)ᴴ * (u k).submatrix ι ι = 1
  rw [conjTranspose_submatrix, submatrix_mul_equiv, h2, submatrix_one_equiv]

theorem exists_unitary_mul_integral :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K), (∀ x, σ (σ x) = x) → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → ∀ g : Matrix n n K, IsUnit g.det → ∃ u : Matrix n n K, (u.map σ)ᵀ * u = 1 ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ i j, (t : K) * (g⁻¹ * u) i j ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ i j, (t : K) * (u⁻¹ * g) i j ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ σ n _ _ 𝔭 α β hσ hα hβ hαβ g hg
  let _ : StarRing K :=
    { star := σ
      star_involutive := hσ
      star_mul := fun x y => by rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hβ0 : (β : K) ≠ 0 := by
    intro h
    apply hβ
    have : β = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have hα0 : (α : K) ≠ 0 := by
    intro h
    apply hβ0
    rw [hαβ, h, map_zero]
  have hq : star ((α : K) / β) = ((α : K) / β)⁻¹ := by
    show σ _ = _
    rw [map_div₀, ← hαβ, hαβ, hσ, inv_div]
  have hw : NumberField.HeightOneSpectrum.adicAbv K 𝔭 ((α : K) / β) < 1 := by
    rw [map_div₀, ← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding]
    have h1 := (FinitePlace.norm_lt_one_iff_mem K 𝔭 α).2 hα
    have h2 := (FinitePlace.norm_eq_one_iff_notMem K 𝔭 β).2 hβ
    erw [h2]
    rw [div_one]
    exact h1
  obtain ⟨u, hu, h1, h2⟩ := exists_near _ (div_ne_zero hα0 hβ0) hq hw g hg
  obtain ⟨s, hs, hsb⟩ := GlobalTheory.UnApprox.exists_denom (J := (n × n) ⊕ (n × n)) 𝔭.ne_bot
    (Sum.elim (fun p => (g⁻¹ * u - 1) p.1 p.2) (fun p => (u⁻¹ * g - 1) p.1 p.2)) (by
      intro v hv
      have : v = 𝔭 := by
        ext1
        exact (𝔭.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.1 hv)).symm
      subst this
      rintro (p | p)
      · exact h1 _ _
      · exact h2 _ _)
  have key : ∀ (M : Matrix n n K) (i j : n), (∃ b : 𝓞 K, (s : K) * (M - 1) i j = b) →
      (s : K) * M i j ∈ (algebraMap (𝓞 K) K).range := by
    rintro M i j ⟨b, hb⟩
    refine ⟨b + if i = j then s else 0, ?_⟩
    rw [Matrix.sub_apply, one_apply, mul_sub] at hb
    rw [map_add]
    split_ifs at hb ⊢
    · show (b : K) + s = _
      linear_combination -hb
    · rw [map_zero]
      show (b : K) + 0 = _
      linear_combination -hb
  refine ⟨u, hu, s, fun h => 𝔭.isPrime.ne_top ?_, fun i j => key _ _ _ (hsb (Sum.inl (i, j))),
    fun i j => key _ _ _ (hsb (Sum.inr (i, j)))⟩
  have := Ideal.isCoprime_iff_sup_eq.1 hs
  rwa [sup_eq_right.2 ((Ideal.span_singleton_le_iff_mem _).2 h)] at this

end GlobalTheory.UnIntApprox
end

open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_mul_integral_at_split_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K), (∀ x, σ (σ x) = x) → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → ∀ g : Matrix n n K, IsUnit g.det → ∃ u : Matrix n n K, (u.map σ)ᵀ * u = 1 ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ i j, (t : K) * (g⁻¹ * u) i j ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ i j, (t : K) * (u⁻¹ * g) i j ∈ (algebraMap (𝓞 K) K).range := by
  atlas_forward_decl GlobalTheory.UnIntApprox.exists_unitary_mul_integral
end

section
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

theorem selfDual_standard_at_rational_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K) (L : Submodule (𝓞 K) (n → K)) (t : 𝓞 K), (∀ x, σ (σ x) = x) → (∀ x : 𝓞 K, ∃ m : ℤ, (x : K) * σ x = m) → p.Prime → (p : 𝓞 K) ∈ 𝔭.asIdeal → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∑ i, x i * σ (y i) ∈ (algebraMap (𝓞 K) K).range) → t ∉ 𝔭.asIdeal → (∀ x ∈ L, ∀ i, (t : K) * x i ∈ (algebraMap (𝓞 K) K).range) → (∀ j, (Pi.single j (t : K) : n → K) ∈ L) → ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, ∀ i, (s : K) * x i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ v : n → K, (∀ i, v i ∈ (algebraMap (𝓞 K) K).range) → (s : K) • v ∈ L := by
  intro K _ _ σ n _ _ p 𝔭 α β L t hσ hN hp hp𝔭 hα hβ hβα hL ht h1 h2
  have hint : ∀ x ∈ (algebraMap (𝓞 K) K).range, σ x ∈ (algebraMap (𝓞 K) K).range := by
    rintro _ ⟨x, rfl⟩
    have : IsIntegral ℤ (σ (algebraMap (𝓞 K) K x)) :=
      (RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom
    exact ⟨⟨_, this⟩, rfl⟩
  obtain ⟨t', ht'⟩ := hint (t : K) ⟨t, rfl⟩
  have ht'' : (t' : K) = σ t := ht'
  have h1' : ∀ x ∈ L, ∀ j, (t' : K) * x j ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx j
    have := (hL x).1 hx _ (h2 j)
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)] at this
    rw [ht'', mul_comm]
    simpa only [Pi.single_eq_same] using this
  have h2' : ∀ j, (Pi.single j (t' : K) : n → K) ∈ L := by
    intro j
    rw [hL]
    intro y hy
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)]
    rw [Pi.single_eq_same, ht'', ← map_mul]
    exact hint _ (h1 y hy j)
  set a : 𝓞 K := β * t + α * t' with ha
  have haK : (a : K) = β * t + α * t' := by simp [ha]
  have ha𝔭 : a ∉ 𝔭.asIdeal := by
    intro h
    have h' : β * t ∈ 𝔭.asIdeal := by
      have := 𝔭.asIdeal.sub_mem h (𝔭.asIdeal.mul_mem_right t' hα)
      simpa [ha] using this
    rcases 𝔭.isPrime.mem_or_mem h' with h | h
    · exact hβ h
    · exact ht h
  have hσa : σ a = a := by
    rw [haK, map_add, map_mul, map_mul, hβα, ht'', hσ, hσ]
    ring
  have ha1 : ∀ x ∈ L, ∀ j, (a : K) * x j ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx j
    have : (a : K) * x j = β * (t * x j) + α * (t' * x j) := by rw [haK]; ring
    rw [this]
    exact add_mem (mul_mem ⟨β, rfl⟩ (h1 x hx j)) (mul_mem ⟨α, rfl⟩ (h1' x hx j))
  have ha2 : ∀ j, (Pi.single j (a : K) : n → K) ∈ L := by
    intro j
    have : (Pi.single j (a : K) : n → K)
        = β • (Pi.single j (t : K) : n → K) + α • (Pi.single j (t' : K) : n → K) := by
      ext i
      by_cases h : i = j
      · subst h
        simp [haK, Algebra.smul_def]
      · simp [Pi.single_eq_of_ne h]
    rw [this]
    exact add_mem (L.smul_mem _ (h2 j)) (L.smul_mem _ (h2' j))
  obtain ⟨m, hm⟩ := hN a
  rw [hσa] at hm
  have hmO : a * a = (m : 𝓞 K) := by
    apply RingOfIntegers.coe_injective
    simpa using hm
  obtain ⟨e, he⟩ : ∃ e : ℤ, ((m.natAbs : ℕ) : ℤ) = e * m := by
    rcases Int.natAbs_eq m with h | h
    · exact ⟨1, by omega⟩
    · exact ⟨-1, by omega⟩
  have hs : ((m.natAbs : ℕ) : K) = (e : K) * (a * a) := by
    rw [hm]
    have := congrArg (Int.cast : ℤ → K) he
    rwa [Int.cast_natCast, Int.cast_mul] at this
  refine ⟨m.natAbs, ?_, ?_, ?_⟩
  · rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    obtain ⟨c, hc⟩ := Int.natCast_dvd.2 h
    have : a * a ∈ 𝔭.asIdeal := by
      rw [hmO, hc]
      push_cast
      exact 𝔭.asIdeal.mul_mem_right _ hp𝔭
    rcases 𝔭.isPrime.mem_or_mem this with h | h <;> exact ha𝔭 h
  · intro x hx i
    have : ((m.natAbs : ℕ) : K) * x i = (e : K) * a * (a * x i) := by rw [hs]; ring
    rw [this]
    exact mul_mem (mul_mem (intCast_mem _ e) ⟨a, rfl⟩) (ha1 x hx i)
  · intro v hv
    choose w hw using hv
    have : ((m.natAbs : ℕ) : K) • v
        = ∑ j, ((e : 𝓞 K) * w j * a) • (Pi.single j (a : K) : n → K) := by
      ext i
      rw [Finset.sum_apply, Finset.sum_eq_single i
        (by intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]) (by simp)]
      rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, hs, ← hw i, Algebra.smul_def (_ : 𝓞 K),
        smul_eq_mul]
      simp only [map_mul, map_intCast]
      change _ = (e : K) * _ * (a : K) * (a : K)
      ring
    rw [this]
    exact L.sum_mem fun j _ => L.smul_mem _ (ha2 j)

end GlobalTheory
end

open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_standard_at_rational_prime : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K) (L : Submodule (𝓞 K) (n → K)) (t : 𝓞 K), (∀ x, σ (σ x) = x) → (∀ x : 𝓞 K, ∃ m : ℤ, (x : K) * σ x = m) → p.Prime → (p : 𝓞 K) ∈ 𝔭.asIdeal → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∑ i, x i * σ (y i) ∈ (algebraMap (𝓞 K) K).range) → t ∉ 𝔭.asIdeal → (∀ x ∈ L, ∀ i, (t : K) * x i ∈ (algebraMap (𝓞 K) K).range) → (∀ j, (Pi.single j (t : K) : n → K) ∈ L) → ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, ∀ i, (s : K) * x i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ v : n → K, (∀ i, v i ∈ (algebraMap (𝓞 K) K).range) → (s : K) • v ∈ L := by
  atlas_forward_decl GlobalTheory.selfDual_standard_at_rational_prime
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

namespace GlobalTheory.Mem.Col2.SplitPrime

theorem mem_xor {A : Type*} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (p t m : ℤ) (hp : (p : A) ∈ P) (a a' : A)
    (hm : a * a' = (p : A) * m) (ht : a + a' = t) (hc : IsCoprime p t) :
    (a ∈ P ∧ a' ∉ P) ∨ (a' ∈ P ∧ a ∉ P) := by
  have hnot : ¬ (a ∈ P ∧ a' ∈ P) := by
    rintro ⟨h1, h2⟩
    have h3 : (t : A) ∈ P := ht ▸ P.add_mem h1 h2
    obtain ⟨u, v, huv⟩ := hc
    have h4 : (u : A) * p + (v : A) * t = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) huv
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (h4 ▸ P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h3)))
  have h5 : a * a' ∈ P := hm ▸ P.mul_mem_right _ hp
  rcases hP.mem_or_mem h5 with h | h
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩

theorem exists_over (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥ (by
    rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]
    exact bot_le)
  have hmem : (p : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Ideal.mem_bot).1 hmem)

theorem exists_elt {R : Ranks} (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (a : H.K) (t m : ℤ), IsIntegral ℤ a ∧ a * HostK.conjK H a = (p : H.K) * m ∧ a + HostK.conjK H a = t ∧
      IsCoprime (p : ℤ) t := by
  set θ : H.K := ⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ with hθ
  have hsq : θ ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa [hθ] using H.sqrtMinusD_sq)
  have hcj : HostK.conjK H θ = -θ := Subtype.ext (by simpa [hθ, HostK.coe_conjK] using H.conj_sqrtMinusD)
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 8 * m := by
      have := H.hyp.2.2.2.1
      exact ⟨(H.d + 1) / 8, by omega⟩
    have hm' : (H.d : H.K) + 1 = 8 * m := by exact_mod_cast hm
    refine ⟨(1 + θ) / 2, 1, m, HostK.isIntegral_half H, ?_, ?_, isCoprime_one_right⟩
    · rw [map_div₀, map_add, map_one, hcj, map_ofNat]
      push_cast
      linear_combination (-1 / 4 : H.K) * hsq + (1 / 4 : H.K) * hm'
    · rw [map_div₀, map_add, map_one, hcj, map_ofNat]
      push_cast
      ring
  · have hj : jacobiSym (-(H.d : ℤ)) p = 1 := hs.resolve_left h2
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
    have hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h
      rw [(legendreSym.eq_zero_iff p _).2 h] at hj
      exact zero_ne_one hj
    obtain ⟨s, hs'⟩ := (legendreSym.eq_one_iff p hne).1 hj
    obtain ⟨r, rfl⟩ := ZMod.intCast_surjective s
    have hr : ¬ (p : ℤ) ∣ r := by
      intro h
      rw [hs', (ZMod.intCast_zmod_eq_zero_iff_dvd r p).2 h] at hne
      exact hne (mul_zero _)
    have hdiv : (p : ℤ) ∣ r * r + H.d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast at hs' ⊢
      linear_combination -hs'
    obtain ⟨m, hm⟩ := hdiv
    have hm' : (r : H.K) * r + H.d = (p : H.K) * m := by exact_mod_cast congrArg (Int.cast : ℤ → H.K) hm
    have hθi : IsIntegral ℤ θ := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hsq]
      exact (isIntegral_natCast H.d).neg
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    refine ⟨r + θ, 2 * r, m, (isIntegral_intCast r).add hθi, ?_, ?_, ?_⟩
    · rw [map_add, map_intCast, hcj]
      linear_combination hm' - hsq
    · rw [map_add, map_intCast, hcj]
      push_cast
      ring
    · refine (hpi.coprime_iff_not_dvd).2 fun h => ?_
      rcases hpi.dvd_or_dvd h with h | h
      · have h' : p ∣ 2 := by exact_mod_cast h
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
      · exact hr h

theorem exists_prime_not_conj (R : Ranks) (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧
      (β : H.K) = HostK.conjK H α := by
  obtain ⟨a, t, m, hai, hm, ht, hc⟩ := exists_elt H p hp hs
  have hai' : IsIntegral ℤ (HostK.conjK H a) := by
    have : HostK.conjK H a = t - a := by linear_combination ht
    rw [this]
    exact (isIntegral_intCast t).sub hai
  obtain ⟨𝔭, h𝔭⟩ := exists_over H.K p hp
  let x : 𝓞 H.K := ⟨a, hai⟩
  let y : 𝓞 H.K := ⟨HostK.conjK H a, hai'⟩
  have hx : (x : H.K) = a := rfl
  have hy : (y : H.K) = HostK.conjK H a := rfl
  have h1 : x * y = ((p : ℤ) : 𝓞 H.K) * m := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using hm
  have h2 : x + y = t := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using ht
  rcases mem_xor 𝔭.asIdeal 𝔭.isPrime p t m (by exact_mod_cast h𝔭) x y h1 h2 hc with h | h
  · exact ⟨𝔭, x, y, h𝔭, h.1, h.2, rfl⟩
  · exact ⟨𝔭, y, x, h𝔭, h.1, h.2, by rw [hx, hy, HostK.conjK_conjK]⟩

end GlobalTheory.Mem.Col2.SplitPrime
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_over_split_not_mem_conj : ∀ (R : Ranks) (H : Host R) (p : ℕ), p.Prime → Th.SplitK H p → ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧ (β : H.K) = HostK.conjK H α := by
  atlas_forward_decl GlobalTheory.Mem.Col2.SplitPrime.exists_prime_not_conj
end

section
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

theorem exists_integral_dual_family (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] :
    ∃ (k : ℕ) (b : Fin k → 𝓞 M) (l : Fin k → M →ₗ[E] E),
      (∀ j (c : 𝓞 M), ∃ a : 𝓞 E, l j (c : M) = (a : E)) ∧
      ∀ y : M, y = ∑ j, (b j : M) * algebraMap E M (l j y) := by
  haveI : Module.Finite (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.Flat (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.FinitePresentation (𝓞 E) (𝓞 M) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (𝓞 M) := Module.Flat.projective_of_finitePresentation
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) (𝓞 M)
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  haveI hL : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 M) (nonZeroDivisors (𝓞 E))) M :=
    IsIntegralClosure.isLocalization (𝓞 E) E M (𝓞 M)
  haveI hL' : IsLocalizedModule (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hL
  have hu : ∀ x : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) x
  let l0 : Fin k → M →ₗ[𝓞 E] E := fun j =>
    IsLocalizedModule.lift (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu
  let l : Fin k → M →ₗ[E] E := fun j =>
    (l0 j).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E
  have hl : ∀ j (c : 𝓞 M), l j (c : M) = ((σ c j : 𝓞 E) : E) := by
    intro j c
    exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu c
  refine ⟨k, fun j => π (Pi.single j 1), l, fun j c => ⟨_, hl j c⟩, ?_⟩
  have hc : ∀ c : 𝓞 M, (c : M) = ∑ j, ((π (Pi.single j 1) : 𝓞 M) : M) * algebraMap E M (l j c) := by
    intro c
    have h1 : c = ∑ j, σ c j • π (Pi.single j 1) := by
      have h2 : π (σ c) = c := LinearMap.congr_fun hσ c
      conv_lhs => rw [← h2, LinearMap.pi_apply_eq_sum_univ π (σ c)]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ext i
      simp [Pi.single_apply, eq_comm]
    have h3 := congrArg (algebraMap (𝓞 M) M) h1
    rw [map_sum] at h3
    refine h3.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [hl, Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply]
    rfl
  intro y
  obtain ⟨⟨c, a⟩, ha⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap y
  have ha' : ((a : 𝓞 E) : E) • y = (c : M) := by
    have : (a : 𝓞 E) • y = (c : M) := ha
    rw [← this]
    exact algebraMap_smul E (a : 𝓞 E) y
  have hne : ((a : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero a.2
    exact_mod_cast this
  have h4 := hc c
  rw [← ha'] at h4
  apply smul_right_injective M hne
  dsimp only
  rw [h4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
  ring

theorem comap_single_span_algebraMap (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι) :
    (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap
      (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) =
    Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap
      (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by
  apply le_antisymm
  · obtain ⟨k, b, l, hl, hy⟩ := exists_integral_dual_family E M
    have key : ∀ j, ∀ w ∈ Submodule.span (𝓞 M)
        ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S), ∀ c : 𝓞 M,
        (fun i => l j ((c : M) * w i)) ∈ Submodule.span (𝓞 E) S := by
      intro j w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        intro c
        obtain ⟨a, ha⟩ := hl j c
        have : (fun i => l j ((c : M) * algebraMap E M (v i))) = a • v := by
          ext i
          rw [mul_comm, ← Algebra.smul_def, map_smul, ha, smul_eq_mul, mul_comm]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
      | zero =>
        intro c
        have : (fun i => l j ((c : M) * (0 : ι → M) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        intro c
        have : (fun i => l j ((c : M) * (x + y) i)) =
            (fun i => l j ((c : M) * x i)) + (fun i => l j ((c : M) * y i)) := by
          ext i; simp [mul_add]
        rw [this]; exact Submodule.add_mem _ (hx c) (hy c)
      | smul a x _ hx =>
        intro c
        have : (fun i => l j ((c : M) * (a • x) i)) =
            (fun i => l j (((c * a : 𝓞 M) : M) * x i)) := by
          ext i
          congr 1
          rw [Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
          simp
        rw [this]; exact hx _
    intro s hs
    rw [hy s]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 : ((b j : 𝓞 M) : M) * algebraMap E M (l j s) = b j • algebraMap E M (l j s) := rfl
    rw [h1]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨l j s, ?_, rfl⟩)
    have h2 := key j _ hs 1
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have key : ∀ v ∈ Submodule.span (𝓞 E) S, (fun i => algebraMap E M (v i)) ∈
        Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have : (fun i => algebraMap E M ((0 : ι → E) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have : (fun i => algebraMap E M ((x + y) i)) =
            (fun i => algebraMap E M (x i)) + (fun i => algebraMap E M (y i)) := by
          ext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        have : (fun i => algebraMap E M ((a • x) i)) =
            algebraMap (𝓞 E) (𝓞 M) a • (fun i => algebraMap E M (x i)) := by
          ext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
            ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have h2 := key _ hs
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]

end GlobalTheory
end

open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comap_single_span_algebraMap_numberField : ∀ (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι), (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) = Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by
  atlas_forward_decl GlobalTheory.comap_single_span_algebraMap
end

section
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

theorem exists_pow_eq_span_singleton_of_fg (E : Type) [Field E] [NumberField E]
    (I : Submodule (𝓞 E) E) (hI : I.FG) :
    ∃ n : ℕ, ∃ β : E, I ^ (n + 1) = Submodule.span (𝓞 E) {β} := by
  classical
  by_cases h0 : I = ⊥
  · exact ⟨0, 0, by simp [h0]⟩
  let F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  have hF : F ≠ 0 := by
    intro h
    apply h0
    have := congrArg (fun G : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (G : Submodule (𝓞 E) E)) h
    simpa [F] using this
  let u := Units.mk0 F hF
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card (ClassGroup (𝓞 E)) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h1 : ClassGroup.mk E (u ^ (n + 1)) = 1 := by
    rw [map_pow, ← hn, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨β, hβ⟩ := h1
  refine ⟨n, β, ?_⟩
  rw [← hβ, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

theorem span_image_eq_span_root {E M : Type} [Field E] [Field M] (ψ : E →+* M)
    (I : Submodule (𝓞 E) E) (n : ℕ) (β : E) (hβ : I ^ (n + 1) = Submodule.span (𝓞 E) {β})
    (γ : M) (hγ : γ ^ (n + 1) = ψ β) :
    Submodule.span (𝓞 M) (ψ '' I) = Submodule.span (𝓞 M) {γ} := by
  set J := Submodule.span (𝓞 M) (ψ '' I) with hJ
  have hint : ∀ c : 𝓞 E, IsIntegral ℤ (ψ c) := fun c =>
    map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe c)
  have hle : J ≤ Submodule.span (𝓞 M) {γ} := by
    rw [hJ, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ^ (n + 1) ∈ Submodule.span (𝓞 E) {β} := hβ ▸ Submodule.pow_mem_pow I hx (n + 1)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxn
    have hc' : ψ x ^ (n + 1) = ψ c * γ ^ (n + 1) := by
      rw [hγ, ← map_pow, ← hc, ← map_mul]; rfl
    by_cases hγ0 : γ = 0
    · have : ψ x = 0 := by
        rw [hγ0] at hc'
        simpa using hc'
      rw [this]; exact Submodule.zero_mem _
    · have hi : IsIntegral ℤ (ψ x / γ) := by
        apply IsIntegral.of_pow (Nat.succ_pos n)
        rw [div_pow, hc', mul_div_assoc, div_self (pow_ne_zero _ hγ0), mul_one]
        exact hint c
      refine Submodule.mem_span_singleton.mpr ⟨⟨ψ x / γ, hi⟩, ?_⟩
      change (ψ x / γ) * γ = ψ x
      exact div_mul_cancel₀ _ hγ0
  have hpow : ∀ k : ℕ, ∀ y ∈ I ^ k, ψ y ∈ J ^ k := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [pow_zero, Submodule.mem_one] at hy ⊢
      obtain ⟨c, rfl⟩ := hy
      exact ⟨⟨ψ c, hint c⟩, rfl⟩
    | succ k ih =>
      intro y hy
      rw [pow_succ] at hy ⊢
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Submodule.mul_mem_mul (ih a ha) (Submodule.subset_span ⟨b, hb, rfl⟩)
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
  refine le_antisymm hle ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  by_cases hγ0 : γ = 0
  · rw [hγ0]; exact Submodule.zero_mem _
  have h1 : γ ^ (n + 1) ∈ J ^ (n + 1) := by
    rw [hγ]; apply hpow; rw [hβ]; exact Submodule.mem_span_singleton_self β
  have h2 : J ^ (n + 1) ≤ J * Submodule.span (𝓞 M) {γ ^ n} := by
    rw [pow_succ']
    refine mul_le_mul_right ?_ _
    rw [← Set.singleton_pow, ← Submodule.span_pow]
    exact pow_le_pow_left' hle n
  obtain ⟨z, hz, hz'⟩ := Submodule.mem_mul_span_singleton.mp (h2 h1)
  rw [pow_succ'] at hz'
  have : z = γ := mul_right_cancel₀ (pow_ne_zero n hγ0) hz'
  exact this ▸ hz

theorem exists_finite_extension_capitulation :
    ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (ι : Type) [Finite ι] (I : ι → Submodule (𝓞 E) E), (∀ τ, (I τ).FG) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ x, φ x ∈ M) ∧ ∀ τ, ∃ s : M, Submodule.span (𝓞 M) {y : M | ∃ x ∈ I τ, (y : ℂ) = φ x} = Submodule.span (𝓞 M) {s} := by
  intro E _ _ φ ι _ I hI
  choose n β hβ using fun τ => exists_pow_eq_span_singleton_of_fg E (I τ) (hI τ)
  choose γ hγ using fun τ => IsAlgClosed.exists_pow_nat_eq (φ (β τ)) (Nat.succ_pos (n τ))
  let φ' : E →ₐ[ℚ] ℂ := φ.toRatAlgHom
  let K : IntermediateField ℚ ℂ := φ'.fieldRange
  haveI hK : FiniteDimensional ℚ K :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ').toLinearEquiv
  haveI : Finite (Set.range γ) := Set.finite_range γ
  haveI hL : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range γ)) := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨τ, rfl⟩
    apply IsIntegral.of_pow (Nat.succ_pos (n τ))
    rw [hγ]
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) (β τ)).map φ'
  let M : IntermediateField ℚ ℂ := K ⊔ IntermediateField.adjoin ℚ (Set.range γ)
  have hM : ∀ x, φ x ∈ M := fun x => (le_sup_left : K ≤ M) ⟨x, rfl⟩
  refine ⟨M, IntermediateField.finiteDimensional_sup _ _, hM, fun τ => ?_⟩
  have hγM : γ τ ∈ M := (le_sup_right : _ ≤ M) (IntermediateField.subset_adjoin ℚ _ ⟨τ, rfl⟩)
  let ψ : E →+* M := φ.codRestrict M.toSubfield hM
  refine ⟨⟨γ τ, hγM⟩, ?_⟩
  rw [← span_image_eq_span_root ψ (I τ) (n τ) (β τ) (hβ τ) ⟨γ τ, hγM⟩ (Subtype.ext (hγ τ))]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, Subtype.ext h.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end GlobalTheory
end

open NumberField IsDedekindDomain Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_capitulation_complex : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (ι : Type) [Finite ι] (I : ι → Submodule (𝓞 E) E), (∀ τ, (I τ).FG) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ x, φ x ∈ M) ∧ ∀ τ, ∃ s : M, Submodule.span (𝓞 M) {y : M | ∃ x ∈ I τ, (y : ℂ) = φ x} = Submodule.span (𝓞 M) {s} := by
  atlas_forward_decl GlobalTheory.exists_finite_extension_capitulation
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

noncomputable section

namespace GlobalTheory.Mem.Col2.CurveLat

theorem exists_periodPair_mul_image {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : 𝓞 K →+* ℂ) (hσ : Function.Injective σ) (a : 𝓞 K) (ha : (σ a).im ≠ 0) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ c : 𝓞 K, z = δ * σ c := by
  let b : Module.Basis (Fin 2) ℤ (𝓞 K) := Module.finBasisOfFinrankEq ℤ _ ((RingOfIntegers.rank K).trans hK)
  have hs : ∀ x : 𝓞 K, σ x = b.repr x 0 * σ (b 0) + b.repr x 1 * σ (b 1) := by
    intro x
    have := congrArg σ (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ (b 0) ≠ 0 := (map_ne_zero_iff σ hσ).2 (b.ne_zero 0)
  have h0 : (σ (b 1) * starRingEnd ℂ (σ (b 0))).im ≠ 0 := by
    intro h0
    have e := hs (a * b 0)
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ (b 0))).im) e
    simp only [map_mul] at e'
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨δ * σ (b 0), δ * σ (b 1), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e0
    have e : (x : ℂ) * σ (b 0) + (y : ℂ) * σ (b 1) = 0 := by
      apply mul_left_cancel₀ hδ
      simp only [Complex.real_smul] at e0
      linear_combination e0
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 1)).im * e1 - (σ (b 1)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ (b 0)).re * e2 - (σ (b 0)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m • b 0 + n • b 1, by simp; ring⟩
    · rintro ⟨x, rfl⟩
      exact ⟨b.repr x 0, b.repr x 1, by rw [hs x]; ring⟩

theorem not_isIntegral_half : ¬ IsIntegral ℤ (1 / 2 : ℂ) := by
  intro h
  have h1 : IsIntegral ℤ (1 / 2 : ℚ) := by
    refine (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).1 ?_
    simpa using h
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  have h2 : (2 * y : ℚ) = 1 := by
    simp only [eq_intCast] at hy
    rw [hy]; norm_num
  have h3 : 2 * y = 1 := by exact_mod_cast h2
  omega

theorem not_isIntegral_of_re {z : ℂ} (hz : z.re = 1 / 4) : ¬ IsIntegral ℤ z := by
  intro h
  have h1 : IsIntegral ℤ (starRingEnd ℂ z) := h.map (starRingEnd ℂ).toIntAlgHom
  have h2 := h.add h1
  rw [Complex.add_conj, hz] at h2
  apply not_isIntegral_half
  have e : ((2 * (1 / 4) : ℝ) : ℂ) = 1 / 2 := by
    push_cast
    norm_num
  rwa [e] at h2

variable {R : Ranks} (H : Host R)

def embO : 𝓞 H.K →+* ℂ := (H.φ₀.comp H.K.val.toRingHom).comp (algebraMap (𝓞 H.K) H.K)

theorem mem_lamOf_top (δ z : ℂ) : z ∈ Th.lamOf H ⊤ δ ↔ ∃ c : 𝓞 H.K, z = δ * embO H c := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, -, rfl⟩ := hx
      exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := hy
      exact ⟨c + c', by rw [map_add, mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, by rw [map_neg, mul_neg]⟩
  · rintro ⟨c, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, Submodule.mem_top, rfl⟩

theorem exists_periodPair_lamOf (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Th.lamOf H ⊤ δ ↔ z ∈ L.lattice := by
  have hK : Module.finrank ℚ H.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq
  have hinj : Function.Injective (embO H) :=
    (H.φ₀.comp H.K.val.toRingHom).injective.comp RingOfIntegers.coe_injective
  have ha : (embO H ⟨_, HostK.isIntegral_half H⟩).im ≠ 0 := by
    have e : embO H ⟨_, HostK.isIntegral_half H⟩ = (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2 := by
      rw [← HostK.φ₀_sqrt]
      change (H.φ₀.comp H.K.val.toRingHom) ((1 + (⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ : H.K)) / 2) = _
      rw [map_div₀, map_add, map_one, map_ofNat]
      rfl
    have hd : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
    rw [e]
    simp [hd.ne']
  obtain ⟨L, hL⟩ := exists_periodPair_mul_image hK (embO H) hinj _ ha δ hδ
  exact ⟨L, fun z => by rw [mem_lamOf_top, hL]⟩

theorem not_mem_lamOf (δ : ℂ) (hδ : δ ≠ 0) {z : ℂ} (hz : z.re = 1 / 4) : δ * z ∉ Th.lamOf H ⊤ δ := by
  rw [mem_lamOf_top]
  rintro ⟨c, hc⟩
  apply not_isIntegral_of_re hz
  rw [mul_left_cancel₀ hδ hc]
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) c).map (embO H).toIntAlgHom

end GlobalTheory.Mem.Col2.CurveLat

namespace GlobalTheory.Mem.Col2

open CurveLat

theorem exists_curve_lattice : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  intro R H
  obtain ⟨L₁, h₁⟩ := exists_periodPair_lamOf H 1 one_ne_zero
  have hΔ := (GlobalTheory.LatticeInvariants.invariants_dictionary L₁ _ h₁).2.2.1
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (Th.lamOf H ⊤ 1)) (n := 12) (by norm_num)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hΔ (by rw [← hδ]; norm_num)
  obtain ⟨L, hL⟩ := exists_periodPair_lamOf H δ hδ0
  refine ⟨δ, L, δ, hδ, AddSubgroup.ext fun z => (hL z).symm, ?_, ?_, ?_⟩
  · exact (mem_lamOf_top H δ _).2 ⟨1, by rw [map_one]; ring⟩
  · have := not_mem_lamOf H δ hδ0 (z := (1 + Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring
  · have := not_mem_lamOf H δ hδ0 (z := (1 - Complex.I * (Real.sqrt H.d : ℂ)) / 4) (by simp)
    convert this using 2
    ring

end GlobalTheory.Mem.Col2

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodPair_lattice_eq_lamOf : ∀ (R : Ranks) (H : Host R), ∃ (δ : ℂ) (L : PeriodPair) (ω₀ : ℂ), Th.IsDiscriminantTwelfthRootOfIdealLattice H ⊤ δ ∧ L.lattice.toAddSubgroup = Th.lamOf H ⊤ δ ∧ Th.IsTwoTorsionPointUnkilled H (Th.lamOf H ⊤ δ) (ω₀ / 2) := by
  atlas_forward_decl GlobalTheory.Mem.Col2.exists_curve_lattice
end

section
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Matrix
open scoped BigOperators

namespace AmbEx

theorem form_mulVec {K n : Type} [Field K] [Fintype n] [DecidableEq n] (σ : K →+* K) (u : Matrix n n K)
    (hu : (u.map σ)ᵀ * u = 1) (x y : n → K) : ∑ i, (u *ᵥ x) i * σ ((u *ᵥ y) i) = ∑ i, x i * σ (y i) := by
  have h1 : ∀ i, σ ((u *ᵥ y) i) = (u.map σ *ᵥ fun j => σ (y j)) i := fun i => RingHom.map_mulVec σ u y i
  simp only [h1]
  change (u *ᵥ x) ⬝ᵥ (u.map σ *ᵥ fun j => σ (y j)) = x ⬝ᵥ fun j => σ (y j)
  rw [dotProduct_comm, dotProduct_mulVec, vecMul_mulVec, hu, vecMul_one, dotProduct_comm]

theorem exists_move : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (p : ℕ) (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K) (L : Submodule (𝓞 K) (n → K)), (∀ x, σ (σ x) = x) → (∀ x : 𝓞 K, ∃ m : ℤ, (x : K) * σ x = m) → p.Prime → (p : 𝓞 K) ∈ 𝔭.asIdeal → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → L.FG → Submodule.span K (L : Set (n → K)) = ⊤ → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∑ i, x i * σ (y i) ∈ (algebraMap (𝓞 K) K).range) → ∃ u : (n → K) ≃ₗ[K] (n → K), (∀ x y, ∑ i, u x i * σ (u y i) = ∑ i, x i * σ (y i)) ∧ ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ L, ∀ i, (s : K) * u x i ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ v : n → K, (∀ i, v i ∈ (algebraMap (𝓞 K) K).range) → (s : K) • u.symm v ∈ L := by
  intro K _ _ σ n _ _ p 𝔭 α β L hσ hN hp hp𝔭 hα hβ hαβ hfg hsp hsd
  obtain ⟨g, hg, t, ht, hL, hc⟩ := GlobalTheory.T.exists_matrix_basis_lattice_up_to_denominator_notMem K n L 𝔭 hfg hsp
  obtain ⟨u, hu, t', ht', h1, h2⟩ := GlobalTheory.T.exists_unitary_mul_integral_at_split_prime K σ n 𝔭 α β hσ hα hβ hαβ g hg
  have hud : IsUnit u.det := Matrix.isUnit_det_of_left_inverse hu
  let e : (n → K) ≃ₗ[K] (n → K) := (Matrix.toLinearEquiv' u (Matrix.invertibleOfIsUnitDet u hud)).symm
  have hes : ∀ v, e.symm v = u *ᵥ v := fun v => rfl
  have he : ∀ x, e x = u⁻¹ *ᵥ x := fun x => by
    apply e.symm.injective
    rw [e.symm_apply_apply, hes, mulVec_mulVec, mul_nonsing_inv _ hud, one_mulVec]
  have hform : ∀ x y, ∑ i, e x i * σ (e y i) = ∑ i, x i * σ (y i) := fun x y => by
    rw [← form_mulVec σ u hu (e x) (e y), ← hes, ← hes, e.symm_apply_apply, e.symm_apply_apply]
  let L' : Submodule (𝓞 K) (n → K) := L.comap (e.symm.toLinearMap.restrictScalars (𝓞 K))
  have hm : ∀ v, v ∈ L' ↔ e.symm v ∈ L := fun v => Iff.rfl
  have htt : t * t' ∉ 𝔭.asIdeal := fun h => (𝔭.isPrime.mem_or_mem h).elim ht ht'
  obtain ⟨s, hs, ha, hb⟩ := GlobalTheory.T.selfDual_lattice_standard_at_rational_prime K σ n p 𝔭 α β L' (t * t') hσ hN hp hp𝔭 hα hβ hαβ
    (fun x => by
      rw [hm, hsd]
      constructor
      · intro h y hy
        have := h _ ((hm y).1 hy)
        rwa [← hform, e.apply_symm_apply, e.apply_symm_apply] at this
      · intro h y hy
        have := h (e y) (by rw [hm, e.symm_apply_apply]; exact hy)
        rwa [← hform, e.apply_symm_apply]) htt
    (fun x hx i => by
      have hx' := hL _ ((hm x).1 hx)
      have : x = (u⁻¹ * g) *ᵥ (g⁻¹ *ᵥ e.symm x) := by
        rw [mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ hg, Matrix.mul_one, ← he, e.apply_symm_apply]
      have e2 : ((t * t' : 𝓞 K) : K) * x i = ∑ j, ((t' : K) * (u⁻¹ * g) i j) * ((t : K) * (g⁻¹ *ᵥ e.symm x) j) := by
        conv_lhs => rw [this]
        simp only [mulVec, dotProduct, Finset.mul_sum]
        push_cast
        exact Finset.sum_congr rfl fun j _ => by simp only [← Finset.mul_sum]; ring
      rw [e2]
      exact sum_mem fun j _ => mul_mem (h2 i j) (hx' j))
    (fun j => by
      rw [hm, hes]
      choose c hc' using fun k => h1 k j
      have e2 : u *ᵥ (Pi.single j ((t * t' : 𝓞 K) : K)) = ∑ k, c k • ((t : K) • fun i => g i k) := by
        have : u = g * (g⁻¹ * u) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hg, Matrix.one_mul]
        funext i
        have h3 : (u *ᵥ (Pi.single j ((t * t' : 𝓞 K) : K))) i = u i j * ((t : K) * t') := by
          simp [mulVec_single]
        have h4 : u i j = ∑ k, g i k * (g⁻¹ * u) k j := by
          conv_lhs => rw [this]
          exact Matrix.mul_apply
        rw [h3, h4, Finset.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, hc', smul_eq_mul]
        ring
      rw [e2]
      exact sum_mem fun k _ => L.smul_mem _ (hc k))
  refine ⟨e, hform, s, hs, fun x hx i => ha _ (by rw [hm, e.symm_apply_apply]; exact hx) i, fun v hv => ?_⟩
  have := (hm _).1 (hb v hv)
  rwa [map_smul] at this

theorem exists_gen_pow {K : Type} [Field K] [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ∃ π : 𝓞 K, 𝔭.asIdeal ^ classNumber K = Ideal.span {π} := by
  have hI0 : 𝔭.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot
  have hp : (𝔭.asIdeal ^ classNumber K).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hI0 _)]
    have : (⟨𝔭.asIdeal ^ classNumber K, pow_mem hI0 _⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨𝔭.asIdeal, hI0⟩ ^ classNumber K := rfl
    rw [this, map_pow, classNumber]
    exact pow_card_eq_one
  exact ⟨_, (Ideal.span_singleton_generator _).symm⟩

variable {R : Ranks} (H : Host R)

theorem nonempty_isoK : Nonempty (Th.IsoK H (Tau R)) :=
  GlobalTheory.T.nonempty_isoKG_of_trace_positive H.K H.E (H.conj : H.E →+* H.E) (HostK.conjK H) (Tau R) (HostK.card_tau H) (fun _ => rfl)
    (UnusedSlot33.HK.conj_conj H) (HostK.trace_conj H) (HostK.trace_pos H)

theorem exists_int_mul_mem_invHalfDifferent (x : H.E) : ∃ N : ℤ, N ≠ 0 ∧ (N : H.E) * x ∈ H.AA0 := by
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ H.AA0, a ≠ 0 := by
    by_contra h
    push Not at h
    refine one_ne_zero (h 1 ((factMMUnimodular R H 1).2 fun y hy => ?_))
    rw [h y hy, map_zero, mul_zero, map_zero]
    exact zero_mem _
  obtain ⟨N, hN, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ H.E).2
    (Algebra.IsAlgebraic.isAlgebraic (x / a))).exists_integral_multiple
  refine ⟨N, hN, ?_⟩
  have h := (H.AA0 : Submodule (𝓞 H.E) H.E).smul_mem (⟨N • (x / a), hi⟩ : 𝓞 H.E) ha
  have e : (⟨N • (x / a), hi⟩ : 𝓞 H.E) • a = (N : H.E) * x := by
    change (N • (x / a)) * a = _
    rw [zsmul_eq_mul]
    field_simp
  rw [← e]
  exact h

def lat4 : Submodule (𝓞 H.K) (Fin 4 → H.E) :=
  Submodule.pi Set.univ fun _ => (H.AA0 : Submodule (𝓞 H.E) H.E).restrictScalars (𝓞 H.K)

theorem mem_fourCopiesInvHalfDifferent_iff (x : Fin 4 → H.E) : x ∈ lat4 H ↔ ∀ a, x a ∈ H.AA0 :=
  ⟨fun h a => h a trivial, fun h a _ => h a⟩

theorem fourCopiesInvHalfDifferent_fg : (lat4 H).FG := by
  refine Submodule.fg_pi fun _ => ?_
  have h1 : Module.Finite (𝓞 H.E) (H.AA0 : Submodule (𝓞 H.E) H.E) :=
    Module.Finite.iff_fg.2 (FractionalIdeal.fg_of_isNoetherianRing le_rfl H.AA0)
  have h2 : Module.Finite (𝓞 H.K) (H.AA0 : Submodule (𝓞 H.E) H.E) := Module.Finite.trans (𝓞 H.E) _
  exact Module.Finite.iff_fg.1 h2

theorem fourCopiesInvHalfDifferent_selfDual (x : Fin 4 → H.E) : x ∈ lat4 H ↔ ∀ y ∈ lat4 H,
    ∑ a, Algebra.trace H.K H.E (x a * H.conj (y a)) ∈ (algebraMap (𝓞 H.K) H.K).range := by
  rw [mem_fourCopiesInvHalfDifferent_iff]
  constructor
  · intro h y hy
    exact sum_mem fun a _ => (factMMUnimodular R H _).1 (h a) _ ((mem_fourCopiesInvHalfDifferent_iff H y).1 hy a)
  · intro h a
    refine (factMMUnimodular R H _).2 fun y hy => ?_
    have := h (Pi.single a y) ((mem_fourCopiesInvHalfDifferent_iff H _).2 fun b => by
      by_cases e : b = a
      · subst e
        rwa [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne e]
        exact (H.AA0 : Submodule (𝓞 H.E) H.E).zero_mem)
    rwa [Finset.sum_eq_single a (fun b _ e => by rw [Pi.single_eq_of_ne e, map_zero, mul_zero, map_zero]) (by simp),
      Pi.single_eq_same] at this

theorem exists_atP (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) : ∃ γ : Th.IsoK H (Tau R), Th.AtP γ p := by
  classical
  obtain ⟨γ⟩ := nonempty_isoK H
  obtain ⟨𝔭, α, β, hp𝔭, hα, hβ, hαβ⟩ := GlobalTheory.T.exists_prime_over_split_not_mem_conj R H p hp hs
  have hiso : ∀ x y, ∑ w, γ.g x w * HostK.conjK H (γ.g y w) = ∑ a, Algebra.trace H.K H.E (x a * H.conj (y a)) := fun x y => by
    apply (algebraMap H.K H.E).injective
    rw [← γ.isom, map_sum]
    exact Finset.sum_congr rfl fun w _ => map_mul _ _ _
  let L : Submodule (𝓞 H.K) (Fin 4 × Tau R → H.K) := (lat4 H).map (γ.g.toLinearMap.restrictScalars (𝓞 H.K))
  have hm : ∀ x, γ.g x ∈ L ↔ x ∈ lat4 H := fun x =>
    ⟨fun ⟨y, hy, e⟩ => (γ.g.injective e : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  obtain ⟨u, hu, s, hsp, h1, h2⟩ := exists_move H.K (HostK.conjK H) (Fin 4 × Tau R) p 𝔭 α β L (HostK.conjK_conjK H)
    (HostK.exists_norm_int H) hp hp𝔭 hα hβ hαβ ((fourCopiesInvHalfDifferent_fg H).map _)
    (by
      rw [eq_top_iff]
      rintro v -
      obtain ⟨x, rfl⟩ := γ.g.surjective v
      choose N hN hx using fun a => exists_int_mul_mem_invHalfDifferent H (x a)
      have h0 : ((∏ a, N a : ℤ) : H.K) ≠ 0 := Int.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => hN a)
      rw [← Submodule.smul_mem_iff _ h0, ← γ.g.map_smul]
      refine Submodule.subset_span ((hm _).2 ((mem_fourCopiesInvHalfDifferent_iff H _).2 fun a => ?_))
      have := (H.AA0 : Submodule (𝓞 H.E) H.E).smul_of_tower_mem (∏ b ∈ Finset.univ.erase a, N b) (hx a)
      rw [Pi.smul_apply, Algebra.smul_def, map_intCast, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a), Int.cast_mul, mul_assoc,
        ← zsmul_eq_mul]
      exact this)
    (fun v => by
      obtain ⟨x, rfl⟩ := γ.g.surjective v
      rw [hm, fourCopiesInvHalfDifferent_selfDual]
      constructor
      · rintro h _ ⟨y, hy, rfl⟩
        exact (hiso x y).symm ▸ h y hy
      · intro h y hy
        exact hiso x y ▸ h _ ((hm y).2 hy))
  refine ⟨⟨γ.g.trans u, fun x y => ?_⟩, fun x hx => ⟨s, hsp, h1 _ ((hm x).2 ((mem_fourCopiesInvHalfDifferent_iff H x).2 hx))⟩, fun v hv => ⟨s, hsp, fun a => ?_⟩⟩
  · rw [← hiso, ← hu, map_sum]
    exact Finset.sum_congr rfl fun w _ => (map_mul (algebraMap H.K H.E) (u (γ.g x) w) (HostK.conjK H (u (γ.g y) w))).symm
  · have h3 := h2 v hv
    rw [← γ.g.apply_symm_apply (u.symm v), ← γ.g.map_smul, hm, mem_fourCopiesInvHalfDifferent_iff] at h3
    have h4 := h3 a
    rwa [Pi.smul_apply, Algebra.smul_def, map_natCast] at h4

def conjVec : Set (Tau R → H.E) := {v | ∃ a ∈ H.AA0, v = fun τ : Tau R => H.sigmaOf (τ : R.GG) a}

def ellE (τ : Tau R) : Submodule (𝓞 H.E) H.E :=
  letI : DecidableEq (Tau R) := fun a b => Classical.propDecidable (a = b)
  (Submodule.span (𝓞 H.E) (conjVec H)).comap (LinearMap.single (𝓞 H.E) (fun _ : Tau R => H.E) τ)

theorem ellE_fg (τ : Tau R) : (ellE H τ).FG := by
  letI : DecidableEq (Tau R) := fun a b => Classical.propDecidable (a = b)
  obtain ⟨d, hd, hA⟩ := H.AA0.isFractional
  have hd0 : (d : H.E) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd
  let g := H.sigmaOf (τ : R.GG)
  have hg0 : g d ≠ 0 := (map_ne_zero g).2 hd0
  have hle : ellE H τ ≤ Submodule.span (𝓞 H.E) {(g d)⁻¹} := by
    intro s hs
    have h1 : Submodule.span (𝓞 H.E) (conjVec H) ≤
        (Submodule.span (𝓞 H.E) {(g d)⁻¹}).comap (LinearMap.proj (R := 𝓞 H.E) (φ := fun _ : Tau R => H.E) τ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := hA a ha
      refine Submodule.mem_span_singleton.2 ⟨⟨g b, b.isIntegral_coe.map (g : H.E →+* H.E).toIntAlgHom⟩, ?_⟩
      change g (algebraMap _ _ b) * (g d)⁻¹ = g a
      rw [hb, Algebra.smul_def, map_mul]
      change g d * g a * (g d)⁻¹ = g a
      field_simp
    have h2 := h1 hs
    simpa using h2
  exact Submodule.FG.of_le (Submodule.fg_span_singleton _) hle

theorem exists_dgen : ∃ cD, Th.IsDgen H (embT H) cD := by
  obtain ⟨M, hM, hφ, hs⟩ := GlobalTheory.T.exists_finite_extension_capitulation_complex H.E H.φ₀ (Tau R) (ellE H) (ellE_fg H)
  choose s hs using hs
  haveI : NumberField M := ⟨⟩
  letI : Algebra H.E M := (H.φ₀.codRestrict M hφ).toAlgebra
  have hal : ∀ x : H.E, ((algebraMap H.E M x : M) : ℂ) = H.φ₀ x := fun _ => rfl
  refine ⟨fun τ => s τ, M, inferInstance, fun τ x => hφ _, fun τ => ⟨s τ, rfl, ?_⟩⟩
  have hl : ∀ x : H.E, TaylorLogMetric.liftM M (H.φ₀ x) = algebraMap H.E M x := fun x => dif_pos (hφ x)
  have h1 : Th.mmM H (embT H) M =
      Submodule.span (𝓞 M) ((fun (v : Tau R → H.E) (i : Tau R) => algebraMap H.E M (v i)) '' conjVec H) := by
    unfold Th.mmM
    congr 1
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨a, ha, rfl⟩, funext fun τ => (hl _).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, funext fun τ => (hl _).symm⟩
  have h2 := @GlobalTheory.T.comap_single_span_algebraMap_numberField H.E M _ _ _ _ _ (Tau R) _ (fun a b => Classical.propDecidable (a = b)) (conjVec H) τ
  rw [← hs τ]
  unfold Th.ellT
  rw [h1]
  refine h2.trans ?_
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, Subtype.ext e.symm⟩

theorem nonempty_kapIn (γ₀ : Th.IsoK H (Tau R)) : Nonempty (Th.KapIn γ₀) := by
  classical
  have h2 : Th.SplitK H 2 := Or.inl rfl
  have hpp : ∀ p : ℕ, ∃ 𝔭 : HeightOneSpectrum (𝓞 H.K), p.Prime → Th.SplitK H p → (p : 𝓞 H.K) ∈ 𝔭.asIdeal := fun p => by
    by_cases h : p.Prime ∧ Th.SplitK H p
    · obtain ⟨𝔭, -, -, h1, -⟩ := GlobalTheory.T.exists_prime_over_split_not_mem_conj R H p h.1 h.2
      exact ⟨𝔭, fun _ _ => h1⟩
    · obtain ⟨𝔭, -⟩ := GlobalTheory.T.exists_prime_over_split_not_mem_conj R H 2 Nat.prime_two h2
      exact ⟨𝔭, fun a b => absurd ⟨a, b⟩ h⟩
  have hga : ∀ p : ℕ, ∃ γ : Th.IsoK H (Tau R), p.Prime → Th.SplitK H p → Th.AtP γ p := fun p => by
    by_cases h : p.Prime ∧ Th.SplitK H p
    · obtain ⟨γ, h1⟩ := exists_atP H p h.1 h.2
      exact ⟨γ, fun _ _ => h1⟩
    · exact ⟨γ₀, fun a b => absurd ⟨a, b⟩ h⟩
  choose pp hpp using hpp
  choose ga hga using hga
  choose pi hpi using fun p => exists_gen_pow (pp p)
  choose rt hrt using fun p => IsAlgClosed.exists_pow_nat_eq
    (H.φ₀ (((pi p : 𝓞 H.K) : H.K) : H.E) / H.φ₀ (H.conj (((pi p : 𝓞 H.K) : H.K) : H.E)))
    (n := 2 * classNumber H.K) (Nat.mul_pos two_pos (classNumber_pos H.K))
  exact ⟨⟨pp, hpp, pi, fun p _ _ => hpi p, ga, hga, rt, fun p _ _ => hrt p⟩⟩

end AmbEx

theorem exists_ambIn_ok {R : Ranks} (H : Host R) : ∃ J : AmbIn H, J.Ok := by
  obtain ⟨δ, L, ω₀, hδ, hL, ht⟩ := GlobalTheory.T.exists_periodPair_lattice_eq_lamOf R H
  obtain ⟨γ₀⟩ := AmbEx.nonempty_isoK H
  obtain ⟨gC, hgC⟩ := GlobalTheory.T.exists_complexLinear_extension_of_traceIsometry' H.K H.E H.conj (Tau R) H.φ₀ (embT H) (HostK.emb_conj H _) (fun _ => HostK.emb_conj H _)
    (HostK.embT_K H) (HostK.sum_embT H) γ₀
  obtain ⟨kc⟩ := AmbEx.nonempty_kapIn H γ₀
  obtain ⟨cD, hc⟩ := AmbEx.exists_dgen H
  exact ⟨⟨δ, ⟨L, hL, ω₀, ht, γ₀, gC, hgC, kc⟩, cD⟩, hδ, hc⟩

end GlobalTheory.Mem.Col2

end
end
