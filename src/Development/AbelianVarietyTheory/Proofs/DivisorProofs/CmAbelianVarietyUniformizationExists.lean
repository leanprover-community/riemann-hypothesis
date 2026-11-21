import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMultiplicationStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationModuleUnitDual
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex

section
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

noncomputable section

namespace GlobalTheory.CMEquiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isReal_res (σ : E →+* ℂ) : ComplexEmbedding.IsReal (σ.comp (maximalRealSubfield E).subtype) := by
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, Subfield.subtype_apply]
  rw [← IsCMField.complexEmbedding_complexConj, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def res (σ : E →+* ℂ) : FR E →+* ℝ := (isReal_res σ).embedding

theorem res_apply (σ : E →+* ℂ) (x : FR E) : ((res σ x : ℝ) : ℂ) = σ (x : E) :=
  ComplexEmbedding.IsReal.coe_embedding_apply _ x

theorem exists_ext (ψ : FR E →+* ℂ) : ∃ σ : E →+* ℂ, ∀ x : FR E, σ (x : E) = ψ x := by
  letI : Algebra (FR E) ℂ := ψ.toAlgebra
  let f : E →ₐ[FR E] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem eq_or_eq_conj (σ σ' : E →+* ℂ) (h : ∀ x : FR E, σ' (x : E) = σ (x : E)) :
    σ' = σ ∨ σ' = ComplexEmbedding.conjugate σ := by
  set c := IsCMField.complexConj E with hc
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra! H
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext H)
  have cc : ∀ z, c (c z) = z := IsCMField.complexConj_apply_apply E
  set α := y - c y with hα
  have hα0 : α ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hcα : c α = -α := by rw [hα, map_sub, cc]; ring
  have mem : ∀ z, c z = z → σ' z = σ z := fun z hz =>
    h ⟨z, (IsCMField.complexConj_eq_self_iff E z).1 hz⟩
  have hsq : σ' α ^ 2 = σ α ^ 2 := by
    rw [← map_pow, ← map_pow]; exact mem _ (by rw [map_pow, hcα]; ring)
  have dec : ∀ z, ∃ a b, c a = a ∧ c b = b ∧ z = a + b * α ∧ c z = a - b * α := by
    intro z
    refine ⟨(z + c z) / 2, (z - c z) / (2 * α), ?_, ?_, ?_, ?_⟩
    · rw [map_div₀, map_add, cc, map_ofNat]; ring
    · rw [map_div₀, map_sub, cc, map_mul, map_ofNat, hcα]
      field_simp
      ring
    · field_simp; ring
    · field_simp; ring
  have hsq' : (σ' α - σ α) * (σ' α + σ α) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hsq' with h1 | h1
  · left
    ext z
    obtain ⟨a, b, ha, hb, hz, -⟩ := dec z
    rw [hz, map_add, map_add, map_mul, map_mul, mem a ha, mem b hb, sub_eq_zero.1 h1]
  · right
    ext z
    obtain ⟨a, b, ha, hb, hz, hcz⟩ := dec z
    rw [ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj, ← hc, hcz, hz,
      map_add, map_sub, map_mul, map_mul, mem a ha, mem b hb, eq_neg_of_add_eq_zero_left h1]
    ring

theorem cmType_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) :
    ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ I) (e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)),
      ∀ j (x : FR E), ((e' j x : ℝ) : ℂ) = φ (e j) (x : E) := by
  have hRC : Function.Bijective (fun τ : FR E →+* ℝ => Complex.ofRealHom.comp τ) := by
    constructor
    · intro τ τ' hτ
      ext x
      exact Complex.ofReal_injective (RingHom.congr_fun hτ x)
    · intro ψ
      obtain ⟨σ, hσ⟩ := exists_ext ψ
      refine ⟨res σ, RingHom.ext fun x => ?_⟩
      simp only [RingHom.coe_comp, Function.comp_apply, Complex.ofRealHom_eq_coe]
      rw [res_apply, hσ]
  let eRC := Equiv.ofBijective _ hRC
  let e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ) :=
    (Fintype.equivFinOfCardEq (Embeddings.card (FR E) ℂ)).symm.trans eRC.symm
  have hb : Function.Bijective (fun i => res (φ i)) := by
    constructor
    · intro i j hij
      have hx : ∀ x : FR E, φ j (x : E) = φ i (x : E) := fun x => by
        rw [← res_apply, ← res_apply]
        exact congrArg (fun τ : FR E →+* ℝ => ((τ x : ℝ) : ℂ)) hij.symm
      obtain ⟨k, -, hk⟩ := hφ (φ j)
      exact (hk i (eq_or_eq_conj (φ i) (φ j) hx)).trans (hk j (Or.inl rfl)).symm
    · intro τ
      obtain ⟨σ, hσ⟩ := exists_ext (Complex.ofRealHom.comp τ)
      obtain ⟨i, hi, -⟩ := hφ σ
      refine ⟨i, RingHom.ext fun x => Complex.ofReal_injective ?_⟩
      rw [res_apply]
      rcases hi with h | h
      · rw [← h, hσ]; rfl
      · have h' : φ i = ComplexEmbedding.conjugate σ := by
          ext z
          rw [ComplexEmbedding.conjugate_coe_eq, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
        rw [h', ComplexEmbedding.conjugate_coe_eq, hσ]
        simp
  let b := Equiv.ofBijective _ hb
  refine ⟨e'.trans b.symm, e', fun j x => ?_⟩
  have hj : res (φ ((e'.trans b.symm) j)) = e' j := b.apply_symm_apply (e' j)
  rw [← hj, res_apply]

end GlobalTheory.CMEquiv
end
end

open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_real_embedding_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ I) (e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)),
      ∀ j (x : FR E), ((e' j x : ℝ) : ℂ) = φ (e j) (x : E) := by
  atlas_forward_decl GlobalTheory.CMEquiv.cmType_equiv
end

section
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMLatticeDiscrete

theorem cmLattice_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E), (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) → DiscreteTopology Λ := by
  intro E _ _ _ I _ φ hφ n e L hL Λ hΛ
  obtain ⟨N, hNpos, hN⟩ := hL

  have hfin : {w : Fin n → ℂ | w ∈ Λ ∧ ‖w‖ ≤ 1}.Finite := by
    have hS := NumberField.Embeddings.finite_of_norm_le E ℂ ((N : ℝ) * 1)
    have hT : {x : E | x ∈ L ∧ ∀ i, ‖φ i x‖ ≤ 1}.Finite := by
      refine (hS.image (fun y : E ↦ y / (N : E))).subset ?_
      rintro x ⟨hxL, hxb⟩
      refine ⟨(N : E) * x, ⟨hN x hxL, fun σ ↦ ?_⟩, ?_⟩
      · obtain ⟨i, hi, -⟩ := hφ σ
        have hb : ‖σ x‖ ≤ 1 := by
          rcases hi with h | h
          · rw [h]; exact hxb i
          · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]; exact hxb i
        rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N)
      · have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
        simp only
        field_simp
    refine (hT.image (fun x : E ↦ fun j ↦ φ (e j) x)).subset ?_
    rintro w ⟨hwΛ, hwb⟩
    obtain ⟨x, hxL, rfl⟩ := (hΛ w).1 hwΛ
    refine ⟨x, ⟨hxL, fun i ↦ ?_⟩, rfl⟩
    have := norm_le_pi_norm (fun j ↦ φ (e j) x) (e.symm i)
    simp only [Equiv.apply_symm_apply] at this
    exact this.trans hwb
  apply discreteTopology_of_isOpen_singleton_zero
  set F : Set (Fin n → ℂ) := {w | w ∈ Λ ∧ ‖w‖ ≤ 1} \ {0}
  have hF : IsClosed F := (hfin.subset Set.diff_subset).isClosed
  have hU : IsOpen (Metric.ball (0 : Fin n → ℂ) 1 ∩ Fᶜ) := Metric.isOpen_ball.inter hF.isOpen_compl
  convert hU.preimage continuous_subtype_val using 1
  ext ⟨w, hw⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
    Set.mem_compl_iff, F, Set.mem_diff, Set.mem_setOf_eq, not_and, not_not]
  constructor
  · intro h
    have h0 : w = 0 := by simpa using congrArg Subtype.val h
    subst h0
    simp
  · rintro ⟨h1, h2⟩
    have : w = 0 := h2 ⟨hw, h1.le⟩
    exact Subtype.ext this

end GlobalTheory.CMLatticeDiscrete
end

open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_image_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E), (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) → DiscreteTopology Λ := by
  atlas_forward_decl GlobalTheory.CMLatticeDiscrete.cmLattice_discrete
end

section
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMSpan

open ComplexConjugate

theorem functional_single {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℝ] ℝ) (j : Fin n) (z : ℂ) :
    ((f (Pi.single j z) : ℝ) : ℂ) =
      (((f (Pi.single j 1) : ℂ) - Complex.I * (f (Pi.single j Complex.I) : ℂ)) / 2) * z +
      conj (((f (Pi.single j 1) : ℂ) - Complex.I * (f (Pi.single j Complex.I) : ℂ)) / 2) * conj z := by
  have hz : (Pi.single j z : Fin n → ℂ) =
      z.re • (Pi.single j (1:ℂ) : Fin n → ℂ) + z.im • (Pi.single j Complex.I : Fin n → ℂ) := by
    ext k
    by_cases h : k = j
    · subst h; simp [Complex.ext_iff]
    · simp [h]
  rw [hz, map_add, map_smul, map_smul]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  apply Complex.ext <;> simp <;> ring

theorem conjugate_ne_self {E : Type} [Field E] [IsTotallyComplex E] (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ ≠ σ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal σ (ComplexEmbedding.isReal_iff.2 h)

end GlobalTheory.CMSpan

namespace GlobalTheory.CMSpan

open ComplexConjugate

theorem cmType_embeddings_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type}
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    Function.Injective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
  have hTC : IsTotallyComplex E := IsCMField.to_isTotallyComplex
  rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl ((hφ (φ i)).unique (Or.inl rfl) (Or.inl h))
  · have hij : i = j := (hφ (φ i)).unique (Or.inl rfl) (Or.inr h)
    subst hij
    exact absurd h.symm (conjugate_ne_self (φ i))
  · have hij : j = i := (hφ (φ j)).unique (Or.inl rfl) (Or.inr h.symm)
    subst hij
    exact absurd h (conjugate_ne_self (φ j))
  · have h' : φ i = φ j := by
      refine RingHom.ext fun x => ?_
      have := congrArg (fun σ : E →+* ℂ => conj (σ x)) h
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
    exact congrArg Sum.inr ((hφ (φ i)).unique (Or.inl rfl) (Or.inl h'))

theorem span_real_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E),
      (∃ N : ℕ, 0 < N ∧ ∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) →
      Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ := by
  intro E _ _ _ I _ φ hφ n e L hL Λ hΛ
  classical
  obtain ⟨N, hN, hNL⟩ := hL
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)

  have hkill : ∀ x : E, f (fun j ↦ φ (e j) x) = 0 := by
    intro x
    obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
    let z : 𝓞 E := ⟨y • x, hyint x (Finset.mem_singleton_self x)⟩
    have hmem : (fun j ↦ φ (e j) ((N : E) * algebraMap (𝓞 E) E z)) ∈ Λ :=
      (hΛ _).2 ⟨_, hNL z, rfl⟩
    have h0 := hfk (Submodule.subset_span hmem)
    rw [LinearMap.mem_ker] at h0
    have hsm : (fun j ↦ φ (e j) ((N : E) * algebraMap (𝓞 E) E z)) =
        ((N : ℝ) * (y : ℝ)) • (fun j ↦ φ (e j) x) := by
      ext j
      simp [z, zsmul_eq_mul, Complex.real_smul, mul_assoc]
    rw [hsm, map_smul, smul_eq_mul] at h0
    have hNy : (N : ℝ) * (y : ℝ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hy0)
    exact (mul_eq_zero.1 h0).resolve_left hNy

  set c : Fin n → ℂ := fun j =>
    ((f (Pi.single j 1) : ℂ) - Complex.I * (f (Pi.single j Complex.I) : ℂ)) / 2 with hc
  have hexp : ∀ w : Fin n → ℂ, ((f w : ℝ) : ℂ) = ∑ j, (c j * w j + conj (c j) * conj (w j)) := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => functional_single f j (w j)

  let ψ : I ⊕ I → (E →* ℂ) := fun a => ((Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)) a : E →+* ℂ) : E →* ℂ)
  have hψ : Function.Injective ψ := by
    intro a b h
    apply cmType_embeddings_injective φ hφ
    exact RingHom.ext fun x => DFunLike.congr_fun h x
  have hli := (linearIndependent_monoidHom E ℂ).comp ψ hψ
  let g : I ⊕ I → ℂ := Sum.elim (fun i => c (e.symm i)) (fun i => conj (c (e.symm i)))
  have hg : ∑ a, g a • (fun x => ψ a x) = 0 := by
    funext x
    have hx := hexp (fun j ↦ φ (e j) x)
    rw [hkill x, Complex.ofReal_zero] at hx
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fintype.sum_sum_type,
      g, ψ, Sum.elim_inl, Sum.elim_inr, MonoidHom.coe_coe, ComplexEmbedding.conjugate_coe_eq]
    rw [← Finset.sum_add_distrib, ← e.sum_comp]
    simpa using hx.symm
  have hc0 : ∀ j, c j = 0 := by
    intro j
    have := Fintype.linearIndependent_iff.1 hli g hg (Sum.inl (e j))
    simpa [g] using this
  apply hf0
  refine LinearMap.ext fun w => ?_
  have hw := hexp w
  simp only [hc0, zero_mul, map_zero, add_zero, Finset.sum_const_zero] at hw
  simpa using hw

end GlobalTheory.CMSpan
end

open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_image_spans_real : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E), (∃ N : ℕ, 0 < N ∧ ∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) →
      Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ := by
  atlas_forward_decl GlobalTheory.CMSpan.span_real_eq_top
end

section
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CxDescent

noncomputable def imForm (n : ℕ) (ρ : ℝ) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v u => (∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (u j)).im)
    (by intro v v' u; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by intro c v u; simp [Finset.mul_sum, Complex.mul_im, Complex.mul_re]; exact Finset.sum_congr rfl (fun i _ => by ring))
    (by intro v u u'; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by intro c v u; simp [Finset.mul_sum, Complex.mul_im, Complex.mul_re]; exact Finset.sum_congr rfl (fun i _ => by ring))

theorem imForm_apply (n : ℕ) (ρ : ℝ) (v u : Fin n → ℂ) :
    imForm n ρ v u = (∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (u j)).im := rfl

theorem imForm_nondeg (n : ℕ) (ρ : ℝ) (hρ : ρ ≠ 0) (v : Fin n → ℂ)
    (h : ∀ u, imForm n ρ v u = 0) : v = 0 := by
  have h1 := h (Complex.I • v)
  rw [imForm_apply, Complex.im_sum] at h1
  have hterm : ∀ j, ((ρ : ℂ) * v j * starRingEnd ℂ ((Complex.I • v) j)).im = -ρ * Complex.normSq (v j) := by
    intro j
    simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply]; ring
  simp_rw [hterm, ← Finset.mul_sum] at h1
  have hs : ∑ j, Complex.normSq (v j) = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (neg_eq_zero.mp h2) hρ
    · exact h2
  funext j
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))).mp hs j (Finset.mem_univ _)
  simpa using this

theorem mem_range_of_int_pairing (E : Type) [Field E] [NumberField E] (n : ℕ)
    (Φ : E →ₗ[ℚ] (Fin n → ℂ)) (L : Set E) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hspan : Submodule.span ℝ (Φ '' L) = ⊤)
    (hrat : ∀ x y : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ y j)).im = q)
    (w : Fin n → ℂ)
    (hw : ∀ x ∈ L, ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m) :
    ∃ x : E, w = Φ x := by
  set B := imForm n ρ with hB
  obtain ⟨t, htsub, htspan, htli⟩ := exists_linearIndependent ℝ (Φ '' L)
  have htfin : t.Finite := htli.setFinite
  haveI : Fintype t := htfin.fintype
  have hts : Submodule.span ℝ t = ⊤ := htspan.trans hspan

  have hvan : ∀ v, (∀ k : t, B v k = 0) → v = 0 := by
    intro v hv
    apply imForm_nondeg n ρ hρ v
    intro u
    have hle : Submodule.span ℝ t ≤ LinearMap.ker (B v) :=
      Submodule.span_le.mpr (fun k hk => by simpa using hv ⟨k, hk⟩)
    have hu : u ∈ LinearMap.ker (B v) := hle (hts ▸ Submodule.mem_top)
    simpa using hu

  have hpre : ∀ k : t, ∃ x ∈ L, Φ x = k := fun k => htsub k.2
  choose xk hxkL hxk using hpre
  choose q hq using hrat
  let Q : Matrix t t ℚ := fun k j => q (xk k) (xk j)
  have hBQ : ∀ k j : t, B k j = (Q k j : ℝ) := by
    intro k j
    rw [hB, imForm_apply, ← hxk k, ← hxk j]; exact hq _ _
  choose m hm using fun j : t => hw (xk j) (hxkL j)
  have hBm : ∀ j : t, B w j = (m j : ℝ) := by
    intro j; rw [hB, imForm_apply, ← hxk j]; exact hm j

  have hinj : Function.Injective (Matrix.vecMulLinear Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hz : ∑ k, (c k : ℝ) • (k : Fin n → ℂ) = 0 := by
      apply hvan
      intro j
      have hj := congrFun hc j
      simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Pi.zero_apply] at hj
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hBQ]
      exact_mod_cast hj
    have := (Fintype.linearIndependent_iff.mp htli) (fun k => (c k : ℝ)) hz
    funext k; exact_mod_cast this k
  have hsurj := (LinearMap.injective_iff_surjective.mp hinj)
  obtain ⟨c, hc⟩ := hsurj (fun j => (m j : ℚ))
  refine ⟨∑ k, c k • xk k, ?_⟩
  rw [← sub_eq_zero]
  apply hvan
  intro j
  have hj := congrFun hc j
  simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct] at hj
  rw [map_sub, LinearMap.sub_apply, hBm, map_sum, map_sum, LinearMap.sum_apply]
  simp only [map_smul, ← Rat.cast_smul_eq_qsmul ℝ, hxk, map_smul, LinearMap.smul_apply, smul_eq_mul, hBQ]
  rw [sub_eq_zero]
  exact_mod_cast hj.symm

end GlobalTheory.CxDescent
end

open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_dual_integral_image : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Φ : E →ₗ[ℚ] (Fin n → ℂ)) (L : Set E) (ρ : ℝ), ρ ≠ 0 →
    Submodule.span ℝ (Φ '' L) = ⊤ →
    (∀ x y : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ y j)).im = q) →
    ∀ w : Fin n → ℂ, (∀ x ∈ L, ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m) → ∃ x : E, w = Φ x := by
  atlas_forward_decl GlobalTheory.CxDescent.mem_range_of_int_pairing
end

section
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMTrace

theorem sum_embeddings_cmType {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (g : (E →+* ℂ) → ℂ) :
    ∑ σ : E →+* ℂ, g σ = ∑ i, (g (φ i) + g (ComplexEmbedding.conjugate (φ i))) := by
  have hnr : ∀ i, ComplexEmbedding.conjugate (φ i) ≠ φ i := fun i h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  let f : I ⊕ I → (E →+* ℂ) := Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))
  have hf : Function.Bijective f := by
    constructor
    · rintro (i | i) (j | j) h
      · simp only [f, Sum.elim_inl] at h
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl h)]
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at h
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        have hi := hk i (Or.inl rfl)
        have hj := hk j (Or.inr h)
        subst hi; subst hj
        exact absurd h.symm (hnr _)
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at h
        obtain ⟨k, _, hk⟩ := hφ (φ j)
        have hi := hk i (Or.inr h.symm)
        have hj := hk j (Or.inl rfl)
        subst hi; subst hj
        exact absurd h (hnr _)
      · simp only [f, Sum.elim_inr] at h
        have h' : φ i = φ j := by
          have := congrArg ComplexEmbedding.conjugate h
          simpa using this
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl h')]
    · intro σ
      obtain ⟨i, hi, _⟩ := hφ σ
      rcases hi with h | h
      · exact ⟨Sum.inl i, h.symm⟩
      · exact ⟨Sum.inr i, h.symm⟩
  rw [← Fintype.sum_bijective f hf (g ∘ f) g (fun _ => rfl), Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

theorem trace_eq_sum_re {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (w : E) :
    ((Algebra.trace ℚ E w : ℚ) : ℝ) = ∑ i, 2 * (φ i w).re := by
  have h1 : ((Algebra.trace ℚ E w : ℚ) : ℂ) = ∑ σ : E →ₐ[ℚ] ℂ, σ w := by
    rw [← trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ)]
    simp
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ w = ∑ σ : E →+* ℂ, σ w :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl))
  have h3 := sum_embeddings_cmType φ hφ (fun σ => σ w)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h1, h2, h3]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  push_cast; ring

end GlobalTheory.CMTrace

open GlobalTheory.CMTrace in
theorem GlobalTheory.trace_riemannForm_eq_im : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (t₁ : E) (ρ : ℝ), (∀ i, φ i t₁ = -Complex.I * ((ρ / 2 : ℝ) : ℂ)) →
    ∀ (a : FR E) (x y : E), ((Algebra.trace ℚ E ((a : E) * t₁ * x * bar y) : ℚ) : ℝ) =
      (∑ j, (φ (e j) (a : E) * (ρ : ℂ)) * φ (e j) x * starRingEnd ℂ (φ (e j) y)).im := by
  intro E _ _ _ I _ φ hφ n e t₁ ρ ht a x y
  rw [trace_eq_sum_re φ hφ, Complex.im_sum, Equiv.sum_comp e (fun i => ((φ i (a : E) * (ρ : ℂ)) * φ i x * starRingEnd ℂ (φ i y)).im)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha : starRingEnd ℂ (φ i (a : E)) = φ i (a : E) := by
    rw [← IsCMField.complexEmbedding_complexConj]
    congr 1
    exact (IsCMField.complexConj E).commutes a
  have hre : φ i (a : E) = ((φ i (a : E)).re : ℂ) := (Complex.conj_eq_iff_re.1 ha).symm
  have hb : φ i (bar y) = starRingEnd ℂ (φ i y) := IsCMField.complexEmbedding_complexConj E (φ i) y
  rw [map_mul, map_mul, map_mul, hb, ht i, hre]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring
end

open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_trace_form_imaginary_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (t₁ : E) (ρ : ℝ), (∀ i, φ i t₁ = -Complex.I * ((ρ / 2 : ℝ) : ℂ)) →
    ∀ (a : FR E) (x y : E), ((Algebra.trace ℚ E ((a : E) * t₁ * x * bar y) : ℚ) : ℝ) =
      (∑ j, (φ (e j) (a : E) * (ρ : ℂ)) * φ (e j) x * starRingEnd ℂ (φ (e j) y)).im := by
  atlas_forward_decl GlobalTheory.trace_riemannForm_eq_im
end

section
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.AntiInvFrac

theorem fracId_of_antiInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E) (ξ : E), ξ ≠ 0 → bar ξ = -ξ →
    (∀ m ∈ M, bar m = -m) → IsUnit M → ∃ 𝔠 : FracId (FR E), ∀ a : FR E, a ∈ 𝔠.elt ↔ (a : E) * ξ ∈ M := by
  intro E _ _ _ M ξ hξ hbξ hM hU
  let f : FR E →ₗ[OF E] E :=
    { toFun := fun a ↦ (a : E) * ξ
      map_add' := fun a b ↦ by push_cast; ring
      map_smul' := fun r a ↦ by
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (OF E) (FR E) E]
        rw [show ∀ x : FR E, algebraMap (FR E) E x = (x : E) from fun _ ↦ rfl]
        push_cast; ring }
  have hf : Function.Injective f := fun a b h ↦ by
    have h' : (a : E) * ξ = (b : E) * ξ := h
    exact Subtype.ext (mul_right_cancel₀ hξ h')
  let S : Submodule (OF E) (FR E) := M.comap f
  have hle : M ≤ LinearMap.range f := fun m hm ↦ by
    have hfix : bar (m / ξ) = m / ξ := by
      simp only [bar, map_div₀] at hbξ ⊢
      rw [show IsCMField.complexConj E m = -m from hM m hm, hbξ, neg_div_neg_eq]
    refine ⟨⟨m / ξ, (IsCMField.complexConj_eq_self_iff E _).1 hfix⟩, ?_⟩
    show (m / ξ) * ξ = m
    exact div_mul_cancel₀ m hξ
  have hmap : S.map f = M := by
    rw [Submodule.map_comap_eq, inf_eq_right.2 hle]
  have hMfg : M.FG := Submodule.fg_of_isUnit hU
  have hSfg : S.FG := Submodule.fg_of_fg_map_injective f hf (hmap ▸ hMfg)
  have hM0 : M ≠ ⊥ := by
    intro h
    have : IsUnit (0 : Submodule (OF E) E) := by rw [← Submodule.zero_eq_bot] at h; rw [← h]; exact hU
    exact not_isUnit_zero this
  have hS0 : S ≠ ⊥ := by
    intro h
    apply hM0
    rw [← hmap, h, Submodule.map_bot]
  let I : FractionalIdeal (nonZeroDivisors (𝓞 (FR E))) (FR E) := ⟨S, FractionalIdeal.isFractional_of_fg hSfg⟩
  have hI : I ≠ 0 := by
    intro h
    apply hS0
    have := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 (FR E))) (FR E) ↦ (J : Submodule (𝓞 (FR E)) (FR E))) h
    simpa [I] using this
  refine ⟨Units.mk0 I hI, fun a ↦ ?_⟩
  show a ∈ S ↔ _
  rfl

end GlobalTheory.AntiInvFrac
end

open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_skew_ideal_fractional_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E) (ξ : E), ξ ≠ 0 → bar ξ = -ξ →
    (∀ m ∈ M, bar m = -m) → IsUnit M → ∃ 𝔠 : FracId (FR E), ∀ a : FR E, a ∈ 𝔠.elt ↔ (a : E) * ξ ∈ M := by
  atlas_forward_decl GlobalTheory.AntiInvFrac.fracId_of_antiInv
end

section
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatTorus

theorem cm_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) : ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ I) (e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)),
      ∀ j (x : FR E), ((e' j x : ℝ) : ℂ) = φ (e j) (x : E) :=
  GlobalTheory.T.cm_type_real_embedding_equiv E I φ hφ

theorem lat_discrete (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E)
    (hL : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) (Λ : Submodule ℤ (Fin n → ℂ))
    (hΛ : ∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) : DiscreteTopology Λ :=
  GlobalTheory.T.cm_lattice_image_discrete E I φ hφ n e L hL Λ hΛ

theorem lat_span (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E)
    (hL : ∃ N : ℕ, 0 < N ∧ ∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) (Λ : Submodule ℤ (Fin n → ℂ))
    (hΛ : ∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) :
    Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ :=
  GlobalTheory.T.cm_lattice_image_spans_real E I φ hφ n e L hL Λ hΛ

theorem dual_descent (E : Type) [Field E] [NumberField E] (n : ℕ) (Φ : E →ₗ[ℚ] (Fin n → ℂ)) (L : Set E) (ρ : ℝ)
    (hρ : ρ ≠ 0) (hspan : Submodule.span ℝ (Φ '' L) = ⊤)
    (hrat : ∀ x y : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ y j)).im = q) (w : Fin n → ℂ)
    (hw : ∀ x ∈ L, ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m) : ∃ x : E, w = Φ x :=
  GlobalTheory.T.cm_lattice_dual_integral_image E n Φ L ρ hρ hspan hrat w hw

theorem trace_eq_im (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (n : ℕ) (e : Fin n ≃ I) (t₁ : E) (ρ : ℝ) (ht₁ : ∀ i, φ i t₁ = -Complex.I * ((ρ / 2 : ℝ) : ℂ))
    (a : FR E) (x y : E) :
    ((Algebra.trace ℚ E ((a : E) * t₁ * x * bar y) : ℚ) : ℝ) =
      (∑ j, (φ (e j) (a : E) * (ρ : ℂ)) * φ (e j) x * starRingEnd ℂ (φ (e j) y)).im :=
  GlobalTheory.T.cm_trace_form_imaginary_part E I φ hφ n e t₁ ρ ht₁ a x y

theorem exists_fracId (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E) (ξ : E) (hξ : ξ ≠ 0)
    (hbar : bar ξ = -ξ) (hM : ∀ m ∈ M, bar m = -m) (hU : IsUnit M) :
    ∃ 𝔠 : FracId (FR E), ∀ a : FR E, a ∈ 𝔠.elt ↔ (a : E) * ξ ∈ M :=
  GlobalTheory.T.cm_skew_ideal_fractional_ideal E M ξ hξ hbar hM hU

theorem trInt_of_integral {E : Type} [Field E] [NumberField E] {x : E} (hx : IsIntegral ℤ x) : TrInt x := by
  have h := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := E) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by rw [← hn]; simp⟩

end GlobalTheory.LatTorus

open GlobalTheory.LatTorus in

theorem GlobalTheory.LatTorus.exists_unif_of_lattice : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∃ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
        ∀ i, U.h i ≠ 0 ∧ IsAlgebraic ℚ ((U.h i : ℂ) * (Real.sqrt d : ℝ)) := by
  intro K _ _ d δ io _ hd hδ E _ _ _ _ I _ φ hφ hio c y hc
  obtain ⟨N, hN, hNO, hNint⟩ := GlobalTheory.T.exists_denominator_of_adelic_lattice E c hc y
  obtain ⟨hU, hML⟩ := GlobalTheory.T.polarization_module_unit_dual E (latMod c y) ⟨N, hN, hNO, hNint⟩
  obtain ⟨e, e', he'⟩ := cm_equiv E I φ hφ
  have hsd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hsq : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have ht : io δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  obtain ⟨s, hs, hts⟩ : ∃ s : ℤ, s ^ 2 = 1 ∧ io δ = (s : ℂ) * Complex.I * (Real.sqrt d : ℝ) := by
    have h0 : (io δ - Complex.I * (Real.sqrt d : ℝ)) * (io δ + Complex.I * (Real.sqrt d : ℝ)) = 0 := by
      linear_combination ht - Complex.I ^ 2 * hsq - (d : ℂ) * Complex.I_sq
    rcases mul_eq_zero.1 h0 with h | h
    · exact ⟨1, by norm_num, by push_cast; linear_combination h⟩
    · exact ⟨-1, by norm_num, by push_cast; linear_combination h⟩
  set r : ℝ := 2 / Real.sqrt d with hr
  set ξ₁ : E := -((s : E) * algebraMap K E δ) / (d : E) with hξ₁
  have hne : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  have hs' : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have hφξ : ∀ i, φ i ξ₁ = -Complex.I * ((r / 2 : ℝ) : ℂ) := by
    intro i
    have h1 : φ i (algebraMap K E δ) = io δ := by rw [← hio i]; rfl
    simp only [hξ₁, map_div₀, map_neg, map_mul, map_intCast, map_natCast, h1, hts, hr]
    push_cast
    rw [← hsq]
    field_simp
    linear_combination (-1 : ℂ) * hs'
  obtain ⟨σ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨i₀, -, -⟩ := hφ σ₀
  have hr0 : 0 < r := div_pos two_pos hsd
  have hξ0 : ξ₁ ≠ 0 := fun h => by
    have h2 := hφξ i₀
    rw [h, map_zero] at h2
    have h3 : ((r / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (half_pos hr0).ne'
    exact h3 (by simpa [Complex.I_ne_zero] using h2.symm)
  have hbar : bar ξ₁ = -ξ₁ := (φ i₀).injective (by
    show φ i₀ (IsCMField.complexConj E ξ₁) = _
    rw [IsCMField.complexEmbedding_complexConj, hφξ, map_neg, hφξ, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring)
  obtain ⟨𝔠, h𝔠⟩ := exists_fracId E (polMod (latMod c y)) ξ₁ hξ0 hbar (fun m hm => hm.1) hU
  have hδint : IsIntegral ℤ (algebraMap K E δ) := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), by monicity!, ?_⟩
    have : (algebraMap K E δ) ^ 2 = -(d : E) := by rw [← map_pow, hδ]; simp
    simp [Polynomial.eval₂_add, this]
  set c₀ : FR E := ((N ^ 2 * d : ℕ) : FR E) with hc₀
  have hc₀E : (c₀ : E) * ξ₁ = -((N : E) ^ 2 * (s : E) * algebraMap K E δ) := by
    have hd0 : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [hc₀, hξ₁]
    push_cast
    field_simp
  have hc₀mem : c₀ ∈ 𝔠.elt := by
    rw [h𝔠]
    refine ⟨?_, fun x hx z hz => ?_⟩
    · simp only [hc₀]; push_cast
      show IsCMField.complexConj E _ = _
      simp only [map_mul, map_pow, map_natCast]
      change _ * bar ξ₁ = _
      rw [hbar]; ring
    · apply trInt_of_integral
      rw [hc₀E]
      have h1 := hNint x hx
      have h2 := map_isIntegral_int (IsCMField.complexConj E) (hNint z hz)
      have e1 : -((N : E) ^ 2 * (s : E) * algebraMap K E δ) * x * bar z =
          -((s : E) * algebraMap K E δ * ((N : E) * x) * IsCMField.complexConj E ((N : E) * z)) := by
        simp only [bar, map_mul, map_natCast]; ring
      rw [e1]
      exact (((isIntegral_algebraMap (R := ℤ) (x := s)).mul hδint).mul h1 |>.mul h2).neg
  let Φ : E →ₗ[ℚ] (Fin (Module.finrank ℚ (FR E)) → ℂ) := LinearMap.pi fun j => (φ (e j)).toRatAlgHom.toLinearMap
  have hΦ : ∀ x j, Φ x j = φ (e j) x := fun _ _ => rfl
  let Λ : Submodule ℤ (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    ((latMod c y).restrictScalars ℤ).map (Φ.restrictScalars ℤ)
  have hΛ : ∀ w, w ∈ Λ ↔ ∃ x ∈ latMod c y, w = fun j ↦ φ (e j) x := by
    intro w
    simp only [Λ, Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.coe_restrictScalars]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  have hdisc := lat_discrete E I φ hφ _ e (latMod c y) ⟨N, hN, hNint⟩ Λ hΛ
  have hfull := lat_span E I φ hφ _ e (latMod c y) ⟨N, hN, hNO⟩ Λ hΛ
  have hstab : ∀ (a : 𝓞 (FR E)), ∀ w ∈ Λ, (fun i ↦ (e' i (a : FR E) : ℂ) * w i) ∈ Λ := by
    intro a w hw
    obtain ⟨x, hx, rfl⟩ := (hΛ w).1 hw
    refine (hΛ _).2 ⟨a • x, (latMod c y).smul_mem a hx, ?_⟩
    funext j
    rw [he', Algebra.smul_def, map_mul]
    rfl
  have htr : ∀ (a : FR E) (x z : E), ((Algebra.trace ℚ E ((a : E) * ξ₁ * x * bar z) : ℚ) : ℝ) =
      (∑ j, ((e' j a * r : ℝ) : ℂ) * φ (e j) x * starRingEnd ℂ (φ (e j) z)).im := by
    intro a x z
    rw [trace_eq_im E I φ hφ _ e ξ₁ r hφξ a x z]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_mul, he']
  have hint : ∀ a ∈ 𝔠.elt, ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e' i a * (fun _ => r) i : ℝ) : ℂ) * l i * starRingEnd ℂ (l' i)).im = n := by
    intro a ha l hl l' hl'
    obtain ⟨x, hx, rfl⟩ := (hΛ l).1 hl
    obtain ⟨z, hz, rfl⟩ := (hΛ l').1 hl'
    obtain ⟨n, hn⟩ := ((h𝔠 a).1 ha).2 x hx z hz
    refine ⟨n, ?_⟩
    rw [← htr, hn]
    simp
  have he'c₀ : ∀ j, e' j c₀ = ((N ^ 2 * d : ℕ) : ℝ) := fun j => by rw [hc₀, map_natCast]
  set ρ : ℝ := ((N ^ 2 * d : ℕ) : ℝ) * r with hρ
  have hρ0 : ρ ≠ 0 := by
    have : (0 : ℝ) < ((N ^ 2 * d : ℕ) : ℝ) := by positivity
    exact (mul_pos this hr0).ne'
  have hsum : ∀ (v : Fin (Module.finrank ℚ (FR E)) → ℂ) (x : E),
      (∑ j, ((e' j c₀ * r : ℝ) : ℂ) * v j * starRingEnd ℂ (φ (e j) x)) =
        ∑ j, (ρ : ℂ) * v j * starRingEnd ℂ (Φ x j) := fun v x =>
    Finset.sum_congr rfl fun j _ => by rw [he'c₀, hΦ]
  have hdual : ∀ w : Fin (Module.finrank ℚ (FR E)) → ℂ, (∀ a ∈ 𝔠.elt, ∀ l ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e' i a * (fun _ => r) i : ℝ) : ℂ) * w i * starRingEnd ℂ (l i)).im = n) → w ∈ Λ := by
    intro w hw
    have hspan : Submodule.span ℝ (Φ '' (latMod c y : Set E)) = ⊤ := by
      have hset : Φ '' (latMod c y : Set E) = (Λ : Set (Fin (Module.finrank ℚ (FR E)) → ℂ)) := by
        ext v
        simp only [Set.mem_image, SetLike.mem_coe, hΛ]
        constructor
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
      rw [hset, hfull]
    have hrat : ∀ x z : E, ∃ q : ℚ, (∑ j, (ρ : ℂ) * Φ x j * starRingEnd ℂ (Φ z j)).im = q := by
      intro x z
      refine ⟨Algebra.trace ℚ E ((c₀ : E) * ξ₁ * x * bar z), ?_⟩
      rw [htr]
      exact (congrArg Complex.im (hsum (fun j => Φ x j) z)).symm
    have hw' : ∀ x ∈ (latMod c y : Set E), ∃ m : ℤ, (∑ j, (ρ : ℂ) * w j * starRingEnd ℂ (Φ x j)).im = m := by
      intro x hx
      obtain ⟨m, hm⟩ := hw c₀ hc₀mem (Φ x) ((hΛ _).2 ⟨x, hx, rfl⟩)
      exact ⟨m, by rw [← hsum]; exact hm⟩
    obtain ⟨x, rfl⟩ := dual_descent E _ Φ (latMod c y) ρ hρ0 hspan hrat w hw'
    have hmx : ∀ m ∈ polMod (latMod c y), m * x ∈ dualLat (latMod c y) := by
      intro m hm z hz
      have hreal : m / ξ₁ ∈ maximalRealSubfield E := by
        rw [← IsCMField.complexConj_eq_self_iff]
        rw [map_div₀]
        change bar m / bar ξ₁ = _
        rw [hm.1, hbar, neg_div_neg_eq]
      set a : FR E := ⟨m / ξ₁, hreal⟩
      have ha : (a : E) * ξ₁ = m := div_mul_cancel₀ m hξ0
      have ha' : a ∈ 𝔠.elt := (h𝔠 a).2 (ha ▸ hm)
      obtain ⟨n, hn⟩ := hw a ha' (Φ z) ((hΛ _).2 ⟨z, hz, rfl⟩)
      refine ⟨n, ?_⟩
      have h1 := htr a x z
      rw [ha] at h1
      have h2 : (∑ j, ((e' j a * r : ℝ) : ℂ) * φ (e j) x * starRingEnd ℂ (φ (e j) z)).im = n := hn
      rw [h2] at h1
      exact_mod_cast h1
    have hsub : polMod (latMod c y) * Submodule.span (OF E) {x} ≤ polMod (latMod c y) * latMod c y := by
      rw [hML]
      refine Submodule.mul_le.2 fun m hm v hv => ?_
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hv
      have : m * (b • x) = (b • m) * x := by rw [Algebra.smul_def, Algebra.smul_def]; ring
      rw [this]
      exact hmx _ ((polMod (latMod c y)).smul_mem b hm)
    obtain ⟨u₀, hu₀⟩ := hU
    have hle : Submodule.span (OF E) {x} ≤ latMod c y := by
      have h3 : (↑u₀⁻¹ : Submodule (OF E) E) * (polMod (latMod c y) * Submodule.span (OF E) {x}) ≤
          (↑u₀⁻¹ : Submodule (OF E) E) * (polMod (latMod c y) * latMod c y) :=
        Submodule.mul_le.2 fun a ha b hb => Submodule.mul_mem_mul ha (hsub hb)
      rwa [← hu₀, ← _root_.mul_assoc, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul, _root_.one_mul] at h3
    exact (hΛ _).2 ⟨x, hle (Submodule.mem_span_singleton_self x), rfl⟩
  have hpos : IsTotPos c₀ := fun τ => by rw [hc₀, map_natCast]; positivity
  obtain ⟨X, u, hu, hact, χ, hχ⟩ := GlobalTheory.T.lattice_multiplication_stable (FR E) e' 𝔠 (fun _ => r) Λ (fun _ => hr0) hdisc hfull hstab hint hdual
    ⟨c₀, hc₀mem⟩ hpos
  refine ⟨𝔠, X, ⟨e, ⟨c₀, hc₀mem⟩, hpos, u, ?_, ?_, fun i => 2 * (e' (e.symm i) c₀ * r), ⟨χ, ?_⟩⟩,
    fun i => ⟨?_, ?_⟩⟩
  · intro w
    rw [hu, hΛ]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by funext j; simp [defCoord]⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by funext j; simp [defCoord]⟩
  · intro a w
    rw [← hact a w]
    congr 1
    funext j
    rw [he']
  · convert hχ using 3
    simp
  · simp only [he'c₀]
    have : (0 : ℝ) < ((N ^ 2 * d : ℕ) : ℝ) := by positivity
    positivity
  · have h4 : ((2 * (e' (e.symm i) c₀ * r) : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = ((4 * (N ^ 2 * d) : ℕ) : ℂ) := by
      rw [he'c₀, hr]
      push_cast
      field_simp
      ring
    rw [h4]
    have h5 := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((4 * (N ^ 2 * d) : ℕ) : ℚ)
    rwa [map_natCast] at h5
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_abelian_variety_uniformization_exists : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∃ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
        ∀ i, U.h i ≠ 0 ∧ IsAlgebraic ℚ ((U.h i : ℂ) * (Real.sqrt d : ℝ)) := by
  atlas_forward_decl GlobalTheory.LatTorus.exists_unif_of_lattice
end
