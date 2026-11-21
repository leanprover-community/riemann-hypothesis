import Mathlib
import Formalism.PeriodIntegrals.UMultOne

section
noncomputable section

namespace PI.UMultOne.GelfSpanWork

open Matrix Module

variable {G : Type} [Group G] {N : ℕ}

def repEnd (ρ : G →* GL (Fin N) ℂ) : G →* Module.End ℂ (Fin N → ℂ) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  map_one' := by simp; rfl
  map_mul' x y := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

theorem repEnd_apply (ρ : G →* GL (Fin N) ℂ) (g : G) (v : Fin N → ℂ) :
    repEnd ρ g v = ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).mulVec v := by
  simp [repEnd, Matrix.toLin'_apply]

def spanAlg (ρ : G →* GL (Fin N) ℂ) : Subalgebra ℂ (Module.End ℂ (Fin N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (repEnd ρ))

instance spanAlg_tower (ρ : G →* GL (Fin N) ℂ) : IsScalarTower ℂ (spanAlg ρ) (Fin N → ℂ) :=
  ⟨fun _ _ _ => rfl⟩

theorem spanAlg_smul (ρ : G →* GL (Fin N) ℂ) (a : spanAlg ρ) (v : Fin N → ℂ) :
    a • v = (a : Module.End ℂ (Fin N → ℂ)) v := rfl

theorem spanAlg_toSubmodule (ρ : G →* GL (Fin N) ℂ) :
    Subalgebra.toSubmodule (spanAlg ρ) = Submodule.span ℂ (Set.range (repEnd ρ)) := by
  rw [spanAlg, Algebra.adjoin_eq_span]
  congr 1
  rw [← MonoidHom.coe_mrange, Submonoid.closure_eq]

theorem repEnd_mem (ρ : G →* GL (Fin N) ℂ) (g : G) : repEnd ρ g ∈ spanAlg ρ :=
  Algebra.subset_adjoin ⟨g, rfl⟩

theorem spanAlg_simple (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ) :
    IsSimpleModule (spanAlg ρ) (Fin N → ℂ) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nontrivial (Fin N → ℂ) := inferInstance
  refine { eq_bot_or_eq_top := fun S => ?_ }
  have hT := hI (S.restrictScalars ℂ) (fun g v hv => by
    have := S.smul_mem ⟨repEnd ρ g, repEnd_mem ρ g⟩ hv
    rw [spanAlg_smul] at this
    simpa [repEnd_apply] using this)
  rcases hT with hT | hT
  · left
    rw [eq_bot_iff]
    intro v hv
    have : v ∈ S.restrictScalars ℂ := hv
    rw [hT] at this
    simpa using this
  · right
    rw [eq_top_iff]
    intro v _
    have : v ∈ S.restrictScalars ℂ := by rw [hT]; trivial
    exact this

theorem schur (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ)
    (φ : (Fin N → ℂ) →ₗ[spanAlg ρ] (Fin N → ℂ)) : ∃ c : ℂ, ∀ v, φ v = c • v := by
  have := spanAlg_simple ρ hN hI
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrictScalars ℂ)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, fun w => ?_⟩
  let K : Submodule (spanAlg ρ) (Fin N → ℂ) :=
    { carrier := {w | φ w = c • w}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at *
        rw [map_add, ha, hb, smul_add]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_ofPred_eq] at *
        rw [map_smul, hx, spanAlg_smul, spanAlg_smul, map_smul] }
  have hvK : v ∈ K := by
    have := hv.apply_eq_smul
    simpa [K] using this
  have hK : K = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · exfalso
      have : v ∈ (⊥ : Submodule (spanAlg ρ) (Fin N → ℂ)) := h ▸ hvK
      exact hv.2 ((Submodule.mem_bot _).mp this)
    · exact h
  have : w ∈ K := hK ▸ Submodule.mem_top
  exact this

theorem spanAlg_eq_top (ρ : G →* GL (Fin N) ℂ) (hN : 0 < N) (hI : Irr ρ) :
    ∀ f : Module.End ℂ (Fin N → ℂ), f ∈ spanAlg ρ := by
  intro f
  have := spanAlg_simple ρ hN hI
  let F : Module.End (Module.End (spanAlg ρ) (Fin N → ℂ)) (Fin N → ℂ) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro φ v
        obtain ⟨c, hc⟩ := schur ρ hN hI φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image (fun i => Pi.single i (1 : ℂ)))
  have : (r : Module.End ℂ (Fin N → ℂ)) = f := by
    apply (Pi.basisFun ℂ (Fin N)).ext
    intro i
    have := hr (Pi.single i 1) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [Pi.basisFun_apply, ← spanAlg_smul]
    exact this.symm
  exact this ▸ r.2

theorem functional_eq_zero (ρ : G →* GL (Fin N) ℂ) (hI : Irr ρ)
    (ℓ : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ g, ℓ ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 0) : ℓ = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    ext T
    have : T = 0 := Subsingleton.elim _ _
    simp [this]
  let ℓ' : Module.End ℂ (Fin N → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ (Matrix.toLin' (R := ℂ) (m := Fin N) (n := Fin N)).symm.toLinearMap
  have hspan : Submodule.span ℂ (Set.range (repEnd ρ)) ≤ LinearMap.ker ℓ' := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    simp [ℓ', repEnd, h]
  have h' : ∀ f, ℓ' f = 0 := by
    intro f
    have hf : f ∈ Subalgebra.toSubmodule (spanAlg ρ) := spanAlg_eq_top ρ hN hI f
    rw [spanAlg_toSubmodule] at hf
    exact hspan hf
  ext T
  have := h' (Matrix.toLin' T)
  simpa [ℓ'] using this

end PI.UMultOne.GelfSpanWork
end
end

section
noncomputable section

namespace PI.UMultOne.GelfSpanWork

open MeasureTheory Matrix ComplexConjugate

theorem intSpan' : IntSpan := by
  intro G _ _ _ _ _ _ _ _ μ _ N ρ hC hI T

  have hE : ∀ i j, Continuous (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hC)
  have hInt : ∀ f : G → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hIntP : ∀ f : G → ℂ, Continuous f → ∀ i j,
      Integrable (fun g => f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j) μ :=
    fun f hf i j => hInt _ (hf.mul (hE i j))

  let S : Submodule ℂ (Matrix (Fin N) (Fin N) ℂ) :=
    { carrier := {T | ∃ f : G → ℂ, Continuous f ∧
        ∀ i j, T i j = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ}
      add_mem' := by
        rintro A B ⟨f₁, hf₁, h₁⟩ ⟨f₂, hf₂, h₂⟩
        refine ⟨f₁ + f₂, hf₁.add hf₂, fun i j => ?_⟩
        simp only [Matrix.add_apply, Pi.add_apply, add_mul]
        rw [integral_add (hIntP f₁ hf₁ i j) (hIntP f₂ hf₂ i j), h₁, h₂]
      zero_mem' := ⟨0, continuous_const, fun i j => by simp⟩
      smul_mem' := by
        rintro c A ⟨f, hf, h⟩
        refine ⟨fun g => c * f g, continuous_const.mul hf, fun i j => ?_⟩
        simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc]
        rw [integral_const_mul, h] }
  suffices hS : S = ⊤ by
    have : T ∈ S := hS ▸ Submodule.mem_top
    exact this
  by_contra hne
  obtain ⟨ℓ, hℓ0, hℓS⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  apply hℓ0
  apply functional_eq_zero ρ hI ℓ

  set h : G → ℂ := fun g => ℓ ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hh
  have hhc : Continuous h := (LinearMap.continuous_of_finiteDimensional ℓ).comp hC
  have hcoef : ∀ A : Matrix (Fin N) (Fin N) ℂ,
      ℓ A = ∑ i, ∑ j, A i j * ℓ (Matrix.single i j 1) := by
    intro A
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [map_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  let M : Matrix (Fin N) (Fin N) ℂ := fun i j =>
    ∫ g, conj (h g) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ
  have hM : M ∈ S := ⟨fun g => conj (h g), Complex.continuous_conj.comp hhc, fun i j => rfl⟩
  have hℓM : ℓ M = 0 := hℓS hM
  have hℓM' : ℓ M = ∫ g, ((Complex.normSq (h g) : ℝ) : ℂ) ∂μ := by
    rw [hcoef M]
    simp only [M]
    have : ∀ g, ((Complex.normSq (h g) : ℝ) : ℂ) = ∑ i, ∑ j,
        conj (h g) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j *
          ℓ (Matrix.single i j 1) := by
      intro g
      rw [Complex.normSq_eq_conj_mul_self, hh]
      simp only
      rw [hcoef ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    simp_rw [this]
    have hcj : Continuous (fun g => conj (h g)) := Complex.continuous_conj.comp hhc
    symm
    rw [integral_finsetSum _ (fun i _ => ?_)]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum _ (fun j _ => ?_)]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [integral_mul_const]
      · exact (hIntP (fun g => conj (h g)) hcj i j).mul_const _
    · exact integrable_finsetSum _ (fun j _ => (hIntP (fun g => conj (h g)) hcj i j).mul_const _)
  rw [hℓM, integral_complex_ofReal] at hℓM'
  have hR : ∫ g, Complex.normSq (h g) ∂μ = 0 := by exact_mod_cast hℓM'.symm
  intro g
  by_contra hg
  have hpos : 0 < ∫ x, Complex.normSq (h x) ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := g)
      (Complex.continuous_normSq.comp hhc) (HasCompactSupport.of_compactSpace _)
      (fun x => Complex.normSq_nonneg _) (by simpa [Complex.normSq_eq_zero] using hg)
  linarith

end PI.UMultOne.GelfSpanWork
end
end
