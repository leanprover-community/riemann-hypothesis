import Mathlib
import GroundTheory.GlobalFields.Artin.ConductorInflation
import GroundTheory.GlobalFields.Artin.PlacesGalois
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.LocalFields.Different

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global.Artin

open NumberField InfinitePlace Complex Module

section Involution

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem isProj_eigenspace_one_of_mul_self_eq_one {T : Module.End ℂ V} (hT : T * T = 1) :
    LinearMap.IsProj (Module.End.eigenspace T 1) ((2 : ℂ)⁻¹ • (1 + T)) where
  map_mem x := by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    have : T (T x) = x := by simpa using LinearMap.congr_fun hT x
    simp [this, add_comm]
  map_id x hx := by
    rw [Module.End.mem_eigenspace_iff, one_smul] at hx
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, hx]
    rw [← two_smul ℂ x, smul_smul]
    norm_num

theorem isProj_eigenspace_neg_one_of_mul_self_eq_one {T : Module.End ℂ V} (hT : T * T = 1) :
    LinearMap.IsProj (Module.End.eigenspace T (-1)) ((2 : ℂ)⁻¹ • (1 - T)) where
  map_mem x := by
    rw [Module.End.mem_eigenspace_iff]
    have : T (T x) = x := by simpa using LinearMap.congr_fun hT x
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul,
      map_sub, this, neg_smul, one_smul, smul_sub]
    abel
  map_id x hx := by
    rw [Module.End.mem_eigenspace_iff, neg_smul, one_smul] at hx
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hx, sub_neg_eq_add]
    rw [← two_smul ℂ x, smul_smul]
    norm_num

theorem finrank_eigenspace_of_mul_self_eq_one [FiniteDimensional ℂ V] {T : Module.End ℂ V} (hT : T * T = 1) :
    ((finrank ℂ (Module.End.eigenspace T 1) : ℂ) + finrank ℂ (Module.End.eigenspace T (-1))
        = finrank ℂ V) ∧
    (LinearMap.trace ℂ V T = finrank ℂ (Module.End.eigenspace T 1)
        - finrank ℂ (Module.End.eigenspace T (-1))) := by
  have hP := (isProj_eigenspace_one_of_mul_self_eq_one hT).trace
  have hQ := (isProj_eigenspace_neg_one_of_mul_self_eq_one hT).trace
  rw [← hP, ← hQ]
  constructor
  · rw [← map_add, ← smul_add, ← LinearMap.trace_one]
    congr 1
    rw [show (1 : Module.End ℂ V) + T + (1 - T) = (2 : ℂ) • 1 by
      rw [two_smul]; abel, smul_smul]
    norm_num
  · rw [← map_sub, ← smul_sub]
    congr 1
    rw [show (1 : Module.End ℂ V) + T - (1 - T) = (2 : ℂ) • T by
      rw [two_smul]; abel, smul_smul]
    norm_num

end Involution

section ComplexConj

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def complexConjAt (w : InfinitePlace L) : L ≃ₐ[K] L := by
  classical
  exact if h : ∃ σ : L ≃ₐ[K] L, ComplexEmbedding.IsConj w.embedding σ then h.choose else 1

variable {K}

theorem exists_isConj_of_isReal_comap [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    ∃ σ : L ≃ₐ[K] L, ComplexEmbedding.IsConj w.embedding σ := by
  by_cases hw : w.IsReal
  · exact ⟨1, ComplexEmbedding.isConj_one_iff.mpr (isReal_iff.mp hw)⟩
  · have hram : IsRamified K w :=
      isRamified_iff.mpr ⟨not_isReal_iff_isComplex.mp hw, hv⟩
    rw [← mk_embedding w] at hram
    exact exists_isConj_of_isRamified hram

theorem isConj_complexConjAt [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    ComplexEmbedding.IsConj w.embedding (complexConjAt K w) := by
  have h := exists_isConj_of_isReal_comap hv
  rw [complexConjAt, dif_pos h]
  exact h.choose_spec

theorem complexConjAt_mul_self [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    complexConjAt K w * complexConjAt K w = 1 :=
  AlgEquiv.ext fun x ↦ ComplexEmbedding.isConj_apply_apply (isConj_complexConjAt hv) x

end ComplexConj

section Factor

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable (ρ : Representation ℂ (L ≃ₐ[K] L) V)

noncomputable def plusDim (w : InfinitePlace L) : ℕ :=
  finrank ℂ (Module.End.eigenspace (ρ (complexConjAt K w)) 1)

noncomputable def minusDim (w : InfinitePlace L) : ℕ :=
  finrank ℂ (Module.End.eigenspace (ρ (complexConjAt K w)) (-1))

variable {ρ}

omit [FiniteDimensional ℂ V] in

theorem rho_complexConjAt_mul_self [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    ρ (complexConjAt K w) * ρ (complexConjAt K w) = 1 := by
  rw [← map_mul, complexConjAt_mul_self hv, map_one]

theorem plusDim_add_minusDim [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    plusDim ρ w + minusDim ρ w = finrank ℂ V := by
  have := (finrank_eigenspace_of_mul_self_eq_one (rho_complexConjAt_mul_self (ρ := ρ) hv)).1
  exact_mod_cast this

theorem character_complexConjAt [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    ρ.character (complexConjAt K w) = (plusDim ρ w : ℂ) - minusDim ρ w :=
  (finrank_eigenspace_of_mul_self_eq_one (rho_complexConjAt_mul_self (ρ := ρ) hv)).2

theorem plusDim_eq_character [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    (plusDim ρ w : ℂ) = (ρ.character 1 + ρ.character (complexConjAt K w)) / 2 := by
  rw [Representation.char_one, character_complexConjAt hv, ← plusDim_add_minusDim hv]
  push_cast
  ring

theorem minusDim_eq_character [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    (minusDim ρ w : ℂ) = (ρ.character 1 - ρ.character (complexConjAt K w)) / 2 := by
  rw [Representation.char_one, character_complexConjAt hv, ← plusDim_add_minusDim hv]
  push_cast
  ring

theorem character_prod {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) (g : L ≃ₐ[K] L) :
    (ρ.prod σ).character g = ρ.character g + σ.character g :=
  LinearMap.trace_prodMap' (ρ g) (σ g)

theorem plusDim_prod {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    plusDim (ρ.prod σ) w = plusDim ρ w + plusDim σ w := by
  have h1 := plusDim_eq_character (ρ := ρ.prod σ) hv
  rw [character_prod, character_prod, add_add_add_comm, add_div, ← plusDim_eq_character hv,
    ← plusDim_eq_character hv] at h1
  exact_mod_cast h1

theorem minusDim_prod {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) :
    minusDim (ρ.prod σ) w = minusDim ρ w + minusDim σ w := by
  have h1 := minusDim_eq_character (ρ := ρ.prod σ) hv
  rw [character_prod, character_prod, add_sub_add_comm, add_div, ← minusDim_eq_character hv,
    ← minusDim_eq_character hv] at h1
  exact_mod_cast h1

variable (L) in

noncomputable def placeOver [Algebra.IsAlgebraic K L] (v : InfinitePlace K) : InfinitePlace L :=
  (comap_surjective (k := K) (K := L) v).choose

theorem comap_placeOver [Algebra.IsAlgebraic K L] (v : InfinitePlace K) :
    (placeOver L v).comap (algebraMap K L) = v :=
  (comap_surjective (k := K) (K := L) v).choose_spec

variable (ρ) in
open scoped Classical in

noncomputable def gammaFactorAt [Algebra.IsAlgebraic K L] (v : InfinitePlace K) (s : ℂ) : ℂ :=
  if v.IsReal then
    Gammaℝ s ^ plusDim ρ (placeOver L v) * Gammaℝ (s + 1) ^ minusDim ρ (placeOver L v)
  else Gammaℂ s ^ finrank ℂ V

theorem gammaFactorAt_prod [IsGalois K L] [Algebra.IsAlgebraic K L]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) (v : InfinitePlace K) (s : ℂ) :
    gammaFactorAt (ρ.prod σ) v s = gammaFactorAt ρ v s * gammaFactorAt σ v s := by
  by_cases hv : v.IsReal
  · have hv' : ((placeOver L v).comap (algebraMap K L)).IsReal := by rwa [comap_placeOver]
    simp only [gammaFactorAt, if_pos hv, plusDim_prod σ hv', minusDim_prod σ hv', pow_add]
    ring
  · simp only [gammaFactorAt, if_neg hv, Module.finrank_prod, pow_add]

variable (ρ) in

noncomputable def gammaFactor [NumberField K] [Algebra.IsAlgebraic K L] (s : ℂ) : ℂ :=
  ∏ v : InfinitePlace K, gammaFactorAt ρ v s

theorem gammaFactor_prod [NumberField K] [IsGalois K L] [Algebra.IsAlgebraic K L]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (L ≃ₐ[K] L) W) (s : ℂ) :
    gammaFactor (ρ.prod σ) s = gammaFactor ρ s * gammaFactor σ s := by
  simp only [gammaFactor, gammaFactorAt_prod, Finset.prod_mul_distrib]

end Factor

example {K L V W : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (L ≃ₐ[K] L) V) (σ : Representation ℂ (L ≃ₐ[K] L) W) (s : ℂ) :
    gammaFactor (ρ.prod σ) s = gammaFactor ρ s * gammaFactor σ s :=
  gammaFactor_prod σ s

end GroundTheory.Global.Artin
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField NumberField.InfinitePlace IntermediateField Module GroundTheory.LocalField _root_.Complex

namespace GroundTheory.Global.Artin

section IndFun

variable {Γ Δ : Type*} [Group Γ] [Group Δ] [Fintype Γ] [Fintype Δ]

theorem indFun_mulEquiv (e : Γ ≃* Δ) {ψ : Γ → ℂ} (hψ : IsClassFun ψ) :
    indFun e.toMonoidHom ψ = ψ ∘ e.symm := by
  classical
  funext s
  rw [indFun_apply]
  have h1 : ∀ t : Δ, (∑ h : Γ, if e.toMonoidHom h = t⁻¹ * s * t then ψ h else 0) =
      ψ (e.symm s) := by
    intro t
    rw [Finset.sum_eq_single (e.symm (t⁻¹ * s * t))]
    · rw [if_pos (by simp), map_mul, map_mul, map_inv]
      have := hψ (e.symm s) (e.symm t)⁻¹
      rwa [inv_inv] at this
    · intro h _ hh
      rw [if_neg]
      intro h'
      apply hh
      rw [← h']
      simp
    · simp
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Function.comp_apply]
  have : (Fintype.card Δ : ℂ) = Nat.card Γ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_congr e.toEquiv]
  rw [this, inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')]

end IndFun

section Stabilizer

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

end Stabilizer

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

section Conj

end Conj

section Mackey

variable (w : InfinitePlace L)

end Mackey

section Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ Gal(L/fixedField H) V)

def charOnSubgroup (h : H) : ℂ :=
  ρ.character (fixedFieldMulEquiv H h)

omit [IsGalois K L] in
open Classical in

theorem character_ind_restrictScalarsHom :
    (ρ.ind (AlgEquiv.restrictScalarsHom K)).character = indFun H.subtype (charOnSubgroup H ρ) := by
  rw [character_ind]
  have hφ : (AlgEquiv.restrictScalarsHom K : Gal(L/fixedField H) →* Gal(L/K)) =
      H.subtype.comp (fixedFieldMulEquiv H).symm.toMonoidHom := MonoidHom.ext fun _ ↦ rfl
  rw [hφ, ← indFun_indFun, indFun_mulEquiv (fixedFieldMulEquiv H).symm
    (isCharacter_character ρ).isClassFun]
  rfl

end Character

section Gamma

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ Gal(L/fixedField H) V)

end Gamma

end GroundTheory.Global.Artin
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField Module

namespace GroundTheory.Global

section Def

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

def relDiscr : Ideal (𝓞 K) :=
  Ideal.relNorm (𝓞 K) (differentIdeal (𝓞 K) (𝓞 M))

theorem relDiscr_ne_bot : relDiscr K M ≠ ⊥ := by
  rw [relDiscr, Ne, Ideal.relNorm_eq_bot_iff]
  exact differentIdeal_ne_bot

end Def

section Multiplicity

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem prime_asIdeal {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    Prime u.asIdeal :=
  Ideal.prime_of_isPrime u.ne_bot u.isPrime

theorem emultiplicity_asIdeal_of_isMaximal {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (p : Ideal (𝓞 F)) [hp : p.IsMaximal] :
    emultiplicity u.asIdeal p = if u.asIdeal = p then 1 else 0 := by
  split_ifs with h
  · have h1 := emultiplicity_pow_self_of_prime (prime_asIdeal u) 1
    rw [pow_one] at h1
    rw [← h, h1]
    rfl
  · rw [emultiplicity_eq_zero, Ideal.dvd_iff_le]
    intro hle
    exact h (hp.eq_of_le u.isPrime.ne_top hle).symm

variable (v : HeightOneSpectrum (𝓞 K))

theorem emultiplicity_relNorm_of_prime (p : Ideal (𝓞 M)) (hp : Prime p) :
    emultiplicity v.asIdeal (Ideal.relNorm (𝓞 K) p) =
      ∑ w : SemiLocal.PlacesOver M v,
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℕ∞) * emultiplicity w.1.asIdeal p := by
  have hp0 : p ≠ ⊥ := hp.ne_zero
  have hpp : p.IsPrime := (Ideal.prime_iff_isPrime hp0).1 hp
  have hpm : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 hpp
  have hqm : (p.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) p
  rw [Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 K)),
    emultiplicity_pow (prime_asIdeal v), emultiplicity_asIdeal_of_isMaximal]
  simp only [emultiplicity_asIdeal_of_isMaximal, mul_ite, mul_one, mul_zero]
  by_cases hv : v.asIdeal = p.under (𝓞 K)
  · rw [if_pos hv]
    have hlies : p.LiesOver v.asIdeal := ⟨hv⟩
    let w0 : SemiLocal.PlacesOver M v := ⟨⟨p, hpp, hp0⟩, hlies⟩
    rw [Finset.sum_eq_single w0]
    · simp [w0]
    · intro w _ hw
      rw [if_neg]
      intro h
      apply hw
      apply Subtype.ext
      apply HeightOneSpectrum.ext
      exact h
    · simp
  · rw [if_neg hv]
    symm
    apply Finset.sum_eq_zero
    intro w _
    rw [if_neg]
    intro h
    apply hv
    rw [← h]
    exact Ideal.over_def w.1.asIdeal v.asIdeal

theorem emultiplicity_relNorm (I : Ideal (𝓞 M)) (hI : I ≠ ⊥) :
    emultiplicity v.asIdeal (Ideal.relNorm (𝓞 K) I) =
      ∑ w : SemiLocal.PlacesOver M v,
        (w.1.asIdeal.inertiaDeg (𝓞 K) : ℕ∞) * emultiplicity w.1.asIdeal I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, Ideal.relNorm_top, ← Ideal.one_eq_top,
      emultiplicity_of_one_right (prime_asIdeal v).not_isUnit]
    symm
    apply Finset.sum_eq_zero
    intro w _
    rw [← Ideal.one_eq_top, emultiplicity_of_one_right (prime_asIdeal w.1).not_isUnit, mul_zero]
  | h₃ a p ha hp ih =>
    rw [map_mul, emultiplicity_mul (prime_asIdeal v), ih ha,
      emultiplicity_relNorm_of_prime v p hp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [emultiplicity_mul (prime_asIdeal w.1), mul_add]

theorem multiplicity_relNorm (I : Ideal (𝓞 M)) (hI : I ≠ ⊥) :
    multiplicity v.asIdeal (Ideal.relNorm (𝓞 K) I) =
      ∑ w : SemiLocal.PlacesOver M v,
        w.1.asIdeal.inertiaDeg (𝓞 K) * multiplicity w.1.asIdeal I := by
  have h := emultiplicity_relNorm v I hI
  rw [(FiniteMultiplicity.of_prime_left (prime_asIdeal v)
    ((Ideal.relNorm_eq_bot_iff (R := 𝓞 K)).not.2 hI)).emultiplicity_eq_multiplicity] at h
  simp only [fun w : SemiLocal.PlacesOver M v ↦
    (FiniteMultiplicity.of_prime_left (prime_asIdeal w.1) hI).emultiplicity_eq_multiplicity] at h
  exact_mod_cast h

theorem multiplicity_relDiscr_eq_sum :
    multiplicity v.asIdeal (relDiscr K M) =
      ∑ w : SemiLocal.PlacesOver M v,
        w.1.asIdeal.inertiaDeg (𝓞 K) * multiplicity w.1.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) :=
  multiplicity_relNorm v _ differentIdeal_ne_bot

end Multiplicity

section Tower

variable (K M N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [Field N] [NumberField N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]


end Tower

section Rat

variable (M : Type*) [Field M] [NumberField M]

theorem differentIdeal_ringOfIntegers_rat :
    differentIdeal (𝓞 ℚ) (𝓞 M) = differentIdeal ℤ (𝓞 M) := by
  have h1 : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ, Rat.numberField_discr]
    rfl
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 ℚ) (𝓞 M), h1, Ideal.map_top,
    Ideal.mul_top]

theorem absNorm_relDiscr_rat : Ideal.absNorm (relDiscr ℚ M) = (discr M).natAbs := by
  rw [relDiscr, Ideal.absNorm_relNorm, differentIdeal_ringOfIntegers_rat,
    absNorm_differentIdeal M]

end Rat

end GroundTheory.Global
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField

open scoped WithZero

namespace GroundTheory.Global

section Local

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion M)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)]

theorem mem_inv_maximalIdeal_pow_iff {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : u.adicCompletion F) :
    y ∈ ((𝓂[u.adicCompletion F] ^ n : Ideal 𝒪[u.adicCompletion F]) :
      FractionalIdeal (nonZeroDivisors 𝒪[u.adicCompletion F]) (u.adicCompletion F))⁻¹ ↔
      Valued.v y ≤ WithZero.exp (n : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[u.adicCompletion F]
  have hv : Valued.v (ϖ : u.adicCompletion F) = WithZero.exp (-1) :=
    valued_of_irreducible_integer u hϖ
  have hvn : Valued.v ((ϖ : u.adicCompletion F) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hv, ← WithZero.exp_nsmul]
    simp
  have hϖ0 : ((ϖ : u.adicCompletion F) ^ n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvn
    exact WithZero.zero_ne_coe hvn
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv, FractionalIdeal.mem_spanSingleton]
  change (∃ b : 𝒪[u.adicCompletion F], (b : u.adicCompletion F) *
    ((ϖ : u.adicCompletion F) ^ n)⁻¹ = y) ↔ _
  constructor
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_inv₀, hvn, WithZero.exp_neg, inv_inv]
    exact mul_le_of_le_one_left zero_le ((integers_valued u).map_le_one b)
  · intro hy
    have hb : Valued.v (y * (ϖ : u.adicCompletion F) ^ n) ≤ 1 := by
      rw [map_mul, hvn]
      calc Valued.v y * WithZero.exp (-(n : ℤ))
          ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) := by gcongr
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    refine ⟨⟨_, (mem_valuationInteger_iff u _).2 hb⟩, ?_⟩
    change y * (ϖ : u.adicCompletion F) ^ n * ((ϖ : u.adicCompletion F) ^ n)⁻¹ = y
    rw [mul_assoc, mul_inv_cancel₀ hϖ0, mul_one]

theorem forall_valued_trace_le_one_iff (n : ℕ) :
    (∀ y : w.adicCompletion M, Valued.v y ≤ WithZero.exp (n : ℤ) →
      Valued.v (Algebra.trace (v.adicCompletion K) (w.adicCompletion M) y) ≤ 1) ↔
      n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  have hI : (𝓂[w.adicCompletion M] ^ n) ≠ ⊥ :=
    pow_ne_zero _ (IsDiscreteValuationRing.not_a_field _)
  rw [← maximalIdeal_pow_dvd_pow_iff (R := 𝒪[w.adicCompletion M]),
    ← differentIdeal_eq_maximalIdeal_pow, Ideal.dvd_iff_le,
    differentialIdeal_le_iff (K := v.adicCompletion K) (L := w.adicCompletion M) hI,
    Submodule.map_le_iff_le_comap]
  constructor
  · intro h y hy
    have hy' := h y ((mem_inv_maximalIdeal_pow_iff w n y).1 hy)
    rw [Submodule.mem_comap]
    exact Submodule.mem_one.2 ⟨⟨_, (mem_valuationInteger_iff v _).2 hy'⟩, rfl⟩
  · intro h y hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (Submodule.mem_comap.1
      (h ((mem_inv_maximalIdeal_pow_iff w n y).2 hy)))
    change (a : v.adicCompletion K) = Algebra.trace (v.adicCompletion K) (w.adicCompletion M) y
      at ha
    rw [← ha]
    exact (integers_valued v).map_le_one a

end Local

section Global

variable {M : Type*} [Field M] [NumberField M]

theorem mem_inv_pow_iff (w : HeightOneSpectrum (𝓞 M)) (n : ℕ) (x : M) :
    x ∈ ((w.asIdeal ^ n : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ↔
      w.valuation M x ≤ WithZero.exp (n : ℤ) ∧
        ∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M x ≤ 1 := by
  have hI : ((w.asIdeal ^ n : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact pow_ne_zero _ w.ne_bot
  rw [FractionalIdeal.mem_inv_iff hI]
  constructor
  · intro h
    have key : ∀ y ∈ w.asIdeal ^ n, ∀ u : HeightOneSpectrum (𝓞 M),
        u.valuation M x * u.intValuation y ≤ 1 := by
      intro y hy u
      obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 M))).1
        (h _ ((FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 M))).2 ⟨y, hy, rfl⟩))
      rw [← valuation_of_algebraMap (K := M), ← map_mul, ← hb, valuation_of_algebraMap]
      exact u.intValuation_le_one b
    refine ⟨?_, fun u hu ↦ ?_⟩
    · obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
      have hπn : w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := by
        rw [map_pow, hπ, ← WithZero.exp_nsmul]
        simp
      have hmem : π ^ n ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem _ n).1 hπn.le
      have h1 := key _ hmem w
      rw [hπn] at h1
      calc w.valuation M x
          = w.valuation M x * WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) := by
            rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
        _ ≤ 1 * WithZero.exp (n : ℤ) := by gcongr
        _ = WithZero.exp (n : ℤ) := one_mul _
    · have hnle : ¬ w.asIdeal ^ n ≤ u.asIdeal := by
        intro hle
        have hwu : w.asIdeal ≤ u.asIdeal := u.isPrime.le_of_pow_le hle
        exact hu (HeightOneSpectrum.ext
          ((w.isMaximal.eq_of_le u.isPrime.ne_top hwu).symm))
      obtain ⟨y, hy, hyu⟩ := SetLike.not_le_iff_exists.1 hnle
      have h1 := key y hy u
      have hy1 : u.intValuation y = 1 := le_antisymm (u.intValuation_le_one y)
        (not_lt.1 fun hlt ↦ hyu ((u.intValuation_lt_one_iff_mem y).1 hlt))
      rwa [hy1, mul_one] at h1
  · rintro ⟨hw, hu⟩ y hy
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 M))).1 hy
    rw [FractionalIdeal.mem_one_iff (nonZeroDivisors (𝓞 M))]
    refine mem_integers_of_valuation_le_one (R := 𝓞 M) (K := M) _ fun u ↦ ?_
    rw [map_mul, valuation_of_algebraMap]
    by_cases huw : u = w
    · subst huw
      calc u.valuation M x * u.intValuation y'
          ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) := by
            gcongr
            exact (u.intValuation_le_pow_iff_mem y' n).2 hy'
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    · simpa using mul_le_mul' (hu u huw) (u.intValuation_le_one y')

theorem exists_valuation_eq_exp (w : HeightOneSpectrum (𝓞 M)) (n : ℕ) :
    ∃ x : M, w.valuation M x = WithZero.exp (n : ℤ) ∧
      ∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M x ≤ 1 := by
  cases n with
  | zero => exact ⟨1, by simp, fun u _ ↦ by simp⟩
  | succ k =>
    by_contra H
    push Not at H
    have hle : ((w.asIdeal ^ (k + 1) : Ideal (𝓞 M)) :
        FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ≤
        ((w.asIdeal ^ k : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ := by
      intro x hx
      obtain ⟨hxw, hxu⟩ := (mem_inv_pow_iff w (k + 1) x).1 hx
      refine (mem_inv_pow_iff w k x).2 ⟨?_, hxu⟩
      have hne : w.valuation M x ≠ WithZero.exp ((k + 1 : ℕ) : ℤ) := by
        intro heq
        obtain ⟨u, hu, hlt⟩ := H x heq
        exact absurd (hxu u hu) (not_le.2 hlt)
      have hlt : w.valuation M x < WithZero.exp (k : ℤ) * WithZero.exp 1 := by
        rw [← WithZero.exp_add]
        have := lt_of_le_of_ne hxw hne
        push_cast at this
        exact this
      exact (WithZero.lt_mul_exp_iff_le (by simp)).1 hlt
    have hge : ((w.asIdeal ^ k : Ideal (𝓞 M)) :
        FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ≤
        ((w.asIdeal ^ (k + 1) : Ideal (𝓞 M)) :
          FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ := by
      intro x hx
      obtain ⟨hxw, hxu⟩ := (mem_inv_pow_iff w k x).1 hx
      refine (mem_inv_pow_iff w (k + 1) x).2 ⟨hxw.trans ?_, hxu⟩
      rw [WithZero.exp_le_exp]
      push_cast
      omega
    have heq := inv_inj.1 (le_antisymm hle hge)
    rw [FractionalIdeal.coeIdeal_inj] at heq
    exact (Ideal.pow_succ_lt_pow w.ne_bot k).ne heq

end Global

section Comparison

open SemiLocal

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem valued_trace_le_one_of_valuation_le_one (v : HeightOneSpectrum (𝓞 K))
    (u : PlacesOver M v) {x : M} (hx : u.1.valuation M x ≤ 1) :
    Valued.v (Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
      (algebraMap M (u.1.adicCompletion M) x)) ≤ 1 := by
  refine (forall_valued_trace_le_one_iff v u.1 0).2 (Nat.zero_le _) _ ?_
  rw [valued_algebraMap_field, Nat.cast_zero, WithZero.exp_zero]
  exact hx

theorem trace_mem_range_of_forall (x : M)
    (h : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : PlacesOver M v),
      Valued.v (Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
        (algebraMap M (u.1.adicCompletion M) x)) ≤ 1) :
    Algebra.trace K M x ∈ (algebraMap (𝓞 K) K).range := by
  refine mem_integers_of_valuation_le_one (R := 𝓞 K) (K := K) _ fun v ↦ ?_
  rw [← valued_algebraMap_field, algebraMap_trace_eq_sum]
  exact Valuation.map_sum_le _ fun u _ ↦ h v u

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]

theorem differentIdeal_le_pow_of_le_differentExponent {n : ℕ}
    (hn : n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M)) :
    differentIdeal (𝓞 K) (𝓞 M) ≤ w.asIdeal ^ n := by
  have hI : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ w.ne_bot
  rw [differentialIdeal_le_iff (K := K) (L := M) hI, Submodule.map_le_iff_le_comap]
  intro x hx
  obtain ⟨hxw, hxu⟩ := (mem_inv_pow_iff w n x).1 hx
  rw [Submodule.mem_comap]
  have hloc : ∀ (v' : HeightOneSpectrum (𝓞 K)) (u : PlacesOver M v'),
      Valued.v (Algebra.trace (v'.adicCompletion K) (u.1.adicCompletion M)
        (algebraMap M (u.1.adicCompletion M) x)) ≤ 1 := by
    intro v' u
    by_cases hu : u.1 = w
    · obtain ⟨u1, hu1⟩ := u
      simp only at hu
      subst hu
      have hv : v' = v := HeightOneSpectrum.ext
        ((Ideal.over_def u1.asIdeal v'.asIdeal).trans (Ideal.over_def u1.asIdeal v.asIdeal).symm)
      subst hv
      refine (forall_valued_trace_le_one_iff v' u1 n).2 hn _ ?_
      rw [valued_algebraMap_field]
      exact hxw
    · exact valued_trace_le_one_of_valuation_le_one v' u (hxu u.1 hu)
  obtain ⟨a, ha⟩ := trace_mem_range_of_forall (K := K) x hloc
  exact Submodule.mem_one.2 ⟨a, ha⟩

theorem le_differentExponent_of_differentIdeal_le_pow {n : ℕ}
    (h : differentIdeal (𝓞 K) (𝓞 M) ≤ w.asIdeal ^ n) :
    n ≤ differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  classical
  have hI : w.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ w.ne_bot
  rw [differentialIdeal_le_iff (K := K) (L := M) hI, Submodule.map_le_iff_le_comap] at h
  let w0 : PlacesOver M v := ⟨w, inferInstance⟩

  have hX : ∀ X : M, w.valuation M X ≤ WithZero.exp (n : ℤ) →
      (∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M X ≤ 1) →
      Valued.v (Algebra.trace (v.adicCompletion K) (w.adicCompletion M)
        (algebraMap M (w.adicCompletion M) X)) ≤ 1 := by
    intro X hXw hXu
    obtain ⟨a, ha⟩ := Submodule.mem_one.1
      (Submodule.mem_comap.1 (h ((mem_inv_pow_iff w n X).2 ⟨hXw, hXu⟩)))
    have ha' : algebraMap (𝓞 K) K a = Algebra.trace K M X := ha
    have htot : Valued.v (algebraMap K (v.adicCompletion K) (Algebra.trace K M X)) ≤ 1 := by
      rw [← ha', ← IsScalarTower.algebraMap_apply]
      exact valued_algebraMap_int_le_one v a
    rw [algebraMap_trace_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ w0)] at htot
    have hrest : Valued.v (∑ u ∈ Finset.univ.erase w0,
        Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
          (algebraMap M (u.1.adicCompletion M) X)) ≤ 1 :=
      Valuation.map_sum_le _ fun u hu ↦ valued_trace_le_one_of_valuation_le_one v u
        (hXu u.1 fun he ↦ Finset.ne_of_mem_erase hu (Subtype.ext he))
    have hsplit : Algebra.trace (v.adicCompletion K) (w.adicCompletion M)
        (algebraMap M (w.adicCompletion M) X) =
        (Algebra.trace (v.adicCompletion K) (w0.1.adicCompletion M)
          (algebraMap M (w0.1.adicCompletion M) X) + ∑ u ∈ Finset.univ.erase w0,
            Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
              (algebraMap M (u.1.adicCompletion M) X)) - ∑ u ∈ Finset.univ.erase w0,
            Algebra.trace (v.adicCompletion K) (u.1.adicCompletion M)
              (algebraMap M (u.1.adicCompletion M) X) := by
      rw [add_sub_cancel_right]
    rw [hsplit]
    exact (Valuation.map_sub _ _ _).trans (max_le htot hrest)
  rw [← forall_valued_trace_le_one_iff v w n]
  intro y hy
  obtain ⟨x0, hx0w, hx0u⟩ := exists_valuation_eq_exp w n
  set X0 := algebraMap M (w.adicCompletion M) x0 with hX0def
  have hX0 : Valued.v X0 = WithZero.exp (n : ℤ) := by
    rw [hX0def, valued_algebraMap_field]
    exact hx0w
  have hX00 : X0 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hX0
    exact WithZero.zero_ne_coe hX0
  set z := X0⁻¹ * y with hzdef
  have hz : Valued.v z ≤ 1 := by
    rw [hzdef, map_mul, map_inv₀, hX0]
    calc (WithZero.exp (n : ℤ))⁻¹ * Valued.v y
        ≤ (WithZero.exp (n : ℤ))⁻¹ * WithZero.exp (n : ℤ) := by gcongr
      _ = 1 := inv_mul_cancel₀ (by simp)
  have hzmem : z ∈ (w.adicCompletionIntegers M : Set (w.adicCompletion M)) := hz
  have hopen : IsOpen ((fun s ↦ X0 * (z - s)) ⁻¹'
      ((Valued.v : Valuation (w.adicCompletion M) ℤᵐ⁰).integer : Set (w.adicCompletion M))) :=
    (Valued.isOpen_integer (w.adicCompletion M)).preimage (continuous_const.mul (continuous_const.sub continuous_id))
  have hzU : z ∈ ((fun s ↦ X0 * (z - s)) ⁻¹'
      ((Valued.v : Valuation (w.adicCompletion M) ℤᵐ⁰).integer : Set (w.adicCompletion M))) := by
    simp
  obtain ⟨_, hs, b, rfl⟩ := mem_closure_iff.1
    (adicCompletionIntegers_subset_closure_ringOfIntegers w hzmem) _ hopen hzU
  have hs' : Valued.v (X0 * (z - algebraMap M (w.adicCompletion M) (algebraMap (𝓞 M) M b))) ≤ 1 :=
    hs
  have hb : ∀ u : HeightOneSpectrum (𝓞 M), u.valuation M (algebraMap (𝓞 M) M b) ≤ 1 :=
    fun u ↦ u.valuation_le_one b
  have key := hX (x0 * algebraMap (𝓞 M) M b)
    (by simpa [map_mul, hx0w] using mul_le_mul' (le_refl (WithZero.exp (n : ℤ))) (hb w))
    (fun u hu ↦ by simpa [map_mul] using mul_le_mul' (hx0u u hu) (hb u))
  have hy : y = X0 * (z - algebraMap M (w.adicCompletion M) (algebraMap (𝓞 M) M b)) +
      algebraMap M (w.adicCompletion M) (x0 * algebraMap (𝓞 M) M b) := by
    rw [map_mul, ← hX0def, hzdef, mul_sub, ← mul_assoc, mul_inv_cancel₀ hX00, one_mul,
      sub_add_cancel]
  rw [hy, map_add]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ key)
  refine (forall_valued_trace_le_one_iff v w 0).2 (Nat.zero_le _) _ ?_
  rw [Nat.cast_zero, WithZero.exp_zero]
  exact hs'

theorem multiplicity_differentIdeal :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) =
      differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [emultiplicity_eq_coe, Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  refine ⟨differentIdeal_le_pow_of_le_differentExponent v w le_rfl, fun h ↦ ?_⟩
  have := le_differentExponent_of_differentIdeal_le_pow v w h
  omega

end Comparison

section Main

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem multiplicity_differentIdeal_eq_differentExponent (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
    [iA : Algebra (v.adicCompletion K) (w.adicCompletion M)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)] :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) =
      differentExponent (v.adicCompletion K) (w.adicCompletion M) := by
  have h : iA = SemiLocal.algebraCompletion v w := Algebra.algebra_ext _ _ fun r ↦ by
    rw [algebraMap_adicCompletion_eq v w]
    rfl
  subst h
  exact multiplicity_differentIdeal v w

open SemiLocal in

theorem multiplicity_relDiscr_semiLocal (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal (relDiscr K M) =
      ∑ w : PlacesOver M v, w.1.asIdeal.inertiaDeg (𝓞 K) *
        differentExponent (v.adicCompletion K) (w.1.adicCompletion M) := by
  rw [multiplicity_relDiscr_eq_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [multiplicity_differentIdeal_eq_differentExponent v w.1]

end Main

end GroundTheory.Global
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module IntermediateField

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section LocalLinear

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem charArtinConductor_const_mul_sum {ι : Type*} (s : Finset ι) (c : ℂ)
    (χ : ι → (L ≃ₐ[K] L) → ℂ) :
    charArtinConductor K L (fun σ ↦ c * ∑ i ∈ s, χ i σ) =
      c * ∑ i ∈ s, charArtinConductor K L (χ i) := by
  simp only [charArtinConductor, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun σ _ ↦ by ring

end LocalLinear

section LocalTower

variable {K F L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
  [ValuativeExtension K F] [ValuativeExtension F L] [ValuativeExtension K L]
  [FiniteDimensional K F] [FiniteDimensional F L] [FiniteDimensional K L] [IsGalois K L]

omit [ValuativeExtension K F] [FiniteDimensional K F] [IsGalois K L] in

theorem lowerIndex_restrictScalars_tower (σ : L ≃ₐ[F] L) :
    lowerIndex K L (σ.restrictScalars K) = lowerIndex F L σ :=
  rfl

open Classical in

theorem artinCharacter_restrictScalars_tower (h : L ≃ₐ[F] L) :
    (artinCharacter K L (h.restrictScalars K) : ℂ) =
      residueDegree K F * artinCharacter F L h +
        if h = 1 then (Nat.card (L ≃ₐ[F] L) : ℂ) * (residueDegree K F * differentExponent K F : ℕ)
        else 0 := by
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  by_cases h1 : h = 1
  · subst h1
    rw [if_pos rfl, show (1 : L ≃ₐ[F] L).restrictScalars K = 1 from AlgEquiv.ext fun _ ↦ rfl,
      artinCharacter_one, artinCharacter_one, IsGalois.card_aut_eq_finrank,
      ← ramificationIndex_mul_residueDegree F L, residueDegree_tower K F L,
      differentExponent_tower K F L]
    push_cast
    ring
  · have h1' : h.restrictScalars K ≠ 1 := by
      intro h'
      apply h1
      ext x
      exact congrArg (fun σ : L ≃ₐ[K] L ↦ σ x) h'
    rw [if_neg h1, artinCharacter_of_ne_one h1', artinCharacter_of_ne_one h1,
      lowerIndex_restrictScalars_tower, residueDegree_tower K F L]
    push_cast
    ring

theorem sum_mul_artinCharacter_restrictScalars (ψ : (L ≃ₐ[F] L) → ℂ) :
    ∑ h : L ≃ₐ[F] L, ψ h * (artinCharacter K L (h.restrictScalars K) : ℂ) =
      Nat.card (L ≃ₐ[F] L) * (residueDegree K F * charArtinConductor F L ψ +
        ((residueDegree K F * differentExponent K F : ℕ) : ℂ) * ψ 1) := by
  classical
  have hH : (Nat.card (L ≃ₐ[F] L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp_rw [artinCharacter_restrictScalars_tower, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  have hs : ∑ h : L ≃ₐ[F] L, ψ h * ((residueDegree K F : ℂ) * artinCharacter F L h) =
      residueDegree K F * ∑ h : L ≃ₐ[F] L, ψ h * artinCharacter F L h := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ ↦ by ring
  rw [hs, charArtinConductor]
  field_simp

end LocalTower

section Tower

open Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (u : HeightOneSpectrum (𝓞 (fixedField H))) (w : HeightOneSpectrum (𝓞 L))

omit [IsGalois K L] in

theorem coe_symm_fixedFieldMulEquiv_mem_stabilizer
    (τ : MulAction.stabilizer Gal(L/fixedField H) w.asIdeal) :
    (((fixedFieldMulEquiv H).symm τ : H) : Gal(L/K)) ∈ MulAction.stabilizer Gal(L/K) w.asIdeal := by
  rw [MulAction.mem_stabilizer_iff]
  have h := fixedFieldMulEquiv_smul_ideal H ((fixedFieldMulEquiv H).symm τ) w.asIdeal
  rw [MulEquiv.apply_symm_apply] at h
  change _ = (((fixedFieldMulEquiv H).symm τ : H) : Gal(L/K)) • w.asIdeal at h
  rw [← h]
  exact τ.2

variable [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal]

attribute [local instance] isScalarTower_adicCompletion

theorem decompositionMulEquiv_restrictScalars
    (τ : MulAction.stabilizer Gal(L/fixedField H) w.asIdeal) :
    decompositionMulEquiv v w ⟨(((fixedFieldMulEquiv H).symm τ : H) : Gal(L/K)),
        coe_symm_fixedFieldMulEquiv_mem_stabilizer H w τ⟩ =
      (decompositionMulEquiv u w τ).restrictScalars (v.adicCompletion K) := by
  refine algEquiv_ext_adicCompletion v w (continuous_decompositionAlgEquiv v w _)
    (by exact continuous_decompositionAlgEquiv u w τ) fun x ↦ ?_
  rw [decompositionMulEquiv_apply, AlgEquiv.restrictScalars_apply, decompositionMulEquiv_apply,
    decompositionToLocal_algebraMap, decompositionToLocal_algebraMap]
  rfl

theorem localToGlobal_restrictScalars
    (S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H))) :
    localToGlobal v w (S.restrictScalars (v.adicCompletion K)) =
      (localToGlobal u w S).restrictScalars K := by
  obtain ⟨τ, rfl⟩ := (decompositionMulEquiv u w).surjective S
  rw [← decompositionMulEquiv_restrictScalars H v u w τ, localToGlobal_decompositionMulEquiv,
    localToGlobal_decompositionMulEquiv]
  rfl

omit [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] in

theorem localToGlobal_injective : Function.Injective (localToGlobal v w) :=
  fun _ _ h ↦ (decompositionMulEquiv v w).symm.injective (Subtype.ext h)

theorem exists_restrictScalars_eq {T : Gal(w.adicCompletion L/v.adicCompletion K)}
    (hT : localToGlobal v w T ∈ H) :
    ∃ S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)),
      S.restrictScalars (v.adicCompletion K) = T := by
  set g : H := ⟨localToGlobal v w T, hT⟩
  have hg : fixedFieldMulEquiv H g ∈ MulAction.stabilizer Gal(L/fixedField H) w.asIdeal := by
    rw [MulAction.mem_stabilizer_iff, fixedFieldMulEquiv_smul_ideal]
    exact ((decompositionMulEquiv v w).symm T).2
  refine ⟨decompositionMulEquiv u w ⟨_, hg⟩, localToGlobal_injective v w ?_⟩
  rw [localToGlobal_restrictScalars H v u w, localToGlobal_decompositionMulEquiv]
  exact AlgEquiv.ext fun _ ↦ rfl

theorem sum_extendByZero_mul_artinCharacter (χ : H → ℂ) :
    ∑ T : Gal(w.adicCompletion L/v.adicCompletion K),
        extendByZero H χ (localToGlobal v w T) *
          (artinCharacter (v.adicCompletion K) (w.adicCompletion L) T : ℂ) =
      ∑ S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)),
        χ ((fixedFieldMulEquiv H).symm (localToGlobal u w S)) *
          (artinCharacter (v.adicCompletion K) (w.adicCompletion L)
            (S.restrictScalars (v.adicCompletion K)) : ℂ) := by
  classical
  set F : Gal(w.adicCompletion L/v.adicCompletion K) → ℂ := fun T ↦
    extendByZero H χ (localToGlobal v w T) *
      (artinCharacter (v.adicCompletion K) (w.adicCompletion L) T : ℂ) with hF
  have hinj : Function.Injective
      (fun S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)) ↦
        S.restrictScalars (v.adicCompletion K)) := AlgEquiv.restrictScalars_injective _
  have hterm : ∀ S : Gal(w.adicCompletion L/u.adicCompletion (fixedField H)),
      χ ((fixedFieldMulEquiv H).symm (localToGlobal u w S)) *
        (artinCharacter (v.adicCompletion K) (w.adicCompletion L)
          (S.restrictScalars (v.adicCompletion K)) : ℂ) =
        F (S.restrictScalars (v.adicCompletion K)) := by
    intro S
    rw [hF]
    simp only
    rw [localToGlobal_restrictScalars H v u w,
      extendByZero_of_mem H χ (restrictScalars_mem H (localToGlobal u w S))]
    rfl
  symm
  rw [Finset.sum_congr rfl fun S _ ↦ hterm S, ← Finset.sum_image fun _ _ _ _ h ↦ hinj h]
  refine Finset.sum_subset (Finset.subset_univ _) fun T _ hT ↦ ?_
  by_cases hmem : localToGlobal v w T ∈ H
  · obtain ⟨S, hS⟩ := exists_restrictScalars_eq H v u w hmem
    exact absurd (Finset.mem_image.2 ⟨S, Finset.mem_univ _, hS⟩) hT
  · rw [hF]
    simp only
    rw [extendByZero_of_notMem H χ hmem, zero_mul]

theorem charArtinConductor_extendByZero {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ Gal(L/fixedField H) V) :
    charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
        (fun T ↦ extendByZero H (charOnSubgroup H ρ) (localToGlobal v w T)) =
      (Nat.card Gal(w.adicCompletion L/v.adicCompletion K) : ℂ)⁻¹ *
        Nat.card Gal(w.adicCompletion L/u.adicCompletion (fixedField H)) *
        (residueDegree (v.adicCompletion K) (u.adicCompletion (fixedField H)) *
          ((differentExponent (v.adicCompletion K) (u.adicCompletion (fixedField H)) *
            finrank ℂ V + artinExponent u ρ : ℕ) : ℂ)) := by
  have hχ : ∀ σ, charOnSubgroup H ρ ((fixedFieldMulEquiv H).symm σ) = ρ.character σ := fun σ ↦ by
    simp only [charOnSubgroup, MulEquiv.apply_symm_apply]
  simp_rw [charArtinConductor, sum_extendByZero_mul_artinCharacter H v u w, hχ]
  rw [
    sum_mul_artinCharacter_restrictScalars (ψ := fun S ↦ ρ.character (localToGlobal u w S)),
    ← natCast_artinExponent u ρ w, map_one, Representation.char_one]
  push_cast
  ring

end Tower

section Global

open Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem natCard_gal_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Nat.card Gal(w.adicCompletion L/v.adicCompletion K) =
      v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) := by
  rw [← Nat.card_congr (decompositionMulEquiv v w).toEquiv,
    Ideal.card_stabilizer_eq v.asIdeal w.asIdeal]

theorem charArtinConductor_conj (v : HeightOneSpectrum (𝓞 K)) (σ : Gal(L/K))
    (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
    (h : w' = σ • w) (F : Gal(L/K) → ℂ) :
    charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
        (fun T ↦ F (σ * localToGlobal v w T * σ⁻¹)) =
      charArtinConductor (v.adicCompletion K) (w'.adicCompletion L)
        (fun T ↦ F (localToGlobal v w' T)) := by
  rw [← charArtinConductor_autCongr (SemiLocal.galEquiv v σ w w' h)]
  congr 1
  funext T
  rw [localToGlobal_autCongr v σ w w' h]

open Classical in

theorem sum_eq_sum_doubleCoset {G : Type*} [Group G] [Fintype G] (H D : Subgroup G) (F : G → ℂ)
    (hF : ∀ x : G, ∀ h ∈ H, ∀ e ∈ D, F (h * x * e) = F x) :
    ∑ t : G, F t = ∑ q : DoubleCoset.Quotient (H : Set G) D,
      (Nat.card H * Nat.card D : ℂ) /
        Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup G).subgroupOf D) * F q.out := by
  rw [← Finset.sum_fiberwise Finset.univ (DoubleCoset.mk H D) F]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have key := sum_mul_mul_eq H D q.out F
  rw [DoubleCoset.out_eq'] at key
  have hE0 : (Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup G).subgroupOf D) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hL : ∑ h : H, ∑ e : D, F (h * q.out * e) = (Nat.card H * Nat.card D : ℂ) * F q.out := by
    rw [Finset.sum_congr rfl fun (h : H) _ ↦ Finset.sum_congr rfl fun (e : D) _ ↦ hF q.out h h.2 e e.2,
      Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, nsmul_eq_mul,
      nsmul_eq_mul, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    ring
  rw [hL] at key
  rw [div_mul_eq_mul_div, key]
  field_simp

variable (H : Subgroup Gal(L/K)) {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ Gal(L/fixedField H) V)

theorem natCast_artinExponent_ind (v : HeightOneSpectrum (𝓞 K)) :
    (artinExponent v (ρ.ind (AlgEquiv.restrictScalarsHom K)) : ℂ) =
      ∑ u : SemiLocal.PlacesOver (fixedField H) v,
        (residueDegree (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) : ℂ) *
          ((differentExponent (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) *
            finrank ℂ V + artinExponent u.1 ρ : ℕ) : ℂ) := by
  classical
  set w := placeAbove (L := L) v with hw
  set D := MulAction.stabilizer Gal(L/K) w.asIdeal with hD
  set c : SemiLocal.PlacesOver (fixedField H) v → ℂ := fun u ↦
    (residueDegree (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) : ℂ) *
      ((differentExponent (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) *
        finrank ℂ V + artinExponent u.1 ρ : ℕ) : ℂ) with hc
  set U : Gal(L/K) → SemiLocal.PlacesOver (fixedField H) v := fun t ↦
    ⟨subfieldPlace H w t, subfieldPlace_liesOver H v w t⟩ with hU
  set g : SemiLocal.PlacesOver (fixedField H) v → ℕ := fun u ↦
    u.1.asIdeal.ramificationIdxIn (𝓞 L) * u.1.asIdeal.inertiaDegIn (𝓞 L) with hg
  set χ := charOnSubgroup H ρ with hχ
  have hDcard : Nat.card D = v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) :=
    Ideal.card_stabilizer_eq v.asIdeal w.asIdeal

  have hterm : ∀ t : Gal(L/K), charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
      (fun T ↦ extendByZero H χ (t * localToGlobal v w T * t⁻¹)) =
        (Nat.card D : ℂ)⁻¹ * (g (U t) * c (U t)) := by
    intro t
    have : (t • w).asIdeal.LiesOver v.asIdeal :=
      (inferInstance : (t • w.asIdeal).LiesOver v.asIdeal)
    have : (t • w).asIdeal.LiesOver (U t).1.asIdeal := liesOver_subfieldPlace H w t
    have : (U t).1.asIdeal.LiesOver v.asIdeal := (U t).2
    rw [charArtinConductor_conj v t w (t • w) rfl (extendByZero H χ),
      charArtinConductor_extendByZero H v (U t).1 (t • w) ρ, natCard_gal_adicCompletion v (t • w),
      natCard_gal_adicCompletion (U t).1 (t • w), hDcard]
    simp only [hg, hc]
    push_cast
    ring

  have hgd : ∀ x : Gal(L/K), (g (U x) : ℂ) =
      Nat.card ((MulAut.conj x⁻¹ • H : Subgroup Gal(L/K)).subgroupOf D) := by
    intro x
    have : (x • w.asIdeal).LiesOver (U x).1.asIdeal := liesOver_subfieldPlace H w x
    rw [Nat.card_congr (conjSubgroupOfEquiv H D x),
      ← Subgroup.card_map_of_injective (f := (fixedFieldMulEquiv H).toMonoidHom)
        (fixedFieldMulEquiv H).injective,
      ← stabilizer_fixedField_smul_eq H w x,
      Ideal.card_stabilizer_eq (U x).1.asIdeal (x • w.asIdeal)]
  have hinv : ∀ x : Gal(L/K), ∀ h ∈ H, ∀ e ∈ D, U (h * x * e) = U x := by
    intro x h hh e he
    exact Subtype.ext ((subfieldPlace_eq_iff H w (h * x * e) x).2
      ((DoubleCoset.eq H D _ _).2 ⟨h⁻¹, H.inv_mem hh, e⁻¹, D.inv_mem he, by group⟩))
  rw [natCast_artinExponent v _ w, character_ind_restrictScalarsHom]
  simp_rw [indFun_subtype_apply]
  rw [charArtinConductor_const_mul_sum]
  have hsum : ∑ t : Gal(L/K), charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
      (fun T ↦ extendByZero H χ (t⁻¹ * localToGlobal v w T * t)) =
        ∑ t : Gal(L/K), charArtinConductor (v.adicCompletion K) (w.adicCompletion L)
          (fun T ↦ extendByZero H χ (t * localToGlobal v w T * t⁻¹)) :=
    Fintype.sum_equiv (Equiv.inv _) _ _ fun t ↦ by simp only [Equiv.inv_apply, inv_inv]
  rw [hsum, Finset.sum_congr rfl fun t _ ↦ hterm t, ← Finset.mul_sum,
    sum_eq_sum_doubleCoset H D (fun t ↦ (g (U t) : ℂ) * c (U t))
      (fun x h hh e he ↦ by simp only [hinv x h hh e he])]
  have hD0 : (Nat.card D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hH0 : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hq : ∀ q : DoubleCoset.Quotient (H : Set Gal(L/K)) D,
      (Nat.card H * Nat.card D : ℂ) /
        Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup Gal(L/K)).subgroupOf D) *
          ((g (U q.out) : ℂ) * c (U q.out)) = Nat.card H * Nat.card D * c (U q.out) := by
    intro q
    have hE0 : (Nat.card ((MulAut.conj q.out⁻¹ • H : Subgroup Gal(L/K)).subgroupOf D) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [hgd q.out]
    field_simp
  rw [Finset.sum_congr rfl fun q _ ↦ hq q, ← Finset.mul_sum]
  have hequiv : ∑ q : DoubleCoset.Quotient (H : Set Gal(L/K)) D, c (U q.out) =
      ∑ u : SemiLocal.PlacesOver (fixedField H) v, c u := by
    refine Fintype.sum_equiv (subfieldPlaceEquiv H v w) _ _ fun q ↦ ?_
    congr 1
    apply Subtype.ext
    have h := subfieldPlaceEquiv_mk H v w q.out
    rw [DoubleCoset.out_eq'] at h
    exact h.symm
  rw [hequiv]
  field_simp

theorem artinExponent_ind (v : HeightOneSpectrum (𝓞 K)) :
    artinExponent v (ρ.ind (AlgEquiv.restrictScalarsHom K)) =
      ∑ u : SemiLocal.PlacesOver (fixedField H) v, u.1.asIdeal.inertiaDeg (𝓞 K) *
        (differentExponent (v.adicCompletion K) (u.1.adicCompletion (fixedField H)) * finrank ℂ V +
          artinExponent u.1 ρ) := by
  apply Nat.cast_injective (R := ℂ)
  rw [natCast_artinExponent_ind]
  push_cast
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← inertiaDeg_integer v u.1]

omit [IsGalois K L] in

theorem multiplicity_artinConductorIdeal [IsGalois K L] {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ Gal(L/K) W) (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal (artinConductorIdeal σ) = artinExponent v σ :=
  multiplicity_finprod_asIdeal_pow (finite_support_artinExponent K σ) v

theorem artinConductorIdeal_ind :
    artinConductorIdeal (ρ.ind (AlgEquiv.restrictScalarsHom K)) =
      relDiscr K (fixedField H) ^ finrank ℂ V * Ideal.relNorm (𝓞 K) (artinConductorIdeal ρ) := by
  have hN : Ideal.relNorm (𝓞 K) (artinConductorIdeal ρ) ≠ ⊥ :=
    (Ideal.relNorm_eq_bot_iff (R := 𝓞 K)).not.2 (artinConductorIdeal_ne_bot ρ)
  have hJ : relDiscr K (fixedField H) ^ finrank ℂ V * Ideal.relNorm (𝓞 K) (artinConductorIdeal ρ) ≠
      ⊥ := mul_ne_zero (pow_ne_zero _ (relDiscr_ne_bot K _)) hN
  rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hJ, artinConductorIdeal]
  refine finprod_congr fun v ↦ congrArg (v.asIdeal ^ ·) ?_
  have hp := prime_asIdeal v
  rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp hJ),
    (FiniteMultiplicity.of_prime_left hp (relDiscr_ne_bot K _)).multiplicity_pow hp,
    multiplicity_relDiscr_semiLocal v, multiplicity_relNorm v _ (artinConductorIdeal_ne_bot ρ),
    artinExponent_ind]
  simp only [multiplicity_artinConductorIdeal]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ ↦ by ring

end Global

end GroundTheory.Global
end
end
