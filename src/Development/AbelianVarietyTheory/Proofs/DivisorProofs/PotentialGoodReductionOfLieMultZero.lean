import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionPullbackCartesianGroupSchemesStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Definitions.Divisors.IntLatGEqCanLatOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackOfGroupSchemeModelBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyPotentialSemiAbelianSplitTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCharacterEndOfTorusExtensionAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusMapOfCharHom

section
section
open NumberField Matrix

namespace GlobalTheory.PrimAnnih

theorem exists_unit_coeff {W V ι : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [AddCommGroup V] [Module W V] [NoZeroSMulDivisors W V] [Fintype ι] (u : ι → V) (w : ι → W)
    (hw : w ≠ 0) (h : ∑ i, w i • u i = 0) :
    ∃ v : ι → W, (∃ i, IsUnit (v i)) ∧ ∑ i, v i • u i = 0 := by
  classical
  let I : Ideal W := Ideal.span (Set.range w)
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal I).principal
  have hdvd : ∀ i, c ∣ w i := fun i => by
    have : w i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    rw [hc] at this
    exact Ideal.mem_span_singleton.1 this
  choose v hv using hdvd
  have hcI : c ∈ I := by rw [hc]; exact Submodule.mem_span_singleton_self c
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hcI
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hw; funext i; rw [hv i, zero_mul]; rfl
  have hsum : ∑ i, a i * v i = 1 := by
    apply mul_left_cancel₀ hc0
    rw [mul_one, Finset.mul_sum]
    conv_rhs => rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv i]; ring
  refine ⟨v, ?_, ?_⟩
  · by_contra hnu
    push_neg at hnu
    have h1 : (1 : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [← hsum]
      exact Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu i))
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · have h2 : c • ∑ i, v i • u i = 0 := by
      rw [Finset.smul_sum, ← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← hv i]
    exact (smul_eq_zero.1 h2).resolve_left hc0

theorem exists_vecMul_eq_zero {W Ω ι κ : Type} [CommRing W] [IsDomain W] [Field Ω] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (f : W →+* Ω) (hf : Function.Injective f)
    (A : Matrix ι κ W) (x : ι → Ω) (hx : x ≠ 0) (h : x ᵥ* A.map f = 0) :
    ∃ w : ι → W, w ≠ 0 ∧ w ᵥ* A = 0 := by
  classical
  by_contra H
  push_neg at H
  let L := FractionRing W
  let g : L →+* Ω := IsFractionRing.lift hf
  have hg : ∀ r, g (algebraMap W L r) = f r := fun r => IsFractionRing.lift_algebraMap hf r
  let AL : Matrix ι κ L := A.map (algebraMap W L)
  have hker : LinearMap.ker AL.vecMulLinear = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro l hl
    obtain ⟨⟨c, hc⟩, hint⟩ :=
      IsLocalization.exist_integer_multiples (nonZeroDivisors W) Finset.univ l
    choose w hw using fun i => RingHom.mem_rangeS.1 (hint i (Finset.mem_univ i))
    have hl' : l ᵥ* AL = 0 := hl
    have h1 : w ᵥ* A = 0 := by
      funext j
      apply IsFractionRing.injective W L
      rw [RingHom.map_vecMul, Pi.zero_apply, map_zero]
      have e : (algebraMap W L ∘ w) = fun i => algebraMap W L c * l i := by
        funext i; simpa [Algebra.smul_def] using hw i
      rw [e]
      have := congrFun hl' j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this ⊢
      simp only [mul_assoc, ← Finset.mul_sum, this, mul_zero, AL]
    have hw0 : w = 0 := by
      by_contra hw0; exact H w hw0 h1
    funext i
    have e1 := hw i
    rw [hw0, Pi.zero_apply, map_zero, Algebra.smul_def] at e1
    have hc0 : algebraMap W L c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
    exact (mul_eq_zero.1 e1.symm).resolve_left hc0
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective AL.vecMulLinear hker
  let P := LinearMap.toMatrix' G
  have hP : AL * P.transpose = 1 := by
    ext i j
    have := congrArg (fun φ => φ (Pi.single i 1) j) hG
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [← LinearMap.toMatrix'_mulVec G] at this
    rw [Matrix.mul_apply, Matrix.one_apply,
      show (if i = j then (1:L) else 0) = (Pi.single i (1:L) : ι → L) j by simp [Pi.single_apply, eq_comm], ← this]
    simp [Matrix.mulVec, dotProduct, P, mul_comm, Matrix.vecMulLinear_apply]
  have hAf : AL.map g = A.map f := by ext i j; simp [AL, hg]
  have hP' : A.map f * (P.transpose.map g) = 1 := by
    rw [← hAf, ← Matrix.map_mul, hP, Matrix.map_one _ (map_zero g) (map_one g)]
  apply hx
  rw [← Matrix.vecMul_one x, ← hP', ← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]

end GlobalTheory.PrimAnnih

namespace GlobalTheory.PrimAnnih

theorem exists_extend (F Ω : Type) [Field F] [NumberField F] [Field Ω] [CharZero Ω]
    (σ : 𝓞 F →+* Ω) : ∃ σ' : F →ₐ[ℚ] Ω, ∀ a : 𝓞 F, σ' (algebraMap (𝓞 F) F a) = σ a := by
  have hk : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [RingHom.comap_ker, show σ.comp (algebraMap ℤ (𝓞 F)) = Int.castRingHom Ω from
      RingHom.ext_int _ _]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Int.cast_injective
  have hinj : Function.Injective σ := (RingHom.injective_iff_ker_eq_bot σ).2 hk
  exact ⟨(IsFractionRing.lift hinj : F →+* Ω).toRatAlgHom,
    fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem exists_primitive_annihilator : ∀ (F : Type) [Field F] [NumberField F] (W Ω : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (f : W →+* Ω), Function.Injective f → ∀ (n : ℕ) (M : 𝓞 F →+* Matrix (Fin n) (Fin n) W) (σ : 𝓞 F →+* Ω), (∀ c : Fin n → Ω, (∀ a, ((M a).map f).mulVec c = σ a • c) → c = 0) → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)), ∃ w : ι → W, (∃ i, IsUnit (w i)) ∧ ∑ i, w i • M (b i) = 0 := by
  intro F _ _ W Ω _ _ _ _ _ _ f hf n M σ hσ ι _ b
  classical
  let b' : Module.Basis ι ℚ F := Module.Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) F b
  have hb' : ∀ i, b' i = algebraMap (𝓞 F) F (b i) := fun i =>
    Module.Basis.localizationLocalization_apply ℚ (nonZeroDivisors ℤ) F b i
  obtain ⟨σ', hσ'⟩ := exists_extend F Ω σ
  have hcard : Fintype.card ι = Fintype.card (F →ₐ[ℚ] Ω) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b']
  let q := Fintype.equivOfCardEq hcard
  let P := Algebra.embeddingsMatrixReindex ℚ Ω b' q
  have hPij : ∀ i j, P i j = q j (b' i) := fun i j => by
    simp [P, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  have hP : P.det ≠ 0 := by
    have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω b' q
    intro h0
    rw [h0, zero_pow two_ne_zero, map_eq_zero] at hd
    exact Algebra.discr_not_zero_of_basis ℚ b' hd
  have inj : ∀ z : ι → Ω, (∀ τ : F →ₐ[ℚ] Ω, ∑ i, z i * τ (b' i) = 0) → z = 0 := by
    intro z hz
    refine Matrix.eq_zero_of_vecMul_eq_zero hP (funext fun j => ?_)
    simpa [Matrix.vecMul, dotProduct, hPij] using hz (q j)
  let y : ι → Ω := fun j => if q j = σ' then 1 else 0
  let x : ι → Ω := y ᵥ* P⁻¹
  have hx : ∀ τ, ∑ i, x i * τ (b' i) = if τ = σ' then 1 else 0 := by
    intro τ
    have h1 : x ᵥ* P = y := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP),
        Matrix.vecMul_one]
    have := congrFun h1 (q.symm τ)
    simpa [Matrix.vecMul, dotProduct, hPij, y] using this

  let Φ : 𝓞 F →+* Matrix (Fin n) (Fin n) Ω := f.mapMatrix.comp M
  have hΦ : ∀ a, Φ a = (M a).map f := fun a => rfl
  have hcoef : ∀ (a : 𝓞 F) j, ∑ i, x i * (b.repr (a * b i) j : Ω) = σ a * x j := by
    intro a
    have hrep : ∀ i (τ : F →ₐ[ℚ] Ω), ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) =
        τ (algebraMap (𝓞 F) F a) * τ (b' i) := by
      intro i τ
      have e := congrArg (fun t : 𝓞 F => τ (algebraMap (𝓞 F) F t)) (b.sum_repr (a * b i))
      simp only [map_sum, map_zsmul, map_mul, zsmul_eq_mul] at e
      simpa [hb'] using e
    have := inj (fun j => ∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) (fun τ => by
      have key : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) =
          τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i) := by
        calc ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j)
            = ∑ j, ∑ i, x i * ((b.repr (a * b i) j : Ω) * τ (b' j)) := by
              simp only [Finset.sum_mul, mul_assoc]
          _ = ∑ i, x i * ∑ j, (b.repr (a * b i) j : Ω) * τ (b' j) := by
              rw [Finset.sum_comm]; simp only [Finset.mul_sum]
          _ = ∑ i, x i * (τ (algebraMap (𝓞 F) F a) * τ (b' i)) := by simp only [hrep]
          _ = τ (algebraMap (𝓞 F) F a) * ∑ i, x i * τ (b' i) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω) - σ a * x j) * τ (b' j) =
          ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) * τ (b' j) -
            σ a * ∑ j, x j * τ (b' j) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      rw [e2, key, hx]
      split_ifs with hτ
      · subst hτ; rw [hσ']; ring
      · ring)
    intro j
    exact sub_eq_zero.1 (congrFun this j)
  let N : Matrix (Fin n) (Fin n) Ω := ∑ i, x i • Φ (b i)
  have hN : ∀ a, Φ a * N = σ a • N := by
    intro a
    calc Φ a * N = ∑ i, x i • Φ (a * b i) := by
          simp only [N, Finset.mul_sum, Matrix.mul_smul, map_mul]
      _ = ∑ i, x i • ∑ j, (b.repr (a * b i) j : Ω) • Φ (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (a * b i)]
          simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
      _ = ∑ j, (∑ i, x i * (b.repr (a * b i) j : Ω)) • Φ (b j) := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
      _ = ∑ j, (σ a * x j) • Φ (b j) := by simp only [hcoef]
      _ = σ a • N := by simp only [N, Finset.smul_sum, smul_smul]
  have hN0 : N = 0 := by
    ext j k
    have := hσ (fun j => N j k) (fun a => by
      funext r
      have e := congrFun (congrFun (hN a) r) k
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hΦ] using e)
    simpa using congrFun this j
  let A : Matrix ι (Fin n × Fin n) W := Matrix.of fun i p => M (b i) p.1 p.2
  have hx0 : x ≠ 0 := by
    intro h0
    have := hx σ'
    simp [h0] at this
  have hxA : x ᵥ* A.map f = 0 := by
    funext p
    have := congrFun (congrFun hN0 p.1) p.2
    simpa [Matrix.vecMul, dotProduct, A, N, hΦ, Matrix.sum_apply, mul_comm] using this
  obtain ⟨w, hw0, hwA⟩ := exists_vecMul_eq_zero f hf A x hx0 hxA
  haveI : NoZeroSMulDivisors W (Matrix (Fin n) (Fin n) W) :=
    inferInstanceAs (NoZeroSMulDivisors W (Fin n → Fin n → W))
  refine exists_unit_coeff (fun i => M (b i)) w hw0 ?_
  ext j k
  have := congrFun hwA (j, k)
  simpa [Matrix.vecMul, dotProduct, A, Matrix.sum_apply, mul_comm] using this

end GlobalTheory.PrimAnnih
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_annihilator' : ∀ (F : Type) [Field F] [NumberField F] (W Ω : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (f : W →+* Ω), Function.Injective f → ∀ (n : ℕ) (M : 𝓞 F →+* Matrix (Fin n) (Fin n) W) (σ : 𝓞 F →+* Ω), (∀ c : Fin n → Ω, (∀ a, ((M a).map f).mulVec c = σ a • c) → c = 0) → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)), ∃ w : ι → W, (∃ i, IsUnit (w i)) ∧ ∑ i, w i • M (b i) = 0 := by
  atlas_forward_decl GlobalTheory.PrimAnnih.exists_primitive_annihilator
end

section
section
open NumberField Polynomial

namespace GlobalTheory

theorem ringOfIntegers_action_injective (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Nontrivial X] (ρ : 𝓞 F →+* Module.End ℤ X) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : a ∈ RingHom.ker ρ := ha
  have hn : ((Ideal.absNorm (RingHom.ker ρ) : ℕ) : 𝓞 F) ∈ RingHom.ker ρ := Ideal.absNorm_mem _
  rw [RingHom.mem_ker, map_natCast] at hn
  obtain ⟨χ, hχ⟩ := exists_ne (0 : X)
  have h1 : (Ideal.absNorm (RingHom.ker ρ) : ℕ) • χ = 0 := by
    have := congrArg (fun f : Module.End ℤ X => f χ) hn
    simpa using this
  rw [← Nat.cast_smul_eq_nsmul ℤ] at h1
  have h2 : Ideal.absNorm (RingHom.ker ρ) = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact_mod_cast h
    · exact absurd h hχ
  rw [Ideal.absNorm_eq_zero_iff] at h2
  rw [h2] at hmem
  simpa using hmem

theorem dvd_coord_of_action_dvd (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Nontrivial X]
    (ρ : 𝓞 F →+* Module.End ℤ X) (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F))
    (p : ℤ) (hp : p ≠ 0) (a : 𝓞 F)
    (h : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      p ∣ (Module.Free.chooseBasis ℤ X).repr (ρ a χ) r) :
    ∀ i, p ∣ b.repr a i := by
  set B := Module.Free.chooseBasis ℤ X
  let T : Module.End ℤ X := B.constr ℤ (fun s => ∑ r, ((B.repr (ρ a (B s)) r) / p) • B r)
  have hT : algebraMap ℤ (Module.End ℤ X) p * T = ρ a := by
    apply B.ext
    intro s
    rw [Module.End.mul_apply, Module.algebraMap_end_apply]
    simp only [T, Module.Basis.constr_basis, Finset.smul_sum, smul_smul]
    conv_rhs => rw [← B.sum_repr (ρ a (B s))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Int.mul_ediv_cancel' (h _ r)]
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) T
  have hf' : aeval T f = 0 := by rw [aeval_def]; exact hf
  have h1 := Polynomial.scaleRoots_aeval_eq_zero (r := p) hf'
  rw [hT] at h1
  have h2 : aeval a (f.scaleRoots p) = 0 := by
    apply ringOfIntegers_action_injective F X ρ
    rw [map_zero]
    have := Polynomial.aeval_algHom_apply (ρ.toIntAlgHom) a (f.scaleRoots p)
    change ρ.toIntAlgHom _ = 0
    rw [← this]
    exact h1
  have h3 : aeval (algebraMap (𝓞 F) F a) (f.scaleRoots p) = 0 := by
    rw [Polynomial.aeval_algebraMap_apply, h2, map_zero]
  have hpF : (algebraMap ℤ F p) ≠ 0 := by simpa using hp
  set β : F := algebraMap (𝓞 F) F a / algebraMap ℤ F p with hβdef
  have hβa : algebraMap ℤ F p * β = algebraMap (𝓞 F) F a := by
    rw [hβdef]; field_simp
  have h4 : eval₂ (algebraMap ℤ F) β f = 0 := by
    have e := Polynomial.scaleRoots_eval₂_mul (p := f) (algebraMap ℤ F) β p
    rw [hβa, ← aeval_def, h3] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hpF)
  have hβ : IsIntegral ℤ β := ⟨f, hfm, h4⟩
  let y : 𝓞 F := ⟨β, hβ⟩
  have hy : p • y = a := by
    apply RingOfIntegers.coe_injective
    rw [map_zsmul, zsmul_eq_mul]
    have : algebraMap (𝓞 F) F y = β := rfl
    rw [this, ← hβa]
    simp
  intro i
  refine ⟨b.repr y i, ?_⟩
  rw [← hy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]

theorem finrank_eq_zero_of_dual_killed : ∀ (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : 𝓞 F →+* Module.End ℤ X)
    (k : Type) [Field k] (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)) (w : ι → k),
    w ≠ 0 → (∀ (l : X →+ k) (χ : X), ∑ i, w i * l (ρ (b i) χ) = 0) →
    Module.finrank ℤ X = 0 := by
  intro F _ _ X _ _ _ ρ k _ ι _ b w hw hyp
  classical
  by_contra hX
  haveI : Nontrivial X := Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hX)
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)
  set B := Module.Free.chooseBasis ℤ X
  have key : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      ∑ i, (B.repr (ρ (b i) χ) r) • w i = 0 := by
    intro χ r
    have := hyp ((Int.castAddHom k).comp (B.coord r).toAddMonoidHom) χ
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_comm]
  have lin : ∀ (e : ι → ℤ) (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      B.repr (ρ (∑ i, e i • b i) χ) r = ∑ i, e i * B.repr (ρ (b i) χ) r := by
    intro e χ r
    simp [map_sum, map_zsmul, LinearMap.sum_apply, Finsupp.finset_sum_apply]
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · set p := ringChar k with hpdef
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP k p := ringChar.charP k
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual (ZMod p) k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff (ZMod p) (w i0)).mp hc)
    set e : ι → ℤ := fun i => ((π (w i)).val : ℤ) with hedef
    have hdiv : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        (p : ℤ) ∣ B.repr (ρ (∑ i, e i • b i) χ) r := by
      intro χ r
      rw [lin, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have := congrArg π (key χ r)
      rw [map_sum, map_zero] at this
      rw [← this]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hedef]
      simp [ZMod.natCast_zmod_val, mul_comm]
    have h := GlobalTheory.dvd_coord_of_action_dvd F X ρ ι b p (by exact_mod_cast hp.ne_zero) _ hdiv i0
    rw [Module.Basis.repr_sum_self] at h
    apply hπ
    rw [← ZMod.natCast_zmod_val (π (w i0))]
    have h' : ((((π (w i0)).val : ℕ) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    exact_mod_cast h'
  · haveI : CharZero k := by
      have := ringChar.charP k; rw [hp] at this; exact CharP.charP_to_charZero k
    letI : Algebra ℚ k := DivisionRing.toRatAlgebra
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual ℚ k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff ℚ (w i0)).mp hc)
    set c : ι → ℚ := fun i => π (w i) with hcdef
    set e : ι → ℤ := fun i => (c i).num * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℤ) with hedef
    have he : ∀ i, (e i : ℚ) = c i * ∏ j, ((c j).den : ℚ) := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← mul_assoc, Rat.mul_den_eq_num, hedef]
      push_cast; rfl
    have hzero : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        B.repr (ρ (∑ i, e i • b i) χ) r = 0 := by
      intro χ r
      rw [lin]
      have := congrArg π (key χ r)
      rw [map_sum, map_zero] at this
      simp only [map_zsmul] at this
      have h2 : ((∑ i, e i * B.repr (ρ (b i) χ) r : ℤ) : ℚ)
          = (∏ j, ((c j).den : ℚ)) * ∑ i, (B.repr (ρ (b i) χ) r) • π (w i) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [he, zsmul_eq_mul, hcdef]; ring
      rw [this, mul_zero] at h2
      exact_mod_cast h2
    have hρ : ρ (∑ i, e i • b i) = 0 := by
      ext χ
      simp only [LinearMap.zero_apply]
      exact B.ext_elem fun r => by rw [hzero, map_zero, Finsupp.zero_apply]
    have ha : (∑ i, e i • b i) = 0 :=
      GlobalTheory.ringOfIntegers_action_injective F X ρ (by rw [hρ, map_zero])
    have h0 := congrArg (fun x => b.repr x i0) ha
    simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h0
    have hc0 : c i0 ≠ 0 := hπ
    have : (e i0 : ℚ) ≠ 0 := by
      rw [he]
      exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (c j).den_nz)
    exact this (by exact_mod_cast h0)

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eq_zero_of_dual_killed_by_tensor : ∀ (F : Type) [Field F] [NumberField F] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : 𝓞 F →+* Module.End ℤ X) (k : Type) [Field k] (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)) (w : ι → k), w ≠ 0 → (∀ (l : X →+ k) (χ : X), ∑ i, w i * l (ρ (b i) χ) = 0) → Module.finrank ℤ X = 0 := by
  atlas_forward_decl GlobalTheory.finrank_eq_zero_of_dual_killed
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocalBasis

theorem exists_isLieBasis_of_isLocalRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B]
    [IsCommMonObj B], Smooth B.hom → ∃ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y := by
  intro R _ _ B _ _ hs
  haveI := hs
  obtain ⟨C⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_chart B
  obtain ⟨g, hg, n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_lieBasis_away C (IsLocalRing.maximalIdeal R)
  have hu : IsUnit g := by
    by_contra h
    exact hg ((IsLocalRing.mem_maximalIdeal g).2 h)
  let L := Localization.Away g
  let f' : L →+* R := IsLocalization.Away.lift (g := RingHom.id R) g hu
  have hf' : f'.comp (algebraMap R L) = RingHom.id R := RingHom.ext fun r => IsLocalization.Away.lift_eq (g := RingHom.id R) g hu r
  let G' := ReciprocityTheory.ChartRestriction.G.Chart.Gs B g
  have hpb : IsGrpPullback G' B (ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (pullback.fst B.hom _) :=
    isGrpPullback_pullback B _
  have hcomp : spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L = 𝟙 (Sp R) := by
    simp only [spMap, ReciprocityTheory.ChartRestriction.G.Chart.fB]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf']
    exact Spec.map_id _
  let φ' : B.left ⟶ G'.left := pullback.lift (𝟙 _) (B.hom ≫ spMap f') (by rw [Category.assoc, hcomp]; simp)
  have hφ : φ' ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hw : φ' ≫ G'.hom = B.hom ≫ spMap f' := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl B).hom := inferInstanceAs (IsMonHom (𝟙 B))
  have hid : IsGrpPullback B B (𝟙 (Sp R)) (𝟙 B.left) := (isGrpPullback_of_iso (Iso.refl B)).congr rfl rfl
  have hn : IsGrpPullback B B (spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (φ' ≫ pullback.fst _ _) :=
    hid.congr hcomp.symm hφ.symm
  have hB : IsGrpPullback B G' (spMap f') φ' := hpb.cancel hn hw
  have hs' : Smooth G'.hom := by
    show Smooth (pullback.snd B.hom _)
    infer_instance
  obtain ⟨v', hv', -⟩ := GlobalTheory.exists_isLieBasis_baseChange L R f' G' B φ' hB hs' n v hv
  exact ⟨n, v', hv'⟩

end GlobalTheory.LieLocalBasis
end
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem card_eq_of_isLieBasis [Nontrivial R] {n m : ℕ} {v : Fin n → (epsR R ⟶ G)}
    {w : Fin m → (epsR R ⟶ G)} (hv : IsLieBasis v) (hw : IsLieBasis w) : n = m := by
  choose b hb using fun i => LieEigen.exists_prodPts hw (hv.1 i)
  have key : ∀ c, prodPts c v = prodPts (∑ i, c i • b i) w := fun c => by
    rw [← LieEigen.prodPts_prodPts hw.1]
    exact congrArg (prodPts c) (funext fun i => (hb i).symm)
  let L : (Fin n → R) →ₗ[R] (Fin m → R) := Fintype.linearCombination R b
  have hL : ∀ c, L c = ∑ i, c i • b i := fun c => Fintype.linearCombination_apply R b c
  have bij : Function.Bijective L := by
    refine ⟨fun c c' h => LieEigen.prodPts_injective hv ?_, fun d => ?_⟩
    · show prodPts c v = prodPts c' v
      rw [key, key, ← hL, ← hL, h]
    · obtain ⟨c, hc⟩ := LieEigen.exists_prodPts hv (LieEigen.isTangent_prodPts hw.1 d)
      exact ⟨c, LieEigen.prodPts_injective hw (show prodPts (L c) w = prodPts d w by rw [hL, ← key, hc])⟩
  have := (LinearEquiv.ofBijective L bij).finrank_eq
  simpa using this

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {k : Type} [Field k] (f : R →+* k)

theorem push_left (x : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) x).left = x.left ≫ pullback.fst G.hom (spMap f) := rfl

theorem push_injective : Function.Injective (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k)) :=
  fun x y e => Over.OverMorphism.ext ((isGrpPullback_pullback G (spMap f)).1.hom_ext
    (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))

theorem push_surjective : Function.Surjective (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k)) := by
  intro w
  have hk := isGrpPullback_pullback G (spMap f)
  refine ⟨Over.homMk (hk.1.lift w.left (epsR k).hom (Over.w w)) (hk.1.lift_snd _ _ _), ?_⟩
  exact Over.OverMorphism.ext (hk.1.lift_fst _ _ _)

theorem unit_fst : η[(Over.pullback (spMap f)).obj G].left ≫ pullback.fst G.hom (spMap f) = spMap f ≫ η[G].left := by
  have e := congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback G (spMap f)) (𝟙_ (Over (Sp k)))))
  have e₁ : (1 : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback (spMap f)).obj G) = η[(Over.pullback (spMap f)).obj G] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {k : Type} [Field k] (f : R →+* k)

theorem isTangent_iff_push (y : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    IsTangent y ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫
      (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) y).left = (1 : Over.mk (spMap f) ⟶ G).left := by
  rw [push_left]
  show _ ↔ _ = spMap f ≫ η[G].left
  unfold IsTangent
  constructor
  · intro h
    rw [← Category.assoc, h, unit_fst]
  · intro h
    apply (isGrpPullback_pullback G (spMap f)).1.hom_ext
    · rw [Category.assoc, h, unit_fst]
    · rw [Category.assoc, Over.w y, Over.w η[(Over.pullback (spMap f)).obj G]]
      simp only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
        ext s; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      simp

def scaleAt (a : k) : epsPt (spMap f) ⟶ epsPt (spMap f) :=
  Over.homMk (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a)).left
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap f) (Over.w (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a)))))

theorem push_scale (a : k) (y : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a) ≫ y) =
      scaleAt f a ≫ pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) y :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
  {v : Fin n → (epsR R ⟶ G)}

open Classical in

def lieMat (hv : IsLieBasis v) (u : G ⟶ G) : Matrix (Fin n) (Fin n) R :=
  if h : IsMonHom u then Matrix.transpose (haveI := h; (SqZero.existsUnique_lieMatrix u hv.1 hv).exists.choose) else 0

theorem comp_eq_prodPts (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (j : Fin n) :
    v j ≫ u = prodPts (fun i => lieMat hv u i j) v := by
  have h := (SqZero.existsUnique_lieMatrix u hv.1 hv).exists.choose_spec j
  rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff] at h
  rw [lieMat, dif_pos (show IsMonHom u from inferInstance)]
  exact h

end GlobalTheory.LieCoordFibre

open GlobalTheory.LieCoordFibre ReciprocityTheory.ChartRestriction.G.Chart in

theorem GlobalTheory.exists_lie_coordinates_fibres : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R), (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → n = g) ∧ ∀ (k : Type) [Field k] (f : R →+* k), ∃ T : (Fin n → k) → (epsPt (spMap f) ⟶ G), Function.Injective T ∧ (∀ v : epsPt (spMap f) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (v).left = (1 : Over.mk (spMap f) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (t : k) c, (T (t • c)).left = spMap (epsScale t) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c) := by
  intro R _ _ G _ _ hs
  obtain ⟨n, v, hv⟩ := LieLocalBasis.exists_isLieBasis_of_isLocalRing R G hs
  refine ⟨n, lieMat hv, fun g hg => ?_, fun k _ f => ?_⟩
  · obtain ⟨w, hw⟩ := KeyPow.exists_isLieBasis G hg
    exact card_eq_of_isLieBasis hv hw
  have hk := isGrpPullback_pullback G (spMap f)
  obtain ⟨v', hv', e⟩ := exists_isLieBasis_baseChange R k f G _ _ hk hs n v hv
  let P := pushHom hk (epsR k)
  refine ⟨fun c => P (prodPts c v'), fun c c' h => LieEigen.prodPts_injective hv' (push_injective f h),
    fun w => ?_, fun c c' => ?_, fun t c => ?_, fun u hu c => ?_⟩
  · constructor
    · intro h
      obtain ⟨y, rfl⟩ := push_surjective f w
      obtain ⟨c, rfl⟩ := LieEigen.exists_prodPts hv' ((isTangent_iff_push f y).2 h)
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact (isTangent_iff_push f _).1 (LieEigen.isTangent_prodPts hv'.1 c)
  · show P _ = P _ * P _
    rw [LieEigen.prodPts_add hv'.1, map_mul]
  · show (prodPts (t • c) v').left ≫ _ = _ ≫ (prodPts c v').left ≫ _
    rw [LieEigen.prodPts_smul, Over.comp_left, Category.assoc]
    rfl
  haveI := hu
  let col : Fin n → Fin n → R := fun j i => lieMat hv u i j
  have hz : ∀ j, P (v' j) ≫ u = P (prodPts (f ∘ col j) v') := fun j => Over.OverMorphism.ext (by
    rw [Over.comp_left, push_left, push_left, e j, Category.assoc, ← Over.comp_left,
      comp_eq_prodPts hv u j, ← LieEigen.prodPts_left hk e])
  let Q := (IsMonHom.monoidHom u (epsPt (spMap f))).comp P
  have hQ : ∀ y, Q y = P y ≫ u := fun y => rfl
  have hs' : ∀ j, Q (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ v' j) =
      P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v') := fun j => by
    rw [hQ, push_scale, push_scale, Category.assoc, hz]
  calc P (prodPts c v') ≫ u = Q (prodPts c v') := rfl
    _ = (List.ofFn fun j => Q (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ v' j)).prod := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]
      rfl
    _ = (List.ofFn fun j => P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v')).prod := by
      simp only [hs']
    _ = P (prodPts c fun j => prodPts (f ∘ col j) v') := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]
      rfl
    _ = P (prodPts (∑ j, c j • (f ∘ col j)) v') := by rw [LieEigen.prodPts_prodPts hv'.1]
    _ = P (prodPts (((lieMat hv u).map f).mulVec c) v') := by
      congr 2
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, col, mul_comm]
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_coordinates_on_field_fibres_local_ring : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R), (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → n = g) ∧ ∀ (k : Type) [Field k] (f : R →+* k), ∃ T : (Fin n → k) → (epsPt (spMap f) ⟶ G), Function.Injective T ∧ (∀ v : epsPt (spMap f) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (v).left = (1 : Over.mk (spMap f) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (t : k) c, (T (t • c)).left = spMap (epsScale t) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c) := by
  atlas_forward_decl GlobalTheory.exists_lie_coordinates_fibres
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory
section
attribute [local instance] Over.cartesianMonoidalCategory
namespace TorusTangent

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

def epsUnit (a : k) : (DualNumber k)ˣ where
  val := 1 + TrivSqZeroExt.inr a
  inv := 1 - TrivSqZeroExt.inr a
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

theorem epsUnit_add (a b : k) : epsUnit (a + b) = epsUnit a * epsUnit b := by
  ext <;> simp [epsUnit, add_comm]

theorem natur {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f x) := by
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  exact (congrArg (fun g => g.hom x) this).symm

noncomputable def phi (l : X →+ k) : Multiplicative X →* Γ((epsPt (𝟙 (Sp k))).left, ⊤)ˣ :=
  (Units.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom.toMonoidHom).comp
    { toFun := fun χ => epsUnit (l χ.toAdd)
      map_one' := by ext <;> simp [epsUnit]
      map_mul' := fun a b => by rw [toAdd_mul, map_add, epsUnit_add] }

noncomputable def tanPt (l : X →+ k) : epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X :=
  (splitTorusPointsEquiv (Sp k) X (epsPt (𝟙 (Sp k)))).symm (phi l)

theorem chV_tanPt (l : X →+ k) (χ : X) :
    (chV (tanPt l) χ).val = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
      (1 + TrivSqZeroExt.inr (l χ)) := by
  show ((splitTorusPointsEquiv _ _ _) ((splitTorusPointsEquiv _ _ _).symm (phi l))
    (Multiplicative.ofAdd χ)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem chV_comp {Z Z' : Over (Sp k)} (j : Z' ⟶ Z) (t : Z ⟶ splitTorus (Sp k) X) (χ : X) :
    (chV (j ≫ t) χ).val = j.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

theorem ext_val {Z : Over (Sp k)} {a b : Z ⟶ splitTorus (Sp k) X}
    (h : ∀ χ, (chV a χ).val = (chV b χ).val) : a = b :=
  TorusOfCharMap.ext_chV fun χ => Units.ext (h χ)

end TorusTangent
end

open TorusTangent in

theorem splitTorus_tangent_addHom : ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X], ∃ U : (X →+ k) → (epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ (τ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X) (ρ : X →+ X), (∀ χ, chV τ χ = charUnit (Sp k) X (ρ χ)) → ∀ l, U l ≫ τ = U (l.comp ρ) := by
  intro k _ X _
  have hΓ := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.symm.injective
  refine ⟨tanPt, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' h
    ext χ
    have e := congrArg (fun t => (chV t χ).val) h
    simp only [chV_tanPt] at e
    have e2 := congrArg TrivSqZeroExt.snd (hΓ e)
    simpa using e2
  · intro l
    let j : Over.mk (𝟙 (Sp k)) ⟶ epsPt (𝟙 (Sp k)) :=
      Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
        simp only [Over.mk_hom, Category.comp_id]
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1)
    have : j ≫ tanPt l = 1 := by
      refine ext_val fun χ => ?_
      rw [chV_comp, chV_tanPt]
      simp only [j, Over.homMk_left]
      rw [natur]
      simp [chV, map_one]
    exact congrArg CommaMorphism.left this
  · intro l l'
    show (splitTorusPointsEquiv _ _ _).symm _ =
      (splitTorusPointsEquiv _ _ _).symm (phi l) * (splitTorusPointsEquiv _ _ _).symm (phi l')
    rw [← map_mul]
    congr 1
    ext χ
    simp [phi, epsUnit_add]
  · intro t l
    let s : epsPt (𝟙 (Sp k)) ⟶ epsPt (𝟙 (Sp k)) :=
      Over.homMk (spMap (epsScale t)) (by
        simp only [Over.mk_hom, Category.comp_id]
        rw [← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change epsScale t (algebraMap k (DualNumber k) x) = algebraMap k (DualNumber k) x
        ext <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl])
    have : tanPt ((AddMonoidHom.mulLeft t).comp l) = s ≫ tanPt l := by
      refine ext_val fun χ => ?_
      rw [chV_comp, chV_tanPt, chV_tanPt]
      simp only [s, Over.homMk_left]
      rw [natur]
      congr 1
      ext <;> simp [epsScale, mul_comm]
    rw [this]
    rfl
  · intro τ ρ hτ l
    have hm := ((splitTorus_map_of_charHom (Sp k) X X ρ).2 τ hτ).2.2
    refine ext_val fun χ => ?_
    rw [hm, chV_tanPt, chV_tanPt]
    rfl

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_tangentVectors_addMonoidHom : ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X], ∃ U : (X →+ k) → (epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ (τ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X) (ρ : X →+ X), (∀ χ, chV τ χ = charUnit (Sp k) X (ρ χ)) → ∀ l, U l ≫ τ = U (l.comp ρ) := by
  atlas_forward_decl GlobalTheory.splitTorus_tangent_addHom
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorLie

section Grp
variable {S Z : Scheme.{0}} {G : Over S} [GrpObj G]

theorem one_left' (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  show (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left, Over.toUnit_left]

theorem mul_left_congr {T T' : Over S} (x y : T ⟶ G) (x' y' : T' ⟶ G) (u : Z ⟶ T.left) (u' : Z ⟶ T'.left)
    (hx : u ≫ x.left = u' ≫ x'.left) (hy : u ≫ y.left = u' ≫ y'.left) :
    u ≫ (x * y).left = u' ≫ (x' * y').left := by
  have hb : u' ≫ T'.hom = u ≫ T.hom := by
    rw [← Over.w x, ← Over.w x', ← Category.assoc, ← hx, Category.assoc]
  let U : Over.mk (u ≫ T.hom) ⟶ T := Over.homMk u rfl
  let U' : Over.mk (u ≫ T.hom) ⟶ T' := Over.homMk u' hb
  have e1 : U ≫ x = U' ≫ x' := Over.OverMorphism.ext hx
  have e2 : U ≫ y = U' ≫ y' := Over.OverMorphism.ext hy
  have : U ≫ (x * y) = U' ≫ (x' * y') := by rw [MonObj.comp_mul, MonObj.comp_mul, e1, e2]
  exact congrArg (fun k => k.left) this

end Grp

theorem pull_one_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (T.hom ≫ f) ≫ η[G].left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have hm := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at hm
  have hx : x₀ * x₀ = x₀ := Over.OverMorphism.ext hm
  have h1 : x₀ = 1 := by simpa using hx
  have : x₀.left = (Over.mk (T.hom ≫ f)).hom ≫ η[G].left := by rw [h1, one_left']
  exact this

end GlobalTheory.TorLie

open GlobalTheory.TorLie in
theorem GlobalTheory.torus_part_lie : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (E : TorusExtension ((Over.pullback x).obj G)), letI := E.addCommGroup; ∃ (ρ : O →+* Module.End ℤ E.X) (U : (E.X →+ k) → (epsPt x ⟶ G)), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk x ⟶ G).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ a l, U l ≫ act a = U (l.comp (ρ a).toAddMonoidHom) := by
  intro S G _ _ O _ act hhom h1 hmul hadd k _ x E
  letI := E.addCommGroup
  haveI := E.i_hom
  set Gx := (Over.pullback x).obj G with hGx
  have hGP := isGrpPullback_pullback G x
  obtain ⟨act', ⟨hhom', h1', hmul', hadd'⟩, hact'⟩ :=
    GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes S (Sp k) x G Gx (pullback.fst G.hom x) hGP O act hhom h1 hmul hadd
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.ringHom_characterEnd_of_torusExtension_action k Gx E O act' hhom' h1' hmul' hadd'
  obtain ⟨U₀, hinj, hone, hU₀mul, hscale, hequi⟩ := GlobalTheory.T.splitTorus_tangentVectors_addMonoidHom k E.X

  have heq : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt (𝟙 (Sp k))).hom ≫ x := by
    intro l
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w (U₀ l ≫ E.i))
  have hw : ∀ l, ((U₀ l ≫ E.i).left ≫ pullback.fst G.hom x) ≫ G.hom = (epsPt x).hom := by
    intro l; rw [heq l]; simp [epsPt]
  let U : (E.X →+ k) → (epsPt x ⟶ G) := fun l => Over.homMk _ (hw l)
  have hUl : ∀ l, (U l).left = (U₀ l).left ≫ E.i.left ≫ pullback.fst G.hom x := by
    intro l; simp [U]
  haveI : Mono E.i := E.isKernel.mono_fst_of_mono (IsTerminal.mono_from isTerminalTensorUnit _)
  refine ⟨ρ, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro l l' h
    have hl := congrArg Over.Hom.left h
    rw [hUl, hUl, ← Category.assoc, ← Category.assoc] at hl
    have h2 : (U₀ l ≫ E.i).left = (U₀ l' ≫ E.i).left := by
      apply pullback.hom_ext
      · simpa [Over.comp_left] using hl
      · exact (Over.w (U₀ l ≫ E.i)).trans (Over.w (U₀ l' ≫ E.i)).symm
    exact hinj ((cancel_mono E.i).1 (Over.OverMorphism.ext h2))
  · intro l
    rw [hUl, ← Category.assoc, hone l, ← Category.assoc, ← Over.comp_left, MonObj.one_comp,
      pull_one_left hGP, one_left']
    simp
  · intro l l'
    let x₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G := Over.homMk _ (heq l)
    let y₀ : Over.mk ((epsPt (𝟙 (Sp k))).hom ≫ x) ⟶ G := Over.homMk _ (heq l')
    have key := hGP.2 (epsPt (𝟙 (Sp k))) (U₀ l ≫ E.i) (U₀ l' ≫ E.i) x₀ y₀ rfl rfl
    rw [← mul_comp, ← hU₀mul] at key
    apply Over.OverMorphism.ext
    have hc := mul_left_congr (U l) (U l') x₀ y₀ (𝟙 _) (𝟙 _) rfl rfl
    simp only [Category.id_comp] at hc
    rw [hc, key, hUl, Over.comp_left, Category.assoc]
  · intro t l
    rw [hUl, hUl, hscale]
    simp [Category.assoc]
  · intro a l
    obtain ⟨τ, hτ, hχ⟩ := hρ a
    have hτl : τ.left ≫ E.i.left = E.i.left ≫ (act' a).left := by
      simpa using congrArg Over.Hom.left hτ
    apply Over.OverMorphism.ext
    have hτU : U₀ l ≫ τ = U₀ (l.comp (ρ a).toAddMonoidHom) := hequi τ (ρ a).toAddMonoidHom (fun χ => hχ χ) l
    rw [Over.comp_left, hUl, hUl, ← hτU, Over.comp_left]
    simp only [Category.assoc, ← hact' a, reassoc_of% hτl]
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_part_fibre_lie_algebra_characters : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (O : Type) [Ring O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (E : TorusExtension ((Over.pullback x).obj G)), letI := E.addCommGroup; ∃ (ρ : O →+* Module.End ℤ E.X) (U : (E.X →+ k) → (epsPt x ⟶ G)), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk x ⟶ G).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ a l, U l ≫ act a = U (l.comp (ρ a).toAddMonoidHom) := by
  atlas_forward_decl GlobalTheory.torus_part_lie
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

open scoped Matrix

namespace GlobalTheory.PotGoodLie

theorem proper_pull {K W L : Type} [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L]
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (hM : GlobalTheory.SS.IsModel (L := L) A G)
    (hA : IsAbelianScheme A) : IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom := by
  obtain ⟨e, -⟩ := hM
  have := hA.proper
  have h : ((Over.pullback (spMap (algebraMap W L))).obj G).hom = e.hom.left ≫ ((Over.pullback (spMap (algebraMap K L))).obj A).hom := (Over.w e.hom).symm
  rw [h]
  have : IsProper ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
    show IsProper (pullback.snd A.hom _)
    infer_instance
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  infer_instance

theorem spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eq_one_of_lieMult_zero {S : Scheme.{0}} {O : Type} [CommRing O] {G : Over S} [GrpObj G] (a : OAct O G)
    {k : Type} [Field k] (t : Sp k ⟶ S) (τ : O →+* k) (h : LieMult a t τ 0) (w : epsPt t ⟶ G)
    (hw : IsLieEigen a t τ w) : w = 1 := by
  obtain ⟨v, -, H⟩ := h
  obtain ⟨c, ⟨u, -, hu⟩, -⟩ := H w hw
  simpa using hu

theorem lift_ext (V K W L Ω : Type) [CommRing V] [Field K] [CommRing W] [IsDomain W] [Field L] [Field Ω]
    [IsAlgClosed Ω] [Algebra V K] [Algebra V W] [Algebra W L] [Algebra K L] [IsFractionRing W L]
    (hc : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K))
    (hfin : Module.Finite V W) (g : K →+* Ω) : ∃ g' : L →+* Ω, g'.comp (algebraMap K L) = g := by
  letI := g.toAlgebra
  have hint : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have halg : ∀ w : W, IsAlgebraic K (algebraMap W L w) := by
    intro w
    obtain ⟨p, hp, hpw⟩ := hint.isIntegral w
    refine ⟨p.map (algebraMap V K), (hp.map _).ne_zero, ?_⟩
    have := congrArg (algebraMap W L) hpw
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← this, hc]
  haveI : Algebra.IsAlgebraic K L := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
    rw [div_eq_mul_inv]
    exact IsAlgebraic.mul (halg a) (IsAlgebraic.inv (halg b))
  exact ⟨(IsAlgClosed.lift : L →ₐ[K] Ω).toRingHom, by ext x; simp [RingHom.algebraMap_toAlgebra]⟩

theorem prod_of_add {A B J : Type} [AddCommMonoid A] [CommMonoid B] (φ : A → B) (h0 : φ 0 = 1)
    (hadd : ∀ x y, φ (x + y) = φ x * φ y) (s : Finset J) (g : J → A) : φ (∑ i ∈ s, g i) = ∏ i ∈ s, φ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, hadd, ih]

theorem exists_ringHom {R : Type} [CommRing R] {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    (a : OAct O G) {n : ℕ} (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R) {k : Type} [Field k] (f : R →+* k)
    (hf : Function.Injective f) {X : Over S} (T : (Fin n → k) → (X ⟶ G)) (Tinj : Function.Injective T)
    (Tadd : ∀ c c', T (c + c') = T c * T c')
    (Tact : ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c)) :
    ∃ Mr : O →+* Matrix (Fin n) (Fin n) R, ∀ x, Mr x = M (a.act x) := by
  have key : ∀ P Q : Matrix (Fin n) (Fin n) R, (∀ c, T ((P.map f) *ᵥ c) = T ((Q.map f) *ᵥ c)) → P = Q := by
    intro P Q h
    apply Matrix.map_injective hf
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun c => by simpa [Matrix.toLin'_apply] using Tinj (h c)
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have act0 : a.act 0 = 1 := by simpa using a.add 0 0
  refine ⟨{ toFun := fun x => M (a.act x), map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun _ => rfl⟩
  · apply key; intro c
    rw [← Tact _ (a.hom 1), a.one]
    simp
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x * y)), mul_comm x y, a.mul, ← Category.assoc, Tact _ (a.hom y), Tact _ (a.hom x),
      Matrix.mulVec_mulVec, ← Matrix.map_mul]
  · apply key; intro c
    rw [← Tact _ (a.hom 0), act0, comp_one]
    simp [T0]
  · intro x y; apply key; intro c
    rw [← Tact _ (a.hom (x + y)), a.add, comp_mul, Tact _ (a.hom x), Tact _ (a.hom y), ← Tadd, Matrix.map_add _ (map_add f),
      Matrix.add_mulVec]

theorem finrank_zero (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W)) [GrpObj G]
    (hG : IsSemiAbelian G) (F : Type) [Field F] [NumberField F] (a : OAct (𝓞 F) G) (Ω : Type) [Field Ω] [CharZero Ω]
    [IsAlgClosed Ω] (f : W →+* Ω) (hf : Function.Injective f) (σ : 𝓞 F →+* Ω) (h0 : LieMult a (spMap f) σ 0)
    (E : TorusExtension (GlobalTheory.SS.spFibre G)) : (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 := by
  classical
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  haveI : IsCommMonObj G := hG.comm
  obtain ⟨n, M, -, hT⟩ := GlobalTheory.T.exists_lie_coordinates_on_field_fibres_local_ring W G hG.smooth
  obtain ⟨T, Tinj, Trange, Tadd, Tsc, Tact⟩ := hT Ω f
  obtain ⟨Mr, hMr⟩ := exists_ringHom a M f hf T Tinj Tadd Tact
  have T0 : T 0 = 1 := by simpa using Tadd 0 0
  have hno : ∀ c : Fin n → Ω, (∀ x, ((Mr x).map f).mulVec c = σ x • c) → c = 0 := by
    intro c hc
    have hE : IsLieEigen a (spMap f) σ (T c) := by
      refine ⟨(Trange (T c)).2 ⟨c, rfl⟩, fun x => ?_⟩
      rw [Tact _ (a.hom x), ← hMr, hc, Tsc]
    exact Tinj ((eq_one_of_lieMult_zero a _ σ h0 _ hE).trans T0.symm)
  let b := Module.Free.chooseBasis ℤ (𝓞 F)
  obtain ⟨w, ⟨i0, hu⟩, hsum⟩ := GlobalTheory.T.exists_primitive_annihilator' F W Ω f hf n Mr σ hno _ b
  obtain ⟨ρ, U, Uinj, Ufst, Uadd, Usc, Uact⟩ := GlobalTheory.T.toric_part_fibre_lie_algebra_characters (Sp W) G (𝓞 F) a.act a.hom a.one a.mul a.add
    (ResidueField W) (spMap (residue W)) E
  obtain ⟨T', -, T'range, T'add, T'sc, T'act⟩ := hT (ResidueField W) (residue W)
  have T'0 : T' 0 = 1 := by simpa using T'add 0 0
  have U0 : U 0 = 1 := by simpa using Uadd 0 0
  refine GlobalTheory.T.finrank_eq_zero_of_dual_killed_by_tensor F E.X ρ (ResidueField W) _ b (fun i => residue W (w i)) ?_ ?_
  · intro h
    exact (residue_ne_zero_iff_isUnit _).2 hu (congrFun h i0)
  · intro l χ
    obtain ⟨c, hc⟩ := (T'range (U l)).1 (Ufst l)
    have step : ∀ i, U ((AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) =
        T' (residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c)) := by
      intro i
      have e : U (l.comp (ρ (b i)).toAddMonoidHom) = T' ((Mr (b i)).map (residue W) *ᵥ c) := by
        rw [← Uact, ← hc, T'act _ (a.hom _), hMr]
      apply Over.OverMorphism.ext
      rw [Usc, T'sc, e]
    have hv : ∑ i, residue W (w i) • ((Mr (b i)).map (residue W) *ᵥ c) = 0 := by
      have := congrArg (fun P => ((residue W).mapMatrix P) *ᵥ c) hsum
      have hsm : ∀ i, (w i • Mr (b i)).map (residue W) = residue W (w i) • (Mr (b i)).map (residue W) := by
        intro i; ext; simp
      simpa [map_sum, Matrix.sum_mulVec, hsm, Matrix.smul_mulVec] using this
    have hL : (∑ i, (AddMonoidHom.mulLeft (residue W (w i))).comp (l.comp (ρ (b i)).toAddMonoidHom)) = 0 := by
      apply Uinj
      rw [prod_of_add U U0 Uadd, U0, Finset.prod_congr rfl (fun i _ => step i), ← prod_of_add T' T'0 T'add, hv, T'0]
    have := congrArg (fun m => m χ) hL
    simpa using this

theorem potGood_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA F _ _ act Ω _ _ g σ hL
  obtain ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, hsemi, ⟨E⟩⟩ :=
    GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus V K A hA
  refine ⟨W, L, iW, iD, iDVR, iL, iVW, iWL, iKL, iFR, hc, hfin, hloc, hcpl, G, iG, hM, ?_⟩
  have hAL := isGrpPullback_pullback A (spMap (algebraMap K L))
  obtain ⟨actL, ⟨h1, h2, h3, h4⟩, hLc⟩ := GlobalTheory.T.exists_ring_action_pullback_cartesian_group_schemes _ _ (spMap (algebraMap K L)) A
    ((Over.pullback (spMap (algebraMap K L))).obj A) _ hAL (𝓞 F) act.act act.hom act.one act.mul act.add
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.isGrpPullback_of_group_scheme_model_base_change K W L A G hM _ _ hAL
  obtain ⟨actG, ⟨g1, g2, g3, g4⟩, hGc⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G _ φ hsemi hφ (𝓞 F) actL h1 h2 h3 h4
  let aL : OAct (𝓞 F) ((Over.pullback (spMap (algebraMap K L))).obj A) := ⟨actL, h1, h2, h3, h4⟩
  let aG : OAct (𝓞 F) G := ⟨actG, g1, g2, g3, g4⟩
  obtain ⟨g', hg'⟩ := lift_ext V K W L Ω hc hfin g
  have e1 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ A _ _ (pullback.fst _ _) act aL hAL hLc Ω (spMap g') σ 0
  have hx : spMap g' ≫ spMap (algebraMap K L) = spMap g := by rw [← hg', spMap_comp]
  have e2 := GlobalTheory.LiePull.lieMult_pull (𝓞 F) _ _ G _ _ φ aG aL hφ hGc Ω (spMap g') σ 0
  have hG0 : LieMult aG (spMap (g'.comp (algebraMap W L))) σ 0 := by
    rw [spMap_comp]
    exact e2.1 (e1.2 (hx ▸ hL))
  haveI : CharZero Ω := charZero_of_injective_ringHom g.injective
  have hinj : Function.Injective (g'.comp (algebraMap W L)) :=
    g'.injective.comp (IsFractionRing.injective W L)
  exact GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus W L G hsemi (proper_pull A G hM hA) E
    (finrank_zero W G hsemi F aG Ω _ hinj σ hG0 E)

end GlobalTheory.PotGoodLie
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialGoodReduction_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  atlas_forward_decl GlobalTheory.PotGoodLie.potGood_of_lieMult_zero
end
