import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdaptedReduction
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicCovolumeFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchInvariant
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchLatticeDiscrete
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArithmeticCovolumeFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedGenerators
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVectorOrbits
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementForm
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCongruenceUnitsFiniteIndex
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenReflection
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenReflectionMaps
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramDetermines
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHyperbolicPairTransitive
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIdealClassesFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIndexLeDet
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIsotropicScaling
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PKTransitive
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLenCauchySchwarz
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineCoeffsFG
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineIndexNeZero
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLinePairOrbitsFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMahlerCompactness
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantExists
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMinkowskiVolumeForm
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PParabolicDecomposition
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PPhaseOnMinus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusIntegralHomogeneous
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingIntegral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingTorus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldOrbit
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedIndexBound
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWittPartner

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

theorem BoundedIndexSubgroupsFinite.proof (G : Type*) [AddCommGroup G] :
    BoundedIndexSubgroupsFinite.Statement G := by
  intro A B hB hAB C
  classical

  have : Module.Finite ℤ B :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg B).mpr hB)
  have : Module.Finite ℤ A :=
    Module.Finite.of_injective (AddSubgroup.inclusion hAB).toIntLinearMap
      (AddSubgroup.inclusion_injective hAB)

  set n := C.factorial with hn
  let K : AddSubgroup A := (nsmulAddMonoidHom n : A →+ A).range

  have : Module.Finite ℤ (A ⧸ K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap
      (QuotientAddGroup.mk'_surjective K)
  have htors : Module.IsTorsion ℤ (A ⧸ K) := by
    intro x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Nat.factorial_pos C).ne')⟩, ?_⟩
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      show (n : ℤ) • (QuotientAddGroup.mk a : A ⧸ K) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, natCast_zsmul]
      exact ⟨a, rfl⟩
  have : Finite (A ⧸ K) := Module.finite_of_fg_torsion _ htors

  have hK : ∀ H ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      K ≤ H.addSubgroupOf A := by
    rintro H ⟨-, h0, hC⟩ _ ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero h0) hC
    rw [AddSubgroup.mem_addSubgroupOf]
    show n • (a : G) ∈ H
    rw [hn, hk, mul_nsmul]
    exact H.nsmul_mem (H.nsmul_relIndex_mem a.2) k

  refine Set.Finite.of_finite_image (f := fun H : AddSubgroup G =>
    (QuotientAddGroup.mk '' ((H.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)))
    (Set.toFinite _) ?_
  have key : ∀ H₁ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      ∀ H₂ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      (QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)) =
        QuotientAddGroup.mk '' ((H₂.addSubgroupOf A : AddSubgroup A) : Set A) → H₁ ≤ H₂ := by
    intro H₁ h₁ H₂ h₂ he x hx
    have hxA : x ∈ A := h₁.1 hx
    have hmem : (QuotientAddGroup.mk (⟨x, hxA⟩ : A) : A ⧸ K) ∈
        QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) :=
      ⟨⟨x, hxA⟩, AddSubgroup.mem_addSubgroupOf.mpr hx, rfl⟩
    rw [he] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hd : -y + ⟨x, hxA⟩ ∈ H₂.addSubgroupOf A := hK H₂ h₂ (QuotientAddGroup.eq.mp hyx)
    have : (⟨x, hxA⟩ : A) ∈ H₂.addSubgroupOf A := by
      simpa using (H₂.addSubgroupOf A).add_mem hy hd
    exact AddSubgroup.mem_addSubgroupOf.mp this
  exact fun H₁ h₁ H₂ h₂ he => le_antisymm (key H₁ h₁ H₂ h₂ he) (key H₂ h₂ H₁ h₁ he.symm)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem CoeffLatticeBasis.proof (E : Type*) [Field E] [NumberField E] :
    CoeffLatticeBasis.Statement E := by
  intro A hO hfg
  have : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).mpr hfg
  obtain ⟨n, b⟩ : Σ n : ℕ, Basis (Fin n) ℤ A := Module.basisOfFiniteTypeTorsionFree'

  let f : A →ₗ[ℤ] E := A.subtype.toIntLinearMap
  let v : Fin n → E := fun i => (b i : E)
  have hv : v = f ∘ b := rfl
  have hliZ : LinearIndependent ℤ v :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ

  have hA : ∀ a ∈ A, a ∈ Submodule.span ℚ (Set.range v) := by
    intro a ha
    have h1 : f ⟨a, ha⟩ ∈ Submodule.span ℤ (f '' Set.range b) :=
      Submodule.apply_mem_span_image_of_mem_span f (b.mem_span _)
    rw [← Set.range_comp, ← hv] at h1
    exact Submodule.span_le_restrictScalars ℤ ℚ _ h1
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range v) := by
    rw [← (integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [integralBasis_apply]
    exact hA _ (hO ⟨_, rfl⟩)
  have hn : finrank ℚ E = n := by
    rw [finrank_eq_card_basis (Basis.mk hliQ hsp), Fintype.card_fin]
  exact ⟨b.reindex (finCongr hn.symm)⟩

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix
open scoped ComplexOrder

theorem EigenspacesOrthogonal.proof (ι : Type*) [Fintype ι] [DecidableEq ι] :
    EigenspacesOrthogonal.Statement ι := by
  intro H P hMaj a b ha hb
  obtain ⟨hP, hH, hdet, -⟩ := hMaj

  have hHA : ∀ v : ι → ℂ, H *ᵥ (majInvolution H P *ᵥ v) = P *ᵥ v := by
    intro v
    rw [majInvolution, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul]

  have hmove : ∀ (M : Matrix ι ι ℂ), M.IsHermitian → ∀ u w : ι → ℂ,
      star u ⬝ᵥ (M *ᵥ w) = star (M *ᵥ u) ⬝ᵥ w := by
    intro M hM u w
    rw [star_mulVec, hM.eq, dotProduct_mulVec]
  have hPa : P *ᵥ a = H *ᵥ a := by rw [← hHA a, ha]
  have hPb : P *ᵥ b = -(H *ᵥ b) := by rw [← hHA b, hb, mulVec_neg]
  have h1 : star a ⬝ᵥ (P *ᵥ b) = star a ⬝ᵥ (H *ᵥ b) := by
    rw [hmove P hP.isHermitian, hPa, ← hmove H hH]
  have h2 : star a ⬝ᵥ (P *ᵥ b) = -(star a ⬝ᵥ (H *ᵥ b)) := by
    rw [hPb, dotProduct_neg]
  have h3 : (2 : ℂ) * (star a ⬝ᵥ (P *ᵥ b)) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h1]
    rw [h2, add_neg_cancel]
  simpa using h3

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem IntegerSmallAtPlaces.proof (E : Type*) [Field E] [NumberField E] :
    IntegerSmallAtPlaces.Statement E := by
  intro a ha hlt
  by_contra hne
  let b : 𝓞 E := ⟨a, ha⟩
  have hb : b ≠ 0 := fun h => hne (congrArg Subtype.val h)
  let w : InfinitePlace E := Classical.arbitrary _
  have h1 : 1 ≤ w b := InfinitePlace.one_le_of_lt_one hb (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr h1)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

theorem IntegralFamilyBound.proof (E : Type*) [Field E] [NumberField E] :
    IntegralFamilyBound.Statement E := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = finrank ℚ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  let e : Fin (finrank ℚ E) ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E) :=
    (Fintype.equivFinOfCardEq hcard).symm
  let a : Fin (finrank ℚ E) → 𝓞 E := fun i => RingOfIntegers.basis E (e i)
  refine ⟨∑ i, ∑ σ : E →+* ℂ, ‖σ (a i)‖, a, ?_, ?_⟩
  · have := (integralBasis E).linearIndependent.comp e e.injective
    convert this using 1
    funext i
    simp [a, integralBasis_apply]
  · intro i σ
    calc ‖σ (a i)‖ ≤ ∑ σ' : E →+* ℂ, ‖σ' (a i)‖ :=
          Finset.single_le_sum (f := fun σ' : E →+* ℂ => ‖σ' (a i)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      _ ≤ ∑ j, ∑ σ' : E →+* ℂ, ‖σ' (a j)‖ :=
          Finset.single_le_sum (f := fun j => ∑ σ' : E →+* ℂ, ‖σ' (a j)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Matrix

theorem IsotropicSplit.proof (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h₁ : EigenspacesOrthogonal.Statement ι) : IsotropicSplit.Statement ι := by
  intro H P hM z hz
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  set A := majInvolution H P with hAdef
  have hA2 : A * A = 1 := by
    rw [hAdef, majInvolution, show H⁻¹ * P * (H⁻¹ * P) = H⁻¹ * (P * H⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPHP, nonsing_inv_mul H hdet]
  have hPA : P * A = H := by
    rw [hAdef, majInvolution, ← Matrix.mul_assoc, hPHP]
  have hAA (v : ι → ℂ) : A *ᵥ (A *ᵥ v) = v := by
    rw [mulVec_mulVec, hA2, one_mulVec]
  set a := plusPart H P z with hadef
  set b := minusPart H P z with hbdef
  have ha : A *ᵥ a = a := by
    rw [hadef, plusPart, ← hAdef, mulVec_smul, mulVec_add, hAA, add_comm]
  have hb : A *ᵥ b = -b := by
    rw [hbdef, minusPart, ← hAdef, mulVec_smul, mulVec_sub, hAA, ← smul_neg, neg_sub]
  have hzab : z = a + b := by
    rw [hadef, hbdef, plusPart, minusPart, ← smul_add]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hAzab : A *ᵥ z = a - b := by
    rw [hadef, hbdef, plusPart, minusPart, ← hAdef, ← smul_sub]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hab : star a ⬝ᵥ (P *ᵥ b) = 0 := h₁ H P ⟨hP, hH, hdet, hPHP⟩ a b ha hb
  have hba : star b ⬝ᵥ (P *ᵥ a) = 0 := by
    rw [star_dotProduct, star_mulVec, ← dotProduct_mulVec, hP.1.eq, hab, star_zero]
  refine ⟨ha, hb, ?_⟩
  have h0 : star (a + b) ⬝ᵥ (P *ᵥ (a - b)) = 0 := by
    rw [← hAzab, ← hzab, mulVec_mulVec, hPA, hz]
  rw [star_add, add_dotProduct, mulVec_sub, dotProduct_sub, dotProduct_sub, hab, hba] at h0
  linear_combination h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem isIsotropicLine_span_singleton (h : HermitianForm F E W) {x : W} (hx : x ≠ 0)
    (hxx : h.toSesq x x = 0) : IsIsotropicLine h (Submodule.span E {x}) := by
  refine ⟨finrank_span_singleton hx, ?_⟩
  intro a ha b hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hb
  simp only [map_smul, LinearMap.map_smulₛₗ₂, hxx, smul_zero]

theorem LatticeOrbitsFinite.proof (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : MahlerCompactness.Statement h v) (h₂ : MajorantExists.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : LinePairOrbitsFinite.Statement h) :
    LatticeOrbitsFinite.Statement h := by
  intro D
  obtain ⟨M⟩ := h₂
  obtain ⟨S₁, hS₁, K, -, hK⟩ := h₁ M D 1 one_pos
  obtain ⟨S₂, hS₂, hP⟩ := h₄ D
  refine ⟨S₁ ∪ Prod.fst '' S₂, hS₁.union (hS₂.image _), ?_⟩
  intro La hLa
  by_cases hshort : ∃ x : W, x ∈ La ∧ x ≠ 0 ∧ M.len (invApply (1 : archUnitary h v) (vecAt v x)) < 1
  · obtain ⟨x, hxL, hx0, hxlt⟩ := hshort
    have hxx : h.toSesq x x = 0 := h₃ M D La 1 x hLa hxL hxlt
    obtain ⟨p, hp, g, hg, -⟩ := hP La (Submodule.span E {x}) hLa
      (isIsotropicLine_span_singleton h hx0 hxx)
    exact ⟨p.1, Or.inr ⟨p, hp, rfl⟩, g, hg⟩
  · push Not at hshort
    obtain ⟨γ, hγ, -⟩ := hK La 1 hLa hshort
    exact ⟨γ • La, Or.inl hγ, γ⁻¹, inv_smul_smul γ La⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

variable (E : Type*) [Field E] [NumberField E]
variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineIndexCoeffs.proof : LineIndexCoeffs.Statement (E := E) W := by
  intro La x hx
  let f : E →+ W := (smulAddHom E W).flip x
  have hfa : ∀ a : E, f a = a • x := fun a => rfl
  have hf : Function.Injective f := by
    intro a b hab
    rw [hfa, hfa] at hab
    exact smul_left_injective E hx hab
  have h1 : (intSubgroup E).map f = ringMultiples E x := by
    rw [intSubgroup, ringMultiples, AddMonoidHom.range_comp]
  have hrange : f.range = (Submodule.span E {x}).toAddSubgroup := by
    ext y
    simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton,
      hfa]
  have h2 : (lineCoeffs La x).map f = La ⊓ (Submodule.span E {x}).toAddSubgroup := by
    rw [lineCoeffs, AddSubgroup.map_comap_eq, hrange, inf_comm]
  unfold lineIndex
  rw [← h1, ← h2, AddSubgroup.relIndex_map_map_of_injective _ _ hf]

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsTotallyReal F] in

theorem ShortestVectorIndex.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LineIndexCoeffs.Statement (E := E) W) (h₂ : LineCoeffsFG.Statement (E := E) W)
    (h₃ : WeightedLenSmul.Statement h v) (h₄ : WeightPos.Statement h v)
    (h₅ : WeightedIndexBound.Statement E) : ShortestVectorIndex.Statement h v := by
  intro M r ha D La g x hD hx hx0 hmin
  set c : InfinitePlace E → ℝ := fun w =>
    (star (invApply g (vecAt v x) w) ⬝ᵥ (M.P w *ᵥ invApply g (vecAt v x) w)).re with hc
  have hcpos : ∀ w, 0 < c w := h₄ M g x hx0
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]

  have hlen : ∀ a : E, M.len (invApply g (vecAt v (a • x))) ^ 2 =
      ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a
    rw [h₃ M g x a]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hlen1 : M.len (invApply g (vecAt v x)) ^ 2 = ∑ w, c w := by
    have := hlen 1
    simpa using this
  have hsub : intSubgroup E ≤ lineCoeffs La x := by
    rintro _ ⟨a, rfl⟩
    exact hD.isLattice.smul_mem a x hx
  have hfg : (lineCoeffs La x).FG := h₂ La x hD.isLattice.fg hx0
  have hmin' : ∀ a ∈ lineCoeffs La x, a ≠ 0 →
      ∑ w, c w ≤ ∑ w, c w * ‖w.embedding a‖ ^ 2 := by
    intro a haA ha0
    have hax : a • x ∈ La := haA
    have hax0 : a • x ≠ 0 := smul_ne_zero ha0 hx0
    have hle := hmin (a • x) hax hax0
    rw [← hlen1, ← hlen a]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  obtain ⟨a, hali, habs⟩ := ha
  have ha' : ∃ b : Fin (finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg, hali.comp _ (Fin.cast_injective hdeg), fun i σ => habs _ σ⟩
  have key := h₅ c hcpos (lineCoeffs La x) hsub hfg hmin' r ha'
  rw [h₁ La x hx0]
  rw [hdeg] at key
  push_cast at key
  exact key

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ShortVectorIsotropic.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : HermAtPlace.Statement h v) (h₂ : GramAtData.Statement h v)
    (h₃ : ArchInvariant.Statement h v) (h₄ : MajorantBound.Statement ι)
    (h₅ : LenSq.Statement h v) (h₆ : IntegerSmallAtPlaces.Statement E) :
    ShortVectorIsotropic.Statement h v := by
  intro M D La g x hLa hx hlen
  apply h₆ _ (hLa.integral x hx x hx)
  intro w
  set y := vecAt v x
  set z := invApply g y
  have hP : IsMajorantOf (gramAt h v w) (M.P w) :=
    ⟨M.posDef w, (h₂ w).1, (h₂ w).2, M.siegel w⟩
  obtain ⟨hnn, hsq⟩ := h₅ M z
  have hlen0 : 0 ≤ M.len z := Real.sqrt_nonneg _
  have hsq1 : M.len z ^ 2 < 1 := by nlinarith
  have hterm : (star (z w) ⬝ᵥ (M.P w *ᵥ z w)).re ≤ M.len z ^ 2 := by
    rw [hsq]
    exact Finset.single_le_sum (f := fun w' => (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re)
      (fun w' _ => hnn w') (Finset.mem_univ w)
  have hform : w.embedding (h.toSesq x x) = star (z w) ⬝ᵥ (gramAt h v w *ᵥ z w) := by
    rw [h₁ w x x, h₃ g y y w]
  rw [← InfinitePlace.norm_embedding_eq, hform]
  exact lt_of_le_of_lt ((h₄ _ _ hP (z w)).trans hterm) hsq1

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Matrix

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (d : ℕ) [Fact (finrank ℝ V = d)]

theorem VolumeFormIntComb.proof : VolumeFormIntComb.Statement V d := by
  intro o b T
  have hd : finrank ℝ V = d := Fact.out
  let e : Basis (Fin d) ℝ V := Module.finBasisOfFinrankEq ℝ V hd
  have key : ∀ v : Fin d → V, o.volumeForm v = o.volumeForm e * e.det v := by
    intro v
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e o.volumeForm]
    rfl
  have hmat : e.toMatrix (fun i => ∑ j, (T i j : ℝ) • b j) =
      e.toMatrix b * (T.map (Int.cast : ℤ → ℝ))ᵀ := by
    ext k i
    simp [Basis.toMatrix_apply, Matrix.mul_apply, map_sum, map_smul, Finset.sum_apply,
      mul_comm]
  rw [key, key b, Basis.det_apply, Basis.det_apply, hmat, det_mul, det_transpose,
    Int.cast_det T]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [IsTotallyReal F] [NumberField E] [IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in

theorem WeightedLenSmul.vecAt_smul (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i
  simp [vecAt, map_mul]

omit [NumberField F] [IsTotallyReal F] [NumberField E] [IsTotallyComplex E] in

theorem WeightedLenSmul.invApply_vecAt_smul {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) (a : E) (x : W) (w : InfinitePlace E) :
    invApply g (vecAt v (a • x)) w = w.embedding a • invApply g (vecAt v x) w := by
  simp only [invApply, WeightedLenSmul.vecAt_smul, Matrix.mulVec_smul]

omit [DecidableEq ι] in

theorem WeightedLenSmul.star_smul_dotProduct_mulVec_smul (P : Matrix ι ι ℂ) (c : ℂ)
    (z : ι → ℂ) :
    star (c • z) ⬝ᵥ (P *ᵥ (c • z)) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (star z ⬝ᵥ (P *ᵥ z)) := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, mul_comm c, Complex.star_def, Complex.conj_mul']
  push_cast
  ring

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem WeightedLenSmul.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : LenSq.Statement h v) : WeightedLenSmul.Statement h v := by
  intro M g x a
  rw [(h₁ M _).2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [WeightedLenSmul.invApply_vecAt_smul, WeightedLenSmul.star_smul_dotProduct_mulVec_smul,
    Complex.re_ofReal_mul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem WeightedNormSq.proof (E : Type*) [Field E] [NumberField E] : WeightedNormSq.Statement E := by
  intro c hc a
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.sum_univ_two]
  simp only [weightedEmbed, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs,
    sq_abs, show ((1 : Fin 2) = 0) = False from by decide, ↓reduceIte]
  rw [mul_pow, mul_pow, Real.sq_sqrt (hc w), Complex.sq_norm, Complex.normSq_apply]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField NumberField.InfinitePlace Module

theorem WeightedSpaceDim.proof (E : Type*) [Field E] [NumberField E] [IsTotallyComplex E] :
    WeightedSpaceDim.Statement E := by
  unfold WeightedSpaceDim.Statement
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin,
    card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    IsTotallyComplex.finrank]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module Matrix
open scoped ComplexOrder

section Steps

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem WeightPos.proof (h : GroundTheory.Automorphic.HermitianForm F E W) (v : Basis ι E W)
    (h₁ : VecAtNeZero.Statement v) : WeightPos.Statement h v := by
  intro M g x hx w
  set k : GL ι ℂ := ((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w with hk
  have hne : invApply g (vecAt v x) w ≠ 0 := by
    intro hz
    have hz' : (k : Matrix ι ι ℂ) *ᵥ vecAt v x w = 0 := hz
    have h2 : ((k⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ ((k : Matrix ι ι ℂ) *ᵥ vecAt v x w) = 0 := by
      rw [hz', mulVec_zero]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at h2
    exact h₁ x hx w h2
  have hpos := (M.posDef w).dotProduct_mulVec_pos hne
  exact (Complex.pos_iff.mp hpos).1

end Steps

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

section Matrices

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem MajorantBound.full : MajorantBound.Statement ι := MajorantBound.proof ι

theorem EigenspacesOrthogonal.full : EigenspacesOrthogonal.Statement ι :=
  EigenspacesOrthogonal.proof ι

theorem EigenReflection.full : EigenReflection.Statement ι := EigenReflection.proof ι

theorem EigenReflectionMaps.full : EigenReflectionMaps.Statement ι :=
  EigenReflectionMaps.proof ι (EigenReflection.full ι) (EigenspacesOrthogonal.full ι)

theorem IsotropicSplit.full : IsotropicSplit.Statement ι :=
  IsotropicSplit.proof ι (EigenspacesOrthogonal.full ι)

theorem PhaseOnMinus.full : PhaseOnMinus.Statement ι := PhaseOnMinus.proof ι

theorem KTransitive.full : KTransitive.Statement ι :=
  KTransitive.proof ι (IsotropicSplit.full ι) (EigenReflectionMaps.full ι) (PhaseOnMinus.full ι)
    (EigenspacesOrthogonal.full ι)

end Matrices

section Groups

theorem UnfoldOrbit.full (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] :
    UnfoldOrbit.Statement G :=
  UnfoldOrbit.proof G

theorem DiscreteFundamentalDomain.full (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] : DiscreteFundamentalDomain.Statement G :=
  DiscreteFundamentalDomain.proof G

theorem TorusIntegralHomogeneous.full (κ : Type*) [Fintype κ] :
    TorusIntegralHomogeneous.Statement κ :=
  TorusIntegralHomogeneous.proof κ

theorem BoundedIndexSubgroupsFinite.full (G : Type*) [AddCommGroup G] :
    BoundedIndexSubgroupsFinite.Statement G :=
  BoundedIndexSubgroupsFinite.proof G

theorem MinkowskiVolumeForm.full (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) [Fact (finrank ℝ V = d)] : MinkowskiVolumeForm.Statement V d :=
  MinkowskiVolumeForm.proof V d

theorem VolumeFormIntComb.full (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) [Fact (finrank ℝ V = d)] : VolumeFormIntComb.Statement V d :=
  VolumeFormIntComb.proof V d

end Groups

section Numbers

variable (E : Type*) [Field E] [NumberField E]

theorem IntegerSmallAtPlaces.full : IntegerSmallAtPlaces.Statement E := IntegerSmallAtPlaces.proof E

theorem CoeffLatticeBasis.full : CoeffLatticeBasis.Statement E := CoeffLatticeBasis.proof E

theorem IndexLeDet.full : IndexLeDet.Statement E := IndexLeDet.proof E

theorem WeightedNormSq.full : WeightedNormSq.Statement E := WeightedNormSq.proof E

theorem IdealClassesFinite.full : IdealClassesFinite.Statement E := IdealClassesFinite.proof E

theorem IntegralFamilyBound.full : IntegralFamilyBound.Statement E := IntegralFamilyBound.proof E

theorem CongruenceUnitsFiniteIndex.full : CongruenceUnitsFiniteIndex.Statement E :=
  CongruenceUnitsFiniteIndex.proof E

theorem WeightedSpaceDim.full [IsTotallyComplex E] : WeightedSpaceDim.Statement E :=
  WeightedSpaceDim.proof E

theorem WeightedIndexBound.full [IsTotallyComplex E] : WeightedIndexBound.Statement E :=
  WeightedIndexBound.proof E (CoeffLatticeBasis.full E) (IndexLeDet.full E) (WeightedNormSq.full E)
    (WeightedSpaceDim.full E) (MinkowskiVolumeForm.full _ _) (VolumeFormIntComb.full _ _)

variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineIndexNeZero.full : LineIndexNeZero.Statement E W := LineIndexNeZero.proof E W

theorem LineIndexCoeffs.full : LineIndexCoeffs.Statement (E := E) W := LineIndexCoeffs.proof E W

theorem LineCoeffsFG.full : LineCoeffsFG.Statement (E := E) W := LineCoeffsFG.proof W

end Numbers

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)

theorem HermAtPlace.full : HermAtPlace.Statement h v := HermAtPlace.proof h v

theorem GramAtData.full : GramAtData.Statement h v := GramAtData.proof h v

theorem ArchInvariant.full : ArchInvariant.Statement h v := ArchInvariant.proof h v

theorem LenSq.full : LenSq.Statement h v := LenSq.proof h v

theorem VecAtNeZero.full : VecAtNeZero.Statement v := VecAtNeZero.proof v

theorem WeightedLenSmul.full : WeightedLenSmul.Statement h v :=
  WeightedLenSmul.proof h v (LenSq.full h v)

theorem WeightPos.full : WeightPos.Statement h v := WeightPos.proof h v (VecAtNeZero.full v)

theorem MajorantExists.full : MajorantExists.Statement h v :=
  MajorantExists.proof h v (GramAtData.full h v)

theorem ArchLatticeDiscrete.full : ArchLatticeDiscrete.Statement h v := ArchLatticeDiscrete.proof h v

theorem LenCauchySchwarz.full : LenCauchySchwarz.Statement h v := LenCauchySchwarz.proof h v

theorem BoundedInverseCompact.full : BoundedInverseCompact.Statement h v :=
  BoundedInverseCompact.proof h v

theorem GramDetermines.full : GramDetermines.Statement h := GramDetermines.proof h

theorem WittPartner.full : WittPartner.Statement h := WittPartner.proof h

theorem ComplementForm.full : ComplementForm.Statement h := ComplementForm.proof h

theorem IsotropicScaling.full : IsotropicScaling.Statement h :=
  IsotropicScaling.proof h (WittPartner.full h)

theorem HyperbolicPairTransitive.full [FiniteDimensional E W] :
    HyperbolicPairTransitive.Statement h :=
  HyperbolicPairTransitive.proof h

theorem ShortVectorIsotropic.full : ShortVectorIsotropic.Statement h v :=
  ShortVectorIsotropic.proof h v (HermAtPlace.full h v) (GramAtData.full h v) (ArchInvariant.full h v)
    (MajorantBound.full ι) (LenSq.full h v) (IntegerSmallAtPlaces.full E)

theorem ShortestVectorIndex.full : ShortestVectorIndex.Statement h v :=
  ShortestVectorIndex.proof h v (LineIndexCoeffs.full E W) (LineCoeffsFG.full E W)
    (WeightedLenSmul.full h v) (WeightPos.full h v) (WeightedIndexBound.full E)

theorem ParabolicDecomposition.full : ParabolicDecomposition.Statement h v :=
  ParabolicDecomposition.proof h v (KTransitive.full ι) (HermAtPlace.full h v) (GramAtData.full h v)
    (ArchInvariant.full h v) (VecAtNeZero.full v)

end Spaces

section Conditional

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

theorem MahlerCompactness.full_of {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) : MahlerCompactness.Statement h v :=
  MahlerCompactness.proof h v (BoundedGenerators.proof h v hR hA hT) (LenCauchySchwarz.full h v)
    (GramDetermines.full h) (BoundedInverseCompact.full h v)

theorem AdaptedReduction.full_of {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (h : HermitianForm F E W) (hLN : LineNormalForm.Statement h)
    (hCL : ComplementLattice.Statement h) : AdaptedReduction.Statement h :=
  AdaptedReduction.proof h (HyperbolicPairTransitive.full h) hLN hCL

theorem LinePairOrbitsFinite.full_of {W : Type u} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h : HermitianForm F E W)
    (hB : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (hCE : ComplementExtension.Statement h)
    (hLN : LineNormalForm.Statement h) (hCL : ComplementLattice.Statement h) :
    LinePairOrbitsFinite.Statement h :=
  LinePairOrbitsFinite.proof h hB (WittPartner.full h) (ComplementForm.full h) hCE
    (AdaptedReduction.full_of h hLN hCL)

theorem LatticeOrbitsFinite.step_of {W : Type u} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h : HermitianForm F E W)
    (hB : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (hR : ReducedBasisBound.Statement)
    (hA : ArchCovolumeBound.Statement h (Module.finBasis E W))
    (hT : MajorantTransport.Statement h (Module.finBasis E W))
    (hCE : ComplementExtension.Statement h) (hLN : LineNormalForm.Statement h)
    (hCL : ComplementLattice.Statement h) : LatticeOrbitsFinite.Statement h :=
  LatticeOrbitsFinite.proof h (Module.finBasis E W) (MahlerCompactness.full_of h _ hR hA hT)
    (MajorantExists.full h _) (ShortVectorIsotropic.full h _)
    (LinePairOrbitsFinite.full_of h hB hCE hLN hCL)

theorem LatticeOrbitsFiniteBelow.of_steps (hR : ReducedBasisBound.Statement)
    (hA : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchCovolumeBound.Statement h v)
    (hT : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantTransport.Statement h v)
    (hCE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementExtension.Statement h)
    (hLN : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), LineNormalForm.Statement h)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementLattice.Statement h)
    (N : ℕ) : LatticeOrbitsFiniteBelow.{u} F E N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ _ _ h hN
    exact LatticeOrbitsFinite.step_of h (ih _ hN) hR (hA W h _ _) (hT W h _ _) (hCE W h)
      (hLN W h) (hCL W h)

theorem ScalingLaw.full_of {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hP : LinePairOrbitsFinite.Statement h) (hU : UnfoldingIntegral.Statement h v) :
    ScalingLaw.Statement h v :=
  ScalingLaw.proof h v hU
    (VectorOrbitsFinite.proof h hP (IsotropicScaling.full h) (BoundedIndexSubgroupsFinite.full W)
      (LineIndexNeZero.full E W))
    (UnfoldOrbit.full _) (DiscreteFundamentalDomain.full _) (ArchLatticeDiscrete.full h v)

theorem UnfoldingIntegral.full_of {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hUA : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (hHP : HaarParabolicCoordinates.Statement h v) (hSC : StabilizerCovolumeFinite.Statement h v) :
    UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.proof h v (UnfoldingTorus.proof h v hUA hHP hSC)
    (TorusIntegralHomogeneous.full _) (DiscreteFundamentalDomain.full _)

theorem ArithmeticCovolumeFinite.step_of {W : Type u} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {ι : Type*} [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W)
    (v : Basis ι E W) (hL : LatticeOrbitsFiniteBelow.{u} F E (finrank E W))
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) (hCE : ComplementExtension.Statement h)
    (hLN : LineNormalForm.Statement h) (hCL : ComplementLattice.Statement h)
    (hUA : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (hHP : HaarParabolicCoordinates.Statement h v) (hSC : StabilizerCovolumeFinite.Statement h v)
    (hPB : LatticePointsBelowFinite.Statement h v) : ArithmeticCovolumeFinite.Statement h v :=
  ArithmeticCovolumeFinite.proof h v
    (ScalingLaw.full_of h v (LinePairOrbitsFinite.full_of h hL hCE hLN hCL)
      (UnfoldingIntegral.full_of h v hUA hHP hSC))
    (MahlerCompactness.full_of h v hR hA hT) (ShortVectorIsotropic.full h v)
    (ShortestVectorIndex.full h v) (IntegralFamilyBound.full E) (MajorantExists.full h v)
    (ArchLatticeDiscrete.full h v) hPB

theorem CovolumeFiniteBelow.of_steps (hR : ReducedBasisBound.Statement)
    (hA : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchCovolumeBound.Statement h v)
    (hT : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantTransport.Statement h v)
    (hCE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementExtension.Statement h)
    (hLN : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), LineNormalForm.Statement h)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementLattice.Statement h)
    (hUA : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W) (M : Majorant h v),
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (hHP : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W),
      HaarParabolicCoordinates.Statement h v)
    (hSC : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W),
      CovolumeFiniteBelow.{u} F E (finrank E W) → StabilizerCovolumeFinite.Statement h v)
    (hPB : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W),
      LatticePointsBelowFinite.Statement h v)
    (N : ℕ) : CovolumeFiniteBelow.{u} F E N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ _ _ h n v hN
    exact ArithmeticCovolumeFinite.step_of h v
      (LatticeOrbitsFiniteBelow.of_steps hR hA hT hCE hLN hCL _) hR (hA W h n v) (hT W h n v)
      (hCE W h) (hLN W h) (hCL W h) (hUA W h n v) (hHP W h n v) (hSC W h n v (ih _ hN))
      (hPB W h n v)

theorem AdelicCovolumeFinite.full_of {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {ι : Type*} [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W)
    (v : Basis ι E W) (hL : LatticeOrbitsFinite.Statement h)
    (hC : ArithmeticCovolumeFinite.Statement h v) (hAU : ArchimedeanUnitaryEquiv.Statement h v)
    (hAL : AdelicLatticeDictionary.Statement h v)
    (hDC : DoubleCosetCovolume.Statement (unitaryPoints F E (gram h.toSesq v) 𝔸[F])
      (archUnitary h v) (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) :
    AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.proof h v hL hC hAU hAL hDC

end Conditional

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
