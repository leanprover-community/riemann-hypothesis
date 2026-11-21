import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialInfinite
import GroundTheory.GlobalFields.NormResidueSymbol.Rational
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
import GroundTheory.GlobalFields.FirstInequality
import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois

section
namespace GroundTheory.Global

open IsDedekindDomain NumberField AdeleBaseChange IdeleGroup

noncomputable section

variable {K K' L L' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Field L'] [NumberField L'] [Algebra K K'] [Algebra K L] [Algebra K L']
  [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

variable (K) in

def restrictScalarsHom : (L' ≃ₐ[K'] L') →* (L' ≃ₐ[K] L') where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField K] [NumberField K'] [NumberField L'] in
@[simp]
theorem restrictScalarsHom_apply (σ : L' ≃ₐ[K'] L') : restrictScalarsHom K σ = σ.restrictScalars K :=
  rfl

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem restrictNormal_restrictScalars_ideleSymbol (x : IdeleGroup K') :
    ((ideleSymbol K' L' x).restrictScalars K).restrictNormal L =
      ideleSymbol K L (ideleNorm K K' x) := by
  have h := IdeleGroup.continuous_monoidHom_ext
    (ψ := (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).comp
      ((restrictScalarsHom K).comp (ideleSymbol K' L')))
    (ψ' := (ideleSymbol K L).comp (ideleNorm K K'))
    ((continuous_of_discreteTopology : Continuous ((AlgEquiv.restrictNormalHom (F := K)
      (K₁ := L') L).comp (restrictScalarsHom (L' := L') K))).comp (continuous_ideleSymbol L'))
    ((continuous_ideleSymbol L).comp (continuous_ideleNorm (K := K) (L := K')))
    (fun v' a ↦ by
      change ((ideleSymbol K' L' (finiteEmbedding v' a)).restrictScalars K).restrictNormal L =
        ideleSymbol K L (ideleNorm K K' (finiteEmbedding v' a))
      rw [ideleSymbol_finiteEmbedding, ideleNorm_finiteEmbedding, ideleSymbol_finiteEmbedding]
      exact restrictNormal_localSymbol_norm (below K v') v' a)
    (fun w' a ↦ by
      change ((ideleSymbol K' L' (infiniteEmbedding w' a)).restrictScalars K).restrictNormal L =
        ideleSymbol K L (ideleNorm K K' (infiniteEmbedding w' a))
      rw [ideleSymbol_infiniteEmbedding, ideleNorm_infiniteEmbedding, ideleSymbol_infiniteEmbedding]
      exact restrictNormal_infiniteLocalSymbol_norm w' a)
  exact congrArg (fun f : IdeleGroup K' →* (L ≃ₐ[K] L) ↦ f x) h

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

section Trivial

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem range_ideleNorm_eq_top_of_ideleSymbol_eq_one (h : ∀ x, ideleSymbol K L x = 1) :
    (ideleNorm K L).range = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ ↦ (IdeleNorm.mem_range_ideleNorm_iff_forall L x).2
    ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · obtain ⟨w⟩ := nonempty_placesOver L v
    have h1 : finiteProj v x ∈ (localSymbol L v).ker := by
      rw [MonoidHom.mem_ker, ← ideleSymbol_finiteEmbedding]
      exact h _
    rw [ker_localSymbol L v w] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨Pi.mulSingle w y, by rw [IdeleNorm.finiteLocalNorm_mulSingle]; exact hy⟩
  · obtain ⟨w⟩ := IdeleNorm.nonempty_infinitePlacesOver L v
    have h1 : infiniteProj v x ∈ (infiniteLocalSymbol L v).ker := by
      rw [MonoidHom.mem_ker, ← ideleSymbol_infiniteEmbedding]
      exact h _
    rw [ker_infiniteLocalSymbol L v w] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨Pi.mulSingle w y, by rw [IdeleNorm.infiniteLocalNorm_mulSingle]; exact hy⟩

end Trivial

universe u

section Cyclic

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

theorem finrank_eq_one_of_ideleSymbol_eq_one (h : ∀ x, ideleSymbol K L x = 1) :
    Module.finrank K L = 1 :=
  firstInequality.finrank_eq_one_of_sup_eq_top
    (top_le_iff.1 (range_ideleNorm_eq_top_of_ideleSymbol_eq_one L h ▸ le_sup_left))

end Cyclic

section Surjective

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

attribute [local instance] galCommGroup

omit [NumberField K] [NumberField L] [IsMulCommutative (L ≃ₐ[K] L)] in

theorem restrictNormal_fixedField_eq_one {N : Subgroup (L ≃ₐ[K] L)} [N.Normal] {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ N) : σ.restrictNormal (fixedField N) = 1 := by
  ext y
  change ((σ.restrictNormal (fixedField N) y : fixedField N) : L) = y
  exact (AlgEquiv.restrictNormal_commutes σ (fixedField N) y).trans
    ((mem_fixedField_iff N y).1 y.2 σ hσ)

theorem ideleSymbol_surjective : Function.Surjective (ideleSymbol K L) := by
  classical
  by_contra hs
  obtain ⟨σ, hσ⟩ := not_forall.1 hs
  set H := (ideleSymbol K L).range with hH
  have hσH : σ ∉ H := fun ⟨x, hx⟩ ↦ hσ ⟨x, hx⟩
  obtain ⟨ι, _, n, _, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite
    ((L ≃ₐ[K] L) ⧸ H)
  have hne : (QuotientGroup.mk' H σ) ≠ 1 := by
    rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨i, hi⟩ : ∃ i, e (QuotientGroup.mk' H σ) i ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne ((MulEquiv.map_eq_one_iff e).1 (funext hall))
  set χ : (L ≃ₐ[K] L) →* Multiplicative (ZMod (n i)) :=
    (Pi.evalMonoidHom (fun j ↦ Multiplicative (ZMod (n j))) i).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' H)) with hχ
  set N := χ.ker with hN
  have hHN : ∀ x, ideleSymbol K L x ∈ N := fun x ↦ by
    have hq : QuotientGroup.mk' H (ideleSymbol K L x) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨x, rfl⟩
    rw [hN, MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, hq, map_one, map_one]
  have hσN : σ ∉ N := hi
  set F := fixedField N with hF
  have : IsCyclic (F ≃ₐ[K] F) := by
    have e1 : (F ≃ₐ[K] F) ≃* χ.range :=
      (IsGalois.normalAutEquivQuotient N).symm.trans (QuotientGroup.quotientKerEquivRange χ)
    exact isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective
  have hF1 : ∀ x, ideleSymbol K F x = 1 := fun x ↦ by
    rw [← restrictNormal_ideleSymbol F L x]
    exact restrictNormal_fixedField_eq_one (hHN x)
  have hbot : F = ⊥ := finrank_eq_one_iff.1 (finrank_eq_one_of_ideleSymbol_eq_one hF1)
  have htop : N = ⊤ := by
    rw [← fixingSubgroup_fixedField N, ← hF, hbot, fixingSubgroup_bot]
  exact hσN (htop ▸ Subgroup.mem_top σ)

end Surjective

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

namespace CyclotomicSymbol

section Roots

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem ideleSymbol_diagonal_apply_of_pow_eq_one (a : Kˣ) {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : ζ ^ n = 1) : ideleSymbol K L (diagonal K a) ζ = ζ := by
  have hk : orderOf ζ ≠ 0 := (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨n, Nat.pos_of_ne_zero hn, hζ⟩)).ne'
  have : NeZero (orderOf ζ) := ⟨hk⟩
  have hprim : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
  set L₀ : IntermediateField ℚ L := ℚ⟮ζ⟯ with hL₀
  have : IsCyclotomicExtension {orderOf ζ} ℚ L₀ :=
    hprim.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsGalois ℚ L₀ := IsCyclotomicExtension.isGalois {orderOf ζ} ℚ L₀
  have : IsMulCommutative (L₀ ≃ₐ[ℚ] L₀) := IsCyclotomicExtension.isMulCommutative {orderOf ζ} ℚ L₀
  have h := restrictNormal_restrictScalars_ideleSymbol (K := ℚ) (L := L₀) (L' := L) (diagonal K a)
  rw [ideleNorm_diagonal, RationalSymbol.ideleSymbol_diagonal_eq_one L₀ {orderOf ζ}] at h
  have h' := congrArg (fun σ : L₀ ≃ₐ[ℚ] L₀ ↦ ((σ ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ : L₀) : L)) h
  simp only [AlgEquiv.one_apply] at h'
  exact (AlgEquiv.restrictNormal_commutes ((ideleSymbol K L (diagonal K a)).restrictScalars ℚ) L₀
    ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩).symm.trans h'

theorem ideleSymbol_diagonal_eq_one (S : Set ℕ) [IsCyclotomicExtension S K L] (a : Kˣ) :
    ideleSymbol K L (diagonal K a) = 1 :=
  IsCyclotomicExtension.algEquiv_eq_of_apply_eq S K L fun m hm hm0 ↦ by
    obtain ⟨r, hr⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L hm hm0
    exact ⟨r, hr, ideleSymbol_diagonal_apply_of_pow_eq_one a hm0 hr.pow_eq_one⟩


end Roots

section Sub

variable {K : Type*} [Field K] [NumberField K] (L M : Type*) [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (M ≃ₐ[K] M)]

theorem ideleSymbol_diagonal_eq_one_of_le (S : Set ℕ) [IsCyclotomicExtension S K M] (a : Kˣ) :
    ideleSymbol K L (diagonal K a) = 1 := by
  rw [← restrictNormal_ideleSymbol L M, ideleSymbol_diagonal_eq_one S a]
  exact map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)

theorem range_diagonal_le_ker_ideleSymbol (S : Set ℕ) [IsCyclotomicExtension S K M] :
    (diagonal K).range ≤ (ideleSymbol K L).ker := by
  rintro _ ⟨a, rfl⟩
  exact ideleSymbol_diagonal_eq_one_of_le L M S a

end Sub

section ClassSymbol

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (ideleSymbol K L) h

variable {L}

@[simp]
theorem ideleClassSymbol_mk (h : (diagonal K).range ≤ (ideleSymbol K L).ker) (x : IdeleGroup K) :
    ideleClassSymbol L h (IdeleClassGroup.mk K x) = ideleSymbol K L x :=
  rfl

theorem continuous_ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    Continuous (ideleClassSymbol L h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ideleSymbol L)

end ClassSymbol

universe u

theorem ideleClassSymbol_surjective {K L : Type u} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    Function.Surjective (ideleClassSymbol L h) := fun σ ↦
  let ⟨x, hx⟩ := ideleSymbol_surjective (K := K) (L := L) σ
  ⟨IdeleClassGroup.mk K x, hx⟩

end CyclotomicSymbol

end

end GroundTheory.Global
end

section
namespace GroundTheory.Global

open NumberField IntermediateField IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicSymbol

open FiniteSubfield

def compositum (K F : FiniteSubfield) : FiniteSubfield :=
  ⟨K.1 ⊔ F.1, inferInstance⟩

variable (K F : FiniteSubfield)

instance fact_le_compositum_left : Fact (K ≤ compositum K F) :=
  ⟨show K.1 ≤ K.1 ⊔ F.1 from le_sup_left⟩

instance fact_le_compositum_right : Fact (F ≤ compositum K F) :=
  ⟨show F.1 ≤ K.1 ⊔ F.1 from le_sup_right⟩

theorem fixingSubgroup_compositum :
    (compositum K F).1.fixingSubgroup = K.1.fixingSubgroup ⊓ F.1.fixingSubgroup :=
  fixingSubgroup_sup

variable [IsGalois ℚ F.1]

theorem fixingSubgroup_normal : F.1.fixingSubgroup.Normal := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  have h : @IsGalois ℚ _ F.1 _ (IntermediateField.algebra' F.1) := by
    convert (inferInstance : IsGalois ℚ F.1)
    exact Subsingleton.elim _ _
  rw [InfiniteGalois.normal_iff_isGalois]
  exact h

instance normal_subgroupOf_compositum :
    ((compositum K F).1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal := by
  rw [fixingSubgroup_compositum, Subgroup.inf_subgroupOf_left]
  have := fixingSubgroup_normal F
  exact Subgroup.Normal.subgroupOf this _

instance isGalois_compositum : IsGalois K.1 (compositum K F).1 :=
  isGalois_of_normal

theorem mem_fixingSubgroup_iff_restrictNormal_eq_one (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) :
    g ∈ F.1.fixingSubgroup ↔ g.restrictNormal F.1 = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg
    ext y
    exact (AlgEquiv.restrictNormal_commutes g F.1 y).trans (hg y y.2)
  · intro hg y hy
    have h1 := AlgEquiv.restrictNormal_commutes g F.1 ⟨y, hy⟩
    rw [hg] at h1
    exact h1.symm

variable [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)] in

theorem commutator_mem_fixingSubgroup (a b : ℚ̄ ≃ₐ[ℚ] ℚ̄) :
    (a * b)⁻¹ * (b * a) ∈ F.1.fixingSubgroup := by
  rw [mem_fixingSubgroup_iff_restrictNormal_eq_one]
  change AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1 ((a * b)⁻¹ * (b * a)) = 1
  rw [map_mul, map_inv, map_mul, map_mul,
    mul_comm' (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1 b), inv_mul_cancel]

variable [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)]

instance isMulCommutative_compositum :
    IsMulCommutative ((compositum K F).1 ≃ₐ[K.1] (compositum K F).1) := by
  refine ⟨⟨fun a b ↦ ?_⟩⟩
  obtain ⟨g, rfl⟩ := restrictHom_surjective (F := K) (E := compositum K F) a
  obtain ⟨h, rfl⟩ := restrictHom_surjective (F := K) (E := compositum K F) b
  rw [← map_mul, ← map_mul, MonoidHom.eq_iff, ker_restrictHom, Subgroup.mem_subgroupOf,
    fixingSubgroup_compositum]
  exact ⟨Subtype.property _, commutator_mem_fixingSubgroup F _ _⟩

omit [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)] in

theorem restrictNormal_restrictHom (g : K.1.fixingSubgroup) :
    ((restrictHom (E := compositum K F) g).restrictScalars ℚ).restrictNormal F.1 =
      (g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 := by
  ext y
  have h1 := AlgEquiv.restrictNormal_commutes
    ((restrictHom (E := compositum K F) g).restrictScalars ℚ) F.1 y
  have h2 := AlgEquiv.restrictNormal_commutes (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) F.1 y
  exact (congrArg Subtype.val h1).trans h2.symm

theorem ideleSymbol_ideleNorm (x : IdeleGroup K.1) :
    ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) =
      ((ideleSymbol K.1 (compositum K F).1 x).restrictScalars ℚ).restrictNormal F.1 :=
  (restrictNormal_restrictScalars_ideleSymbol x).symm

theorem exists_restrictNormal_eq_ideleSymbol (x : IdeleGroup K.1) :
    ∃ g ∈ K.1.fixingSubgroup,
      g.restrictNormal F.1 = ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) := by
  obtain ⟨g, hg⟩ := restrictHom_surjective (F := K) (E := compositum K F)
    (ideleSymbol K.1 (compositum K F).1 x)
  refine ⟨g, g.2, ?_⟩
  rw [ideleSymbol_ideleNorm, ← hg, restrictNormal_restrictHom]

theorem exists_ideleSymbol_eq_restrictNormal {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g ∈ K.1.fixingSubgroup) :
    ∃ x : IdeleGroup K.1, ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) = g.restrictNormal F.1 := by
  obtain ⟨x, hx⟩ := ideleSymbol_surjective (K := K.1) (L := (compositum K F).1)
    (restrictHom (E := compositum K F) ⟨g, hg⟩)
  refine ⟨x, ?_⟩
  rw [ideleSymbol_ideleNorm, hx, restrictNormal_restrictHom]

theorem restrictHom_eq_ideleSymbol (g : K.1.fixingSubgroup) (x : IdeleGroup K.1)
    (h : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 = ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x)) :
    restrictHom (E := compositum K F) g = ideleSymbol K.1 (compositum K F).1 x := by
  obtain ⟨g', hg'⟩ := restrictHom_surjective (F := K) (E := compositum K F)
    (ideleSymbol K.1 (compositum K F).1 x)
  have h' : (g' : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 = (g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 := by
    rw [h, ideleSymbol_ideleNorm, ← hg', restrictNormal_restrictHom]
  rw [← hg', eq_comm, MonoidHom.eq_iff, ker_restrictHom, Subgroup.mem_subgroupOf,
    fixingSubgroup_compositum]
  refine ⟨(g⁻¹ * g' : K.1.fixingSubgroup).2, (mem_fixingSubgroup_iff_restrictNormal_eq_one F _).2 ?_⟩
  change AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1
    ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ * (g' : ℚ̄ ≃ₐ[ℚ] ℚ̄)) = 1
  rw [map_mul, map_inv]
  change ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1)⁻¹ * (g' : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 = 1
  rw [h', inv_mul_cancel]

end CyclotomicSymbol

end

end GroundTheory.Global
end
