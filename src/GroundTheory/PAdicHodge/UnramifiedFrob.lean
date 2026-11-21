import Mathlib
import GroundTheory.PAdicHodge.BCrisNewton

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Polynomial TensorProduct

section Lifts

variable {R E : Type*} [Field R] [Field E]


end Lifts

section Disjoint

variable {K₀ C E : Type*} [Field K₀] [Field C] [Field E] [Algebra K₀ C] [Algebra K₀ E]
  (j : C →ₐ[K₀] E) (F : IntermediateField K₀ E) (M N : IntermediateField K₀ C)
  (L : Type*) [Field L] [Algebra K₀ L] [Algebra L C] [IsScalarTower K₀ L C]




end Disjoint

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

section MaxUnramified

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

instance algebraMaxUnramified : Algebra (maxUnramified p K) K :=
  (IntermediateField.inclusion (inf_le_left : maxUnramified p K ≤ K)).toRingHom.toAlgebra


instance isScalarTower_maxUnramified_algCl :
    IsScalarTower (maxUnramified p K) K (PadicAlgCl p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_padic_maxUnramified :
    IsScalarTower ℚ_[p] (maxUnramified p K) K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance finiteDimensional_maxUnramified [FiniteDimensional ℚ_[p] K] :
    FiniteDimensional (maxUnramified p K) K :=
  Module.Finite.of_restrictScalars_finite ℚ_[p] (maxUnramified p K) K

def unramifiedOver : IntermediateField (maxUnramified p K) (PadicAlgCl p) :=
  IntermediateField.extendScalars (inf_le_right : maxUnramified p K ≤ unramifiedClosure p)


instance isAlgClosure_maxUnramified : IsAlgClosure (maxUnramified p K) (PadicAlgCl p) :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) (maxUnramified p K)⟩

instance normal_unramifiedOver : Normal (maxUnramified p K) (unramifiedOver K) := by
  refine IntermediateField.normal_iff_forall_map_le'.2 fun σ x hx => ?_
  obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
  exact gal_mem_unramifiedClosure (σ.restrictScalars ℚ_[p]) hy



end MaxUnramified

namespace ACris

open scoped TensorProduct

section Tensor

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def unramifiedToBCrisPlus : unramifiedClosure p →ₐ[ℚ_[p]] BCrisPlus ℂ_[p] p :=
  ((AlgEquiv.ofInjective (iotaPlusAlg (p := p))
      fun _ _ h => iotaPlus_injective (K := ℂ_[p]) (p := p) h).symm :
      (iotaPlusAlg (p := p)).range →ₐ[ℚ_[p]] BCrisPlus ℂ_[p] p).comp
    (((algClToBdR p).comp (unramifiedClosure p).val).codRestrict _ fun u => unramifiedClosure_le u.2)

theorem iotaPlus_unramifiedToBCrisPlus (u : unramifiedClosure p) :
    iotaPlus ℂ_[p] p (unramifiedToBCrisPlus u) = algClToBdR p u :=
  congrArg Subtype.val ((AlgEquiv.ofInjective (iotaPlusAlg (p := p)) fun _ _ h =>
    iotaPlus_injective (K := ℂ_[p]) (p := p) h).apply_symm_apply
      ⟨algClToBdR p u, unramifiedClosure_le u.2⟩)

instance algebraMaxUnramifiedBCrisPlus : Algebra (maxUnramified p K) (BCrisPlus ℂ_[p] p) :=
  (unramifiedToBCrisPlus.comp (IntermediateField.inclusion
    (inf_le_right : maxUnramified p K ≤ unramifiedClosure p))).toRingHom.toAlgebra

instance moduleMaxUnramifiedBCrisPlus : Module (maxUnramified p K) (BCrisPlus ℂ_[p] p) :=
  Algebra.toModule

theorem iotaPlus_algebraMap_maxUnramified (k : maxUnramified p K) :
    iotaPlus ℂ_[p] p (algebraMap (maxUnramified p K) (BCrisPlus ℂ_[p] p) k) = algClToBdR p k :=
  iotaPlus_unramifiedToBCrisPlus _

instance algebraMaxUnramifiedBdRPlus : Algebra (maxUnramified p K) 𝔹 :=
  ((algClToBdR p).comp (maxUnramified p K).val).toRingHom.toAlgebra

def algToBdRPlus : K →ₐ[maxUnramified p K] 𝔹 :=
  { (algClToBdR p).toRingHom.comp (algebraMap K (PadicAlgCl p)) with commutes' := fun _ => rfl }

def iotaPlusMaxUnramified : BCrisPlus ℂ_[p] p →ₐ[maxUnramified p K] 𝔹 :=
  { iotaPlus ℂ_[p] p with commutes' := iotaPlus_algebraMap_maxUnramified K }

def tensorBCrisPlusToBdRPlus :
    K ⊗[maxUnramified p K] BCrisPlus ℂ_[p] p →ₐ[maxUnramified p K] 𝔹 :=
  Algebra.TensorProduct.lift (algToBdRPlus K) (iotaPlusMaxUnramified K) fun _ _ => Commute.all _ _


def algClToBdRFieldMaxUnramified : PadicAlgCl p →ₐ[maxUnramified p K] 𝔹dR :=
  { algClToBdRField p with commutes' := fun _ => rfl }

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

def iotaBMaxUnramified : BCris hε →ₐ[maxUnramified p K] 𝔹dR :=
  { iotaB hε hζ with
    commutes' := fun k => by
      change iotaB hε hζ (algebraMap (maxUnramified p K) (BCris hε) k) = _
      rw [IsScalarTower.algebraMap_apply (maxUnramified p K) (BCrisPlus ℂ_[p] p) (BCris hε),
        iotaB_algebraMap, iotaPlus_algebraMap_maxUnramified]
      rfl }

def tensorBCrisToBdR : K ⊗[maxUnramified p K] BCris hε →ₐ[maxUnramified p K] 𝔹dR :=
  Algebra.TensorProduct.lift ((algClToBdRFieldMaxUnramified K).comp
    (IsScalarTower.toAlgHom (maxUnramified p K) K (PadicAlgCl p))) (iotaBMaxUnramified K hε hζ)
    fun _ _ => Commute.all _ _


def fracBCrisOver : IntermediateField (maxUnramified p K) 𝔹dR :=
  (fracBCris hε hζ).toIntermediateField fun k => (mem_fracBCris_of_mem_maxUnramified hε hζ k.2).1

def tensorFracBCrisToBdR :
    K ⊗[maxUnramified p K] fracBCrisOver K hε hζ →ₐ[maxUnramified p K] 𝔹dR :=
  Algebra.TensorProduct.lift ((algClToBdRFieldMaxUnramified K).comp
    (IsScalarTower.toAlgHom (maxUnramified p K) K (PadicAlgCl p))) (fracBCrisOver K hε hζ).val
    fun _ _ => Commute.all _ _


variable [FiniteDimensional ℚ_[p] K]



end Tensor

end ACris

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

local notation "K₀" => maxUnramified p K

theorem gal_smul_algebraMap_maxUnramified (σ : Gal(PadicAlgCl p/K)) (k : K₀) :
    σ • algebraMap K₀ (BCrisPlus ℂ_[p] p) k = algebraMap K₀ (BCrisPlus ℂ_[p] p) k := by
  apply iotaPlus_injective (K := ℂ_[p]) (p := p)
  rw [iotaPlus_gal_smul, iotaPlus_algebraMap_maxUnramified, gal_smul_algClToBdR]
  congr 1
  exact σ.commutes ⟨(k : PadicAlgCl p), (mem_maxUnramified.1 k.2).1⟩

theorem algebraMap_maxUnramified_padic (q : ℚ_[p]) :
    algebraMap K₀ (BCrisPlus ℂ_[p] p) (algebraMap ℚ_[p] K₀ q) =
      algebraMap ℚ_[p] (BCrisPlus ℂ_[p] p) q := by
  apply iotaPlus_injective (K := ℂ_[p]) (p := p)
  rw [iotaPlus_algebraMap_maxUnramified, iotaPlus_algebraMap_padic, IntermediateField.coe_algebraMap_apply,
    AlgHom.commutes]

theorem algebraMap_maxUnramified_injective :
    Function.Injective (algebraMap K₀ (BCrisPlus ℂ_[p] p)) := by
  intro a b h
  have h' := congrArg (iotaPlus ℂ_[p] p) h
  rw [iotaPlus_algebraMap_maxUnramified, iotaPlus_algebraMap_maxUnramified] at h'
  exact Subtype.ext ((algClToBdR p).injective h')

section Frob

variable [FiniteDimensional ℚ_[p] K]

instance finiteDimensional_padic_maxUnramified : FiniteDimensional ℚ_[p] K₀ :=
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : maxUnramified p K ≤ K)).toLinearMap
    (IntermediateField.inclusion (inf_le_left : maxUnramified p K ≤ K)).injective

theorem exists_phiPlus_algebraMap_maxUnramified (k : K₀) :
    ∃ k' : K₀, phiPlus ℂ_[p] p (algebraMap K₀ (BCrisPlus ℂ_[p] p) k) =
      algebraMap K₀ (BCrisPlus ℂ_[p] p) k' := by
  obtain ⟨k₁, hk₁, h⟩ := bCrisPlus_fixed (K := K) (phiPlus ℂ_[p] p (algebraMap K₀ _ k)) fun σ => by
    rw [← phiPlus_gal_smul, gal_smul_algebraMap_maxUnramified]
  refine ⟨⟨k₁, hk₁⟩, iotaPlus_injective (K := ℂ_[p]) (p := p) ?_⟩
  rw [h, iotaPlus_algebraMap_maxUnramified]

def maxUnramifiedFrobeniusFun (k : K₀) : K₀ := (exists_phiPlus_algebraMap_maxUnramified K k).choose

theorem phiPlus_algebraMap_maxUnramifiedFrobeniusFun (k : K₀) :
    phiPlus ℂ_[p] p (algebraMap K₀ (BCrisPlus ℂ_[p] p) k) =
      algebraMap K₀ (BCrisPlus ℂ_[p] p) (maxUnramifiedFrobeniusFun K k) :=
  (exists_phiPlus_algebraMap_maxUnramified K k).choose_spec

def maxUnramifiedFrobeniusHom : K₀ →ₐ[ℚ_[p]] K₀ where
  toFun := maxUnramifiedFrobeniusFun K
  map_one' := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun]; simp only [map_one])
  map_mul' a b := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun, map_mul, map_mul, map_mul, phiPlus_algebraMap_maxUnramifiedFrobeniusFun,
      phiPlus_algebraMap_maxUnramifiedFrobeniusFun])
  map_zero' := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun]; simp only [map_zero])
  map_add' a b := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun, map_add, map_add, map_add, phiPlus_algebraMap_maxUnramifiedFrobeniusFun,
      phiPlus_algebraMap_maxUnramifiedFrobeniusFun])
  commutes' q := algebraMap_maxUnramified_injective K (by
    rw [← phiPlus_algebraMap_maxUnramifiedFrobeniusFun, algebraMap_maxUnramified_padic, phiPlus_algebraMap_padic])

def maxUnramifiedFrobenius : K₀ ≃ₐ[ℚ_[p]] K₀ :=
  AlgEquiv.ofBijective (maxUnramifiedFrobeniusHom K) (maxUnramifiedFrobeniusHom K).bijective



end Frob

section Valuation

variable {K}

theorem exists_norm_eq_zpow_maxUnramified {x : K₀} (hx : x ≠ 0) :
    ∃ D : ℤ, ‖(x : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ D :=
  (isACrisFraction_of_mem (mem_maxUnramified.1 x.2).2).exists_norm_eq_zpow
    (by simpa using hx)

theorem norm_p_algCl_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)

theorem zpow_norm_p_injective : Function.Injective fun D : ℤ => ‖(p : PadicAlgCl p)‖ ^ D :=
  zpow_right_injective₀ norm_p_algCl_pos (norm_p_algCl_lt_one (p := p)).ne

open Classical in

def maxUnramifiedValFun (x : K₀) : WithTop ℤ :=
  if hx : x = 0 then ⊤ else ((exists_norm_eq_zpow_maxUnramified hx).choose : ℤ)

theorem maxUnramifiedValFun_zero : maxUnramifiedValFun (0 : K₀) = ⊤ := by
  classical
  rw [maxUnramifiedValFun, dif_pos rfl]

theorem maxUnramifiedValFun_eq {x : K₀} (hx : x ≠ 0) {D : ℤ} (h : ‖(x : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ D) :
    maxUnramifiedValFun x = D := by
  classical
  rw [maxUnramifiedValFun, dif_neg hx]
  congr 1
  exact zpow_norm_p_injective ((exists_norm_eq_zpow_maxUnramified hx).choose_spec.symm.trans h)

theorem maxUnramifiedValFun_add_le (x y : K₀) : min (maxUnramifiedValFun x) (maxUnramifiedValFun y) ≤ maxUnramifiedValFun (x + y) := by
  by_cases hx : x = 0
  · rw [hx, zero_add, maxUnramifiedValFun_zero]; exact min_le_right _ _
  by_cases hy : y = 0
  · rw [hy, add_zero, maxUnramifiedValFun_zero]; exact min_le_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, maxUnramifiedValFun_zero]; exact le_top
  obtain ⟨D, hD⟩ := exists_norm_eq_zpow_maxUnramified hx
  obtain ⟨E, hE⟩ := exists_norm_eq_zpow_maxUnramified hy
  obtain ⟨F, hF⟩ := exists_norm_eq_zpow_maxUnramified hxy
  rw [maxUnramifiedValFun_eq hx hD, maxUnramifiedValFun_eq hy hE, maxUnramifiedValFun_eq hxy hF, ← WithTop.coe_min, WithTop.coe_le_coe]
  have h := IsUltrametricDist.norm_add_le_max (x : PadicAlgCl p) (y : PadicAlgCl p)
  rw [← IntermediateField.coe_add, hF, hD, hE] at h
  have hp0 := norm_p_algCl_pos (p := p)
  have hp1 := norm_p_algCl_lt_one (p := p)
  rcases le_total D E with hDE | hDE
  · rw [min_eq_left hDE]
    rw [max_eq_left ((zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).2 hDE)] at h
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).1 h
  · rw [min_eq_right hDE]
    rw [max_eq_right ((zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).2 hDE)] at h
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hp0 hp1).1 h

theorem maxUnramifiedValFun_mul (x y : K₀) : maxUnramifiedValFun (x * y) = maxUnramifiedValFun x + maxUnramifiedValFun y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, maxUnramifiedValFun_zero, WithTop.top_add]
  by_cases hy : y = 0
  · rw [hy, mul_zero, maxUnramifiedValFun_zero, WithTop.add_top]
  obtain ⟨D, hD⟩ := exists_norm_eq_zpow_maxUnramified hx
  obtain ⟨E, hE⟩ := exists_norm_eq_zpow_maxUnramified hy
  rw [maxUnramifiedValFun_eq hx hD, maxUnramifiedValFun_eq hy hE, maxUnramifiedValFun_eq (mul_ne_zero hx hy) (D := D + E), ← WithTop.coe_add]
  rw [IntermediateField.coe_mul, norm_mul, hD, hE, zpow_add₀ norm_p_algCl_pos.ne']

theorem maxUnramifiedValFun_one : maxUnramifiedValFun (1 : K₀) = 0 :=
  maxUnramifiedValFun_eq (one_ne_zero : (1 : K₀) ≠ 0) (D := 0) (by simp)

variable (K) in

def maxUnramifiedValuation : AddValuation K₀ (WithTop ℤ) :=
  AddValuation.of maxUnramifiedValFun maxUnramifiedValFun_zero maxUnramifiedValFun_one maxUnramifiedValFun_add_le maxUnramifiedValFun_mul





end Valuation

section FrobValuation

variable [FiniteDimensional ℚ_[p] K]



end FrobValuation

end ACris

end GroundTheory.PAdicHodge
end
end
