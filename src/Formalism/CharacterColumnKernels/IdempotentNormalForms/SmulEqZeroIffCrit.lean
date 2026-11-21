import Formalism.CharacterColumnKernels.StatCompMultSimple
import Formalism.CharacterColumnKernels.StatementMF
import Formalism.CharacterColumnKernels.IdempotentNormalForms.RightMulEpsAlgebraMap

section
noncomputable section

namespace Formalism.NG

universe u

section LenEpsAux

variable {O OO : Type*} [CommRing O] [Ring OO] [Algebra O OO]

lemma mem_epsImg_iff {M : Type*} [AddCommGroup M] [Module OO M] [Module O M]
    [IsScalarTower O OO M] (ε : OO) (x : M) :
    x ∈ epsImg O (M := M) ε ↔ ∃ y : M, ε • y = x := by
  simp [epsImg]

def epsMap {A B : Type*} [AddCommGroup A] [Module OO A] [Module O A] [IsScalarTower O OO A]
    [AddCommGroup B] [Module OO B] [Module O B] [IsScalarTower O OO B]
    (φ : A →ₗ[OO] B) (ε : OO) : epsImg O (M := A) ε →ₗ[O] epsImg O (M := B) ε :=
  LinearMap.restrict (φ.restrictScalars O) (fun x hx => by
    rw [mem_epsImg_iff] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨φ y, by simp⟩)

@[simp] lemma epsMap_apply {A B : Type*} [AddCommGroup A] [Module OO A] [Module O A]
    [IsScalarTower O OO A]
    [AddCommGroup B] [Module OO B] [Module O B] [IsScalarTower O OO B]
    (φ : A →ₗ[OO] B) (ε : OO) (x : epsImg O (M := A) ε) :
    ((epsMap (O := O) φ ε x : epsImg O (M := B) ε) : B) = φ x := rfl

end LenEpsAux

end Formalism.NG
end
end

section
open Classical

noncomputable section

namespace Formalism.NG

namespace IdempotentCriticalLength

variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]

lemma jac_smul {V : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    {a : Λ} (ha : a ∈ Ring.jacobson Λ) (w : V) : a • w = 0 :=
  Module.mem_annihilator.mp (IsSemisimpleModule.jacobson_le_annihilator (R := Λ) (M := V) ha) w

def Crit (O : Type*) [CommRing O] [IsLocalRing O] [Algebra O Λ] (ε x : Λ) : Prop :=
  ∀ y : Λ, ∀ c : O, ε * (y * x) * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ →
    c ∈ IsLocalRing.maximalIdeal O

lemma smul_eq_zero_iff_crit {V : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    {ε : Λ} (hii : ∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ)
    (hiii : ∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ)
    {v : V} (hv0 : v ≠ 0) (hv : ε • v = v) (x : Λ) :
    x • v = 0 ↔ Crit O ε x := by
  have e2 : ∀ c : O, (algebraMap O Λ c * ε) • v = algebraMap O Λ c • v := by
    intro c; rw [mul_smul, hv]
  constructor
  · intro hx y c hc
    have h1 := jac_smul hc v
    have e1 : (ε * (y * x) * ε) • v = 0 := by
      rw [mul_smul, hv, mul_smul, mul_smul, hx, smul_zero, smul_zero]
    rw [sub_smul, e1, e2, zero_sub, neg_eq_zero] at h1
    by_contra hcm
    have hu : IsUnit c := by
      by_contra hu'
      exact hcm hu'
    exact hv0 (((hu.map (algebraMap O Λ)).smul_eq_zero).mp h1)
  · intro hc
    by_contra hx
    obtain ⟨y, hy⟩ := (IsSimpleModule.toSpanSingleton_surjective Λ hx) v
    rw [LinearMap.toSpanSingleton_apply] at hy
    obtain ⟨c, hc'⟩ := hii (y * x)
    have h1 := jac_smul hc' v
    have e1 : (ε * (y * x) * ε) • v = v := by
      rw [mul_smul, hv, mul_smul, mul_smul, hy, hv]
    rw [sub_smul, e1, e2, sub_eq_zero, jac_smul (hiii c (hc y c hc')) v] at h1
    exact hv0 h1

lemma nonempty_equiv {V W : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    [AddCommGroup W] [Module Λ W] [IsSimpleModule Λ W] {ε : Λ} (hε : IsIdempotentElem ε)
    (hii : ∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ)
    (hiii : ∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ)
    (hV : ∃ t : V, ε • t ≠ 0) (hW : ∃ s : W, ε • s ≠ 0) : Nonempty (V ≃ₗ[Λ] W) := by
  obtain ⟨t, ht⟩ := hV
  obtain ⟨s, hs⟩ := hW
  have hv : ε • (ε • t) = ε • t := by rw [← mul_smul, hε.eq]
  have hu : ε • (ε • s) = ε • s := by rw [← mul_smul, hε.eq]
  have hker : LinearMap.ker (LinearMap.toSpanSingleton Λ V (ε • t)) =
      LinearMap.ker (LinearMap.toSpanSingleton Λ W (ε • s)) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    rw [smul_eq_zero_iff_crit hii hiii ht hv, smul_eq_zero_iff_crit hii hiii hs hu]
  exact ⟨(LinearMap.quotKerEquivOfSurjective _
      (IsSimpleModule.toSpanSingleton_surjective Λ ht)).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective _ (IsSimpleModule.toSpanSingleton_surjective Λ hs)))⟩

end IdempotentCriticalLength

namespace IdempotentCriticalLengthFinite

variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]

end IdempotentCriticalLengthFinite

end Formalism.NG
end
end
