import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.Model

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

open NumberField in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.Model.mem_sumLat (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam))
    (u : Fin N → K) : u ∈ _root_.GlobalTheory.TestLat.sumLat lam e T ↔
      ∀ c, _root_.GlobalTheory.TestLat.valAt lam e c u ∈ T c := by
  simp only [_root_.GlobalTheory.TestLat.sumLat, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

omit [NumberField K] in
theorem valAt_apply (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (c : C) (u : Fin N → K) :
    valAt lam e c u = ∑ i, u (e.symm (c, i)) • bVV K lam i := by
  simp [valAt, Module.Basis.equivFun_symm_apply, LinearMap.funLeft_apply]

open NumberField in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
omit [NumberField K] in

theorem _root_.GlobalTheory.TestLat.Model.valAt_bijective (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) :
    Function.Bijective fun (u : Fin N → K) (c : C) => _root_.GlobalTheory.TestLat.valAt lam e c u := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun f a => (_root_.Formalism.L2.DIV.bVV K lam).equivFun (f (e a).1) (e a).2, fun u => ?_, fun f => ?_⟩
  · ext a
    simp only [_root_.GlobalTheory.TestLat.valAt, LinearMap.comp_apply, LinearMap.funLeft_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]
  · ext c
    simp [_root_.GlobalTheory.TestLat.valAt, LinearMap.funLeft_apply]

open NumberField in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
omit [NumberField K] in

theorem _root_.GlobalTheory.TestLat.Model.sumGram_form [StarRing K] [Fintype C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (G : ι → Matrix (Fin n) (Fin n) K) (u w : Fin N → K) :
    star u ⬝ᵥ (_root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ w) =
      ∑ c, _root_.Formalism.L2.DIV.pairK lam G (_root_.GlobalTheory.TestLat.valAt lam e c u)
        (_root_.GlobalTheory.TestLat.valAt lam e c w) := by
  classical
  simp only [dotProduct, Matrix.mulVec, _root_.GlobalTheory.TestLat.sumGram, Matrix.of_apply, Pi.star_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [_root_.GlobalTheory.TestLat.valAt, LinearMap.comp_apply, LinearMap.funLeft_apply,
    LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos rfl]
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring




omit [NumberField K] in
theorem isDefGram_one [StarRing K] : IsDefGram (1 : Matrix (Fin n) (Fin n) K) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro a b
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro φ
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.PosDef.one

def stdLat (K : Type) [Field K] [NumberField K] (n : ℕ) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))

theorem mem_stdLat (x : Fin n → K) : x ∈ stdLat K n ↔ ∀ a, x a ∈ (algebraMap (𝓞 K) K).range := by
  rw [stdLat, Module.Basis.mem_span_iff_repr_mem]
  simp

theorem isLattice_stdLat : Submodule.IsLattice K (stdLat K n) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [stdLat, Submodule.span_span_of_tower]
    exact (Pi.basisFun K (Fin n)).span_eq

theorem map_mem_range (σ : K →+* K) {x : K} (hx : x ∈ (algebraMap (𝓞 K) K).range) :
    σ x ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨σ y, (RingOfIntegers.isIntegral_coe y).map σ.toIntAlgHom⟩, rfl⟩




def wOne : DomWeight 2 := ⟨![1, 0], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩



end GlobalTheory.TestLat.Model
