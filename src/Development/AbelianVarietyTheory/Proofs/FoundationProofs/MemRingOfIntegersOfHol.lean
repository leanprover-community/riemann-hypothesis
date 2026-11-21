import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionHolomorphic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVectorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTowerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariant

section
section
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ

theorem act_sub_int_of_Gamma (x : Fin 2 → ℚ) (M : ℕ) (hM : 0 < M)
    (hx : ∃ a b : ℤ, x 0 = a / M ∧ x 1 = b / M) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M) :
    ∃ n : Fin 2 → ℤ, act x γ = fun i => x i + n i := by
  obtain ⟨a, b, ha, hb⟩ := hx
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  have d00 : (M : ℤ) ∣ γ 0 0 - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (γ 0 0) M).mp (by rw [Int.cast_one]; exact h00.symm)
  have d11 : (M : ℤ) ∣ γ 1 1 - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (γ 1 1) M).mp (by rw [Int.cast_one]; exact h11.symm)
  have d01 : (M : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
  have d10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  obtain ⟨k00, e00⟩ := d00
  obtain ⟨k11, e11⟩ := d11
  obtain ⟨k01, e01⟩ := d01
  obtain ⟨k10, e10⟩ := d10
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * k00 := by
    rw [show (γ 0 0 : ℤ) = 1 + M * k00 by linarith]; push_cast; ring
  have q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * k11 := by
    rw [show (γ 1 1 : ℤ) = 1 + M * k11 by linarith]; push_cast; ring
  have q01 : ((γ 0 1 : ℤ) : ℚ) = M * k01 := by rw [e01]; push_cast; ring
  have q10 : ((γ 1 0 : ℤ) : ℚ) = M * k10 := by rw [e10]; push_cast; ring
  refine ⟨![a * k00 + b * k10, a * k01 + b * k11], ?_⟩
  funext i
  fin_cases i
  · simp only [act, Fin.sum_univ_two]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [q00, q10, ha, hb]; push_cast; field_simp; ring
  · simp only [act, Fin.sum_univ_two]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
    rw [q01, q11, ha, hb]; push_cast; field_simp; ring

theorem siegel_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ)
    (x : Fin 2 → ℚ) (M : ℕ), admitted c x → 0 < M → (∃ a b : ℤ, x 0 = a / M ∧ x 1 = b / M) →
    ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) (siegel T c x) = siegel T c x := by
  intro Ω _ _ _ ε T c x M hx hM hden γ hγ
  rw [GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε T c x γ hx]
  obtain ⟨n, hn⟩ := act_sub_int_of_Gamma x M hM hden γ hγ
  have hs : sgC c (act x γ) = sgC c x := by
    rw [hn]; funext z; exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x n _ hx
  unfold siegel
  rw [hs]

end GlobalTheory.KZ
end

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_invariant_principal_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (x : Fin 2 → ℚ) (M : ℕ), admitted c x → 0 < M → (∃ a b : ℤ, x 0 = a / M ∧ x 1 = b / M) → ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) (siegel T c x) = siegel T c x := by
  atlas_forward_decl GlobalTheory.KZ.siegel_level
end

section
noncomputable section

open scoped MatrixGroups UpperHalfPlane
open Polynomial

namespace GlobalTheory.K4.TopUnits

open GlobalTheory.KZ GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def holSub (X : Tower Ω ε) : Subring X.K where
  carrier := {f | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an f = (φ : Mero)}
  mul_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ * ψ, h1.mul h3, by rw [map_mul, h2, h4, Filter.Germ.coe_mul]⟩
  one_mem' := ⟨1, differentiableOn_const 1, by rw [map_one, Filter.Germ.coe_one]⟩
  add_mem' := by
    rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
    exact ⟨φ + ψ, h1.add h3, by rw [map_add, h2, h4, Filter.Germ.coe_add]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, by rw [map_zero, Filter.Germ.coe_zero]⟩
  neg_mem' := by
    rintro f ⟨φ, h1, h2⟩
    exact ⟨-φ, h1.neg, by rw [map_neg, h2, Filter.Germ.coe_neg]⟩

theorem finite_conj (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) {f : X.K} (hf : f ∈ topL X M) :
    (Set.range fun γ : SL(2, ℤ) => X.sl (ofSL γ) f).Finite := by
  haveI : NeZero M := ⟨hM⟩
  haveI : (CongruenceSubgroup.Gamma M).FiniteIndex := by
    show (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))).ker.FiniteIndex
    exact Subgroup.finiteIndex_ker _
  refine (Set.finite_range fun q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M => X.sl (ofSL q.out⁻¹) f).subset ?_
  rintro _ ⟨γ, rfl⟩
  obtain ⟨δ, hδ⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma M) γ⁻¹
  refine ⟨QuotientGroup.mk γ⁻¹, ?_⟩
  show X.sl (ofSL _) f = X.sl (ofSL γ) f
  rw [hδ, mul_inv_rev, inv_inv, map_mul, X.sl_mul, (mem_lev_iff X _ f).1 hf _ (inv_mem δ.2)]


theorem siegel_hol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {c : ℕ} {y : Fin 2 → ℚ} (hy : admitted c y) :
    siegel X c y ∈ holSub X ∧ (siegel X c y)⁻¹ ∈ holSub X := by
  have hd : DifferentiableOn ℂ (sgC c y) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c y hy)
  have hne : ∀ z, sgC c y z ≠ 0 := fun z => GlobalTheory.Sieg.sg_ne_zero c y _ hy
  have ha := SiegelMem.an_siegel_eq Ω ε X c y hy
  refine ⟨⟨_, hd, ha⟩, (sgC c y)⁻¹, hd.inv fun z _ => hne z, ?_⟩
  have h1 : X.an (siegel X c y)⁻¹ * X.an (siegel X c y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c y hy), map_one]
  have h2 : X.an (siegel X c y) * (((sgC c y)⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [ha, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_one]
    congr 1
    funext z
    exact mul_inv_cancel₀ (hne z)
  rw [← mul_one (X.an _), ← h2, ← mul_assoc, h1, one_mul]

def IsTopUnit (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  f ≠ 0 ∧ f ∈ topF X M ∧ ∃ hf : f ∈ topL X M,
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    (⟨f, hf⟩ : topL X M) ∈ FunctionField.ringOfIntegers Ω (topL X M) ∧
      (⟨f, hf⟩ : topL X M)⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M)




end GlobalTheory.K4.TopUnits

namespace GlobalTheory.K4

open GlobalTheory.KZ

end GlobalTheory.K4
end
end
