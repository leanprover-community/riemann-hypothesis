import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement

section
namespace GlobalTheory.UnitaryCharpolyRootNorm

open Matrix NumberField

theorem norm_root_of_unitary {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (hA : Aᴴ * A = 1) (z : ℂ)
    (hz : A.charpoly.IsRoot z) : ‖z‖ = 1 := by
  have hdet : (Matrix.scalar m z - A).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hz
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv : A *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.mulVec_diagonal]
  have h1 : star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  rw [hAv, star_smul, smul_dotProduct, dotProduct_smul, smul_smul] at h1
  have hne : star v ⬝ᵥ v ≠ 0 := by
    open scoped ComplexOrder in
    exact fun h => hv0 (dotProduct_star_self_eq_zero.mp h)
  have h2 : star z * z = 1 := by
    apply mul_right_cancel₀ hne
    rw [one_mul]; exact h1
  have h3 : ‖z‖ * ‖z‖ = 1 := by
    have := congrArg norm h2
    rwa [norm_mul, norm_star, norm_one] at this
  nlinarith [norm_nonneg z]

theorem norm_root_charpoly {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : GlobalTheory.BCT.UE E n)
    (τ : E →+* ℂ) :
    ∀ z ∈ (Polynomial.map τ (Matrix.charpoly ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))).roots,
      ‖z‖ = (1 : ℝ) := by
  intro z hz
  set g : Matrix (Fin n) (Fin n) E := ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hg
  have h : (Matrix.of fun i j => IsCMField.complexConj E (g j i)) * 1 * g = 1 := γ.2
  rw [mul_one] at h
  have hA : (g.map τ)ᴴ * g.map τ = 1 := by
    have e : (g.map τ)ᴴ = (Matrix.of fun i j => IsCMField.complexConj E (g j i)).map τ := by
      ext i j
      simp [IsCMField.complexEmbedding_complexConj]
    rw [e, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero τ) (map_one τ)]
  apply norm_root_of_unitary _ hA
  rw [Matrix.charpoly_map]
  exact Polynomial.isRoot_of_mem_roots hz

end GlobalTheory.UnitaryCharpolyRootNorm
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocRatPt

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_mem_UL (hU : Unr E) (w : Pl E) (γ : UE E n) :
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
    have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    change cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) * 1 *
      (γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) = 1
    have key : cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E)).map
          (algebraMap E (w.adicCompletion E)) := by
      exact Matrix.ext fun i j => hc _
    rw [key, Matrix.mul_one, ← Matrix.map_mul]
    rw [Matrix.mul_one] at hγ
    rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locPt_val (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  rw [locPt, toSub, dif_pos (map_mem_UL hU w γ)]

theorem eventually_valuation_le_one (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), w.valuation E x ≤ 1 := by
  rw [Filter.eventually_cofinite]
  refine (HeightOneSpectrum.Support.finite (𝓞 E) x).subset fun w hw => ?_
  exact lt_of_not_ge hw

theorem algebraMap_mem_Ov {w : Pl E} {x : E} (h : w.valuation E x ≤ 1) :
    algebraMap E (w.adicCompletion E) x ∈ Ov E w := by
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [show Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  exact h

theorem mem_GLint_of_entries {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O)
    (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem eventually_mem_KL (hU : Unr E) (γ : UE E n) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w := by
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E ((γ.1 : GL (Fin n) E).1 i j) ≤ 1 ∧
      w.valuation E (((γ.1 : GL (Fin n) E)⁻¹).1 i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    intro i j
    exact (eventually_valuation_le_one _).and (eventually_valuation_le_one _)
  filter_upwards [h1] with w hw
  rw [KL, Subgroup.mem_subgroupOf, locPt_val hU]
  refine mem_GLint_of_entries (fun i j => algebraMap_mem_Ov (hw i j).1) (fun i j => ?_)
  rw [← map_inv]
  exact algebraMap_mem_Ov (hw i j).2

theorem norm_eq_one_of_root (γ : UE E n) (τ : E →+* ℂ) (z : ℂ)
    (hz : z ∈ ((γ.1 : GL (Fin n) E).val.charpoly.map τ).roots) : ‖z‖ = 1 := by
  first
  | (rename_i h_1 h_2 h_3; revert E h_1 h_2 h_3 n γ τ z hz; exact @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly)
  | exact @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly
  | exact _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly
  | (apply _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly ..)

theorem charpoly_mem_Ell (γ : UE E n) (hs : (γ.1 : GL (Fin n) E).val.charpoly.Separable) :
    (γ.1 : GL (Fin n) E).val.charpoly ∈ Ell E n :=
  ⟨Matrix.charpoly_monic _, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], hs,
    fun τ z hz => norm_eq_one_of_root γ τ z hz⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : UE E n), (∀ w : Pl E, (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1) ∧ (∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w) ∧ (γ.1.val.charpoly.Separable → γ.1.val.charpoly ∈ Ell E n) := by
  intro E _ _ _ hU n γ
  exact ⟨fun w => locPt_val hU w γ, eventually_mem_KL hU γ, charpoly_mem_Ell γ⟩

end GlobalTheory.LocRatPt
end
end
