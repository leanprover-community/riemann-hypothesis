module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.HfSelfProj

@[expose] public section

noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)

theorem sum_mulVec' {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι K) (x : ι → K) :
    (∑ c ∈ s, A c) *ᵥ x = ∑ c ∈ s, A c *ᵥ x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, add_mulVec, ih]

theorem vecMul_sum' {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι K) (x : ι → K) :
    x ᵥ* (∑ c ∈ s, A c) = ∑ c ∈ s, x ᵥ* A c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih => rw [Finset.sum_insert hc, Finset.sum_insert hc, vecMul_add, ih]

section Drop

variable {m : ℕ} (i : Fin (m + 1))

def ins (x : Fin m → K) : Fin (m + 1) → K := Fin.insertNth i 0 x

omit S in
theorem ins_same (x : Fin m → K) : ins i x i = 0 := Fin.insertNth_apply_same _ _ _

omit S in
theorem ins_succAbove (x : Fin m → K) (s : Fin m) : ins i x (i.succAbove s) = x s :=
  Fin.insertNth_apply_succAbove _ _ _ _

omit S in
theorem mulVec_ins (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (x : Fin m → K) (s : Fin m) :
    (G *ᵥ ins i x) (i.succAbove s) = (G.submatrix i.succAbove i.succAbove *ᵥ x) s := by
  simp only [mulVec, dotProduct, Fin.sum_univ_succAbove _ i, ins_same, ins_succAbove, mul_zero, zero_add,
    submatrix_apply]

omit S in
theorem vecMul_ins (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (x : Fin m → K) (s : Fin m) :
    (ins i x ᵥ* G) (i.succAbove s) = (x ᵥ* G.submatrix i.succAbove i.succAbove) s := by
  simp only [vecMul, dotProduct, Fin.sum_univ_succAbove _ i, ins_same, ins_succAbove, zero_mul, zero_add,
    submatrix_apply]

theorem cv_ins (x : Fin m → K) : S.cv (ins i x) = ins i (S.cv x) := by
  funext r
  rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨s, rfl⟩
  · simp [cv, ins_same]
  · simp [cv, ins_succAbove]

theorem hf_ins (G : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (x y : Fin m → K) :
    S.hf G (ins i x) (ins i y) = S.hf (G.submatrix i.succAbove i.succAbove) x y := by
  rw [hf, hf, S.cv_ins, dotProduct, dotProduct, Fin.sum_univ_succAbove _ i]
  simp only [ins_same, ins_succAbove, zero_mul, zero_add, mulVec_ins]

theorem IntV_ins {x : Fin m → K} (hx : S.IntV x) : S.IntV (ins i x) := by
  intro r
  rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨s, rfl⟩
  · rw [ins_same]; exact S.O.zero_mem
  · rw [ins_succAbove]; exact hx s

theorem ext_drop {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) K} {a : Fin (m + 1) → K} (ha : a i ≠ 0)
    (hσa : S.σ (a i) ≠ 0) (hM : M *ᵥ a = 0) (hN : N *ᵥ a = 0) (hM' : S.cv a ᵥ* M = 0)
    (hN' : S.cv a ᵥ* N = 0)
    (h : ∀ s t, M (i.succAbove s) (i.succAbove t) = N (i.succAbove s) (i.succAbove t)) : M = N := by
  have hcol : ∀ s, M (i.succAbove s) i = N (i.succAbove s) i := by
    intro s
    have e1 := congrFun hM (i.succAbove s)
    have e2 := congrFun hN (i.succAbove s)
    simp only [mulVec, dotProduct, Fin.sum_univ_succAbove _ i, Pi.zero_apply] at e1 e2
    simp only [h] at e1
    have : (M (i.succAbove s) i - N (i.succAbove s) i) * a i = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' ha
  have hrow : ∀ s j, M (i.succAbove s) j = N (i.succAbove s) j := by
    intro s j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨t, rfl⟩
    · exact hcol s
    · exact h s t
  ext r j
  rcases Fin.eq_self_or_eq_succAbove i r with hr | ⟨s, rfl⟩
  · rw [hr]
    have e1 := congrFun hM' j
    have e2 := congrFun hN' j
    simp only [vecMul, dotProduct, Fin.sum_univ_succAbove _ i, Pi.zero_apply, cv] at e1 e2
    simp only [hrow] at e1
    have : S.σ (a i) * (M i j - N i j) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hσa
    · exact sub_eq_zero.mp h'
  · exact hrow s j

theorem UM_drop {G : Matrix (Fin (m + 1)) (Fin (m + 1)) K} {a : Fin (m + 1) → K} (hU : S.UM G)
    (ha : S.IntV a) (hai : ¬ S.NU (a i)) (hGa : G *ᵥ a = 0) (haG : S.cv a ᵥ* G = 0) :
    S.UM (G.submatrix i.succAbove i.succAbove) := by
  intro x hx hNU
  have hall : ∀ s, S.NU ((G *ᵥ ins i x) (i.succAbove s)) := fun s => by rw [mulVec_ins]; exact hNU s
  have hσO := S.hσO _ (ha i)
  have hσn := S.not_NU_σ (ha i) hai
  have hne : S.σ (a i) ≠ 0 := S.ne_zero_of_not_NU hσn
  have hNU' : ∀ r, S.NU ((G *ᵥ ins i x) r) := by
    intro r
    rcases Fin.eq_self_or_eq_succAbove i r with hr | ⟨s, rfl⟩
    · rw [hr]
      have e := congrArg (fun v => v ⬝ᵥ ins i x) haG
      simp only [zero_dotProduct] at e
      rw [← dotProduct_mulVec, dotProduct, Fin.sum_univ_succAbove _ i] at e
      have e' : S.σ (a i) * (G *ᵥ ins i x) i
          = -(∑ s, S.cv a (i.succAbove s) * (G *ᵥ ins i x) (i.succAbove s)) := by
        simp only [cv] at e ⊢; linear_combination e
      have hv : (G *ᵥ ins i x) i
          = (S.σ (a i))⁻¹ * -(∑ s, S.cv a (i.succAbove s) * (G *ᵥ ins i x) (i.succAbove s)) := by
        rw [← e', ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      rw [hv]
      exact S.NU_mul (S.hinv _ hσO hσn) (S.NU_neg (S.NU_sum _ _ fun s _ =>
        S.NU_mul (S.IntV_cv ha _) (hall s)))
    · exact hall s
  obtain ⟨x', hx', hxx⟩ := hU (ins i x) (S.IntV_ins i hx) hNU'
  have hai0 : a i ≠ 0 := S.ne_zero_of_not_NU hai
  set y := x' - (x' i * (a i)⁻¹) • a with hy_def
  have hyI : S.IntV y := S.IntV_sub hx' (S.IntV_smul (S.O.mul_mem (hx' i) (S.hinv _ (ha i) hai)) ha)
  have hyi : y i = 0 := by
    simp only [hy_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp; ring
  have hGy : G *ᵥ y = G *ᵥ x' := by
    rw [hy_def, mulVec_sub, mulVec_smul, hGa, smul_zero, sub_zero]
  have hins : ins i (fun s => y (i.succAbove s)) = y := by
    funext r
    rcases Fin.eq_self_or_eq_succAbove i r with rfl | ⟨s, rfl⟩
    · rw [ins_same, hyi]
    · rw [ins_succAbove]
  refine ⟨fun s => y (i.succAbove s), fun s => hyI _, ?_⟩
  funext s
  rw [← mulVec_ins, hxx, Pi.smul_apply, Pi.smul_apply, ← mulVec_ins, hins, hGy]

end Drop

end JSetup
end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
