import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CircleAsphGNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb

noncomputable section
namespace GlobalTheory.KS
namespace Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.EtC GlobalTheory.UPel.HT
open scoped TensorProduct

variable {S : Scheme.{0}} {O : Type} [Ring O]

theorem act_zero {A : Over S} [GrpObj A] (act : OActN O A) : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have : act.act 0 * act.act 0 = act.act 0 * 1 := h.symm.trans (_root_.mul_one _).symm
  exact mul_left_cancel this

theorem matEnd_one {A : Over S} [GrpObj A] (act : OActN O A) (m : ℕ) :
    matEnd act (1 : Matrix (Fin m) (Fin m) O) = 𝟙 _ := by
  classical
  unfold matEnd
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Pi.lift_π, Category.id_comp, List.ofFn_eq_map]
  rw [List.prod_map_eq_pow_single i]
  · rw [List.count_finRange, pow_one, Matrix.one_apply_eq, act.one, Category.comp_id]
  · intro j hj _
    rw [Matrix.one_apply_ne' hj, act_zero, comp_one]

theorem matBC_one {A : Over S} [GrpObj A] (act : OActN O A) {B B' : Scheme.{0}} (p : S ⟶ B) (b : B' ⟶ B) (m : ℕ) :
    matBC act p b (1 : Matrix (Fin m) (Fin m) O) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [matBC, matEnd_one]



theorem pts_comm {A : Over S} [GrpObj A] (act : OActN O A) {T : Over S} (x y : T ⟶ A) : x * y = y * x := by
  have hh := act.hom (1 + 1)
  have h2 : ∀ z : T ⟶ A, z ≫ act.act (1 + 1) = z * z := fun z => by
    rw [act.add, act.one, comp_mul, Category.comp_id]
  have h : (x * y) ≫ act.act (1 + 1) = (x ≫ act.act (1 + 1)) * (y ≫ act.act (1 + 1)) := mul_comp _ _ _
  rw [h2, h2, h2] at h
  have h' : x * (y * x) * y = x * (x * y) * y := by simpa [_root_.mul_assoc] using h
  exact (mul_left_cancel (mul_right_cancel h')).symm

theorem comp_matEnd_pr {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) {T : Over S}
    (x : T ⟶ pow A m) (i : Fin m) :
    x ≫ matEnd act M ≫ pr A i = (List.ofFn fun j => (x ≫ pr A j) ≫ act.act (M i j)).prod := by
  unfold matEnd
  rw [Pi.lift_π]
  let φ : (pow A m ⟶ A) →* (T ⟶ A) := { toFun := fun g => x ≫ g, map_one' := comp_one _, map_mul' := fun _ _ => comp_mul _ _ _ }
  change φ _ = _
  rw [map_list_prod, List.map_ofFn]
  congr 2
  all_goals (funext j; simp [φ])

theorem matEnd_mul {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ} (M N : Matrix (Fin m) (Fin m) O) :
    matEnd act (M * N) = matEnd act N ≫ matEnd act M := by
  letI : CommGroup (pow A m ⟶ A) := { (inferInstance : Group (pow A m ⟶ A)) with mul_comm := pts_comm act }
  refine Pi.hom_ext _ _ fun i => ?_
  have h1 := comp_matEnd_pr act (M * N) (𝟙 _) i
  have h2 := comp_matEnd_pr act M (matEnd act N) i
  have h3 := fun j => comp_matEnd_pr act N (𝟙 _) j
  simp only [Category.id_comp] at h1 h3
  rw [Category.assoc]
  refine h1.trans (Eq.trans ?_ h2.symm)
  simp only [h3, List.prod_ofFn]
  have hψ : ∀ (b : O) (g : Fin m → (pow A m ⟶ A)), (∏ k, g k) ≫ act.act b = ∏ k, g k ≫ act.act b := fun b g => by
    have := act.hom b
    let ψ : (pow A m ⟶ A) →* (pow A m ⟶ A) :=
      { toFun := fun g => g ≫ act.act b, map_one' := one_comp _, map_mul' := fun _ _ => mul_comp _ _ _ }
    exact map_prod ψ g Finset.univ
  have hχ : ∀ (z : pow A m ⟶ A) (c : Fin m → O), z ≫ act.act (∑ j, c j) = ∏ j, z ≫ act.act (c j) := fun z c => by
    let χ : Multiplicative O →* (pow A m ⟶ A) :=
      { toFun := fun b => z ≫ act.act b.toAdd
        map_one' := by change z ≫ act.act 0 = 1; rw [act_zero, comp_one]
        map_mul' := fun a b => by change z ≫ act.act (a.toAdd + b.toAdd) = _; rw [act.add, comp_mul] }
    exact map_prod χ (fun j => Multiplicative.ofAdd (c j)) Finset.univ
  simp only [hψ, Matrix.mul_apply, hχ, act.mul, Category.assoc]
  exact Finset.prod_comm


variable (l : ℕ) [Fact l.Prime] {E : Type} [CommRing E] [Algebra ℚ_[l] E]







section Gal
variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]






end Gal

theorem powMap_pr {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) : powMap f φ h m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_π]
  rfl

theorem powMap_over {S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) : powMap f φ h m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _


def intAct (A : Over S) [GrpObj A] [IsCommMonObj A] : OActN ℤ A where
  act n := 𝟙 A ^ n
  hom n := by
    have hn : ∀ j : ℕ, IsMonHom (𝟙 A ^ j) := fun j => by
      induction j with
      | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
      | succ j ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift (𝟙 A ^ j) (𝟙 A) ≫ μ[A]))
    obtain ⟨j, rfl | rfl⟩ := n.eq_nat_or_neg
    · rw [zpow_natCast]; exact hn j
    · rw [zpow_neg, zpow_natCast]
      have := hn j
      exact inferInstanceAs (IsMonHom ((𝟙 A ^ j) ≫ ι[A]))
  one := zpow_one _
  mul b c := by
    let φ : (A ⟶ A) →* (A ⟶ A) :=
      { toFun := fun g => (𝟙 A ^ c) ≫ g, map_one' := comp_one _, map_mul' := fun _ _ => comp_mul _ _ _ }
    change _ = φ _
    rw [map_zpow, mul_comm b c, zpow_mul]
    simp [φ]
  add b c := zpow_add _ _ _


end Model
end GlobalTheory.KS
