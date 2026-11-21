import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplitStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TensorAmple

open GlobalTheory.CechPic GlobalTheory.HermTensorLB

theorem exists_leftInverse {O : Type} [CommRing O] (bar : O →+* O) {M : Type} [AddCommGroup M] [Module O M]
    (h : M → M → O) (hadd : ∀ m m' n, h (m + m') n = h m n + h m' n)
    (hsmul : ∀ (c : O) m n, h (c • m) n = c * h m n) (hsym : ∀ m n, h n m = bar (h m n))
    (hperf : ∀ l : M →ₗ[O] O, ∃! n, ∀ m, l m = h m n) {n k : ℕ} (l : Fin k → (M →ₗ[O] O))
    (hl : ∀ m m', (n : O) * h m m' = ∑ i, l i m * bar (l i m')) :
    ∃ r : (Fin k → O) →ₗ[O] M, ∀ m, r (LinearMap.pi l m) = n • m := by
  choose e he using fun i => (hperf (l i)).exists
  let f : M → (M →ₗ[O] O) := fun y =>
    { toFun := fun x => h x y, map_add' := fun a b => hadd a b y, map_smul' := fun c a => hsmul c a y }
  refine ⟨Fintype.linearCombination O e, fun m => ?_⟩
  refine (hperf (f (n • m))).unique (fun x => ?_) (fun x => rfl)
  change h x (n • m) = h x _
  rw [hsym (n • m), hsym (Fintype.linearCombination O e _), Fintype.linearCombination_apply]
  change bar (f x (n • m)) = bar (f x _)
  rw [map_sum, map_nsmul, map_sum, map_nsmul]
  change n • bar (h m x) = ∑ i, bar (h (l i m • e i) x)
  simp only [hsmul, map_mul, ← hsym, ← he]
  rw [nsmul_eq_mul, hl]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem lam_self (laws : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) {T : Over S}
    (x : T ⟶ P.A) : lam (cls P.L P.isLB) x x = 2 • pull x.left (cls P.L P.isLB) := by
  have h₂ := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 (laws.mulPull S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h₂
  have h₀ : pull (eSec P.A) (cls P.L P.isLB) = 0 := (cls_eq_zero_iff (pull_isLB P.isLB _)).2 P.rigid
  have h₁ : pull (1 : T ⟶ P.A).left (cls P.L P.isLB) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    exact (congrArg _ h₀).trans (map_zero _)
  have h₃ := congrArg (pull x.left) h₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_zsmul, ← pull_comp, Category.comp_id,
    ← Over.comp_left, Out.mulA, MonObj.comp_pow, map_zero, pow_two, MonObj.comp_mul] at h₃
  rw [lam, h₁, add_zero, ← sub_eq_zero, ← neg_eq_zero, ← h₃]
  push_cast
  abel


end GlobalTheory.TensorAmple
