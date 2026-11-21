import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLinearEquivAddHaarLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadExtTopology

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp

def twoSidedMulLin {E : Type} [Field E] {α ν : Type} [Fintype α] [Fintype ν]
    (u : Matrix α α E) (a : Matrix ν ν E) : Matrix α ν E →ₗ[E] Matrix α ν E where
  toFun x := u * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem det_twoSidedMulLin {E : Type} [Field E] {α ν : Type} [Fintype α] [DecidableEq α]
    [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) :
    LinearMap.det (twoSidedMulLin u a) = u.det ^ Fintype.card ν * a.det ^ Fintype.card α := by
  let e : (α × ν → E) ≃ₗ[E] Matrix α ν E := LinearEquiv.curry E E α ν
  have h : twoSidedMulLin u a =
      (e : _ →ₗ[E] _) ∘ₗ (Matrix.toLin' (Matrix.kroneckerMap (· * ·) u a.transpose)) ∘ₗ
        (e.symm : _ →ₗ[E] _) := by
    refine LinearMap.ext fun z => ?_
    funext i j
    change (u * z * a) i j = (Matrix.kroneckerMap (· * ·) u a.transpose).mulVec (Function.uncurry z) (i, j)
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Function.uncurry_apply_pair, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [show Function.uncurry z (b, c) = z b c from rfl]
    ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]

theorem det_restrictScalars_twoSidedMul : ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
    [FiniteDimensional F E] (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E),
    (∀ x, T x = u * x * a) →
      LinearMap.det T = Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by
  intro F _ E _ _ _ α _ _ ν _ _ u a T hT
  have hT' : T = (twoSidedMulLin u a).restrictScalars F := by
    refine LinearMap.ext fun x => ?_
    rw [hT]; rfl
  rw [hT', LinearMap.det_restrictScalars, det_twoSidedMulLin, map_mul, map_pow, map_pow]

end GlobalTheory.KSp
end
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul : ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E), (∀ x, T x = u * x * a) → LinearMap.det T = Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by
  atlas_forward_decl GlobalTheory.KSp.det_restrictScalars_twoSidedMul
end

section
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

noncomputable def twoSidedEquiv (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
    {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν]
    (u : GL α E) (a : GL ν E) : Matrix α ν E ≃ₗ[F] Matrix α ν E where
  toFun x := (u : Matrix α α E) * x * (a : Matrix ν ν E)
  invFun x := ((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv x := by
    show ((u⁻¹ : GL α E) : Matrix α α E) * ((u : Matrix α α E) * x * (a : Matrix ν ν E)) * ((a⁻¹ : GL ν E) : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  right_inv x := by
    show (u : Matrix α α E) * (((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)) * (a : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]

theorem map_twoSided_haar : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ _ _ μ _ u a
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  have := hfd
  have := (hmat α ν).1
  let T := twoSidedEquiv F E u a

  have hdet : LinearEquiv.det T =
      (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u) ^ Fintype.card ν *
        (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a) ^
          Fintype.card α := by
    ext
    rw [LinearEquiv.coe_det, GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul F E α ν (u : Matrix α α E) (a : Matrix ν ν E)
      (T : Matrix α ν E →ₗ[F] Matrix α ν E) (fun x ↦ rfl)]
    simp
  have hT : (fun x ↦ (u : Matrix α α E) * x * (a : Matrix ν ν E)) = ⇑T := rfl
  rw [hT, GlobalTheory.T.map_linearEquiv_addHaar_localField F (Matrix α ν E) μ T, hdet, map_mul, map_pow, map_pow]

end GlobalTheory.KSp
end

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  atlas_forward_decl GlobalTheory.KSp.map_twoSided_haar
end
