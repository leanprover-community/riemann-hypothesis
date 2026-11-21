import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHorizontalVectorOfBreuilKisinJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowMulPhiMatrixInvAhat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionMulOneStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisInclIBEqDeRhamInclID
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrysLatticeBdRPlusActionCompat
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModCoefficientsEqSumOfInverseMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusBasisTensorLatticeFree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeBasisIndexedByBreuilKisin
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsUnitInvertibleMatrixIdentificationBasis
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonImageEisensteinPowPhiInvColumns
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.FiltrationEqSpanOfEisensteinPowBasisChange

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem mem_DdRE_qlExt {l : ℕ} [Fact l.Prime] (Pl : LocPrime l) {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] (ρ : Representation LL ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)) V)
    (τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] LL) (y : V ⊗[ℚ_[l]] Pl.R.BdR)
    (hy : y ∈ DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ) :
    y ∈ DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ τ := by
  refine Submodule.mem_inf.mpr ⟨hy, ?_⟩
  clear hy
  refine Submodule.mem_iInf _ |>.mpr fun c => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply]
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp c.2
  obtain rfl : c = algebraMap ℚ_[l] _ r := Subtype.ext hr.symm
  rw [AlgHom.commutes, algebraMap_smul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      LinearMap.mulLeft_apply]
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      TensorProduct.tmul_smul]
  | add a b ha hb => rw [map_add, ha, hb, smul_add]

theorem isJumpV_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (LL : FinExt l) (T : QLat LL) (F : FinExt l), IsGalois ℚ_[l] ↥F.1 → ∀ (i : ℤ) (x : T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ g : Gl l, (g : GQ l) ∈ GK F → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i → x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) → ∀ τ, IsJumpV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ i := by
  intro l _ Pl LL T F _ i x hfix hi hni τ
  have h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ F.1 := bot_le
  have hE : ∀ u, DdRE (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u =
      DdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ⊓ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) u := by
    intro u
    refine le_antisymm (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ fun y hy => ?_)
    exact mem_DdRE_qlExt Pl T.ρ τ y hy
  unfold IsJumpV FildR
  rw [hE, hE]
  refine (GlobalTheory.JumpDescent.jump_iff l Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F LL h T i).mp ?_
  intro heq
  have hxD : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) := by
    refine (GlobalTheory.JumpDescent.mem_DdR Pl F _ x).mpr fun g => ?_
    rw [GlobalTheory.JumpDescent.actVdR_comp Pl h]
    exact hfix _ g.2
  have hx : x ∈ DdR (Pl.PD F) (T.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
      FilV (Pl.PD F) (LL := ↥LL.1) (V := T.V) i :=
    ⟨hxD, by rw [GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hi⟩
  rw [← heq] at hx
  exact hni (by rw [← GlobalTheory.JumpDescent.FilV_eq Pl (Formalism.MainNotions.ElementDenominator.qlExt l) F]; exact hx.2)

end GlobalTheory.BKGal
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHodgeTateJump_of_galois_fixed_filtration_vector : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (LL : FinExt l) (T : QLat LL) (F : FinExt l), IsGalois ℚ_[l] ↥F.1 → ∀ (i : ℤ) (x : T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ g : Gl l, (g : GQ l) ∈ GK F → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) → x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i → x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) → ∀ τ, IsJumpV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ i := by
  atlas_forward_decl GlobalTheory.BKGal.isJumpV_of_fixed
end

section
section
set_option synthInstance.maxHeartbeats 400000

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.BKGal.CrisTensDR

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
  {LL : FinExt l} (T : QLat LL)

theorem coe_smul_lat (o : ↥(OL LL)) (x : ↥T.L.T) :
    ((o • x : ↥T.L.T) : T.V) = (o : ↥LL.1) • (x : T.V) := by
  rw [Submodule.coe_smul]
  exact (algebraMap_smul (↥LL.1) o (x : T.V)).symm

def gx (o : ↥(OL LL)) (b : Per.Bcris l) : ↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR :=
  AddMonoidHom.mk' (fun x => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (fun x y => by
      simp only [Submodule.coe_add, smul_add, TensorProduct.add_tmul])

def gb (o : ↥(OL LL)) : Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun b => gx Td T o b)
    (fun b c => by
      ext x
      simp only [gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, TensorProduct.tmul_add])

def g : ↥(OL LL) →+ Per.Bcris l →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  AddMonoidHom.mk' (fun o => gb Td T o)
    (fun o o' => by
      ext b x
      simp only [gb, gx, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Subalgebra.coe_add, add_smul,
        TensorProduct.add_tmul])

theorem cB_smul (z : ℤ_[l]) (b : Per.Bcris l) :
    GlobalTheory.BKGal.JumpDR.cB Td (z • b) = (z : ℚ_[l]) • GlobalTheory.BKGal.JumpDR.cB Td b := by
  rw [Algebra.smul_def, map_mul, GlobalTheory.BKGal.JumpDR.cB_algebraMap, ← Algebra.smul_def]

theorem zsmul_lat (z : ℤ_[l]) (o : ↥(OL LL)) (x : ↥T.L.T) :
    (((z • o : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (z : ℚ_[l]) • ((o : ↥LL.1) • (x : T.V)) := by
  show ((z : ℚ_[l]) • (o : ↥LL.1)) • (x : T.V) = _
  exact smul_assoc _ _ _

theorem g_balanced (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.Bcris l) : g Td T (z • o) b = g Td T o (z • b) := by
  ext x
  have h1 := congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (zsmul_lat T z o x)
  have h2 := congrArg (fun w => ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] w) (cB_smul Td z b)
  exact h1.trans ((TensorProduct.smul_tmul _ _ _).trans h2.symm)

def f1 : OB l ↥(OL LL) →+ (↥T.L.T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
  TensorProduct.liftAddHom (g Td T) (g_balanced Td T)

theorem mul_smul_lat (o o' : ↥(OL LL)) (x : ↥T.L.T) :
    (((o * o' : ↥(OL LL)) : ↥LL.1) • (x : T.V)) = (o' : ↥LL.1) • ((o • x : ↥T.L.T) : T.V) := by
  rw [coe_smul_lat, smul_smul, Subalgebra.coe_mul, mul_comm]

theorem crisTensorDRLiftFromCoeffBcris_smul_comm (o : ↥(OL LL)) :
    (f1 Td T).comp (DistribMulAction.toAddMonoidHom (OB l ↥(OL LL)) o) =
      (AddMonoidHom.compHom' (DistribMulAction.toAddMonoidHom (↥T.L.T) o)).comp (f1 Td T) := by
  refine AddMonoidHom.ext fun u => ?_
  induction u using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul o' b =>
    refine AddMonoidHom.ext fun x => ?_
    show g Td T (o * o') b x = g Td T o' b (o • x)
    exact congrArg (fun v => v ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) (mul_smul_lat T o o' x)
  | add u v hu hv => exact (map_add _ u v).trans ((congrArg₂ (· + ·) hu hv).trans (map_add _ u v).symm)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  intro l _ Pl AI Td LL T
  exact ⟨TensorProduct.liftAddHom (f1 Td T) fun o u x =>
    DFunLike.congr_fun (DFunLike.congr_fun (crisTensorDRLiftFromCoeffBcris_smul_comm Td T o) u) x, fun o b x => rfl⟩

end GlobalTheory.BKGal.CrisTensDR
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bcrisTensorLattice_to_deRham_map : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR, ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b := by
  atlas_forward_decl GlobalTheory.BKGal.CrisTensDR.main
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem exists_odAction : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR),
      A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  intro l _ Pl AI Td LL T
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdRp l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (cD Td b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (cD Td b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add, add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdRp l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdRp l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, cD_algebraMap, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl

end GlobalTheory.BKGal.JumpDR
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffDeRhamPlus_action_on_VTensorBdR : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL), ∃ A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c) := by
  atlas_forward_decl GlobalTheory.BKGal.JumpDR.exists_odAction
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.BKGal.JumpDR

theorem cB_gal {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (g : Gl l) (b : Per.Bcris l) :
    cB Td (Per.σB (sQ l g) b) = Pl.actQdR (sQ l g) (cB Td b) := by
  have h1 : Td.eB.symm (Per.σB (sQ l g) b) = Pl.actQ (sQ l g) (Td.eB.symm b) := by
    apply Td.eB.injective
    rw [RingEquiv.apply_symm_apply, Td.actB, RingEquiv.apply_symm_apply]
  have h2 := (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).ι_comm g (Td.eB.symm b)
  rw [Pl.PD_ι, Pl.PD_ι, Pl.PD_actB, Pl.PD_actdR] at h2
  change Pl.ιB (Td.eB.symm (Per.σB (sQ l g) b)) = Pl.actQdR (sQ l g) (Pl.ιB (Td.eB.symm b))
  rw [h1]; exact h2

theorem X_equivariant (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI)
    (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)
    (hX : ∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T),
      X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (g : Gl l) (b : TW (OB l ↥(OL LL)) T) :
    X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul u x =>
    induction u using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
    | tmul o b =>
      have e1 : actB (sQ l) T g ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.σB (sQ l g) b) ⊗ₜ[↥(OL LL)] T.actT g x := rfl
      rw [e1, hX, hX]
      have e2 : ((T.actT g x : ↥T.L.T) : T.V) = T.ρ g (x : T.V) := rfl
      rw [e2, cB_gal]
      show _ = (T.ρ g ((o : ↥LL.1) • (x : T.V))) ⊗ₜ[ℚ_[l]] ((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actdR g (cB Td b))
      rw [map_smul, Pl.PD_actdR]
      rfl

end GlobalTheory.BKGal.JumpDR
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (g : Gl l) (b : TW (OB l ↥(OL LL)) T), X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  atlas_forward_decl GlobalTheory.BKGal.JumpDR.X_equivariant
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpConst

variable {l : ℕ} [hl : Fact l.Prime]

theorem σDp_aDp (g : GQ l) (w : Ainf l) :
    Per.σDp g (GlobalTheory.MemLoc.aDp l w) = GlobalTheory.MemLoc.aDp l (Per.σA g w) := by
  change Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) (Per.AinfP l) w)) = _
  rw [GlobalTheory.MemLoc.CrisUnique.σDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]
  rfl

def galDp (g : GQ l) : Per.BdRp l →ₐ[ℤ_[l]] Per.BdRp l where
  toRingHom := Per.σDp g
  commutes' z := by
    change Per.σDp g (GlobalTheory.MemLoc.aDp l (algebraMap ℤ_[l] (Ainf l) z)) =
      GlobalTheory.MemLoc.aDp l (algebraMap ℤ_[l] (Ainf l) z)
    rw [σDp_aDp]
    exact congrArg (GlobalTheory.MemLoc.aDp l) ((galA g).commutes z)

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def galOD (g : GQ l) : OD l O →ₐ[O] OD l O := Algebra.TensorProduct.map (AlgHom.id O O) (galDp g)

theorem galOD_tmul (g : GQ l) (o : O) (b : Per.BdRp l) : galOD O g (o ⊗ₜ b) = o ⊗ₜ Per.σDp g b := rfl

theorem galOD_zero (g : GQ l) : galOD O g 0 = 0 := map_zero _

theorem galOD_add (g : GQ l) (x y : OD l O) : galOD O g (x + y) = galOD O g x + galOD O g y := map_add _ _ _

theorem galOD_toOD (g : GQ l) (x : OA l O) : galOD O g (toOD l O x) = toOD l O (galOA O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y) (σDp_aDp g w)
  | add x y hx hy => simp only [map_add, hx, hy]

variable {O}

theorem isUnit_natCast_OD {e : ℕ} (he : e ≠ 0) : IsUnit (e : OD l O) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd he l hl.out.ne_one
  have h1 : IsUnit (m : ℤ_[l]) :=
    PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hm))
  have h2 : IsUnit (m : OD l O) := by
    simpa only [map_natCast] using h1.map (algebraMap ℤ_[l] (OD l O))
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (isUnit_l_OD.pow k).mul h2

theorem eq_of_pow_eq {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {e : ℕ} (he : IsUnit (e : R))
    {x y : R} (hx : IsUnit x) (hxy : x ^ e = y ^ e) (h : x - y ∈ I) : x = y := by
  set S := ∑ i ∈ Finset.range e, x ^ i * y ^ (e - 1 - i) with hSdef
  have hq : Ideal.Quotient.mk I y = Ideal.Quotient.mk I x := (Ideal.Quotient.eq.2 h).symm
  have h1 : Ideal.Quotient.mk I S = Ideal.Quotient.mk I ((e : R) * x ^ (e - 1)) := by
    rw [hSdef, map_sum, map_mul, map_natCast, map_pow]
    simp only [map_mul, map_pow, hq]
    rw [Finset.sum_congr rfl fun i hi => by
      rw [← pow_add, Nat.add_sub_cancel' (by have := Finset.mem_range.1 hi; omega)]]
    simp
  have h2 : S - (e : R) * x ^ (e - 1) ∈ (⊥ : Ideal R).jacobson :=
    IsAdicComplete.le_jacobson_bot I (Ideal.Quotient.eq.1 h1)
  have hu : IsUnit ((e : R) * x ^ (e - 1)) := he.mul (hx.pow _)
  have h3 : IsUnit S := by
    obtain ⟨u, hu'⟩ := hu
    have := Ideal.mem_jacobson_bot.1 h2 (↑u⁻¹ : R)
    have h4 : S = ((S - (e : R) * x ^ (e - 1)) * ↑u⁻¹ + 1) * u := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hu']; ring
    rw [h4]
    exact this.mul u.isUnit
  have h5 := geom_sum₂_mul x y e
  rw [← hSdef, hxy, sub_self] at h5
  exact sub_eq_zero.1 ((h3.mul_right_eq_zero).1 h5)

section Root

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (ϖ : PiSys l e)

variable (O) in

def piHat : Ahat O K l e :=
  AhatEq.equivAhat O K l e (PowerSeries.C (AdjoinRoot.root (Polynomial.X ^ e + Polynomial.C (l : K))))

theorem root_pow_add : AdjoinRoot.root (Polynomial.X ^ e + Polynomial.C (l : K)) ^ e + (l : AdjoinRoot _) = 0 := by
  have := AdjoinRoot.eval₂_root (Polynomial.X ^ e + Polynomial.C (l : K))
  simpa using this

variable (O) in
theorem piHat_pow_add : piHat O K ^ e + (l : Ahat O K l e) = 0 := by
  rw [piHat, ← map_pow, ← map_natCast (AhatEq.equivAhat O K l e) l, ← map_add,
    ← map_natCast (PowerSeries.C (R := AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K)))) l, ← map_pow, ← map_add,
    root_pow_add, map_zero, map_zero]

variable (O) in

theorem exists_uhat_eq : ∃ w : Ahat O K l e, uhat O K l e = piHat O K + Ehat O K l e * w := by
  obtain ⟨v, hv⟩ := AhatEq.associated_taylor (AhatEq.separable_E K l e)
  refine ⟨AhatEq.equivAhat O K l e v, ?_⟩
  have h1 : AhatEq.equivAhat O K l e (AhatEq.taylor (Polynomial.X ^ e + Polynomial.C (l : K)) Polynomial.X) =
      uhat O K l e := by
    have := AhatEq.toAhat_taylor O K l e Polynomial.X
    rw [AhatEq.incl, Polynomial.aeval_X] at this
    exact this
  have h2 : AhatEq.equivAhat O K l e (AhatEq.taylor (Polynomial.X ^ e + Polynomial.C (l : K))
      (Polynomial.X ^ e + Polynomial.C (l : K))) = Ehat O K l e := by
    have := AhatEq.toAhat_taylor O K l e (Polynomial.X ^ e + Polynomial.C (l : K))
    exact this.trans (congrArg (ofAl O K l e) (AhatEq.incl_E O K l e))
  rw [← h1, ← h2, ← map_mul, hv, piHat, ← map_add]
  congr 1
  rw [AhatEq.taylor, Polynomial.aeval_X]

theorem iHat_uhat : ϖ.iHat O K (uhat O K l e) = 1 ⊗ₜ GlobalTheory.MemLoc.aDp l ϖ.teich := by
  rw [uhat, PiSys.iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (HasU.X_mem (B := A O K)) (uIn (invL l (A O K))).2).trans
    (congrArg (toOD l O) (ϖ.iA_u O K))

theorem iAl_E : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e)) :=
  (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))

theorem iHat_Ehat : ϖ.iHat O K (Ehat O K l e) = ϖ.iAl O K (EIn l e _) := ϖ.iHat_ofAl O K _

end Root

section Gal

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (ϖ : PiSys l e)

theorem dvd_σA_ev (g : GQ l) : ϖ.ev 1 (eis l 1 e) ∣ Per.σA g (ϖ.ev 1 (eis l 1 e)) := by
  rw [← Ideal.mem_span_singleton, ϖ.span_ev_eis 1, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA, ϖ.theta_ev_eis 1, map_zero]

theorem dvd_mu {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0) : ϖ.ev 1 (eis l 1 e) ∣ ϖ.mu g := by
  rw [← Ideal.mem_span_singleton, ϖ.span_ev_eis 1, RingHom.mem_ker]
  exact ϖ.theta_mu hg

theorem one_tmul_mul (u v : Per.BdRp l) : (1 : O) ⊗ₜ[ℤ_[l]] (u * v) = (1 ⊗ₜ u) * (1 ⊗ₜ v) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem galOD_mem_I (g : GQ l) {x : OD l O} (hx : x ∈ Ideal.span {ϖ.iAl O K (EIn l e _)}) :
    galOD O g x ∈ Ideal.span {ϖ.iAl O K (EIn l e _)} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hx
  obtain ⟨d, hd⟩ := dvd_σA_ev ϖ g
  rw [map_mul, iAl_E, galOD_tmul, σDp_aDp, hd, map_mul, one_tmul_mul, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem galOD_teich_sub {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0) :
    galOD O g (1 ⊗ₜ GlobalTheory.MemLoc.aDp l ϖ.teich) - 1 ⊗ₜ GlobalTheory.MemLoc.aDp l ϖ.teich ∈
      Ideal.span {ϖ.iAl O K (EIn l e _)} := by
  obtain ⟨d, hd⟩ := dvd_mu ϖ hg
  rw [galOD_tmul, σDp_aDp, ϖ.gal_teich, hd, add_mul, one_mul, map_add, tmul_add, add_sub_cancel_left, mul_assoc,
    map_mul, one_tmul_mul, iAl_E]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem galOD_iHat_piHat {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0) :
    galOD O g (ϖ.iHat O K (piHat O K)) = ϖ.iHat O K (piHat O K) := by
  haveI := ϖ.complete_OD O K
  have hx : ϖ.iHat O K (piHat O K) ^ e = -(l : OD l O) := by
    have := congrArg (ϖ.iHat O K) (piHat_pow_add O K (l := l) (e := e))
    rw [map_add, map_pow, map_natCast, map_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have hux : IsUnit (ϖ.iHat O K (piHat O K)) :=
    (isUnit_pow_iff (NeZero.ne e)).1 (hx ▸ (isUnit_l_OD (O := O)).neg)
  obtain ⟨w, hw⟩ := exists_uhat_eq O K (l := l) (e := e)
  have h1 : ϖ.iHat O K (piHat O K) - 1 ⊗ₜ GlobalTheory.MemLoc.aDp l ϖ.teich ∈ Ideal.span {ϖ.iAl O K (EIn l e _)} := by
    have := congrArg (ϖ.iHat O K) hw
    rw [iHat_uhat, map_add, map_mul, iHat_Ehat] at this
    rw [this, sub_add_cancel_left]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  refine eq_of_pow_eq (Ideal.span {ϖ.iAl O K (EIn l e _)}) (isUnit_natCast_OD (NeZero.ne e))
    (hux.map (galOD O g)) (by rw [← map_pow, hx, map_neg, map_natCast]) ?_
  have h2 := galOD_mem_I K ϖ g h1
  have h3 := galOD_teich_sub K ϖ (O := O) hg
  rw [map_sub] at h2
  have := Ideal.add_mem _ (Ideal.sub_mem _ h2 h1) h3
  convert this using 1
  ring

theorem exists_l_pow_mul (k : K) : ∃ (n : ℕ) (o : O), (l : K) ^ n * k = algebraMap O K o := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨0, 0, by simp⟩
  have hl1 : ‖(l : K)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
    exact Padic.norm_p_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hk)) hl1
  obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := O) ((l : K) ^ n * k)).2 (by
    rw [norm_mul, norm_pow]
    have := norm_pos_iff.2 hk
    have h2 := mul_lt_mul_of_pos_right hn this
    rw [inv_mul_cancel₀ this.ne'] at h2
    exact h2.le)
  exact ⟨n, o, ho.symm⟩

theorem galOD_iHat_algebraMap (g : GQ l) (k : K) :
    galOD O g (ϖ.iHat O K (algebraMap K (Ahat O K l e) k)) = ϖ.iHat O K (algebraMap K (Ahat O K l e) k) := by
  obtain ⟨n, o, h⟩ := exists_l_pow_mul K (O := O) (l := l) k
  have h1 : (l : OD l O) ^ n * ϖ.iHat O K (algebraMap K (Ahat O K l e) k) = algebraMap O (OD l O) o := by
    rw [← (ϖ.iHat O K).commutes o, IsScalarTower.algebraMap_apply O K (Ahat O K l e), ← h]
    simp only [map_mul, map_pow, map_natCast]
  refine ((isUnit_l_OD (O := O)).pow n).mul_left_cancel ?_
  rw [h1, ← map_natCast (galOD O g), ← map_pow, ← map_mul, h1, AlgHom.commutes]

end Gal

section Const

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (ϖ : PiSys l e)

theorem galOD_iHat_C {g : GQ l} (hg : g (ϖ.seq 0) = ϖ.seq 0)
    (c : AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K))) :
    galOD O g (ϖ.iHat O K (AhatEq.equivAhat O K l e (PowerSeries.C c))) =
      ϖ.iHat O K (AhatEq.equivAhat O K l e (PowerSeries.C c)) := by
  let F : Subring (Ahat O K l e) :=
    RingHom.eqLocus ((galOD O g).toRingHom.comp (ϖ.iHat O K).toRingHom) (ϖ.iHat O K).toRingHom
  change AhatEq.equivAhat O K l e (PowerSeries.C c) ∈ F
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, map_add]; exact F.add_mem hp hq
  | monomial n k =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_mul, map_pow,
      map_mul, map_pow]
    refine F.mul_mem ?_ (F.pow_mem (galOD_iHat_piHat K ϖ hg) n)
    have : PowerSeries.C (AdjoinRoot.of (Polynomial.X ^ e + Polynomial.C (l : K)) k) =
        algebraMap K (AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K)))⟦X⟧ k := by
      rw [PowerSeries.algebraMap_apply]; rfl
    rw [this, AlgEquiv.commutes]
    exact galOD_iHat_algebraMap K ϖ g k

theorem galOD_idem {a : ℕ} [NeZero a] (t : Wq l a →ₐ[ℤ_[l]] O) {g : GQ l} (hg : ∀ x ∈ Kunr l a, g x = x)
    (τ : ZMod a) : galOD O g (idem (constD t) τ) = idem (constD t) τ := by
  change galOD O g (toOD l O (constA t (Pi.single τ 1))) = toOD l O (constA t (Pi.single τ 1))
  rw [galOD_toOD, galOA_constA t hg]

theorem galOD_iD_kLift {a : ℕ} [NeZero a] (t : Wq l a →ₐ[ℤ_[l]] O) {g : GQ l} (hK : ∀ x ∈ Kunr l a, g x = x)
    (hg : g (ϖ.seq 0) = ϖ.seq 0) (c : ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K))) :
    galOD O g (ϖ.iD t K (GlobalTheory.BKGal.JumpDR.kLift O c)) = ϖ.iD t K (GlobalTheory.BKGal.JumpDR.kLift O c) := by
  rw [PiSys.iD, glue_apply, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, galOD_idem t hK]
  exact congrArg _ (galOD_iHat_C K ϖ hg (c τ))

end Const

theorem cD_σDp {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI) (g : GQ l) (b : Per.BdRp l) :
    GlobalTheory.BKGal.JumpDR.cD Td (Per.σDp g b) = Pl.actQdR g (GlobalTheory.BKGal.JumpDR.cD Td b) := by
  apply Td.eD.injective
  rw [Td.actD]
  change Td.eD (Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g b))) =
    Per.σD g (Td.eD (Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) b)))
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact (GlobalTheory.MemLoc.ActLaws.σD_alg g b).symm

theorem actVdR_A {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI) {LL : FinExt l} (T : QLat LL)
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR),
      A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (g : Gl l) (w : OD l ↥(OL LL)) (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) :
    actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (A w y) =
      A (galOD ↥(OL LL) (g : GQ l) w) (actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g y) := by
  have hact : ∀ (v : T.V) (b : Pl.R.BdR), actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (v ⊗ₜ[ℚ_[l]] b) =
      T.ρ g v ⊗ₜ[ℚ_[l]] Pl.actQdR (g : GQ l) b := fun v b => by
    rw [← Pl.PD_actdR]; rfl
  induction w using TensorProduct.induction_on generalizing y with
  | zero => simp only [galOD_zero, AddMonoidHom.map_zero, AddMonoidHom.zero_apply, LinearMap.map_zero]
  | add w w' hw hw' => simp only [galOD_add, AddMonoidHom.map_add, AddMonoidHom.add_apply, LinearMap.map_add, hw, hw']
  | tmul o b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v x =>
      simp only [hA, galOD_tmul, hact, cD_σDp, map_smul, map_mul]

end GlobalTheory.BKGal.JumpConst

open GlobalTheory.BKGal.JumpConst in

theorem GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (c : ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : ↥LL.1))) (g : Gl l), (g : GQ l) ∈ GK (ϖ.field a) → ∀ y : T.V ⊗[ℚ_[l]] Pl.R.BdR, actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) y) = A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) (actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g y) := by
  intro l _ Pl AI Td LL T A hA a e _ _ ϖ _ _ c g hg y
  have hπ : (g : GQ l) (ϖ.seq 0) = ϖ.seq 0 := ϖ.gal_pi a ⟨g, hg⟩
  have hK : ∀ x ∈ Kunr l a, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (ϖ.Kunr_le_field a hx)
  have hz := galOD_iD_kLift (↥LL.1) ϖ (thetaW a LL) hK hπ c
  exact (actVdR_A Td T A hA g _ y).trans (congrArg (fun w => A w (actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g y)) hz)
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffDeRhamPlusAction_constants_galois_comm : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (c : ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : ↥LL.1))) (g : Gl l), (g : GQ l) ∈ GK (ϖ.field a) → ∀ y : T.V ⊗[ℚ_[l]] Pl.R.BdR, actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) y) = A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) c)) (actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g y) := by
  atlas_forward_decl GlobalTheory.BKGal.JumpConst.actVdR_comm_kLift
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eisenstein_pow_mul_phiMatrix_inv_ahat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i) := by
  first | exact @GlobalTheory.BK.coordE_mxInv | exact GlobalTheory.BK.coordE_mxInv | (intros; apply GlobalTheory.BK.coordE_mxInv <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

section General

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K] [NeZero a]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_Ehat_pow_mul (w : ZMod a → ι → AhatE O K l e) :
    ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * w τ i := by
  classical
  choose r z hz using fun p : ZMod a × ι => IsLocalization.Away.surj (Ehat O K l e) (w p.1 p.2)
  refine ⟨Finset.univ.sup r, fun τ i => Ehat O K l e ^ (Finset.univ.sup r - r (τ, i)) * z (τ, i),
    fun τ i => ?_⟩
  have hle : r (τ, i) ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ _)
  rw [map_mul, map_pow, ← hz (τ, i), mul_left_comm, ← pow_add, Nat.sub_add_cancel hle, mul_comm]

end General

theorem hsum_mul_Ehat_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl), ∃ (N : ℕ) (x : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (x τ i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P n s m
  exact exists_Ehat_pow_mul (GlobalTheory.BKGal.JumpDR.hsum P s fun k => (m k).1)

end GlobalTheory.BKGal.JumpDR
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hsum_mul_eisensteinCompletion_pow_integral : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl), ∃ (N : ℕ) (x : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (x τ i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
  atlas_forward_decl GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open GlobalTheory.BKGal.HatVal in
private theorem gen {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) {W : Type} [AddCommGroup W] (Y : TW (OB l O) T →+ W)
    (act : OD l O →+ (W →+ W)) (hmul : ∀ x y w, act (x * y) w = act x (act y w)) (C : GlobalTheory.MemLoc.Core l)
    (hact : ∀ (b : OB l O) (y : OD l O), iotaO O C b = dRO l O y → ∀ z : TW (OB l O) T, Y (b • z) = act y (Y z))
    (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e)
    (hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) =
      ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) :
    ∑ k, act (ϖ.iD t K (s k)) (Y (jB (toBcris t ϖ P (m k)))) =
      ∑ j, act (ϖ.iD t K (fun τ => c τ j)) (Y (jB (Pi.single j 1))) := by
  have hco := UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix l a e O K t ϖ ι P n s m c hc
  have h1 : ∀ k, Y (jB (toBcris t ϖ P (m k))) = ∑ j, act (ϖ.iD t K
      (fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)))
      (Y (jB (Pi.single j 1))) := by
    intro k
    have h2 : toBcris t ϖ P (m k) = ∑ j, ϖ.iB t K
        (coordL P (invL l (S O K e)) (m k) j) • (Pi.single j 1 : ι → OB l O) := by
      funext i
      rw [toBcris_apply, Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro j _ hj
        rw [Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [jB.map_smul]
    exact hact _ _ (UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD l a e O K t ϖ C _) _
  simp only [h1, hco, map_sum, map_mul, AddMonoidHom.finset_sum_apply, hmul]
  exact Finset.sum_comm

theorem _root_.GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (c τ j) = ∑ i, hat ↥(OL LL) l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => c τ j)) (X (jB (Pi.single j 1))) := by
  intro _ l _ a e _ _ ϖ LL _ _ _ ι _ _ P T jB Pl AI Td Y hY act hA n s m c hc
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  exact gen (thetaW a LL) ϖ P T jB Y act (GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA).1 C
    (UpperTheory.KN.crysLattice_bdRPlus_action_compat l LL T Pl AI Td Y hY act hA C) n s m c hc
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.CoordInv

section Gen

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_ofA_of_injective [NeZero a] (hinj : Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)))
    (P : PhiMod O K l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e)
    (hy : ∀ τ j i, algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i))
    (hβ : ∀ τ j i, E K l e ^ β * P.mxInv τ j i ∈ A O K) (τ : ZMod a) (j i : ι) :
    y τ j i = ofA O K l e ⟨E K l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  apply hinj
  rw [hy, ← hat_coe_A, hat_mul l e (E_pow_mem_RpiE _) (invE_A_le_RpiE l e (P.mxInv_mem τ j i)), hat_E_pow]

theorem algebraMap_AhatE_injective :
    Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
  IsLocalization.injective (M := Submonoid.powers (Ehat O K l e)) _
    (Submonoid.powers_le.2 (Ehat_mem_nonZeroDivisors O K l e))

end Gen

end GlobalTheory.BK.CoordInv

open GlobalTheory.BK.CoordInv in

theorem GlobalTheory.BK.coordE_mxInv_eq_ofA : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1), ∀ τ j i, y τ j i = ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  intro l _ a e _ _ _ LL _ _ ι _ _ P β y hy hβ τ j i
  exact eq_ofA_of_injective (algebraMap_AhatE_injective l e) P β y hy hβ τ j i
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinates_eq_of_eisensteinPow_mul_inverse_matrix : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1), ∀ τ j i, y τ j i = ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  atlas_forward_decl GlobalTheory.BK.coordE_mxInv_eq_ofA
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem linIndep_of_mutual_span_of_indep :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)),
      (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b f : ι → W),
        (∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) →
        (∀ i, ∃ d : ι → R, f i = ∑ k, act (d k) (b k)) →
        (∀ k, ∃ d : ι → R, b k = ∑ i, act (d i) (f i)) →
        ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro R W _ _ act hmul hone ι _ _ b f hb hf hbf d hd
  letI : Module R W :=
    { smul := fun r w => act r w
      one_smul := hone
      mul_smul := fun r s w => hmul r s w
      smul_zero := fun r => map_zero (act r)
      smul_add := fun r x y => map_add (act r) x y
      add_smul := fun r s w => by
        show act (r + s) w = act r w + act s w
        rw [map_add, AddMonoidHom.add_apply]
      zero_smul := fun w => by
        show act 0 w = 0
        rw [map_zero, AddMonoidHom.zero_apply] }
  have hs : ∀ (r : R) (w : W), act r w = r • w := fun _ _ => rfl
  simp only [hs] at hb hf hbf hd
  choose P hP using hf
  choose Q hQ using hbf
  have expand : ∀ c : ι → R,
      ∑ i, c i • f i = ∑ k, (Matrix.vecMul c (Matrix.of P)) k • b k := by
    intro c
    simp only [hP, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Matrix.of_apply,
      Finset.sum_smul]
    rw [Finset.sum_comm]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext k k'
    have h0 : ∑ k'', ((Matrix.vecMul (Q k) (Matrix.of P)) k'' - (1 : Matrix ι ι R) k k'') • b k''
        = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← expand, ← hQ, Matrix.one_apply,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    have := hb _ h0 k'
    rw [sub_eq_zero] at this
    rw [← this, Matrix.mul_apply]
    simp [Matrix.vecMul, dotProduct]
  have hPQ : Matrix.of P * Matrix.of Q = 1 := mul_eq_one_comm.mp hQP
  have he : Matrix.vecMul d (Matrix.of P) = 0 := by
    rw [expand] at hd
    funext k
    exact hb _ hd k
  have : d = 0 := by
    rw [← Matrix.vecMul_one d, ← hPQ, ← Matrix.vecMul_vecMul, he, Matrix.zero_vecMul]
  intro i
  rw [this]
  rfl

end GlobalTheory
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_of_mutual_span_of_indep : ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)), (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b f : ι → W), (∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) → (∀ i, ∃ d : ι → R, f i = ∑ k, act (d k) (b k)) → (∀ k, ∃ d : ι → R, b k = ∑ i, act (d i) (f i)) → ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  atlas_forward_decl GlobalTheory.linIndep_of_mutual_span_of_indep
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (α β : ℕ), (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → (∀ v ∈ P.M, E ↥LL.1 l e ^ β • v ∈ P.L) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (w : T.V ⊗[ℚ_[l]] Pl.R.BdR), w ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) ((β : ℤ)) ↔ ∃ d : ι → OD l ↥(OL LL), w = ∑ i, act (d i) (∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1)))) := by
  intro _ l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB Pl AI Td hC X hX act hA α β _ _ hβ w
  obtain ⟨hmul, hone⟩ := GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA
  obtain ⟨hbij, hshift⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  obtain ⟨b⟩ := GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin l a e ϖ LL ι P T I
  have hb0 := (GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b).1
  obtain ⟨m, m', u, r, hu, hm, hr, hrm⟩ := UpperTheory.KN.exists_unit_invertible_matrix_identification_basis l a e ϖ LL ι P T I b
  have hf := UpperTheory.KN.crisComparison_image_eisensteinPow_phiInvColumns l a e ϖ LL ι P T I jB Pl AI Td hC X hX act hA b m u r hu hr hrm β hβ
  exact UpperTheory.KN.filtration_eq_span_of_eisensteinPow_basisChange _ _ act hmul hone _ hbij
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) => v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j))
    hshift ι β
    (fun i => ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1))))
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) m m' hm hf hb0 w
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis {R W : Type} [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w) (eD : R)
    (hbij : Function.Bijective (act eD)) (F : ℤ → W → Prop) (hshift : ∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y))
    {ι : Type} [Fintype ι] [DecidableEq ι] (β β₀ : ℕ) (g h b : ι → W) (hg : ∀ i, act (eD ^ β₀) (g i) = h i)
    (hspan : ∀ w, F ((β₀ + β : ℕ) : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i))
    (hb0 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k))
    (hbi : ∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) :
    ∃ f : ι → W, (∀ i, act (eD ^ β) (f i) = g i) ∧ (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (f i)) ∧
      ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  have hcomm : ∀ (d d' : R) (w : W), act d (act d' w) = act d' (act d w) := by
    intro d d' w
    rw [← hmul, ← hmul, mul_comm]
  have hpow : ∀ (n : ℕ) (w : W), act (eD ^ n) w = (act eD)^[n] w := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, hone]; rfl
    | succ n ih => intro w; rw [pow_succ', hmul, ih, Function.iterate_succ_apply']
  have hinj : ∀ n : ℕ, Function.Injective (act (eD ^ n)) := by
    intro n x x' hxx
    rw [hpow, hpow] at hxx
    exact (hbij.1.iterate n) hxx
  have hsh : ∀ (n : ℕ) (w : W) (j : ℤ), F j w ↔ F (j + n) (act (eD ^ n) w) := by
    intro n
    induction n with
    | zero => intro w j; rw [pow_zero, hone, Nat.cast_zero, add_zero]
    | succ n ih =>
      intro w j
      rw [ih w j, hshift (act (eD ^ n) w) (j + n), pow_succ', hmul, Nat.cast_succ, ← add_assoc]
  have hsingle : ∀ (v : ι → W) (i : ι), ∑ k, act ((Pi.single i (1 : R) : ι → R) k) (v k) = v i := by
    intro v i
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, AddMonoidHom.zero_apply])
      (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, hone]
  let ginv : W → W := (Equiv.ofBijective _ hbij).symm
  have hginv : ∀ x, act eD (ginv x) = x := fun x => (Equiv.ofBijective _ hbij).apply_symm_apply x
  have h1 : ∀ i, act (eD ^ β) (ginv^[β] (g i)) = g i := by
    intro i
    rw [hpow]
    exact Function.RightInverse.iterate hginv β _
  have h2 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (ginv^[β] (g i)) := by
    have hf : ∀ i, act (eD ^ (β₀ + β)) (ginv^[β] (g i)) = h i := by
      intro i
      rw [pow_add, hmul, hpow β, Function.RightInverse.iterate hginv β, hg]
    intro v
    rw [hsh (β₀ + β) v 0, zero_add, hspan]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, hinj (β₀ + β) ?_⟩
      rw [hd, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
  refine ⟨fun i => ginv^[β] (g i), h1, h2, ?_⟩
  refine GlobalTheory.T.linearIndependent_of_mutual_span_of_indep R W act hmul hone ι b _ hbi ?_ ?_
  · intro i
    exact (hb0 _).1 ((h2 _).2 ⟨Pi.single i 1, (hsingle (fun i => ginv^[β] (g i)) i).symm⟩)
  · intro k
    exact (h2 _).1 ((hb0 _).2 ⟨Pi.single k 1, (hsingle b k).symm⟩)

set_option maxHeartbeats 8000000 in

theorem GlobalTheory.BKGal.JumpDR.basis_images : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI Td hC X hX act hA β y hy
  obtain ⟨hmul, hone⟩ := GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA
  obtain ⟨hbij, hshift⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  obtain ⟨α, β0, hα, hβ0⟩ := P.exists_exponents
  have hLM1 : ∀ v ∈ P.M, E ↥LL.1 l e ^ (β0 + β) • v ∈ P.L := by
    intro v hv
    have := P.L.smul_mem (⟨_, pow_mem (E_mem l e _) β⟩ : A ↥(OL LL) ↥LL.1) (hβ0 v hv)
    rw [pow_add, mul_comm, mul_smul]
    exact this
  have hβ1 : ∀ τ j i, E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1 := by
    intro τ j i
    have hv : (fun (_ : ZMod a) (i' : ι) => if i' = i then (1 : (↥LL.1)⟦X⟧) else 0) ∈ P.M := by
      refine mem_tot.2 fun τ' i' => ?_
      show (if i' = i then (1 : (↥LL.1)⟦X⟧) else 0) ∈ A ↥(OL LL) ↥LL.1
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := (P.mem_extc_iff.1 (mem_tot.1 (hLM1 _ hv) τ)) j
    convert h2 using 1
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hy1 : ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
      (Ehat ↥(OL LL) ↥LL.1 l e ^ β0 * y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
      (Ehat ↥(OL LL) ↥LL.1 l e) ^ (β0 + β) * hat ↥(OL LL) l e (P.mxInv τ j i) := fun τ j i =>
    (map_mul _ _ _).trans ((congrArg₂ (· * ·) (map_pow _ _ _) (hy τ j i)).trans
      ((mul_assoc _ _ _).symm.trans (congrArg (· * _) (pow_add _ _ _).symm)))
  have hyA := GlobalTheory.T.coordinates_eq_of_eisensteinPow_mul_inverse_matrix l a e ϖ LL ι P (β0 + β) (fun τ j i => Ehat ↥(OL LL) ↥LL.1 l e ^ β0 * y τ j i) hy1 hβ1
  have hg : ∀ i, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0)
      (∑ j, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) =
      ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩))) (X (jB (Pi.single j 1))) := by
    intro i
    refine (map_sum (act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0)) _ _).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    refine (hmul _ _ _).symm.trans (congrArg (fun z => act z (X (jB (Pi.single j 1)))) ?_)
    refine Eq.trans ?_ (PiSys.iD_ofA (thetaW a LL) ↥LL.1 ϖ _)
    have hpt : (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0 * (fun τ => y τ j i) =
        fun τ => ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩ :=
      funext fun τ => hyA τ j i
    exact (congrArg (· * ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i))
      (map_pow (ϖ.iD (thetaW a LL) ↥LL.1) (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) β0).symm).trans
      ((map_mul (ϖ.iD (thetaW a LL) ↥LL.1) _ _).symm.trans (congrArg (ϖ.iD (thetaW a LL) ↥LL.1) hpt))
  have hspan := GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice hF l a e ϖ LL hl2 ι P T I jB Pl AI Td hC X hX act hA α (β0 + β) hα hLM1 hβ1
  obtain ⟨b⟩ := GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin l a e ϖ LL ι P T I
  obtain ⟨hb0, hbi⟩ := GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b
  exact GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis act hmul hone _ hbij
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) => v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j)) hshift β β0
    (fun i => ∑ j, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1))))
    (fun i => ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩))) (X (jB (Pi.single j 1))))
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) hg hspan hb0 hbi

end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  atlas_forward_decl GlobalTheory.BKGal.JumpDR.basis_images
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR.CmpFil

theorem amulG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ∀ o o', ι' (o * o') = ι' o * ι' o') (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (x y : OD l O) (v : V ⊗[ℚ_[l]] R) : A (x * y) v = A x (A y v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul v c =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [add_mul, map_add, AddMonoidHom.add_apply, hx, hx']
    | tmul o b =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
      | add y y' hy hy' => simp only [mul_add, map_add, AddMonoidHom.add_apply, hy, hy']
      | tmul o' b' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hA, hA, hA, map_mul, mul_assoc, h1, mul_smul]

theorem aoneG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ι' 1 = 1) (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (v : V ⊗[ℚ_[l]] R) : A 1 v = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul v c => rw [Algebra.TensorProduct.one_def, hA, map_one, one_mul, h1, one_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem amulL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (x y : OD l ↥(OL LL)) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A (x * y) v = A x (A y v) :=
  amulG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) (fun _ _ => rfl) (GlobalTheory.BKGal.JumpDR.cD Td) A hA x y v

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem aoneL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A 1 v = v :=
  aoneG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) rfl (GlobalTheory.BKGal.JumpDR.cD Td) A hA v

set_option maxHeartbeats 1000000 in
theorem coreG {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {W : Type} [AddCommGroup W] (A : OD l O →+ (W →+ W)) (Fil : ℤ → W → Prop)
    (amul : ∀ x y v, A (x * y) v = A x (A y v)) (aone : ∀ v, A 1 v = v)
    (hbij : Function.Bijective (A (ϖ.iD t K (fun _ => Ehat O K l e))))
    (hS : ∀ (y : W) (j : ℤ), Fil j y ↔ Fil (j + 1) (A (ϖ.iD t K (fun _ => Ehat O K l e)) y))
    (gB : ι → W) (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e)
    (hy : ∀ τ j i, algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i))
    (f : ι → W) (hf1 : ∀ i, A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i) = ∑ j, A (ϖ.iD t K (fun τ => y τ j i)) (gB j))
    (hspan : ∀ v, Fil 0 v ↔ ∃ d : ι → OD l O, v = ∑ i, A (d i) (f i))
    (hind : ∀ d : ι → OD l O, ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0)
    {n : ℕ} (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (g : Fin n → W)
    (hC : ∀ (s' : Fin n → ZMod a → Ahat O K l e) (c : ZMod a → ι → Ahat O K l e), (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD t K (s' k)) (g k) = ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j))
    (hE1 : ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i)
    (j : ℤ) :
    GlobalTheory.BKGal.JumpDR.InEhat O K l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ Fil j (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
  classical
  have hbijN : ∀ N : ℕ, Function.Bijective (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) := by
    intro N
    induction N with
    | zero =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ 0)) = id := funext fun v => by rw [pow_zero]; exact aone v
      rw [h0]; exact Function.bijective_id
    | succ N ih =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1))) = ⇑(A (ϖ.iD t K (fun _ => Ehat O K l e))) ∘ ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) :=
        funext fun v => by rw [pow_succ', amul]; rfl
      rw [h0]; exact hbij.comp ih
  have hSh : ∀ (N : ℕ) (y : W) (j : ℤ), Fil j y ↔ Fil (j + N) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by
    intro N
    induction N with
    | zero => intro y j; rw [pow_zero, aone, Nat.cast_zero, add_zero]
    | succ N ih =>
      intro y j
      have e1 : (j + ((N + 1 : ℕ) : ℤ)) = (j + N) + 1 := by push_cast; ring
      have e2 : A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1)) y = A (ϖ.iD t K (fun _ => Ehat O K l e)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by rw [pow_succ', amul]
      rw [e1, e2]
      exact (ih y j).trans (hS _ _)
  have Fb : ∀ (d : ι → OD l O) (kk : ℕ), Fil kk (∑ i, A (d i) (f i)) ↔ ∀ i, d i ∈ Ideal.span {(ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk} := by
    intro d kk
    constructor
    · intro hd
      obtain ⟨v', hv'⟩ := (hbijN kk).2 (∑ i, A (d i) (f i))
      have h0 : Fil 0 v' := (hSh kk v' 0).2 (by rw [hv', zero_add]; exact hd)
      obtain ⟨z, rfl⟩ := (hspan v').1 h0
      have h4 : ∑ i, A (d i - (ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk * z i) (f i) = 0 := by
        simp only [map_sub, AddMonoidHom.sub_apply, Finset.sum_sub_distrib, amul]
        rw [← map_sum, hv', sub_self]
      intro i
      have h5 := hind _ h4 i
      rw [sub_eq_zero] at h5
      rw [h5]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hd
      choose z hz using fun i => Ideal.mem_span_singleton'.1 (hd i)
      have h6 : ∑ i, A (d i) (f i) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk) (∑ i, A (z i) (f i)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hz i, mul_comm, amul]
      have h7 := (hSh kk _ 0).1 ((hspan _).2 ⟨z, rfl⟩)
      rw [zero_add] at h7
      rw [h6]; exact h7
  have key : ∀ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), (∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
      A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) (∑ k, A (ϖ.iD t K (s k)) (g k)) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i) := by
    intro N x hx
    let s' : Fin n → ZMod a → Ahat O K l e := fun k => (fun _ => Ehat O K l e) ^ (N + β) * s k
    let c : ZMod a → ι → Ahat O K l e := fun τ j => ∑ i, y τ j i * x τ i
    have hw : ∀ τ i, GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N + β) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i
      simp only [GlobalTheory.BKGal.JumpDR.hsum, s', Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, Finset.mul_sum, mul_assoc]
    have hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i := by
      intro τ j
      simp only [c, map_sum, map_mul, hy, hx, hw]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hC' := hC s' c hc
    have h1 : ∑ k, A (ϖ.iD t K (s' k)) (g k) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + β)) (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [s', map_mul, map_pow]
      rw [amul]
    have h2' : ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) := by
      have h3 : ∀ j, (fun τ => c τ j) = ∑ i, (fun τ => x τ i) * (fun τ => y τ j i) := by
        intro j; funext τ; simp only [c, Finset.sum_apply, Pi.mul_apply, mul_comm]
      simp only [h3, map_sum, AddMonoidHom.finset_sum_apply, map_mul, amul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf1 i, map_sum]
    rw [h1, h2'] at hC'
    have h3 : ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← amul, ← amul, mul_comm]
    rw [h3, pow_add, mul_comm, amul] at hC'
    exact (hbijN β).1 hC'
  constructor
  · rintro ⟨N, hN, hx⟩
    choose x' hx' using hx
    have hkj : (((j + N).toNat : ℕ) : ℤ) = j + N := Int.toNat_of_nonneg hN
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ (j + N).toNat * x' τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; rw [← map_pow]; exact hx' τ i
    have hK := key N x hxx
    have hmem : Fil (((j + N).toNat : ℕ) : ℤ) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      refine (Fb _ _).2 fun i => ?_
      have h8 : (fun τ => x τ i) = (fun _ => Ehat O K l e) ^ (j + N).toNat * fun τ => x' τ i := by
        funext τ; simp only [x, Pi.mul_apply, Pi.pow_apply]
      rw [h8, map_mul, map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [← hK, hkj] at hmem
    exact (hSh N _ j).2 hmem
  · intro hF
    obtain ⟨N₁, x₁, hx₁⟩ := hE1
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ j.natAbs * x₁ τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N₁ + j.natAbs) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; simp only [x, map_mul, map_pow, hx₁, pow_add]; ring
    have hK := key _ x hxx
    have hN : 0 ≤ j + ((N₁ + j.natAbs : ℕ) : ℤ) := by push_cast; have := neg_abs_le j; omega
    have hkj : (((j + ((N₁ + j.natAbs : ℕ) : ℤ)).toNat : ℕ) : ℤ) = j + ((N₁ + j.natAbs : ℕ) : ℤ) := Int.toNat_of_nonneg hN
    have h1 := (hSh (N₁ + j.natAbs) _ j).1 hF
    rw [hK, ← hkj] at h1
    have h2 := (Fb _ _).1 h1
    refine ⟨N₁ + j.natAbs, hN, fun τ i => ?_⟩
    obtain ⟨z, hz⟩ := PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ _ _ (h2 i)
    refine ⟨z τ, ?_⟩
    have h9 := congrFun hz τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h9
    rw [← h9, map_pow]
    exact hxx τ i

end GlobalTheory.BKGal.JumpDR.CmpFil

open GlobalTheory.BKGal.JumpDR.CmpFil in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.BKGal.JumpDR.inEhat_iff_filV : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (j : ℤ), GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j := by
  intro hFont l _ a e _ _ ϖ LL _ _ h2 ι _ _ P T I jB Pl AI Td hcmp X hX A hA n s m j
  obtain ⟨hbij, hS⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td A hA
  obtain ⟨β, y, hy⟩ := GlobalTheory.T.exists_eisenstein_pow_mul_phiMatrix_inv_ahat l a e ϖ LL ι P
  obtain ⟨f, hf1, hspan, hind⟩ := GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus hFont l a e ϖ LL h2 ι P T I jB Pl AI Td hcmp X hX A hA β y hy
  exact coreG (thetaW a LL) ϖ P A (fun j y => y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j)
    (amulL A hA) (aoneL A hA) hbij hS (fun j => X (jB (Pi.single j 1))) β y hy f hf1 hspan hind s m
    (fun k => X (jB (toBcris (thetaW a LL) ϖ P (m k))))
    (fun s' c h => GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates hFont l a e ϖ LL h2 ι P T jB Pl AI Td X hX A hA n s' m c h)
    (GlobalTheory.T.hsum_mul_eisensteinCompletion_pow_integral l a e ϖ LL ι P n s m) j
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completionFiltration_iff_deRhamFiltration : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (j : ℤ), GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j := by
  atlas_forward_decl GlobalTheory.BKGal.JumpDR.inEhat_iff_filV
end

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  intro hF l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN i hi
  have Td : LocTied l Pl AI := hStd.some
  obtain ⟨X, hX⟩ := GlobalTheory.T.exists_bcrisTensorLattice_to_deRham_map l Pl AI Td LL T
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_coeffDeRhamPlus_action_on_VTensorBdR l Pl AI Td LL T
  obtain ⟨n, d, c, hd, h1, h2⟩ := GlobalTheory.T.exists_horizontal_vector_of_breuilKisin_jump l a e LL hl ι P hEN i hi
  let m : Fin n → P.MMl := fun k => ⟨P.xi (d k), hd k⟩
  have key := fun j => GlobalTheory.T.mem_completionFiltration_iff_deRhamFiltration hF l a e ϖ LL hl ι P T I jB Pl AI Td hCmp X hX A hA n
    (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) m j
  refine ⟨∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)))
    (X (jB (toBcris (thetaW a LL) ϖ P (m k)))), ?_, (key i).1 h1, fun h => h2 ((key (i + 1)).2 h)⟩
  intro g hg
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 := GlobalTheory.T.coeffDeRhamPlusAction_constants_galois_comm l Pl AI Td LL T A hA a e ϖ (c k) g hg (X (jB (toBcris (thetaW a LL) ϖ P (m k))))
  have e2 := GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant l Pl AI Td LL T X hX g (jB (toBcris (thetaW a LL) ϖ P (m k)))
  have e3 := hHor g hg (d k) (hd k)
  rw [e1, ← e2]
  exact congrArg _ (congrArg X e3)
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ x : T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ g : Gl l, (g : GQ l) ∈ GK (ϖ.field a) → actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g x = x) ∧ x ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) i ∧ x ∉ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (i + 1) := by
  atlas_forward_decl GlobalTheory.BKGal.JumpDR.jump_gives_fixed_vector
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.JumpsOfM

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  intro hF l _ a e _ _ ϖ LL _ hT hl ι _ _ P T I jB Pl AI hStd hCmp hHor hEN U hU i hi
  obtain ⟨x, hfix, hx, hx'⟩ := GlobalTheory.T.exists_fixed_vector_filtration_jump_breuilKisin hF l a e ϖ LL hl ι P T I jB Pl AI hStd hCmp hHor hEN i hi
  have hdvd : e ∣ l ^ a - 1 := ⟨1, by rw [← hT.succ_eq]; simp⟩
  have hG := PiSys.isGalois_field a ϖ hdvd
  let τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1 :=
    (Algebra.ofId ℚ_[l] ↥LL.1).comp (IntermediateField.botEquiv ℚ_[l] (Om l)).toAlgHom
  exact hU τ i (GlobalTheory.T.isHodgeTateJump_of_galois_fixed_filtration_vector l Pl LL T (ϖ.field a) hG i x hfix hx hx' τ)

end GlobalTheory.JumpsOfM
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_jumps_breuilKisin_subset_galoisJumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  atlas_forward_decl GlobalTheory.JumpsOfM.main
end
