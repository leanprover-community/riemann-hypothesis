import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsCrisPOfIsCrisDR

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.exists_tensorBdR_action_on_latticeBdR :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), ∃ B : OdR l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdR l) (v : T.V) (c : Pl.R.BdR), B (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := by
  intro l _ LL T Pl AI Td
  have hz : ∀ z : ℤ_[l], Td.eD.symm (algebraMap ℤ_[l] (Per.BdR l) z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) :=
    fun z => GlobalTheory.BKGal.JumpDR.cD_algebraMap Td z
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdR l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (Td.eD.symm b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add, add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdR l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdR l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, hz, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem actDRG {Z Q O P D V R : Type} [CommRing Z] [CommRing Q] [CommRing O] [Algebra Z O]
    [CommRing P] [Algebra Z P] [CommRing D] [Algebra Z D] [AddCommGroup V] [Module Q V]
    [CommRing R] [Algebra Q R] (s : O → V → V) (g : P → D) (cD : P → R) (e : D → R)
    (hg : ∀ b, cD b = e (g b)) (d : O ⊗[Z] P →+ O ⊗[Z] D)
    (hd : ∀ o b, d (o ⊗ₜ[Z] b) = o ⊗ₜ[Z] g b)
    (A : O ⊗[Z] P →+ (V ⊗[Q] R →+ V ⊗[Q] R))
    (hA : ∀ (o : O) (b : P) (v : V) (c : R), A (o ⊗ₜ[Z] b) (v ⊗ₜ[Q] c) = (s o v) ⊗ₜ[Q] (cD b * c))
    (B : O ⊗[Z] D →+ (V ⊗[Q] R →+ V ⊗[Q] R))
    (hB : ∀ (o : O) (b : D) (v : V) (c : R), B (o ⊗ₜ[Z] b) (v ⊗ₜ[Q] c) = (s o v) ⊗ₜ[Q] (e b * c))
    (y : O ⊗[Z] P) (w : V ⊗[Q] R) : A y w = B (d y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add, hv, hw]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']
    | tmul o b => rw [hd, hA, hB, hg]

private theorem actCrisG {Z Q O P D M V R : Type} [CommRing Z] [CommRing Q] [CommRing O] [Algebra Z O]
    [CommRing P] [Algebra Z P] [CommRing D] [Algebra Z D] [AddCommGroup V] [Module Q V]
    [AddCommGroup M] [Module O M]
    [CommRing R] [Algebra Q R] (s : O → V → V) (hs : ∀ o o' v, s (o * o') v = s o (s o' v))
    (j : M → V) (g : P → D) (cB : P →+* R) (e : D → R)
    (hg : ∀ b, cB b = e (g b)) (d : O ⊗[Z] P →+ O ⊗[Z] D)
    (hd : ∀ o b, d (o ⊗ₜ[Z] b) = o ⊗ₜ[Z] g b)
    (Y : (O ⊗[Z] P) ⊗[O] M →+ V ⊗[Q] R)
    (hY : ∀ (o : O) (b : P) (x : M), Y ((o ⊗ₜ[Z] b) ⊗ₜ[O] x) = (s o (j x)) ⊗ₜ[Q] cB b)
    (B : O ⊗[Z] D →+ (V ⊗[Q] R →+ V ⊗[Q] R))
    (hB : ∀ (o : O) (b : D) (v : V) (c : R), B (o ⊗ₜ[Z] b) (v ⊗ₜ[Q] c) = (s o v) ⊗ₜ[Q] (e b * c))
    (b : O ⊗[Z] P) (z : (O ⊗[Z] P) ⊗[O] M) : Y (b • z) = B (d b) (Y z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add v w hv hw => simp only [smul_add, map_add, hv, hw]
  | tmul u x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    induction b using TensorProduct.induction_on with
    | zero => simp only [zero_mul, zero_tmul, map_zero, AddMonoidHom.zero_apply]
    | add y y' hy hy' => simp only [add_mul, add_tmul, map_add, AddMonoidHom.add_apply, hy, hy']
    | tmul o' b' =>
      induction u using TensorProduct.induction_on with
      | zero => simp only [mul_zero, zero_tmul, map_zero]
      | add y y' hy hy' => simp only [mul_add, add_tmul, map_add, hy, hy']
      | tmul o b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hY, hY, hd, hB, map_mul, hs, hg b']

private theorem hcB {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (C : GlobalTheory.MemLoc.Core l) (β : Per.Bcris l) : GlobalTheory.BKGal.JumpDR.cB Td β = Td.eD.symm (C.ι β) := by
  have e0 := GlobalTheory.FundSeq.eq_core_of_isCrisDR Td.incl C
  rw [← e0]
  exact (Td.eD.symm_apply_apply _).symm

private theorem hcD {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (β : Per.BdRp l) : GlobalTheory.BKGal.JumpDR.cD Td β = Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) β) := rfl

private theorem hdR {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O) (b : Per.BdRp l) :
    dRO l O (o ⊗ₜ[ℤ_[l]] b) = o ⊗ₜ[ℤ_[l]] algebraMap (Per.BdRp l) (Per.BdR l) b := rfl

private theorem hio {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (o : O) (b : Per.Bcris l) :
    iotaO O C (o ⊗ₜ[ℤ_[l]] b) = o ⊗ₜ[ℤ_[l]] C.ι b := rfl

private theorem mainG {l : ℕ} [Fact l.Prime] {O M V : Type} [CommRing O] [Algebra ℤ_[l] O]
    [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup M] [Module O M]
    {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (s : O → V → V) (hs : ∀ o o' v, s (o * o') v = s o (s o' v)) (j : M → V)
    (Y : OB l O ⊗[O] M →+ V ⊗[ℚ_[l]] Pl.R.BdR)
    (hY : ∀ (o : O) (b : Per.Bcris l) (x : M), Y ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[O] x) = (s o (j x)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (act : OD l O →+ (V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR))
    (hact : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (s o v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (B : OdR l O →+ (V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR))
    (hB : ∀ (o : O) (b : Per.BdR l) (v : V) (c : Pl.R.BdR), B (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (s o v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c))
    (C : GlobalTheory.MemLoc.Core l) (b : OB l O) (y : OD l O) (hby : iotaO O C b = dRO l O y) (z : OB l O ⊗[O] M) :
    Y (b • z) = act y (Y z) := by
  have h1 : act y (Y z) = B (dRO l O y) (Y z) :=
    actDRG s (algebraMap (Per.BdRp l) (Per.BdR l))
      (GlobalTheory.BKGal.JumpDR.cD Td) Td.eD.symm (hcD Td) (AddMonoidHom.mk' (dRO l O) (map_add _))
      hdR act hact B hB y (Y z)
  have h2 : Y (b • z) = B (iotaO O C b) (Y z) :=
    actCrisG s hs j C.ι
      (GlobalTheory.BKGal.JumpDR.cB Td) Td.eD.symm (hcB Td C) (AddMonoidHom.mk' (iotaO O C) (map_add _))
      (hio C) Y hY B hB b z
  exact h2.trans (hby ▸ h1.symm)

theorem _root_.UpperTheory.KN.crysLattice_bdRPlus_action_compat :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (Y : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), Y ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) →
    ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)),
    (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) →
    ∀ (C : GlobalTheory.MemLoc.Core l) (b : OB l ↥(OL LL)) (y : OD l ↥(OL LL)), iotaO ↥(OL LL) C b = dRO l ↥(OL LL) y → ∀ z : TW (OB l ↥(OL LL)) T, Y (b • z) = act y (Y z) := by
  intro l _ LL T Pl AI Td Y hY act hact C b y hby z
  obtain ⟨B, hB⟩ := UpperTheory.KN.exists_tensorBdR_action_on_latticeBdR l LL T Pl AI Td
  exact mainG Td (fun (o : ↥(OL LL)) (v : T.V) => (o : ↥LL.1) • v)
    (fun o o' v => mul_smul (o : ↥LL.1) (o' : ↥LL.1) v) (fun x : ↥T.L.T => (x : T.V)) Y hY act hact B hB C b y hby z
end
