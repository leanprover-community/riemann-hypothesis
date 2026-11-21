import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionMulOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.UpperTheory.KN.inclL_eisensteinPow_phiInv_eq_single : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (i : ι), inclL (thetaW a LL) ϖ P (fun j => ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩)) = Pi.single i (inclO l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun _ => ⟨E ↥LL.1 l e ^ β, pow_mem (E_mem l e _) β⟩))) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P β hβ i
  ext i'
  rw [inclL_apply]
  simp only [Matrix.mulVec, dotProduct, ← ϖ.iW_of_mem (thetaW a LL) ↥LL.1, frobMat, Matrix.map_apply,
    Matrix.of_apply, ← map_mul, ← map_sum]
  simp only [Pi.single_apply]
  have key : ∀ i' i τ, ∑ j, P.mx τ i' j * (E ↥LL.1 l e ^ β * P.mxInv τ j i) =
      E ↥LL.1 l e ^ β * (1 : Matrix ι ι _) i' i := by
    intro i' i τ
    rw [← P.mx_mul_mxInv τ, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  split_ifs with h
  · subst h
    refine congrArg _ (funext fun τ => Subtype.ext ?_)
    rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    have h1 := key i' i' τ
    rw [Matrix.one_apply_eq, mul_one] at h1
    exact h1
  · have hz : ∀ F : ZMod a → invE l e (A ↥(OL LL) ↥LL.1), (∀ τ, ((F τ : invE l e (A ↥(OL LL) ↥LL.1)) : PowerSeries ↥LL.1) = 0) →
        ϖ.iW (thetaW a LL) ↥LL.1 F = 0 := fun F hF => by
      have hF0 : F = 0 := funext fun τ => Subtype.ext (hF τ)
      rw [hF0]
      exact map_zero _
    refine hz _ fun τ => ?_
    rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    have h1 := key i' i τ
    rw [Matrix.one_apply_ne h, mul_zero] at h1
    exact h1
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.crisComparison_ainf_eq_deRhamComparison :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (w : Ainf l), GlobalTheory.BKGal.JumpDR.cB Td (acrisToBcris l (ainfToAcris l w)) = GlobalTheory.BKGal.JumpDR.cD Td (ainfToBdRp l w) := by
  intro l _ Pl AI Td w
  refine Td.eD.injective ?_
  have h := GlobalTheory.CrisIncl.incl_aB l _ Td.incl w
  refine Eq.trans h ?_
  exact (Td.eD.apply_symm_apply _).symm
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem smul_abstract {Z O A B D M N : Type} [CommRing Z] [CommRing O] [CommRing A] [CommRing B]
    [CommRing D] [Algebra Z O] [Algebra Z A] [Algebra Z B] [Algebra Z D] [AddCommGroup M] [Module O M]
    [AddCommGroup N] (fB : O ⊗[Z] A →ₐ[O] O ⊗[Z] B) (fD : O ⊗[Z] A →ₐ[O] O ⊗[Z] D)
    (gB : A → B) (gD : A → D) (hB : ∀ o w, fB (o ⊗ₜ[Z] w) = o ⊗ₜ[Z] gB w)
    (hD : ∀ o w, fD (o ⊗ₜ[Z] w) = o ⊗ₜ[Z] gD w)
    (X : (O ⊗[Z] B) ⊗[O] M →+ N) (act : O ⊗[Z] D →+ (N →+ N))
    (h : ∀ (o o' : O) (w : A) (b : B) (x : M),
      X (((o * o') ⊗ₜ[Z] (gB w * b)) ⊗ₜ[O] x) = act (o ⊗ₜ[Z] gD w) (X ((o' ⊗ₜ[Z] b) ⊗ₜ[O] x)))
    (c : O ⊗[Z] A) (y : (O ⊗[Z] B) ⊗[O] M) : X (fB c • y) = act (fD c) (X y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' hc hc' => rw [map_add, add_smul, map_add, hc, hc', map_add, map_add, AddMonoidHom.add_apply]
  | tmul o w =>
    rw [hB, hD]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, map_add]
    | tmul r x =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add r r' hr hr' => rw [TensorProduct.add_tmul, smul_add, map_add, hr, hr', map_add, map_add]
      | tmul o' b =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, h]

theorem _root_.UpperTheory.KN.crisComparison_toB_smul_eq_deRham_act :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (c : OA l ↥(OL LL)) (y : TW (OB l ↥(OL LL)) T), X (toB l ↥(OL LL) c • y) = act (toOD l ↥(OL LL) c) (X y) := by
  intro l _ LL T Pl AI Td X hX act hact c y
  refine smul_abstract (toB l ↥(OL LL)) (toOD l ↥(OL LL)) (fun w => acrisToBcris l (ainfToAcris l w))
    (fun w => ainfToBdRp l w) (fun _ _ => rfl) (fun _ _ => rfl) X act (fun o o' w b x => ?_) c y
  refine (hX _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg (act _) (hX o' b x)).symm
  refine Eq.trans ?_ (hact _ _ _ _).symm
  have h1 : ((o * o' : ↥(OL LL)) : ↥LL.1) = (o : ↥LL.1) * (o' : ↥LL.1) := rfl
  rw [h1, mul_smul, map_mul, UpperTheory.KN.crisComparison_ainf_eq_deRhamComparison l Pl AI Td w]
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem sum_through_tensor_basis {O A B M V ι κ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup M] [Module O M] [AddCommGroup V] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : A →ₐ[O] B) (jB : (ι → B) ≃ₗ[B] B ⊗[O] M) (X : B ⊗[O] M →+ V) (F : A → V → V)
    (hF : ∀ (c : A) (y : B ⊗[O] M), X (f c • y) = F c (X y))
    (c : ι → A) (r : κ → A) (x : κ → M)
    (h : jB (fun i => f (c i)) = TensorProduct.map f.toLinearMap LinearMap.id (∑ k, r k ⊗ₜ[O] x k)) :
    ∑ j, F (c j) (X (jB (Pi.single j 1))) = ∑ k, F (r k) (X ((1 : B) ⊗ₜ[O] x k)) := by
  have e1 : (fun i => f (c i)) = ∑ j, f (c j) • (Pi.single j 1 : ι → B) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have e2 : TensorProduct.map f.toLinearMap LinearMap.id (∑ k, r k ⊗ₜ[O] x k) =
      ∑ k, f (r k) • ((1 : B) ⊗ₜ[O] x k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [TensorProduct.smul_tmul']
  rw [e1, e2, map_sum] at h
  have h2 := congrArg X h
  simp only [map_sum, map_smul, hF] at h2
  exact h2

theorem _root_.UpperTheory.KN.crisComparison_transfer_basis_coordinates :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (c : ι → OA l ↥(OL LL)) (r : κ → OA l ↥(OL LL)) (x : κ → ↥T.L.T), I.j (inclL (thetaW a LL) ϖ P c) = TWincl (inclO l ↥(OL LL)) T (∑ k, r k ⊗ₜ[↥(OL LL)] x k) → ∑ j, act (toOD l ↥(OL LL) (c j)) (X (jB (Pi.single j 1))) = ∑ k, act (toOD l ↥(OL LL) (r k)) (((x k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I jB Pl AI Td hcmp X hX act hact κ _ c r x h
  have hF := UpperTheory.KN.crisComparison_toB_smul_eq_deRham_act l LL T Pl AI Td X hX act hact
  have h1 := hcmp c _ h
  have h2 := sum_through_tensor_basis (toB l ↥(OL LL)) jB X (fun c v => act (toOD l ↥(OL LL) c) v) hF c r x h1
  refine h2.trans (Finset.sum_congr rfl fun k _ => ?_)
  have h3 : X ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x k) =
      ((x k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR) := by
    refine (hX 1 1 (x k)).trans ?_
    rw [map_one, OneMemClass.coe_one, one_smul]
  exact congrArg (fun v => act (toOD l ↥(OL LL) (r k)) v) h3
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.iTot_eisensteinPow_eq_iD_eisensteinHatPow :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (β : ℕ), toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun _ => ⟨E ↥LL.1 l e ^ β, pow_mem (E_mem l e _) β⟩)) = ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β := by
  intro l _ a e _ _ ϖ LL _ _ β
  refine (ϖ.iD_ofA (thetaW a LL) ↥LL.1 _).symm.trans ?_
  refine Eq.trans ?_ (map_pow (ϖ.iD (thetaW a LL) ↥LL.1) _ β)
  refine congrArg (ϖ.iD (thetaW a LL) ↥LL.1) ?_
  funext τ
  exact map_pow (ofA ↥(OL LL) ↥LL.1 l e) ⟨E ↥LL.1 l e, E_mem l e _⟩ β
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

private theorem tensor_inclusion_smul_sum {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]
    {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G ℚ_[l] K O) (s : R) {κ : Type} [Fintype κ] (r : κ → R) (x : κ → ↥T.L.T) :
    TWincl f T (∑ k, (s * r k) ⊗ₜ[O] x k) = f s • TWincl f T (∑ k, r k ⊗ₜ[O] x k) := by
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [TWincl, TensorProduct.smul_tmul']

private theorem ennreal_volume_ratio_step_cancel {R W ι : Type} [CommRing R] [AddCommGroup W] [Fintype ι] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w)
    (u : R) (hu : IsUnit u) (y z y' z' : ι → R) (v w : ι → W) (hy : ∀ j, y' j = u * y j)
    (hz : ∀ j, z' j = u * z j) (h : ∑ j, act (y' j) (v j) = ∑ k, act (z' k) (w k)) :
    ∑ j, act (y j) (v j) = ∑ k, act (z k) (w k) := by
  obtain ⟨u, rfl⟩ := hu
  have h2 := congrArg (act ((u⁻¹ : Rˣ) : R)) h
  simp only [map_sum, hy, hz, ← hmul, ← mul_assoc, Units.inv_mul, one_mul] at h2
  exact h2

private theorem tame_lattice_inclusion (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)
    (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (i : ι) (y : ι → OA l O) (s u : OA l O)
    (r : ι → OA l O) (x : ι → ↥T.L.T) (hI : inclL t ϖ P y = Pi.single i (inclO l O s))
    (hj : I.j (inclV l O ι (Pi.single i u)) = TWincl (inclO l O) T (∑ k, r k ⊗ₜ[O] x k)) :
    I.j (inclL t ϖ P (fun j => u * y j)) = TWincl (inclO l O) T (∑ k, (s * r k) ⊗ₜ[O] x k) := by
  have h1 : inclL t ϖ P (fun j => u * y j) = inclO l O s • inclV l O ι (Pi.single i u) := by
    have h2 : inclL t ϖ P (fun j => u * y j) = inclO l O u • inclL t ϖ P y := by
      rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
      congr 1
      funext j
      simp only [map_mul, Pi.smul_apply, smul_eq_mul]
    rw [h2, hI]
    funext j
    change inclO l O u * _ = inclO l O s * inclO l O ((Pi.single i u : ι → OA l O) j)
    by_cases hij : j = i
    · subst hij
      rw [Pi.single_eq_same, Pi.single_eq_same, mul_comm]
    · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, map_zero, mul_zero, mul_zero]
  rw [h1, I.j.map_smul, hj]
  exact (tensor_inclusion_smul_sum (inclO l O) T s r x).symm

private theorem cancel_unit_in_sum_action {A R W ι : Type} [CommRing A] [CommRing R] [AddCommGroup W] [Fintype ι]
    (f : A → R) (hf : ∀ x y, f (x * y) = f x * f y) (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w)
    (u s : A) (s' : R) (hs : f s = s') (hu : IsUnit (f u)) (y r : ι → A) (m : ι → R)
    (hr : ∀ k, f (r k) = f u * m k) (v w : ι → W)
    (h : ∑ j, act (f (u * y j)) (v j) = ∑ k, act (f (s * r k)) (w k)) :
    ∑ j, act (f (y j)) (v j) = ∑ k, act (s' * m k) (w k) :=
  ennreal_volume_ratio_step_cancel act hmul hone (f u) hu _ _ _ _ v w (fun j => hf _ _)
    (fun k => by rw [hf, hs, hr, mul_left_comm]) h

theorem _root_.UpperTheory.KN.crisComparison_image_eisensteinPow_phiInvColumns :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (b : Module.Basis ι ↥(OL LL) ↥T.L.T) (m : Matrix ι ι (OD l ↥(OL LL))) (u : OA l ↥(OL LL)) (r : ι → ι → OA l ↥(OL LL)), IsUnit (toOD l ↥(OL LL) u) → (∀ i, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T (∑ k, r i k ⊗ₜ[↥(OL LL)] b k)) → (∀ i k, toOD l ↥(OL LL) (r i k) = toOD l ↥(OL LL) u * m i k) → ∀ (β : ℕ) (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (i : ι), ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1))) = ∑ k, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β * m i k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I jB Pl AI Td hcmp X hX act hact b m u r hu hj hr β hβ i
  have hact' := GlobalTheory.BKGal.JumpDR.odAct_mul_one l LL T Pl AI Td act hact
  have hI := UpperTheory.KN.inclL_eisensteinPow_phiInv_eq_single l a e ϖ LL ι P β hβ i
  have hE := UpperTheory.KN.iTot_eisensteinPow_eq_iD_eisensteinHatPow l a e ϖ LL β
  have h3 := tame_lattice_inclusion l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I i _ _ u (r i) (fun k => b k) hI (hj i)
  have h4 := UpperTheory.KN.crisComparison_transfer_basis_coordinates l a e ϖ LL ι P T I jB Pl AI Td hcmp X hX act hact ι _ _ _ h3
  have h5 := cancel_unit_in_sum_action (toOD l ↥(OL LL)) (map_mul (toOD l ↥(OL LL))) act hact'.1 hact'.2 u _ _ hE hu _ (r i) (m i)
    (hr i) _ _ h4
  exact h5
end
