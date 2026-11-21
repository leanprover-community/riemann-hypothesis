import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBallQuotientEqSumMulFdeg
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijOnKerAndExactOfQuasiIsoBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CyclicIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularLocalRingAndRingKrullDimEqOfPolAV

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_cech_finite_vanishes_off_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → IsNoetherianRing R ∧ (∀ p, Module.Flat R ((cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D).X p)) ∧ (∀ p, Module.Finite R ((cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology p)) ∧ ∀ χ : R →+* K, (Spec.map (CommRingCat.ofHom χ) ≫ t) ≫ P.A.hom = 𝟙 _ → Spec.map (CommRingCat.ofHom χ) ≫ t ≠ η[P.A].left → ∀ p, ∃ r : R, χ r ≠ 0 ∧ ∀ z : (cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology p, r • z = 0 := by
  first | exact @GlobalTheory.MumfordSupport.cohomology_finite_and_vanishes_off_origin | exact GlobalTheory.MumfordSupport.cohomology_finite_and_vanishes_off_origin | (intros; apply GlobalTheory.MumfordSupport.cohomology_finite_and_vanishes_off_origin <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.MumfordAway

theorem subsingleton_of_points (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R]
    (s : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType s]
    (H : Type) [AddCommGroup H] [Module R H]
    (h : ∀ χ : R →+* K, Spec.map (CommRingCat.ofHom χ) ≫ s = 𝟙 _ →
      ∃ r : R, χ r ≠ 0 ∧ ∀ z : H, r • z = 0) : Subsingleton H := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hφ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [← Module.annihilator_eq_top_iff (R := R)]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨χ, rfl⟩ := GlobalTheory.PointSupport.exists_algHom_ker_eq K R M
  obtain ⟨r, hr, hz⟩ := h χ.toRingHom (by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext k
    exact χ.commutes k)
  exact hr (hle (Module.mem_annihilator.mpr hz))

theorem acyclic_away : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t → (∀ p q, t p ≠ η[P.A].left q) → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D).Acyclic := by
  intro K _ _ P R _ t Y π f hpb ht hne κ _ _ D hD hcov p
  obtain ⟨-, -, -, h⟩ := GlobalTheory.T.mumfordBundle_cech_finite_vanishes_off_origin K P R t Y π f hpb ht κ D hD hcov
  haveI := P.smoothDim
  haveI : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]
  refine subsingleton_of_points K R (t ≫ P.A.hom) _ fun χ hχ => h χ (by simpa using hχ) ?_ p
  intro e
  let q : Spec (CommRingCat.of K) := default
  refine hne (Spec.map (CommRingCat.ofHom χ) q) q ?_
  rw [← e]
  rfl

end GlobalTheory.MumfordAway
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.MumfordLocal

section Matrices

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

def vec {P : Type} [AddCommGroup P] [Module R P] {a : ℕ} (b : Module.Basis (Fin a) R P) :
    (Fin a → R') ≃ₗ[R'] R' ⊗[R] P :=
  (Algebra.TensorProduct.basis R' b).equivFun.symm

theorem vec_apply {P : Type} [AddCommGroup P] [Module R P] {a : ℕ} (b : Module.Basis (Fin a) R P)
    (v : Fin a → R') : vec b v = ∑ k, v k ⊗ₜ[R] b k := by
  simp [vec, TensorProduct.smul_tmul']

theorem vec_mulVec {P Q : Type} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] {a c : ℕ}
    (b : Module.Basis (Fin a) R P) (b' : Module.Basis (Fin c) R Q) (d : P →ₗ[R] Q) (v : Fin a → R') :
    vec b' (((LinearMap.toMatrix b b' d).map (algebraMap R R')).mulVec v) =
      d.baseChange R' (vec b v) := by
  rw [vec, LinearEquiv.symm_apply_eq, ← LinearMap.toMatrix_baseChange, Module.Basis.equivFun_apply,
    ← LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis R' b)]
  congr 1
  exact ((Algebra.TensorProduct.basis R' b).equivFun.apply_symm_apply v).symm

theorem coker_dualMap_equiv {P Q : Type} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {a c : ℕ} (b : Module.Basis (Fin a) R P) (b' : Module.Basis (Fin c) R Q) (d : P →ₗ[R] Q) :
    Nonempty ((Module.Dual R P ⧸ LinearMap.range d.dualMap) ≃ₗ[R]
      ((Fin a → R) ⧸ LinearMap.range (LinearMap.toMatrix b b' d).transpose.mulVecLin)) := by
  have h : ∀ ψ, b.dualBasis.equivFun (d.dualMap ψ) =
      (LinearMap.toMatrix b b' d).transpose.mulVecLin (b'.dualBasis.equivFun ψ) := fun ψ => by
    rw [← LinearMap.toMatrix_transpose, Matrix.mulVecLin_apply]
    exact (LinearMap.toMatrix_mulVec_repr b'.dualBasis b.dualBasis _ ψ).symm
  refine ⟨Submodule.Quotient.equiv _ _ b.dualBasis.equivFun ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
    exact ⟨_, (h ψ).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨ψ, rfl⟩ := b'.dualBasis.equivFun.surjective y
    exact ⟨_, ⟨ψ, rfl⟩, h ψ⟩

end Matrices

section Complex

variable {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {M : LB Y}
  {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → Y.Opens}
  {C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : C ⟶ cechLB f M D)

def loc (x : C.X 0) (p : κ × M.ι) : Γ(Y, (⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2) :=
  SecOnR.coord (f := f) (M := M) ((φ.f 0).hom x ⟨{p.1}, Finset.card_singleton _⟩) p.2

variable {R' : Type} [CommRing R'] [Algebra R R'] {Y' : Scheme.{0}} {π : Y' ⟶ Y}
  {f' : Y' ⟶ Spec (CommRingCat.of R')}

omit [Fintype κ] in

theorem cech_d (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (D : κ → Y.Opens) (p : ℕ) :
    ((cechLB f M D).d p (p + 1)).hom = Cube.d (secCube f M D) (p + 1) :=
  congrArg ModuleCat.Hom.hom (cechLB_d f M D p)

theorem exists_equiv_sec (hM : M.IsLB) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hφ : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    ∃ E : LinearMap.ker ((C.d 0 1).hom.baseChange R') ≃ LB.Sec (M.pull π), ∀ x s,
      SecOnR.of f' _ _ (GlobalTheory.LB.ofSec (E x) (⨅ i ∈ s.1, π ⁻¹ᵁ D i)) =
        secTermBaseChange M D H.w 1 ((φ.f 0).hom.baseChange R' x.1) s := by
  have hb := (bijOn_ker_and_exact_of_quasiIso_baseChange R R' C _ φ hφ).1
  have hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hc]; rfl
  have h₁ := secTermBaseChange_bijective hM H 1 fun s hs => hD s (Finset.card_pos.1 (by omega))
  have h₂ := secTermBaseChange_bijective hM H 2 fun s hs => hD s (Finset.card_pos.1 (by omega))
  rw [cech_d f M D 0] at hb
  have hk : ∀ y, secTermBaseChange M D H.w 1 y ∈
      LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom ↔
      y ∈ LinearMap.ker ((Cube.d (secCube f M D) 1).baseChange R') := fun y => by
    rw [cech_d f' _ _ 0]
    change Cube.d _ 1 _ = 0 ↔ _
    rw [d_secTermBaseChange]
    exact map_eq_zero_iff _ h₂.1
  let F : LinearMap.ker ((C.d 0 1).hom.baseChange R') →
      LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom := fun x =>
    ⟨secTermBaseChange M D H.w 1 ((φ.f 0).hom.baseChange R' x.1), (hk _).2 (hb.1 x.2)⟩
  have hF : Function.Bijective F := by
    refine ⟨fun x y h => Subtype.ext (hb.2.1 x.2 y.2 (h₁.1 (congrArg Subtype.val h))), fun z => ?_⟩
    obtain ⟨y, hy⟩ := h₁.2 z.1
    obtain ⟨x, hx, rfl⟩ := hb.2.2 ((hk y).1 (hy ▸ z.2))
    exact ⟨⟨x, hx⟩, Subtype.ext hy⟩
  refine ⟨(Equiv.ofBijective F hF).trans (CechOne.secKerEquiv (M.pull π) f' hc').toEquiv.symm,
    fun x s => ?_⟩
  refine (CechOne.secKerEquiv_val (M.pull π) f' hc' _ s).symm.trans ?_
  exact congrFun (congrArg Subtype.val
    ((CechOne.secKerEquiv (M.pull π) f' hc').apply_symm_apply (F x))) s

theorem exact_of_h1Zero (hM : M.IsLB) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hφ : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ))
    (h : FirstCohomologyVanishes (M.pull π)) :
    Function.Exact ((C.d 0 1).hom.baseChange R') ((C.d 1 2).hom.baseChange R') := by
  refine (bijOn_ker_and_exact_of_quasiIso_baseChange R R' C _ φ hφ).2 ?_
  have hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hc]; rfl
  have h₁ := secTermBaseChange_bijective hM H 1 fun s hs => hD s (Finset.card_pos.1 (by omega))
  have h₂ := secTermBaseChange_bijective hM H 2 fun s hs => hD s (Finset.card_pos.1 (by omega))
  have h₃ := secTermBaseChange_bijective hM H 3 fun s hs => hD s (Finset.card_pos.1 (by omega))
  have he := (cechComplex_exactAt_succ_iff _ 0).1
    (CechOne.exactAt_one_of_h1Zero f' (LB.isLB_pull hM π) hc' h)
  rw [cech_d f M D 0, cech_d f M D 1]
  intro y
  have e := he (secTermBaseChange M D H.w 2 y)
  erw [d_secTermBaseChange, map_eq_zero_iff _ h₃.1] at e
  refine e.trans ⟨fun ⟨z, hz⟩ => ?_, fun ⟨x, hx⟩ => ⟨secTermBaseChange M D H.w 1 x, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := h₁.2 z
    exact ⟨x, h₂.1 ((d_secTermBaseChange M D H.w 1 x).symm.trans hz)⟩
  · exact (d_secTermBaseChange M D H.w 1 x).trans (congrArg _ hx)

omit [Fintype κ] in

theorem coord_secTermBaseChange (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    {a : ℕ} (v : Fin a → R') (x : Fin a → C.X 0) (p : κ × M.ι)
    (h : π ⁻¹ᵁ ((⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2) ≤
      (⨅ l ∈ ({p.1} : Finset κ), π ⁻¹ᵁ D l) ⊓ (M.pull π).U fun _ => p.2) :
    rs Y' h (SecOnR.coord (f := f') (M := M.pull π) (secTermBaseChange M D w 1
      ((φ.f 0).hom.baseChange R' (∑ k, v k ⊗ₜ[R] x k)) ⟨{p.1}, Finset.card_singleton _⟩) fun _ => p.2) =
      ∑ k, cst f' _ (v k) * (π.app _).hom (loc φ (x k) p) := by
  let G : R' ⊗[R] C.X 0 →+ Γ(Y', π ⁻¹ᵁ ((⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2)) :=
    AddMonoidHom.mk' (fun z => rs Y' h (SecOnR.coord (f := f') (M := M.pull π) (secTermBaseChange M D w 1
      ((φ.f 0).hom.baseChange R' z) ⟨{p.1}, Finset.card_singleton _⟩) fun _ => p.2))
      fun z z' => by
        erw [map_add, map_add]
        exact map_add (rs Y' h) _ _
  refine (map_sum G _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  change rs Y' h (SecOnR.coord (f := f') (M := M.pull π) (v k • secCubePull M D w {p.1}
    ((φ.f 0).hom (x k) ⟨{p.1}, Finset.card_singleton _⟩)) fun _ => p.2) = _
  erw [SecOnR.coord_base_smul]
  rw [map_mul, rs_cst]
  congr 1
  refine (congrArg (rs Y' h) (SecOn.coord_pullLE π (preimage_biInf D π _).ge _ _)).trans ?_
  refine (GlobalTheory.LB.resG_appLE π _ _ _).trans ?_
  exact congrArg (fun q => q.hom (loc φ (x k) p)) (Scheme.Hom.app_eq_appLE π).symm

def perfOfBases (hM : M.IsLB) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i))
    (hφ : ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ))
    {a b c : ℕ} (b₀ : Module.Basis (Fin a) R (C.X 0)) (b₁ : Module.Basis (Fin b) R (C.X 1))
    (b₂ : Module.Basis (Fin c) R (C.X 2)) : Perf f M where
  a := a
  b := b
  c := c
  D₀ := LinearMap.toMatrix b₀ b₁ (C.d 0 1).hom
  D₁ := LinearMap.toMatrix b₁ b₂ (C.d 1 2).hom
  comp := by
    rw [← LinearMap.toMatrix_comp, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero, map_zero]
  I := κ × M.ι
  W p := (⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2
  ch p := p.2
  le _ := inf_le_right
  cover := by
    refine top_unique fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ y))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), CechOne.le_single D le_rfl hi, hj⟩
  u k := loc φ (b₀ k)
  sec R' _ g Y' π f' H := by
    letI := g.toAlgebra
    obtain ⟨E, hE⟩ := exists_equiv_sec φ hM hc hD H (hφ R')
    refine ⟨((vec b₀).toEquiv.subtypeEquiv fun v => ?_).trans E, fun v p => ?_⟩
    · rw [← (vec b₁).map_eq_zero_iff]
      exact (congrArg (· = 0) (vec_mulVec b₀ b₁ _ v)).to_iff
    · have h : π ⁻¹ᵁ ((⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2) ≤
          (⨅ l ∈ ({p.1} : Finset κ), π ⁻¹ᵁ D l) ⊓ (M.pull π).U fun _ => p.2 :=
        le_inf ((π.preimage_mono inf_le_left).trans (preimage_biInf D π _).le)
          (le_pull M π inf_le_right)
      refine Eq.trans ?_ (coord_secTermBaseChange φ H.w v.1 b₀ p h)
      rw [← vec_apply]
      exact (rs_rs _ h _).symm.trans (congrArg (fun z => rs Y' h (SecOnR.coord (f := f') (M := M.pull π) z fun _ => p.2))
        (hE _ ⟨{p.1}, Finset.card_singleton _⟩))
  exact R' _ g Y' π f' H h w hw := by
    letI := g.toAlgebra
    obtain ⟨x, hx⟩ := (exact_of_h1Zero φ hM hc hD H (hφ R') h (vec b₁ w)).1
      ((vec_mulVec b₁ b₂ _ w).symm.trans ((congrArg (vec b₂) hw).trans (map_zero _)))
    obtain ⟨v, rfl⟩ := (vec b₀).surjective x
    exact ⟨v, (vec b₁).injective ((vec_mulVec b₀ b₁ _ v).trans hx)⟩

end Complex

section Geometry

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)

theorem triv_of_origin (hL : L.IsLB) {X : Scheme.{0}} (q : X ⟶ (A ⊗ A).left) (s : X ⟶ S)
    (h : q ≫ (fst A A).left = s ≫ η[A].left) : Triv ((translDiff A L (𝟙 A)).pull q) := by
  refine (KerPow.pull_iff _ _ q).2 (KerPow.hasGen_of_trivial hL fun U _ g => ?_)
  let q' : Over.mk (q ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk q rfl
  have hs : s = q ≫ (A ⊗ A).hom := by
    have h₁ : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
    rw [← Over.w (fst A A), reassoc_of% h, h₁]
    exact (Category.comp_id _).symm
  have h₁ : q' ≫ fst A A = 1 := by
    apply Over.OverMorphism.ext
    refine h.trans ?_
    change s ≫ η[A].left = (toUnit (Over.mk (q ≫ (A ⊗ A).hom))).left ≫ η[A].left
    rw [hs, Over.toUnit_left]
    rfl
  have h₂ : q ≫ (lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left = q ≫ (snd A A).left := by
    change (q' ≫ lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left = (q' ≫ snd A A).left
    rw [comp_lift_assoc, Category.comp_id, h₁, ← Hom.mul_def, _root_.one_mul]
  rw [Fin.prod_univ_two]
  change g (q ≫ (lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left) ^ (1 : ℤ) *
    g (q ≫ (snd A A).left) ^ (-1 : ℤ) = 1
  rw [h₂, ← zpow_add]
  simp

theorem isPullback_whiskerRight {T : Over S} (x : T ⟶ A) :
    IsPullback (x ▷ A).left (fst T A).left (fst A A).left x.left := by
  have h₀ : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have h₁ : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
    (IsPullback.of_hasPullback T.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h₀
  · rw [← Over.comp_left, whiskerRight_snd, Over.w]
    exact h₁
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

theorem eq_origin_of_triv (hK : KTriv A L) {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ S}
    (x : Over.mk t ⟶ A) (h : Triv ((translDiff A L (𝟙 A)).pull (x ▷ A).left)) :
    x.left = t ≫ η[A].left := by
  have h₁ := (KerPow.pull_iff _ _ _).1 h
  have h₂ := hK R t x fun p => ⟨⊤, trivial, (KerPow.pull_iff _ _ _).2
    (h₁.pull ((fst (Over.mk t) A).left ⁻¹ᵁ ⊤).ι fun k => ?_)⟩
  · rw [h₂, Over.comp_left, Over.toUnit_left]
    rfl
  · congr 1
    fin_cases k
    · change (x ▷ A ≫ lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left =
        (lift (fst _ A ≫ x) (snd _ A) ≫ μ[A]).left
      rw [comp_lift_assoc, Category.comp_id, whiskerRight_fst, whiskerRight_snd]
    · change (x ▷ A ≫ snd A A).left = (snd _ A).left
      rw [whiskerRight_snd]

end Geometry

theorem coker_dualMap_equiv_residueField_of_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t₀ : Spec (CommRingCat.of R) ⟶ P.A.left) (χ₀ : R →+* K) (O : Type) [CommRing O] [IsLocalRing O] [Algebra R O] [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)] (t : Spec (CommRingCat.of O) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of O)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t₀ → Spec.map (CommRingCat.ofHom χ₀) ≫ t₀ = η[P.A].left → t = Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ t₀ → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (C : CochainComplex (ModuleCat.{0} O) ℕ) (φ : C ⟶ cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ p, Module.Free O (C.X p) ∧ Module.Finite O (C.X p)) → (∀ (R' : Type) [CommRing R'] [Algebra O R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap O R')).mapHomologicalComplex _).map φ)) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] IsLocalRing.ResidueField O) := by
  intro K _ _ P R _ t₀ χ₀ O _ _ _ _ _ t Y π f H ht₀ hχ ht κ _ _ D C φ hD hc hC hφ
  obtain ⟨-, hsep, -, hcl, hsurj, HA⟩ := (AbProj.abelian_projective_baseChange K P).2 O t Y π f H
  have hM : ((translDiff P.A P.L (𝟙 P.A)).pull π).IsLB := LB.isLB_pull (LB.isLB_linComb P.isLB _ _) π
  haveI : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  have hD' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) := fun s hs => by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton i => simpa using hD i
    | cons i s hi _ ih =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert]
      exact (hD i).inf ih
  haveI := fun p => (hC p).1
  haveI := fun p => (hC p).2
  let χ : O →+* K := IsLocalization.lift (M := (RingHom.ker χ₀).primeCompl) (g := χ₀)
    fun y => Ne.isUnit y.2
  have hχ₀ : χ.comp (algebraMap R O) = χ₀ := IsLocalization.lift_comp _
  have hm := IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker χ₀) O
  have hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker χ := by
    rw [← hm, Ideal.map_le_iff_le_comap, RingHom.comap_ker, hχ₀]
  have hloc : IsLocalHom χ := ⟨fun a ha => by
    by_contra h
    exact ha.ne_zero (hker h)⟩
  have horig : Spec.map (CommRingCat.ofHom χ) ≫ t = η[P.A].left := by
    rw [ht, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχ₀, hχ]
  have H₀ := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  have htriv : Triv (((translDiff P.A P.L (𝟙 P.A)).pull π).pull
      (pullback.fst f (Spec.map (CommRingCat.ofHom χ)))) :=
    CubeOpen.triv_pull_pull _ _ (triv_of_origin P.A P.L P.isLB _ (pullback.snd _ _) (by
      rw [Category.assoc, H.w, H₀.w_assoc, horig]))
  obtain ⟨I, ⟨e⟩, hI⟩ := UU.SecCyclic.cyclic_ideal O Y f _ hM
    (perfOfBases φ hM hc hD' hφ (Module.finBasis O _) (Module.finBasis O _) (Module.finBasis O _))
    hcl hsurj K χ hloc _ _ _ H₀
    (CubeOpen.bijective_appTop globalFns_holds P.A P.isAb (H₀.paste_horiz HA)) htriv
  have h₁ : I ≤ IsLocalRing.maximalIdeal O := ((hI K χ _ _ _ H₀).1 htriv).trans
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top χ))
  have h₂ : IsLocalRing.maximalIdeal O ≤ I := by
    let x : Over.mk ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ≫ P.A.hom) ⟶ P.A :=
      Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) rfl
    have Hx := isPullback_whiskerRight P.A x
    let π' := H.lift (x ▷ P.A).left
      ((fst _ P.A).left ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Hx.w.trans (Category.assoc _ _ _).symm)
    have hπ : π' ≫ π = (x ▷ P.A).left := H.lift_fst _ _ _
    have H' : IsPullback π' (fst _ P.A).left f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsPullback.of_right (by rw [hπ]; exact Hx) (H.lift_snd _ _ _) H
    have h₃ := (KerPow.pull_iff _ _ _).1 ((hI _ _ _ _ _ H').2 (Ideal.mk_ker (I := I)).ge)
    have h₄ := eq_origin_of_triv P.A P.L P.ktriv x (h₃.pull (𝟙 _) fun _ => by
      rw [Category.id_comp, hπ])
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ≫ P.A.hom)
    have h₅ : Spec.map (CommRingCat.ofHom (algebraMap R O) ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Spec.map (CommRingCat.ofHom χ₀ ≫ ψ) := by
      rw [← cancel_mono t₀, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, ← ht, hχ, hψ]
      exact h₄
    rw [← hm, Ideal.map_le_iff_le_comap]
    intro r hr
    have h₆ : Ideal.Quotient.mk I (algebraMap R O r) = ψ.hom (χ₀ r) :=
      congrArg (fun q => q.hom r) (Spec.map_injective h₅)
    rw [show χ₀ r = 0 from hr, map_zero] at h₆
    exact (Ideal.Quotient.eq_zero_iff_mem (I := I)).1 h₆
  obtain ⟨e'⟩ := coker_dualMap_equiv (Module.finBasis O (C.X 0)) (Module.finBasis O (C.X 1))
    (C.d 0 1).hom
  exact ⟨(e'.trans e).trans (Submodule.quotEquivOfEq _ _ (le_antisymm h₁ h₂))⟩

end GlobalTheory.MumfordLocal
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.OriginCohom

theorem nonempty_extendScalars_equiv {R : Type} (O : Type) [CommRing R] [CommRing O]
    [inst : Algebra R O] (M : ModuleCat.{0} R) :
    Nonempty ((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).obj M ≃ₗ[O] O ⊗[R] M) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* O, inst = φ.toAlgebra :=
    ⟨algebraMap R O, Algebra.algebra_ext _ _ fun _ => rfl⟩
  exact ⟨LinearEquiv.refl _ _⟩

theorem nonempty_homology_extendScalars_equiv {R : Type} (O : Type) [CommRing R] [CommRing O]
    [Algebra R O] [Module.Flat R O] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
      C).homology n ≃ₗ[O] O ⊗[R] C.homology n) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
  have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
  obtain ⟨e⟩ := nonempty_extendScalars_equiv O (C.homology n)
  exact ⟨((C.sc n).mapHomologyIso
    (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩

theorem finrank_homology (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (χ₀ : R →ₐ[K] K) (O : Type) [CommRing O] [Algebra R O]
    [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)] [IsRegularLocalRing O]
    (g : ℕ) (hg : ringKrullDim O = g) (C : CochainComplex (ModuleCat.{0} R) ℕ)
    (hz : ∀ p, g < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p))
    (hsupp : ∀ χ : R →ₐ[K] K, χ ≠ χ₀ → ∀ p, ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology p, r • z = 0)
    (C' : CochainComplex (ModuleCat.{0} O) ℕ)
    (e : ((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj C ≅ C')
    (hq : ∀ (E : CochainComplex (ModuleCat.{0} O) ℕ) (φ : E ⟶ C'),
      (∀ p, Module.Free O (E.X p) ∧ Module.Finite O (E.X p)) →
      (∀ (R' : Type) [CommRing R'] [Algebra O R'], QuasiIso
        (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap O R')).mapHomologicalComplex _).map φ)) →
      Nonempty ((Module.Dual O (E.X 0) ⧸ LinearMap.range (E.d 0 1).hom.dualMap) ≃ₗ[O]
        IsLocalRing.ResidueField O)) (n : ℕ) :
    Module.Finite K ((ModuleCat.restrictScalars (algebraMap K R)).obj (C.homology n)) ∧
      Module.finrank K ((ModuleCat.restrictScalars (algebraMap K R)).obj (C.homology n)) =
        if n = g then 1 else 0 := by
  have : Module.Flat R O := IsLocalization.flat O (RingHom.ker χ₀).primeCompl
  have hX (p : ℕ) : Nonempty (C'.X p ≃ₗ[O] O ⊗[R] C.X p) := by
    obtain ⟨e₁⟩ := nonempty_extendScalars_equiv O (C.X p)
    exact ⟨((HomologicalComplex.eval _ _ p).mapIso e.symm).toLinearEquiv ≪≫ₗ e₁⟩
  have hH (p : ℕ) : Nonempty (C'.homology p ≃ₗ[O] O ⊗[R] C.homology p) := by
    obtain ⟨e₁⟩ := nonempty_homology_extendScalars_equiv O C p
    exact ⟨(HomologicalComplex.homologyMapIso e.symm p).toLinearEquiv ≪≫ₗ e₁⟩
  obtain ⟨E, φ, hE0, hEfin, -, hEproj, hφ, -, hφ'⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} C' g
      (fun p hp => by
        obtain ⟨e₁⟩ := hX p
        have := ModuleCat.isZero_iff_subsingleton.1 (hz p hp)
        exact ModuleCat.isZero_iff_subsingleton.2 e₁.toEquiv.subsingleton)
      (fun p => by
        obtain ⟨e₁⟩ := hX p
        have := hflat p
        exact Module.Flat.of_linearEquiv e₁)
      (fun p => by
        obtain ⟨e₁⟩ := hH p
        have := hfin p
        exact Module.Finite.equiv e₁.symm)
  have hfree (p : ℕ) : Module.Free O (E.X p) ∧ Module.Finite O (E.X p) := by
    have := hEfin p
    have := hEproj p
    exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
  have hEH (p : ℕ) : Nonempty (E.homology p ≃ₗ[O] O ⊗[R] C.homology p) := by
    obtain ⟨e₁⟩ := hH p
    exact ⟨(asIso (HomologicalComplex.homologyMap φ p)).toLinearEquiv ≪≫ₗ e₁⟩
  have hlen (p : ℕ) :=
    letI : Module K (C.homology p) := Module.compHom _ (algebraMap K R)
    haveI : IsScalarTower K R (C.homology p) :=
      ⟨fun a r z => by rw [Algebra.smul_def, mul_smul]; rfl⟩
    haveI := hfin p
    PointSupport.finiteLength_and_finrank_eq_length K R χ₀ O (C.homology p)
      fun χ hχ => hsupp χ hχ p
  obtain ⟨h₁, h₂⟩ := homology_of_free_complex_of_isFiniteLength O g hg E hfree hE0
    (fun p => by
      obtain ⟨e₁⟩ := hEH p
      exact (hlen p).1.of_injective (f := e₁.toLinearMap) e₁.injective)
    (hq E φ hfree hφ')
  obtain ⟨e₁⟩ := hEH n
  obtain ⟨-, h₃, h₄⟩ := hlen n
  refine ⟨h₃, ?_⟩
  rw [← e₁.length_eq] at h₄
  split_ifs with hn
  · subst hn
    rw [h₂] at h₄
    exact_mod_cast h₄
  · have := ModuleCat.isZero_iff_subsingleton.1 (h₁ n hn)
    rw [Module.length_eq_zero] at h₄
    exact_mod_cast h₄

theorem nonempty_homology_restrictScalars_equiv {K R : Type} [CommRing K] [CommRing R]
    (a : K →+* R) {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R))
    (f₀ : Y ⟶ Spec (CommRingCat.of K)) (w : f₀ = f ≫ Spec.map (CommRingCat.ofHom a)) (M : LB Y)
    {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) (n : ℕ) :
    Nonempty ((cechLB f₀ M D).homology n ≃ₗ[K]
      (ModuleCat.restrictScalars a).obj ((cechLB f M D).homology n)) := by
  have hc (V : Y.Opens) (r : K) : cst f₀ V r = cst f V (a r) := by
    rw [← appLE_cst (π := 𝟙 Y) ((Category.id_comp f₀).trans w) (le_rfl : V ≤ 𝟙 Y ⁻¹ᵁ V) r]
    exact (rs_self le_rfl _).symm
  let e : secCube f₀ M D ≅ secCube f M D ⋙ ModuleCat.restrictScalars a :=
    Cube.isoMk (fun s =>
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun r x =>
          congrArg (fun u : Γ(Y, ⨅ i ∈ s, D i) => u • (id x : SecOn M (⨅ i ∈ s, D i)))
            (hc (⨅ i ∈ s, D i) r) }) fun _ _ => rfl
  exact ⟨(HomologicalComplex.homologyMapIso
    ((cechFunctor κ K).mapIso e ≪≫ (cechRestrictScalarsIso a (secCube f M D)).symm) n ≪≫
    ((cechLB f M D).sc n).mapHomologyIso (ModuleCat.restrictScalars a)).toLinearEquiv⟩

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem lbIso_pull_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : Y ⟶ X)
    (ψ : Z ⟶ Y) : LBIso ((L.pull φ).pull ψ) (L.pull (ψ ≫ φ)) :=
  LBIso.chartPull (chartPullLinComb L φ (fun _ : PUnit => ψ) (fun _ => ψ ≫ φ) (fun _ => 1) (𝟙 _)
    fun _ => (Category.id_comp _).symm) (chartPullId _)
    (PolBaseChange.lbIso_refl (pull_isLB hL _))

theorem finrank_cechLB_homology :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t → (∃ p q, t p = η[P.A].left q) → ∀ D : Fin (P.g + 1) → Y.Opens, (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, Module.Finite K ((cechLB (f ≫ t ≫ P.A.hom) ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology n) ∧ Module.finrank K ((cechLB (f ≫ t ≫ P.A.hom) ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology n) = if n = P.g then 1 else 0 := by
  intro K _ _ P R _ t Y π f H ht ⟨p, q, hpq⟩ D hD hc n
  have hsm : Smooth P.A.hom := P.isAb.smooth
  have hpr : IsProper P.A.hom := P.isAb.proper
  let φ : CommRingCat.of K ⟶ CommRingCat.of R := Spec.preimage (t ≫ P.A.hom)
  let _ : Algebra K R := φ.hom.toAlgebra
  have hφ : t ≫ P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap K R)) :=
    (Spec.map_preimage _).symm
  have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K R))) :=
    hφ ▸ inferInstance
  have : Algebra.FiniteType K R := RingHom.finiteType_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 hft)
  let o : Spec (CommRingCat.of K) ⟶ P.A.left := η[P.A].left
  have ho : o ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have hr : Set.range o ⊆ Set.range t := by
    rintro _ ⟨x, rfl⟩
    exact ⟨p, hpq.trans (congrArg o (Subsingleton.elim _ _))⟩
  let c : CommRingCat.of R ⟶ CommRingCat.of K := Spec.preimage (IsOpenImmersion.lift t o hr)
  have hco : Spec.map c ≫ t = o := by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hcφ : CommRingCat.ofHom (algebraMap K R) ≫ c = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hφ, ← Category.assoc, hco, ho, Spec.map_id]
  let χ₀ : R →ₐ[K] K := ⟨c.hom, fun r => congrArg (fun u => u.hom r) hcφ⟩
  have hmax : (RingHom.ker χ₀).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun r => ⟨algebraMap K R r, χ₀.commutes r⟩
  have hprime : (RingHom.ker c.hom).IsPrime := hmax.isPrime
  let O := Localization.AtPrime (RingHom.ker χ₀)
  have hloc : IsLocalization.AtPrime O (RingHom.ker c.hom) :=
    inferInstanceAs (IsLocalization.AtPrime O (RingHom.ker χ₀))
  obtain ⟨hreg, hdim⟩ :=
    isRegularLocalRing_and_ringKrullDim_eq_of_polAV K P R t (RingHom.ker χ₀) O ht
  obtain ⟨-, hflat, hfin, hsupp⟩ := MumfordSupport.cohomology_finite_and_vanishes_off_origin K P R t Y π f H ht _ D hD hc
  have hF : (translDiff P.A P.L (𝟙 P.A)).IsLB := LB.isLB_linComb P.isLB _ _
  have hsep₀ : IsSeparated (fst P.A P.A).left :=
    inferInstanceAs (IsSeparated (pullback.fst P.A.hom P.A.hom))
  have hsep : IsSeparated f := MorphismProperty.of_isPullback H hsep₀
  have : IsSeparated (terminal.from Y) := by
    rw [← terminal.comp_from f]
    infer_instance
  have hDs (s : Finset (Fin (P.g + 1))) (hs : s.Nonempty) : IsAffineOpen (⨅ i ∈ s, D i) :=
    IsAffineOpen.biInf _ (Finset.finite_toSet _) hs fun i _ => hD i
  let j := Spec.map (CommRingCat.ofHom (algebraMap R O))
  have H' := IsPullback.of_hasPullback f j
  obtain ⟨w, hw⟩ := lbIso_pull_pull_comp hF π (pullback.fst f j)
  let e := cechLBBaseChangeIso (LB.isLB_pull hF π) H' hDs ≪≫
    cechLBCongr _ _ (LB.isLB_pull (LB.isLB_pull hF π) _) (LB.isLB_pull hF _) w hw
  obtain ⟨h₁, h₂⟩ := finrank_homology K R χ₀ O P.g hdim _
    (fun p hp => isZero_cechLB_X _ _ _ (by rw [Fintype.card_fin]; exact hp)) hflat hfin
    (fun χ hχ => hsupp χ.toRingHom
      (by
        rw [Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext r
        exact χ.commutes r)
      (fun h => hχ (by
        have h' : CommRingCat.ofHom χ.toRingHom = c :=
          Spec.map_injective ((cancel_mono t).1 (h.trans hco.symm))
        ext r
        exact congrArg (fun u => u.hom r) h'))) _ e
    (fun E ψ hE hψ => GlobalTheory.MumfordLocal.coker_dualMap_equiv_residueField_of_origin K P R t c.hom O (j ≫ t) _ (pullback.fst f j ≫ π)
      (pullback.snd f j) (H'.paste_horiz H) ht hco rfl _ _ E ψ
      (fun i => isAffineOpen_preimage_of_isPullback H' (hD i))
      (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) hE hψ) n
  obtain ⟨e₀⟩ := nonempty_homology_restrictScalars_equiv (algebraMap K R) f (f ≫ t ≫ P.A.hom)
    (by rw [hφ]) ((translDiff P.A P.L (𝟙 P.A)).pull π) D n
  exact ⟨Module.Finite.equiv e₀.symm, e₀.finrank_eq.trans h₂⟩

end GlobalTheory.OriginCohom
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_mumfordBundle_cech_homology_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t → (∃ p q, t p = η[P.A].left q) → ∀ D : Fin (P.g + 1) → Y.Opens, (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, Module.Finite K ((cechLB (f ≫ t ≫ P.A.hom) ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology n) ∧ Module.finrank K ((cechLB (f ≫ t ≫ P.A.hom) ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology n) = if n = P.g then 1 else 0 := by
  first | exact @GlobalTheory.OriginCohom.finrank_cechLB_homology | exact GlobalTheory.OriginCohom.finrank_cechLB_homology | (intros; apply GlobalTheory.OriginCohom.finrank_cechLB_homology <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.MumfordCohom

theorem exists_cover_point (X : Scheme.{0}) [CompactSpace X] (o : X) (ho : IsClosed {o}) :
    ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      o ∈ V 0 ∧ ∀ j, j ≠ 0 → o ∉ V j := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hoV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ o) isOpen_univ
  have hc : IsCompact (V₀ : Set X)ᶜ := V₀.isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : {W : X.Opens // IsAffineOpen W ∧ o ∉ W} => (W.1 : Set X)) (fun W => W.1.isOpen) (by
      intro x hx
      have hx' : x ∈ ({o} : Set X)ᶜ := by
        rintro rfl
        exact hx hoV
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx' ho.isOpen_compl
      exact Set.mem_iUnion.2 ⟨⟨W, hW, fun h => hWo h rfl⟩, hxW⟩)
  refine ⟨s.card, Fin.cons V₀ fun j => (s.equivFin.symm j).1.1, fun j => ?_, ?_, hoV, fun j hj => ?_⟩
  · refine Fin.cases hV₀ (fun j => ?_) j
    exact (s.equivFin.symm j).1.2.1
  · refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hx : x ∈ V₀
    · exact ⟨0, hx⟩
    · obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 (hs hx)
      refine ⟨(s.equivFin ⟨W, hW⟩).succ, ?_⟩
      simpa using hxW
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hj
    exact (s.equivFin.symm j).1.2.2

theorem isAffineOpen_preimage_inf {X Y : Scheme.{0}} [X.IsSeparated] (g : Y ⟶ X) {D : X.Opens}
    (hD : IsAffineOpen D) {V : Y.Opens} (hV : IsAffineOpen V) : IsAffineOpen (g ⁻¹ᵁ D ⊓ V) := by
  have : IsAffine V := hV
  have : IsAffineHom (V.ι ≫ g) :=
    haveI : IsAffineHom ((V.ι ≫ g) ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  have h := (hD.preimage (V.ι ≫ g)).image_of_isOpenImmersion V.ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_comm] at h

theorem acyclic_cechLB_of_acyclic {R R' : Type} [CommRing R] [CommRing R'] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (f' : Y ⟶ Spec (CommRingCat.of R')) (M : LB Y) {κ : Type}
    [LinearOrder κ] (D : κ → Y.Opens) (h : (cechLB f M D).Acyclic) : (cechLB f' M D).Acyclic := by
  have e (p : ℕ) : (Cube.d (secCube f' M D) p : Cube.Term (secCube f' M D) p → _) =
      (Cube.d (secCube f M D) p : Cube.Term (secCube f M D) p → _) :=
    funext fun x => funext fun t => (Cube.d_apply (secCube f' M D) p x t).trans
      (Cube.d_apply (secCube f M D) p x t).symm
  intro n
  cases n with
  | zero =>
    have h₀ := h 0
    rw [cochainComplex_exactAt_zero_iff, cechLB_d _ _ _ 0] at h₀ ⊢
    exact (e 1).symm ▸ h₀
  | succ n =>
    have h₀ := (cechComplex_exactAt_succ_iff (secCube f M D) n).1 (h (n + 1))
    refine (cechComplex_exactAt_succ_iff (secCube f' M D) n).2 ?_
    rw [e, e]
    exact h₀

theorem nonempty_cech_sliceFst_iso {R : Type} [CommRing R] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) {κ₁ κ₂ : Type} [LinearOrder κ₁] [LinearOrder κ₂]
    (U : κ₁ → Y.Opens) (W : κ₂ → Y.Opens) (T : Finset κ₂) (O : Y.Opens) (hO : O = ⨅ j ∈ T, W j) :
    Nonempty (cechLB f M (fun i => U i ⊓ O) ≅ cechComplex (Cube.sliceFst
      (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) T)) := by
  subst hO
  have h₁ (s : Finset κ₁) : ⨅ u ∈ Cube.sumVertex s T, Sum.elim U W (ofLex u) ≤
      ⨅ i ∈ s, (U i ⊓ ⨅ j ∈ T, W j) :=
    le_iInf₂ fun i hi => le_inf
      (biInf_le (fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) (Cube.inl_mem_sumVertex.2 hi))
      (le_iInf₂ fun j hj =>
        biInf_le (fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) (Cube.inr_mem_sumVertex.2 hj))
  have h₂ (s : Finset κ₁) (hs : s.Nonempty) : ⨅ i ∈ s, (U i ⊓ ⨅ j ∈ T, W j) ≤
      ⨅ u ∈ Cube.sumVertex s T, Sum.elim U W (ofLex u) := by
    refine le_iInf₂ fun u hu => ?_
    rcases u with i | j
    · exact (biInf_le (fun i => U i ⊓ ⨅ j ∈ T, W j) (Cube.inl_mem_sumVertex.1 hu)).trans inf_le_left
    · obtain ⟨i, hi⟩ := hs
      exact (biInf_le (fun i => U i ⊓ ⨅ j ∈ T, W j) hi).trans
        (inf_le_right.trans (biInf_le W (Cube.inr_mem_sumVertex.1 hu)))
  let φ : secCube f M (fun i => U i ⊓ ⨅ j ∈ T, W j) ⟶ Cube.sliceFst
      (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)) T :=
    Cube.homMk (fun s => SecOnR.restrict f M (h₁ s)) fun {s t} _ x =>
      (SecOnR.restrict_restrict f _ (h₁ t) x).trans (SecOnR.restrict_restrict f (h₁ s) _ x).symm
  exact ⟨@asIso _ _ _ _ (cechComplexMap φ) (isIso_cechComplexMap φ fun s hs =>
    SecOnR.restrict_bijective f (h₁ s) (h₂ s hs))⟩

variable {K : Type} [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K)))

theorem over_affineOpen {V : P.A.left.Opens} (hV : IsAffineOpen V) {κ : Type} [LinearOrder κ]
    [Fintype κ] (D : κ → P.A.left.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (M : LB (P.A ⊗ P.A).left) (hM : M.IsLB) :
    (∀ i, IsAffineOpen ((snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V)) ∧
    ∃ (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec Γ(P.A.left, V)) (E : κ → Y.Opens),
      IsPullback π f (fst P.A P.A).left hV.fromSpec ∧ (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ ∧
      Nonempty (cechLB (f ≫ hV.fromSpec ≫ P.A.hom) (M.pull π) E ≅ cechLB (P.A ⊗ P.A).hom M
        fun i => (snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V) := by
  let π := pullback.fst (fst P.A P.A).left hV.fromSpec
  let f := pullback.snd (fst P.A P.A).left hV.fromSpec
  have H : IsPullback π f (fst P.A P.A).left hV.fromSpec := IsPullback.of_hasPullback _ _
  have H' := ((AbProj.abelian_projective_baseChange K P).2 Γ(P.A.left, V) hV.fromSpec _ π f H).2.2.2.2.2
  have hq : IsAffineHom (π ≫ (snd P.A P.A).left) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H'.flip inferInstance
  have hr : π.opensRange = (fst P.A P.A).left ⁻¹ᵁ V := by
    ext1
    rw [Scheme.Hom.coe_opensRange]
    erw [Scheme.Pullback.range_fst]
    rw [hV.range_fromSpec]
    rfl
  have hE (i : κ) : π ⁻¹ᵁ ((snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V) =
      (π ≫ (snd P.A P.A).left) ⁻¹ᵁ D i := by
    rw [← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq,
      Scheme.Hom.comp_preimage]
  have hA (i : κ) : IsAffineOpen ((π ≫ (snd P.A P.A).left) ⁻¹ᵁ D i) := (hD i).preimage _
  refine ⟨fun i => ?_, _, π, f,
    fun i => π ⁻¹ᵁ ((snd P.A P.A).left ⁻¹ᵁ D i ⊓ (fst P.A P.A).left ⁻¹ᵁ V), H,
    fun i => (congrArg IsAffineOpen (hE i)).mpr (hA i), ?_, ?_⟩
  · have h := (hA i).image_of_isOpenImmersion π
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm] at h
  · simp only [hE]
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  · have e : f ≫ hV.fromSpec ≫ P.A.hom = π ≫ (P.A ⊗ P.A).hom := by
      rw [← H.w_assoc, Over.w (fst P.A P.A)]
    rw [e]
    exact cechLB_pull_iso_of_isOpenImmersion K _ _ M _ π κ _ hM fun i => hr ▸ inf_le_right

theorem finrank_cechLB_translDiff : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (P.A ⊗ P.A).left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, Module.finrank K ((cechLB (P.A ⊗ P.A).hom (translDiff P.A P.L (𝟙 P.A)) D).homology n) = if n = P.g then 1 else 0 := by
  intro K _ _ P κ _ _ D hD hc n
  obtain ⟨B, hB, hBc⟩ := AffineCover.exists_cover
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    trdeg_eq_of_smoothOfRelativeDimension K P
  have hsep : IsSeparated P.A.hom := (AbProj.abelian_projective_baseChange K P).1.2
  have hpr : IsProper P.A.hom := P.isAb.proper
  have : P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from P.A.hom]
    infer_instance⟩
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  let q₀ : (𝟙_ (Over (Spec (CommRingCat.of K)))).left := IsLocalRing.closedPoint K
  have hq (q : (𝟙_ (Over (Spec (CommRingCat.of K)))).left) : q = q₀ :=
    Subsingleton.elim (α := PrimeSpectrum K) _ _
  have ho : IsClosed {η[P.A].left q₀} := by
    rw [← Set.image_singleton]
    refine η[P.A].left.isClosedEmbedding.isClosedMap _ ?_
    rw [show ({q₀} : Set _) = Set.univ from Set.eq_univ_of_forall hq]
    exact isClosed_univ
  obtain ⟨r, V, hV, hVc, hV₀, hV₁⟩ := exists_cover_point P.A.left _ ho
  have hM : (translDiff P.A P.L (𝟙 P.A)).IsLB := LB.isLB_linComb P.isLB _ _
  have hsep' : IsSeparated (P.A ⊗ P.A).hom := by
    rw [← Over.w (fst P.A P.A)]
    have : IsSeparated (fst P.A P.A).left :=
      inferInstanceAs (IsSeparated (pullback.fst P.A.hom P.A.hom))
    infer_instance
  obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ K _ (P.A ⊗ P.A).hom _ κ D _ (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) _
    (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) hM hsep' hD hc
    (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
    (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
    (fun i _ h => isAffineOpen_preimage_inf _ (hB i) h)
    (fun j _ h => isAffineOpen_preimage_inf _ (hV j) h)
    (fun i j => (over_affineOpen P (hV j) B hB hBc _ hM).1 i) n
  have e₂ := trunc₂HomologyIsoFstSingleton (0 : Fin (r + 1)) (secCube (P.A ⊗ P.A).hom
    (translDiff P.A P.L (𝟙 P.A)) fun u : Fin (P.g + 1) ⊕ₗ Fin (r + 1) =>
      Sum.elim (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) (ofLex u))
    (fun t ht ht' => by
      have hVt : IsAffineOpen (⨅ j ∈ t, V j) :=
        IsAffineOpen.biInf _ t.finite_toSet ht fun j _ => hV j
      obtain ⟨j, hj, hj₀⟩ : ∃ j ∈ t, j ≠ 0 := by
        by_contra! h
        exact ht' (Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨ht, h⟩)
      obtain ⟨-, Y, π, f, E, H, hE, hEc, ⟨i₁⟩⟩ := over_affineOpen P hVt B hB hBc _ hM
      obtain ⟨i₂⟩ := nonempty_cech_sliceFst_iso (P.A ⊗ P.A).hom (translDiff P.A P.L (𝟙 P.A))
        (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) t _
        (preimage_biInf V (fst P.A P.A).left t)
      have h := MumfordAway.acyclic_away K P Γ(P.A.left, ⨅ j ∈ t, V j) hVt.fromSpec Y π f H inferInstance
        (fun p q hpq => by
          have hp : hVt.fromSpec p ∈ (⨅ j ∈ t, V j : P.A.left.Opens) :=
            hVt.range_fromSpec.le ⟨p, rfl⟩
          rw [hpq, hq q] at hp
          exact hV₁ j hj₀ (biInf_le V hj hp)) _ E hE hEc
      exact fun m => (acyclic_cechLB_of_acyclic f _ _ E h m).of_iso (i₁ ≪≫ i₂)) n
  obtain ⟨-, Y, π, f, E, H, hE, hEc, ⟨i₁⟩⟩ := over_affineOpen P (hV 0) B hB hBc _ hM
  obtain ⟨i₂⟩ := nonempty_cech_sliceFst_iso (P.A ⊗ P.A).hom (translDiff P.A P.L (𝟙 P.A))
    (fun i => (snd P.A P.A).left ⁻¹ᵁ B i) (fun j => (fst P.A P.A).left ⁻¹ᵁ V j) {0}
    ((fst P.A P.A).left ⁻¹ᵁ V 0) (by simp)
  obtain ⟨p, hp⟩ := (hV 0).range_fromSpec.ge hV₀
  have h := (T.finrank_mumfordBundle_cech_homology_origin K P Γ(P.A.left, V 0) (hV 0).fromSpec Y π f H inferInstance ⟨p, q₀, hp⟩
    E hE hEc n).2
  rw [← h]
  exact (e₁ ≪≫ₗ (e₂ ≪≫ (HomologicalComplex.homologyMapIso (i₁ ≪≫ i₂) n).symm).toLinearEquiv).finrank_eq

end GlobalTheory.MumfordCohom
end
end
