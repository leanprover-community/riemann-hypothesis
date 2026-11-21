import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicPropertiesStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobeniusStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsMapAlgHomStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsConjInvariantStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.NilpotentTwistStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsUnitCharacterDiffAtChosenInertiaStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ContinuousUnitsInvOfContinuousCoeFiniteQpAlgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.TriangularRankThreeCrystallineAfterPush
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPowMemOfMulMemPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CrLocal

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem qcont_map {X V W : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup W]
    [Module ℚ_[l] W] (f : V →ₗ[ℚ_[l]] W) {c : X → V} (hc : QCont l c) : QCont l fun x => f (c x) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : ContinuousAdd W := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap f).comp hc

theorem qcont_add {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c d : X → V}
    (hc : QCont l c) (hd : QCont l d) : QCont l fun x => c x + d x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact Continuous.add hc hd

theorem qcont_sum {X V ι : Type} [Fintype ι] [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V] {c : ι → X → V}
    (hc : ∀ i, QCont l (c i)) : QCont l fun x => ∑ i, c i x := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact continuous_finset_sum _ fun i _ => hc i

theorem contAction_of_qcont {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V)
    (h : ∀ v, QCont l fun g => ρ g v) : ContAction ρ := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  have h' : ∀ v, Continuous fun g => ρ g v := fun v => by
    have := h v
    unfold QCont at this
    rwa [← eq_moduleTopology ℚ_[l] V] at this
  let b := Module.finBasis ℚ_[l] V
  have e : (fun p : G × V => ρ p.1 p.2) = fun p => ∑ i, b.coord i p.2 • ρ p.1 (b i) := by
    funext p
    conv_lhs => rw [← b.sum_repr p.2, map_sum]
    simp only [map_smul, Basis.coord_apply]
  unfold ReciprocityTheory.Gal.ContAction
  rw [e]
  exact continuous_finset_sum _ fun i _ =>
    ((IsModuleTopology.continuous_of_linearMap (b.coord i)).comp continuous_snd).smul ((h' _).comp continuous_fst)

theorem qcont_colRep {B : Type} [CommRing B] [Algebra ℚ_[l] B] (ρ : G →* GL (Fin 3) B)
    (h : ∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) (v : Fin 3 → B) :
    QCont l fun g => resCoef ℚ_[l] (colRep ρ) g v := by
  have e : (fun g => resCoef ℚ_[l] (colRep ρ) g v) = fun g => ∑ i, ∑ j,
      ((LinearMap.single ℚ_[l] (fun _ : Fin 3 => B) i).comp (LinearMap.mulRight ℚ_[l] (v j)))
        ((ρ g : Matrix (Fin 3) (Fin 3) B) i j) := by
    funext g
    ext k
    change (ρ g : Matrix (Fin 3) (Fin 3) B).mulVec v k = _
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [e]
  exact qcont_sum fun i => qcont_sum fun j => qcont_map _ (h i j)

variable [IsTopologicalGroup G] {φ : G →* GQ l}

theorem cr_sub (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (f : V →ₗ[ℚ_[l]] W) (hf : ∀ g x, f (ρ g x) = σ g (f x)) (hi : Function.Injective f) (h : IsCr φ σ) :
    IsCr φ ρ := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact ((isCrys_isDR_sub_quot φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ) f hf).1 hi).1 h

theorem cr_prod (hφ : IsOpenEmbedding φ) {V W : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] W] (ρ : Representation ℚ_[l] G V)
    (σ : Representation ℚ_[l] G W) (hρ : ∀ v, QCont l fun g => ρ g v) (hσ : ∀ v, QCont l fun g => σ g v)
    (h : IsCr φ ρ) (h' : IsCr φ σ) : IsCr φ (ρ.prod σ) := by
  letI := moduleTopology ℚ_[l] V
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  haveI : IsTopologicalAddGroup W := IsModuleTopology.topologicalAddGroup ℚ_[l] W
  exact (isCrys_isDR_prod φ hφ ρ σ (contAction_of_qcont ρ hρ) (contAction_of_qcont σ hσ)).1 h h'

theorem exists_cr_of_finset (hφ : IsOpenEmbedding φ) {V ι : Type} [AddCommGroup V] [Module ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (N : ι → Set V)
    (h : ∀ i, ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → x ∈ N i) (S : Finset ι) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℚ_[l] W) (_ : FiniteDimensional ℚ_[l] W)
      (σ : Representation ℚ_[l] G W) (f : V →ₗ[ℚ_[l]] W), (∀ v, QCont l fun g => σ g v) ∧ IsCr φ σ ∧
      (∀ g x, f (ρ g x) = σ g (f x)) ∧ ∀ x, f x = 0 → ∀ i ∈ S, x ∈ N i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, 0, fun v => ?_, ?_,
      fun _ _ => Subsingleton.elim _ _, by simp⟩
    · exact @continuous_const _ _ _ (moduleTopology ℚ_[l] PUnit) v
    · unfold IsCr
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton, mul_zero]
  | insert a S _ ih =>
    obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := ih
    obtain ⟨W', _, _, _, σ', f', h1', h2', h3', h4'⟩ := h a
    refine ⟨W × W', inferInstance, inferInstance, inferInstance, σ.prod σ', f.prod f', fun v => ?_,
      cr_prod hφ σ σ' h1 h1' h2 h2', fun g x => ?_, fun x hx i hi => ?_⟩
    · have := qcont_add (qcont_map (LinearMap.inl ℚ_[l] W W') (h1 v.1)) (qcont_map (LinearMap.inr ℚ_[l] W W') (h1' v.2))
      convert this using 2 with g
      ext <;> simp [Representation.prod]
    · ext <;> simp [Representation.prod, h3, h3']
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h4' x (congrArg Prod.snd hx)
      · exact h4 x (congrArg Prod.fst hx) i hi

theorem isCr_of_local : ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] (ρ : G →* GL (Fin 3) B), (∀ i j, QCont l fun g => (ρ g : Matrix (Fin 3) (Fin 3) B) i j) → (∀ (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra B B'] [IsScalarTower ℚ_[l] B B'], IsCr φ (colRep ((Matrix.GeneralLinearGroup.map (algebraMap B B')).comp ρ))) → IsCr φ (colRep ρ) := by
  intro l _ G _ _ _ φ hφ B _ _ _ ρ hc h
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  obtain ⟨W, _, _, _, σ, f, h1, h2, h3, h4⟩ := exists_cr_of_finset hφ (resCoef ℚ_[l] (colRep ρ))
    (fun m : MaximalSpectrum B => {v | ∀ i, algebraMap B (Localization.AtPrime m.asIdeal) (v i) = 0})
    (fun m => by
      let a : B →ₗ[ℚ_[l]] Localization.AtPrime m.asIdeal :=
        (IsScalarTower.toAlgHom ℚ_[l] B (Localization.AtPrime m.asIdeal)).toLinearMap
      haveI : Module.Finite ℚ_[l] (Localization.AtPrime m.asIdeal) :=
        Module.Finite.of_surjective a (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
      refine ⟨Fin 3 → Localization.AtPrime m.asIdeal, inferInstance, inferInstance, inferInstance,
        resCoef ℚ_[l] (colRep ((Matrix.GeneralLinearGroup.map
          (algebraMap B (Localization.AtPrime m.asIdeal))).comp ρ)), a.compLeft (Fin 3),
        qcont_colRep _ fun i j => qcont_map a (hc i j), h _, fun g x => ?_, fun x hx i => congrFun hx i⟩
      ext k
      exact RingHom.map_mulVec (algebraMap B (Localization.AtPrime m.asIdeal)) _ x k) Finset.univ
  refine cr_sub hφ (resCoef ℚ_[l] (colRep ρ)) σ (qcont_colRep ρ hc) h1 f h3 ?_ h2
  rw [injective_iff_map_eq_zero]
  intro x hx
  funext i
  exact eq_zero_of_localization _ fun J hJ => h4 x hx ⟨J, hJ⟩ (Finset.mem_univ _) i

end GlobalTheory.CrLocal
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.LCrConj

open TensorProduct

private theorem isCr_transfer {l : ℕ} [Fact l.Prime] {G A A' V V' : Type} [Group G] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [CommRing A']
    [Algebra ℚ_[l] A'] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V']
    (φ : G →* GQ l) (ρ : Representation A G V)
    (ρ' : Representation A' G V') (f : V ≃ₗ[ℚ_[l]] V') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) :
    IsCr φ ρ ↔ IsCr φ ρ' := by
  let F : V ⊗[ℚ_[l]] Bcr l ≃ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bcr l := TensorProduct.congr f (LinearEquiv.refl _ _)
  have hF : ∀ g x, F (actC φ (resCoef ℚ_[l] ρ) g x) = actC φ (resCoef ℚ_[l] ρ') g (F x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul v b => simp [F, actC, resCoef, hf]
  have hD : (Dcr φ (resCoef ℚ_[l] ρ)).map F.toLinearMap = Dcr φ (resCoef ℚ_[l] ρ') := by
    ext x
    obtain ⟨x, rfl⟩ := F.surjective x
    rw [Submodule.mem_map_equiv, F.symm_apply_apply]
    simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      ← hF, F.injective.eq_iff]
  unfold IsCr
  rw [← hD, LinearEquiv.finrank_map_eq, f.finrank_eq]

private theorem isCr_conjGL {l : ℕ} [Fact l.Prime] {G A : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] {n : ℕ}
    (φ : G →* GQ l) (r : G →* GL (Fin n) A) (h : GL (Fin n) A) :
    IsCr φ (colRep r) ↔ IsCr φ (colRep (conjGL h r)) :=
  isCr_transfer φ (colRep r) (colRep (conjGL h r))
    ((Matrix.toLinearEquiv' (h : Matrix (Fin n) (Fin n) A) h.invertible).restrictScalars ℚ_[l]) fun g x => by
      simp [colRep, conjGL, Matrix.toLinearEquiv', Matrix.mul_assoc]

private def glPart {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G) (r : G →* GG m R)
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem isLCr_iff' {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B] (r : GQ l →* GG 3 B)
    (h : ∀ g ∈ D.HL, (r g).right = 1) : D.IsLCr r ↔ IsCr D.HL.subtype (colRep (glPart D.HL r h)) := by
  refine ⟨fun ⟨ρ, h1, h2⟩ => ?_, fun h2 => ⟨_, fun _ => rfl, h2⟩⟩
  have : ρ = glPart D.HL r h := MonoidHom.ext h1
  exact this ▸ h2

end GlobalTheory.LCrConj

open GlobalTheory.LCrConj in

theorem GlobalTheory.LCrConj.main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG 3 B) (h : GL (Fin 3) B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → D.IsLCr (conjBy h r) → D.IsLCr r := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _ _ r h hm _ hc
  have h1 : ∀ g ∈ D.HL, (r g).right = 1 := fun g hg => (hm g).trans hg.1
  have hm' : HasMult D.η (conjBy h r) := fun g => (by simp [conjBy] : (conjBy h r g).right = (r g).right).trans (hm g)
  have h1' : ∀ g ∈ D.HL, (conjBy h r g).right = 1 := fun g hg => (hm' g).trans hg.1
  have he : glPart D.HL (conjBy h r) h1' = conjGL h (glPart D.HL r h1) := by
    ext g : 1
    have h2 : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by rw [map_inv]; rfl
    show (conjBy h r g).left = _
    rw [h2, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, h1 g g.2, mul_one, sgnAct_one,
      sgnAct_one]
    rfl
  rw [isLCr_iff' D r h1, isCr_conjGL _ _ h, ← he, ← isLCr_iff']
  exact hc
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLCrystalline_conjBy_invariant : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (r : GQ l →* GG 3 B) (h : GL (Fin 3) B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → D.IsLCr (conjBy h r) → D.IsLCr r := by
  atlas_forward_decl GlobalTheory.LCrConj.main
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

theorem isUnit_det_sub_smul_one_of_forall_not_isUnit {C : Type} [CommRing C] [IsLocalRing C]
    {n : Type} [Fintype n] [DecidableEq n] (Q : Matrix n n C) (hQ : ∀ i j, ¬ IsUnit (Q i j))
    (c : C) (hc : IsUnit c) : IsUnit (Q - c • (1 : Matrix n n C)).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hm : (IsLocalRing.residue C).mapMatrix (Q - c • (1 : Matrix n n C)) =
      (-(IsLocalRing.residue C c)) • (1 : Matrix n n _) := by
    ext i j
    have hq : IsLocalRing.residue C (Q i j) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (hQ i j))
    by_cases h : i = j
    · subst h; simp [hq]
    · simp [hq, h]
  rw [hm, Matrix.det_smul, Matrix.det_one, mul_one]
  refine pow_ne_zero _ (neg_ne_zero.2 ?_)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hc

theorem exists_GL_conj_eq_diagonal_of_charpoly_eq_prod :
    ∀ {C : Type} [CommRing C] [IsLocalRing C] (A : Matrix (Fin 3) (Fin 3) C) (p : Fin 3 → C),
      (∀ a b, a ≠ b → IsUnit (p a - p b)) → A.charpoly = ∏ a, (X - Polynomial.C (p a)) →
      ∃ h : GL (Fin 3) C, (h : Matrix (Fin 3) (Fin 3) C) * A *
        ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = Matrix.diagonal p := by
  intro C _ _ A p hp hchar
  classical
  set P : Fin 3 → C[X] := fun a => ∏ b ∈ Finset.univ.erase a, (X - Polynomial.C (p b)) with hPdef
  have hfull : ∀ a, (X - Polynomial.C (p a)) * P a = ∏ b, (X - Polynomial.C (p b)) := fun a =>
    Finset.mul_prod_erase _ (fun b => X - Polynomial.C (p b)) (Finset.mem_univ a)
  have hz : aeval A (∏ b, (X - Polynomial.C (p b))) = 0 := by
    rw [← hchar]; exact Matrix.aeval_self_charpoly A
  have hsplit : ∀ (f : C[X]) a, f = Polynomial.C (f.eval (p a)) +
      (X - Polynomial.C (p a)) * (f /ₘ (X - Polynomial.C (p a))) := by
    intro f a
    have h := modByMonic_add_div f (X - Polynomial.C (p a))
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact h.symm
  have key : ∀ (f : C[X]) a, aeval A (f * P a) = f.eval (p a) • aeval A (P a) := by
    intro f a
    conv_lhs => rw [hsplit f a]
    rw [add_mul, mul_comm (X - Polynomial.C (p a)), mul_assoc, hfull]
    simp only [map_add, map_mul, hz, mul_zero, add_zero, aeval_C, Algebra.smul_def]
  have hq : ∀ a, IsUnit ((P a).eval (p a)) := by
    intro a
    simp only [hPdef, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
      (fun b hb => hp a b (Finset.ne_of_mem_erase hb).symm)
  have hq0 : ∀ a b, a ≠ b → (P a).eval (p b) = 0 := by
    intro a b hab
    simp only [hPdef, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩) (sub_self _)
  have hBA : ∀ a, aeval A (P a) * A = p a • aeval A (P a) := by
    intro a
    have h := key X a
    rwa [mul_comm, map_mul, aeval_X, eval_X] at h
  have hBB : ∀ a b, aeval A (P a) * aeval A (P b) = (P a).eval (p b) • aeval A (P b) := by
    intro a b
    rw [← map_mul]
    exact key (P a) b
  have hex : ∀ a, ∃ i j, IsUnit (aeval A (P a) i j) := by
    intro a
    by_contra hne
    push_neg at hne
    obtain ⟨u, hu⟩ := hq a
    set E := ((u⁻¹ : Cˣ) : C) • aeval A (P a) with hE
    have hEn : ∀ i j, ¬ IsUnit (E i j) := by
      intro i j h
      apply hne i j
      have h' : aeval A (P a) i j = (u : C) * E i j := by
        rw [hE, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, Units.mul_inv, one_mul]
      rw [h']
      exact (Units.isUnit u).mul h
    have hEE : E * E = E := by
      rw [hE, Matrix.smul_mul, Matrix.mul_smul, hBB, ← hu, smul_smul, smul_smul,
        mul_assoc, Units.inv_mul, mul_one]
    have hdet := isUnit_det_sub_smul_one_of_forall_not_isUnit E hEn 1 isUnit_one
    rw [one_smul] at hdet
    have hE0 : E = 0 := by
      have h1 : (E - 1) * E = 0 := by rw [sub_mul, hEE, one_mul, sub_self]
      obtain ⟨w, hw⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
      calc E = ((w⁻¹ : (Matrix (Fin 3) (Fin 3) C)ˣ) : Matrix (Fin 3) (Fin 3) C) * ((E - 1) * E) := by
            rw [← mul_assoc, ← hw, Units.inv_mul, one_mul]
        _ = 0 := by rw [h1, mul_zero]
    have hB0 : aeval A (P a) = 0 := by
      have h' : aeval A (P a) = (u : C) • E := by rw [hE, smul_smul, Units.mul_inv, one_smul]
      rw [h', hE0, smul_zero]
    have hs := congrArg (aeval A) (hsplit (P a) a)
    rw [hB0, map_add, aeval_C, map_mul, ← hu] at hs
    have hinv : aeval A (X - Polynomial.C (p a)) *
        (-(((u⁻¹ : Cˣ) : C) • aeval A (P a /ₘ (X - Polynomial.C (p a))))) = 1 := by
      have h2 : aeval A (X - Polynomial.C (p a)) * aeval A (P a /ₘ (X - Polynomial.C (p a))) =
          -algebraMap C _ (u : C) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hs.symm
      rw [mul_neg, Matrix.mul_smul, h2, smul_neg, neg_neg, Algebra.smul_def, ← map_mul,
        Units.inv_mul, map_one]
    have hdx : IsUnit (aeval A (X - Polynomial.C (p a))).det :=
      IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hinv, Matrix.det_one])
    have hev : A.charpoly.eval (p a) = 0 := by
      rw [hchar, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
    rw [Matrix.eval_charpoly] at hev
    have hneg : Matrix.scalar (Fin 3) (p a) - A = -(aeval A (X - Polynomial.C (p a))) := by
      simp [Algebra.algebraMap_eq_smul_one, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [hneg, Matrix.det_neg] at hev
    have hu2 : IsUnit ((-1 : C) ^ Fintype.card (Fin 3) * (aeval A (X - Polynomial.C (p a))).det) :=
      ((isUnit_neg_one).pow _).mul hdx
    rw [hev] at hu2
    exact not_isUnit_zero hu2
  choose i j hij using hex
  let H : Matrix (Fin 3) (Fin 3) C := Matrix.of fun a k => aeval A (P a) (i a) k
  let Q : Matrix (Fin 3) (Fin 3) C := Matrix.of fun k b => aeval A (P b) k (j b)
  have hHQ : H * Q = Matrix.diagonal fun a => (P a).eval (p a) * aeval A (P a) (i a) (j a) := by
    ext a b
    have h' : (H * Q) a b = (aeval A (P a) * aeval A (P b)) (i a) (j b) := by
      simp [H, Q, Matrix.mul_apply]
    rw [h', hBB, Matrix.smul_apply, smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp
    · rw [hq0 a b hab, zero_mul, Matrix.diagonal_apply_ne _ hab]
  have hdetH : IsUnit H.det := by
    have h2 : IsUnit (H * Q).det := by
      rw [hHQ, Matrix.det_diagonal]
      exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one
        (fun a _ => (hq a).mul (hij a))
    rw [Matrix.det_mul] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hHA : H * A = Matrix.diagonal p * H := by
    ext a k
    have h' : (H * A) a k = (aeval A (P a) * A) (i a) k := by simp [H, Matrix.mul_apply]
    rw [h', hBA, Matrix.diagonal_mul]
    simp [H]
  have hU := (Matrix.isUnit_iff_isUnit_det H).2 hdetH
  refine ⟨hU.unit, ?_⟩
  rw [IsUnit.unit_spec, hHA, mul_assoc, hU.mul_val_inv, mul_one]

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalize_of_distinct_eigenvalues : ∀ {C : Type} [CommRing C] [IsLocalRing C] (A : Matrix (Fin 3) (Fin 3) C) (p : Fin 3 → C), (∀ a b, a ≠ b → IsUnit (p a - p b)) → A.charpoly = ∏ a, (X - Polynomial.C (p a)) → ∃ h : GL (Fin 3) C, (h : Matrix (Fin 3) (Fin 3) C) * A * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = Matrix.diagonal p := by
  atlas_forward_decl GlobalTheory.exists_GL_conj_eq_diagonal_of_charpoly_eq_prod
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory


end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.UpperTriCoord

variable {G B : Type} [Group G] [CommRing B]

theorem entry_mul (ρ : G →* GL (Fin 3) B) (g h : G) (i j : Fin 3) :
    (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) i j =
      ∑ k, (ρ g : Matrix (Fin 3) (Fin 3) B) i k * (ρ h : Matrix (Fin 3) (Fin 3) B) k j := by
  rw [map_mul, Units.val_mul, Matrix.mul_apply]

section Tri

variable (ρ : G →* GL (Fin 3) B) (hT : ∀ g i j, j < i → (ρ g : Matrix (Fin 3) (Fin 3) B) i j = 0)
include hT

theorem diag_mul (g h : G) (i : Fin 3) :
    (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) i i =
      (ρ g : Matrix (Fin 3) (Fin 3) B) i i * (ρ h : Matrix (Fin 3) (Fin 3) B) i i := by
  rw [entry_mul, Fin.sum_univ_three]
  fin_cases i
  · simp [hT h 1 0 (by decide), hT h 2 0 (by decide)]
  · simp [hT g 1 0 (by decide), hT h 2 1 (by decide)]
  · simp [hT g 2 0 (by decide), hT g 2 1 (by decide)]

def dg (i : Fin 3) : G →* Bˣ where
  toFun g := ⟨(ρ g : Matrix (Fin 3) (Fin 3) B) i i, (ρ g⁻¹ : Matrix (Fin 3) (Fin 3) B) i i,
    by rw [← diag_mul ρ hT, mul_inv_cancel, map_one]; simp,
    by rw [← diag_mul ρ hT, inv_mul_cancel, map_one]; simp⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; exact diag_mul ρ hT g h i

end Tri

end GlobalTheory.UpperTriCoord
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem conjBy_right_eq {G C : Type} [Group G] [CommRing C] (h : GL (Fin 3) C) (r : G →* GG 3 C) (g : G) :
    (conjBy h r g).right = (r g).right := by
  simp [conjBy, MulAut.conj_apply]


end GlobalTheory.OrdLoc

private theorem fin_eq_eI_or_wI_or_esI {C : Type} [CommRing C] (p q : Fin 3 → C)
    (hp : ∀ a b, a ≠ b → IsUnit (p a - p b)) (N : Matrix (Fin 3) (Fin 3) C)
    (h0 : (N - Matrix.scalar (Fin 3) (q 0)) * (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 1)) *
      (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 2)) = 0)
    (h1 : (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 0)) * (N - Matrix.scalar (Fin 3) (q 1)) *
      (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 2)) = 0)
    (h2 : (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 0)) * (Matrix.diagonal p - Matrix.scalar (Fin 3) (p 1)) *
      (N - Matrix.scalar (Fin 3) (q 2)) = 0) :
    N 1 0 = 0 ∧ N 2 0 = 0 ∧ N 2 1 = 0 ∧ N 0 0 = q 0 ∧ N 1 1 = q 1 ∧ N 2 2 = q 2 := by
  have e : ∀ c, Matrix.diagonal p - Matrix.scalar (Fin 3) c = Matrix.diagonal (fun i => p i - c) := by
    intro c
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  simp only [e] at h0 h1 h2
  have u01 := hp 0 1 (by decide)
  have u02 := hp 0 2 (by decide)
  have u10 := hp 1 0 (by decide)
  have u12 := hp 1 2 (by decide)
  have u20 := hp 2 0 (by decide)
  have u21 := hp 2 1 (by decide)
  have a10 := congrFun (congrFun h0 1) 0
  have a20 := congrFun (congrFun h0 2) 0
  have a00 := congrFun (congrFun h0 0) 0
  have b21 := congrFun (congrFun h1 2) 1
  have b11 := congrFun (congrFun h1 1) 1
  have c22 := congrFun (congrFun h2 2) 2
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul] at a10 a20 a00 b21 b11 c22
  have k : ∀ {x a b : C}, IsUnit a → IsUnit b → x * a * b = 0 → x = 0 := by
    intro x a b ha hb h
    rw [mul_assoc] at h
    exact (ha.mul hb).mul_left_eq_zero.mp h
  rw [mul_comm (p 2 - p 0)] at b21
  rw [mul_comm (p 1 - p 0)] at b11
  rw [mul_comm] at c22
  refine ⟨k u01 u02 a10, k u01 u02 a20, k u20 u12 b21, sub_eq_zero.mp (k u01 u02 a00),
    sub_eq_zero.mp (k u10 u12 b11), sub_eq_zero.mp ((u20.mul u21).mul_left_eq_zero.mp c22)⟩

private theorem exists_isUnit_det_apply_eq_sum_of_mem_Nof {C : Type} [CommRing C] (p : Fin 3 → C)
    (hp : ∀ a b, a ≠ b → IsUnit (p a - p b)) (M T : Matrix (Fin 3) (Fin 3) C)
    (hT : T 1 0 = 0 ∧ T 2 0 = 0 ∧ T 2 1 = 0 ∧ T 0 0 = p 0 ∧ T 1 1 = p 1 ∧ T 2 2 = p 2)
    (h : T * M = M * Matrix.diagonal p) : M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 := by
  obtain ⟨t10, t20, t21, t00, t11, t22⟩ := hT
  have e20 := congrFun (congrFun h 2) 0
  have e10 := congrFun (congrFun h 1) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_diagonal, t10, t20, t21, t00, t11, t22] at e20 e10 e21
  have m20 : M 2 0 = 0 := by
    have : (p 2 - p 0) * M 2 0 = 0 := by linear_combination e20
    exact (hp 2 0 (by decide)).mul_right_eq_zero.mp this
  have m10 : M 1 0 = 0 := by
    have : (p 1 - p 0) * M 1 0 = 0 := by linear_combination e10 - T 1 2 * m20
    exact (hp 1 0 (by decide)).mul_right_eq_zero.mp this
  have m21 : M 2 1 = 0 := by
    have : (p 2 - p 1) * M 2 1 = 0 := by linear_combination e21
    exact (hp 2 1 (by decide)).mul_right_eq_zero.mp this
  exact ⟨m10, m20, m21⟩

private theorem upperTriangular_fin_three_mul_entries {C : Type} [CommRing C] (A B : Matrix (Fin 3) (Fin 3) C)
    (hA : A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0) (hB : B 1 0 = 0 ∧ B 2 0 = 0 ∧ B 2 1 = 0) :
    (∀ i, (A * B) i i = A i i * B i i) ∧ (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
      (A * B) 1 2 = A 1 1 * B 1 2 + A 1 2 * B 2 2 ∧
      (A * B) 0 2 = A 0 0 * B 0 2 + A 0 1 * B 1 2 + A 0 2 * B 2 2 := by
  obtain ⟨a10, a20, a21⟩ := hA
  obtain ⟨b10, b20, b21⟩ := hB
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, a10, a20, a21, b10, b20, b21]

open GlobalTheory.OrdLoc in

theorem GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (r : GQ l →* GG 3 B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ → ∃ (h : GL (Fin 3) B) (ρ : ↥D.HL →* GL (Fin 3) B) (κ : Fin 3 → ↥D.HL →* Bˣ) (x y z : ↥D.HL → B), (∀ g, ρ g = (conjBy h r g).left) ∧ (∀ i, Continuous fun g => (κ i g : B)) ∧ (∀ g : ↥D.HL, (g : GQ l) ∈ Iq l → ∀ i, κ i g = cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i)) ∧ Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ x ∈ Z1 (chRep (κ 0 / κ 1)) ∧ y ∈ Z1 (chRep (κ 1 / κ 2)) ∧ ∀ hσ : GlobalTheory.OrdLoc.fr D ∈ D.HL, (∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 0 = v * (((κ 0 / κ 1) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B))) ∧ ∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 1 = v * (((κ 1 / κ 2) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B)) := by
  intro l _ O _ _ _ _ _ _ _ D B _ _ _ _ _ _ _ _ _ _ _ r hmult hcont hbot
  obtain ⟨hHLn, -, -, hPsi, hS0⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  obtain ⟨hsHL, hsIq, -⟩ := hS0
  obtain ⟨hpu, hcc⟩ := GlobalTheory.T.isUnit_characterDiff_at_chosenInertia D B
  set p : Fin 3 → B := fun a => algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0) with hp_def
  have hchar : (r D.s0).mat.charpoly = ∏ a : Fin 3, (X - Polynomial.C (p a)) := by
    rw [← sub_eq_zero]
    ext i
    have hm : ((r D.s0).mat.charpoly - ∏ a : Fin 3, (X - Polynomial.C (p a))).coeff i ∈
        GlobalTheory.OrdLoc.ordIdeal D r :=
      Ideal.subset_span (Set.mem_union_left _ ⟨D.s0, ⟨hsHL, hsIq⟩, i, rfl⟩)
    rw [hbot, Ideal.mem_bot] at hm
    simpa using hm
  obtain ⟨h, hh⟩ := GlobalTheory.T.diagonalize_of_distinct_eigenvalues (r D.s0).mat p hpu hchar
  have hright : ∀ g ∈ D.HL, (r g).right = 1 := by
    intro g hg
    rw [hmult g]
    have := (Subgroup.mem_inf.mp hg).1
    simpa using this
  set r' := conjBy h r with hr'_def
  have hright' : ∀ g ∈ D.HL, (r' g).right = 1 := by
    intro g hg
    rw [hr'_def, GlobalTheory.OrdLoc.conjBy_right_eq]
    exact hright g hg
  have hmat : ∀ g ∈ D.HL, (r' g).mat = (h : Matrix (Fin 3) (Fin 3) B) * (r g).mat * ((h⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) :=
    fun g hg => GlobalTheory.OrdLoc.conjBy_mat h r g (hright g hg)
  have hs0' : (r' D.s0).mat = Matrix.diagonal p := by rw [hmat _ hsHL, hh]
  have hbot' : GlobalTheory.OrdLoc.ordIdeal D r' = ⊥ := by rw [(GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant D r h hmult).1, hbot]
  have hsh : ∀ s : Fin 3 → GQ l, (∀ a, s a ∈ D.HL ⊓ Iq l) →
      D.sh r' 0 (s 0) * D.sh r' 1 (s 1) * D.sh r' 2 (s 2) = 0 := by
    intro s hs
    ext i j
    have hm : (D.sh r' 0 (s 0) * D.sh r' 1 (s 1) * D.sh r' 2 (s 2)) i j ∈ GlobalTheory.OrdLoc.ordIdeal D r' :=
      Ideal.subset_span (Set.mem_union_right _ ⟨s, hs, i, j, rfl⟩)
    rw [hbot', Ideal.mem_bot] at hm
    simpa using hm
  have hs0I : D.s0 ∈ D.HL ⊓ Iq l := ⟨hsHL, hsIq⟩
  have htriI : ∀ t ∈ D.HL ⊓ Iq l, (r' t).mat 1 0 = 0 ∧ (r' t).mat 2 0 = 0 ∧ (r' t).mat 2 1 = 0 ∧
      (r' t).mat 0 0 = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 0 t) ∧
      (r' t).mat 1 1 = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 1 t) ∧
      (r' t).mat 2 2 = algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ 2 t) := by
    intro t ht
    apply fin_eq_eI_or_wI_or_esI p (fun a => algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a t)) hpu
    · have := hsh ![t, D.s0, D.s0] (by intro a; fin_cases a <;> simpa)
      simpa [UpperTheory.V.Loc.Dat3.sh, hs0'] using this
    · have := hsh ![D.s0, t, D.s0] (by intro a; fin_cases a <;> simpa)
      simpa [UpperTheory.V.Loc.Dat3.sh, hs0'] using this
    · have := hsh ![D.s0, D.s0, t] (by intro a; fin_cases a <;> simpa)
      simpa [UpperTheory.V.Loc.Dat3.sh, hs0'] using this
  have hmm : ∀ x y : GG 3 B, x.right = 1 → (x * y).mat = x.mat * y.mat := by
    intro x y hx
    simp [UpperTheory.V.U3.GG.mat, SemidirectProduct.mul_left, hx]
  have hpsiconj : ∀ g a, UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (g * D.s0 * g⁻¹) = UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a D.s0 := by
    intro g a
    simp [UpperTheory.V.UnitaryThreeInertia.psi, mul_inv_cancel_comm]
  have htri : ∀ g ∈ D.HL, (r' g).mat 1 0 = 0 ∧ (r' g).mat 2 0 = 0 ∧ (r' g).mat 2 1 = 0 := by
    intro g hg
    have ht : g * D.s0 * g⁻¹ ∈ D.HL ⊓ Iq l :=
      ⟨hHLn.conj_mem _ hsHL g, (UpperTheory.V.Loc.iqBasic l).1.conj_mem _ hsIq g⟩
    obtain ⟨a, b, c, d, e, f⟩ := htriI _ ht
    apply exists_isUnit_det_apply_eq_sum_of_mem_Nof p hpu (r' g).mat (r' (g * D.s0 * g⁻¹)).mat
    · refine ⟨a, b, c, ?_, ?_, ?_⟩
      · rw [d, hpsiconj]
      · rw [e, hpsiconj]
      · rw [f, hpsiconj]
    · rw [← hs0', ← hmm _ _ (hright' _ ht.1), ← hmm _ _ (hright' _ hg), ← map_mul, ← map_mul]
      rw [show g * D.s0 * g⁻¹ * g = g * D.s0 by group]
  have hc : ∀ a b, Continuous fun g : GQ l => (r g).mat a b := by
    intro a b
    have := hcont a b
    unfold UpperTheory.V.Loc.QCont at this
    rwa [← eq_moduleTopology ℚ_[l] B] at this
  have hMc : ∀ i j, Continuous fun g : ↥D.HL => (r' (g : GQ l)).mat i j := by
    intro i j
    have e : (fun g : ↥D.HL => (r' (g : GQ l)).mat i j) = fun g : ↥D.HL =>
        ((h : Matrix (Fin 3) (Fin 3) B) * (r (g : GQ l)).mat *
          ((h⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) i j := by
      funext g
      rw [hmat g g.2]
    rw [e]
    have hr : Continuous fun g : GQ l => (r g).mat := continuous_matrix fun a b => hc a b
    exact ((continuous_const.matrix_mul (hr.comp continuous_subtype_val)).matrix_mul
      continuous_const).matrix_elem i j
  have hmulHL : ∀ a b : ↥D.HL, (r' ((a * b : ↥D.HL) : GQ l)).mat = (r' a).mat * (r' b).mat := by
    intro a b
    rw [Subgroup.coe_mul, map_mul, hmm _ _ (hright' _ a.2)]
  have hinv1 : ∀ a : ↥D.HL, (r' a).mat * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat = 1 := by
    intro a
    rw [← hmulHL, mul_inv_cancel]
    simp [UpperTheory.V.U3.GG.mat]
  have hdiag : ∀ (a b : ↥D.HL) i,
      (r' ((a * b : ↥D.HL) : GQ l)).mat i i = (r' a).mat i i * (r' b).mat i i := by
    intro a b i
    rw [hmulHL]
    exact (upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ b.2)).1 i
  have hunit : ∀ (a : ↥D.HL) i, (r' a).mat i i * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat i i = 1 := by
    intro a i
    rw [← (upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ (a⁻¹).2)).1 i, hinv1]
    simp
  have hunit' : ∀ (a : ↥D.HL) i, (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat i i * (r' a).mat i i = 1 := by
    intro a i
    rw [mul_comm]
    exact hunit a i
  let κ : Fin 3 → ↥D.HL →* Bˣ := fun i => MonoidHom.mk'
    (fun g => ⟨(r' g).mat i i, (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat i i, hunit g i, hunit' g i⟩)
    (fun a b => by
      ext
      simp only [Units.val_mul]
      exact hdiag a b i)
  let ρ : ↥D.HL →* GL (Fin 3) B := MonoidHom.mk' (fun g => (r' g).left) (fun a b => by
    rw [Subgroup.coe_mul, map_mul, SemidirectProduct.mul_left, hright' _ a.2, map_one]
    rfl)
  have hκ : ∀ i (g : ↥D.HL), ((κ i g : Bˣ) : B) = (r' g).mat i i := fun i g => rfl
  have hq : ∀ (i j : Fin 3) (a : ↥D.HL), (((κ i / κ j) a : Bˣ) : B) =
      (r' a).mat i i * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat j j := by
    intro i j a
    rw [MonoidHom.div_apply, div_eq_mul_inv, Units.val_mul]
    rfl
  have hcyc : ∀ s, Units.map (algebraMap O B : O →* B) (cycA l l O s) = cycA l l B s := by
    intro s
    ext
    simp [UpperTheory.V.Loc.cycA, ← IsScalarTower.algebraMap_apply]
  refine ⟨h, ρ, κ, fun g => (r' g).mat 0 1 * (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat 1 1,
    fun g => (r' g).mat 1 2 * (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat 2 2,
    fun g => (r' g).mat 0 2 * (r' ((g⁻¹ : ↥D.HL) : GQ l)).mat 2 2,
    fun g => rfl, fun i => hMc i i, ?_, (hMc 0 2).mul ((hMc 2 2).comp continuous_inv), ?_, ?_, ?_, ?_⟩
  · intro g hgI i
    obtain ⟨-, -, -, d0, d1, d2⟩ := htriI _ ⟨g.2, hgI⟩
    have key : ∀ i, algebraMap O B (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ i g) =
        ((cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i) : Bˣ) : B) := by
      intro i
      rw [UpperTheory.V.UnitaryThreeInertia.psi, hPsi _ g.2 hgI, ← hcyc, ← map_zpow, Units.coe_map, zpow_mul, zpow_natCast]
      rfl
    ext
    fin_cases i
    · exact d0.trans (key 0)
    · exact d1.trans (key 1)
    · exact d2.trans (key 2)
  · intro g
    obtain ⟨t10, t20, t21⟩ := htri _ g.2
    have u1 := hunit g 1
    have u2 := hunit g 2
    change (r' (g : GQ l)).mat = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperTheory.V.Loc.triM, hκ, t10, t20, t21] at u1 u2 ⊢
    all_goals first
      | linear_combination -(r' (g : GQ l)).mat 0 1 * u1
      | linear_combination -(r' (g : GQ l)).mat 0 2 * u2
      | linear_combination -(r' (g : GQ l)).mat 1 2 * u2
  · refine ⟨(hMc 0 1).mul ((hMc 1 1).comp continuous_inv), fun a b => ?_⟩
    dsimp only
    rw [UpperTheory.V.Loc.chRep_apply, hq, mul_inv_rev, hmulHL, hmulHL]
    obtain ⟨-, e01, -, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ b.2)
    obtain ⟨dB, -, -, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ (b⁻¹).2) (htri _ (a⁻¹).2)
    rw [e01, dB 1]
    linear_combination ((r' a).mat 0 1 * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat 1 1) * hunit b 1
  · refine ⟨(hMc 1 2).mul ((hMc 2 2).comp continuous_inv), fun a b => ?_⟩
    dsimp only
    rw [UpperTheory.V.Loc.chRep_apply, hq, mul_inv_rev, hmulHL, hmulHL]
    obtain ⟨-, -, e12, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ a.2) (htri _ b.2)
    obtain ⟨dB, -, -, -⟩ := upperTriangular_fin_three_mul_entries _ _ (htri _ (b⁻¹).2) (htri _ (a⁻¹).2)
    rw [e12, dB 2]
    linear_combination ((r' a).mat 1 2 * (r' ((a⁻¹ : ↥D.HL) : GQ l)).mat 2 2) * hunit b 2
  · intro hσ
    have hdd : ∀ a, D.dd r a = D.dd r' a := fun a => ((GlobalTheory.T.ordinaryIdeal_saturators_conj_invariant D r h hmult).2.1 a).symm
    have hdiag' := GlobalTheory.T.ordinary_derivative_entry_formula D r' hs0'
    have hc' : algebraMap O B ((cycA l l O (GlobalTheory.OrdLoc.fr D) : Oˣ) : O) =
        ((cycA l l B (GlobalTheory.OrdLoc.fr D) : Bˣ) : B) := by
      rw [← hcyc]
      rfl
    have u1 := hunit ⟨_, hσ⟩ 1
    have u2 := hunit ⟨_, hσ⟩ 2
    refine ⟨⟨(hcc 0).unit * (hcc 1).unit * κ 1 ⟨_, hσ⟩, ?_⟩, ⟨(hcc 1).unit * (hcc 2).unit * κ 2 ⟨_, hσ⟩, ?_⟩⟩
    · rw [hdd, hdiag' 0, hq, Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hκ, ← hc']
      simp only [map_mul]
      have e01 : (0 : Fin 3) + 1 = 1 := rfl
      rw [e01]
      linear_combination (-(algebraMap O B (D.cc 0) * algebraMap O B (D.cc 1) *
        (r' (GlobalTheory.OrdLoc.fr D)).mat 0 0)) * u1
    · rw [hdd, hdiag' 1, hq, Units.val_mul, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hκ, ← hc']
      simp only [map_mul]
      have e12 : (1 : Fin 3) + 1 = 2 := rfl
      rw [e12]
      linear_combination (-(algebraMap O B (D.cc 1) * algebraMap O B (D.cc 2) *
        (r' (GlobalTheory.OrdLoc.fr D)).mat 1 1)) * u2
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_conj_of_ordIdeal_eq_bot : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (r : GQ l →* GG 3 B), HasMult D.η r → (∀ a b, QCont l fun g => (r g).mat a b) → GlobalTheory.OrdLoc.ordIdeal D r = ⊥ → ∃ (h : GL (Fin 3) B) (ρ : ↥D.HL →* GL (Fin 3) B) (κ : Fin 3 → ↥D.HL →* Bˣ) (x y z : ↥D.HL → B), (∀ g, ρ g = (conjBy h r g).left) ∧ (∀ i, Continuous fun g => (κ i g : B)) ∧ (∀ g : ↥D.HL, (g : GQ l) ∈ Iq l → ∀ i, κ i g = cycA l l B (g : GQ l) ^ ((D.e : ℤ) * wt1 i)) ∧ Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ x ∈ Z1 (chRep (κ 0 / κ 1)) ∧ y ∈ Z1 (chRep (κ 1 / κ 2)) ∧ ∀ hσ : GlobalTheory.OrdLoc.fr D ∈ D.HL, (∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 0 = v * (((κ 0 / κ 1) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B))) ∧ ∃ v : Bˣ, GlobalTheory.OrdLoc.dd D r 1 = v * (((κ 1 / κ 2) ⟨_, hσ⟩ : Bˣ) - (cycA l l B (GlobalTheory.OrdLoc.fr D) : B)) := by
  atlas_forward_decl GlobalTheory.OrdLoc.triangular_of_ordIdeal_eq_bot
end

section
namespace GlobalTheory

theorem exists_pow_mem_of_mul_mem_pow :
    ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (m : Ideal A) (δ : A),
      (∀ a, δ * a = 0 → a = 0) → ∀ j : ℕ, ∃ k : ℕ, j ≤ k ∧ ∀ a, δ * a ∈ m ^ k → a ∈ m ^ j :=
  _root_.UpperTheory.Reformulated.B.Qg1.exists_pow_mem_of_mul_mem_pow

end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_le_mem_pow_of_mul_mem_pow_of_nonZeroDivisor : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (m : Ideal A) (δ : A), (∀ a, δ * a = 0 → a = 0) → ∀ j : ℕ, ∃ k : ℕ, j ≤ k ∧ ∀ a, δ * a ∈ m ^ k → a ∈ m ^ j := by
  atlas_forward_decl GlobalTheory.exists_pow_mem_of_mul_mem_pow
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_quotient_maximal_pow : ∀ {K A : Type} [Field K] [CommRing A] [Algebra K A] [IsNoetherianRing A] (m : Ideal A), Module.Finite K (A ⧸ m) → ∀ k : ℕ, Module.Finite K (A ⧸ m ^ k) := by
  intro K A _ _ _ _ m hm k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, Ideal.one_eq_top]
    infer_instance
  have hle : m ^ k ≤ m := Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hk)
  let f : (A ⧸ m ^ k) →ₐ[K] A ⧸ m := Ideal.Quotient.factorₐ K hle
  have hsurj : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  refine Module.finite_of_surjective_of_ker_le_nilradical f hsurj ?_ ?_
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ m := by
      rw [RingHom.mem_ker] at hx
      have : Ideal.Quotient.mk m a = 0 := hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    refine ⟨k, ?_⟩
    rw [← map_pow, Ideal.zero_eq_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow ha k
  · exact IsNoetherian.noetherian _
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.ThickenSaturated

theorem isLocalRing_quot_pow {A : Type} [CommRing A] (m : Ideal A) [hm : m.IsMaximal] (k : ℕ)
    (hk : k ≠ 0) : IsLocalRing (A ⧸ m ^ k) := by
  have hne : m ^ k ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk))
  haveI : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (A ⧸ m ^ k)
  have key : ∀ M : Ideal (A ⧸ m ^ k), M.IsMaximal → M.comap (Ideal.Quotient.mk (m ^ k)) = m := by
    intro M hM
    have h1 : (M.comap (Ideal.Quotient.mk (m ^ k))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : m ^ k ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact M.zero_mem
    have h3 : m ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := h1.isPrime.le_of_pow_le h2
    exact (hm.eq_of_le h1.ne_top h3).symm
  exact IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM =>
    Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      ((key M hM).trans (key M0 hM0).symm)⟩

theorem core {K : Type} [Field K] {A : Type} [CommRing A] [IsNoetherianRing A] [Algebra K A]
    (δ : A) (hδ : ∀ a, δ * a = 0 → a = 0)
    {B : Type} [CommRing B] [IsLocalRing B] [Algebra K B] [Module.Finite K B] (g : A →ₐ[K] B) :
    ∃ I : Ideal A, IsLocalRing (A ⧸ I) ∧ Module.Finite K (A ⧸ I) ∧ I ≤ RingHom.ker g ∧
      ∀ a, δ * a ∈ I → g a = 0 := by
  set mB := IsLocalRing.maximalIdeal B with hmB
  set m : Ideal A := mB.comap (g : A →+* B) with hm
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨n, hn⟩ : IsNilpotent mB := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  have hj : m ^ (n + 1) ≤ RingHom.ker g := by
    intro x hx
    have h1 : x ∈ (mB ^ (n + 1)).comap (g : A →+* B) := Ideal.le_comap_pow _ _ hx
    rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Ideal.mem_comap, Ideal.mem_bot] at h1
    exact RingHom.mem_ker.2 h1
  obtain ⟨k, hjk, hk⟩ := GlobalTheory.T.exists_le_mem_pow_of_mul_mem_pow_of_nonZeroDivisor m δ hδ (n + 1)
  haveI : m.IsPrime := Ideal.comap_isPrime _ _
  have hinj : Function.Injective (Ideal.quotientMapₐ mB g le_rfl : A ⧸ m →ₐ[K] B ⧸ mB) :=
    Ideal.quotientMap_injective
  haveI : Module.Finite K (B ⧸ mB) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K mB).toLinearMap Ideal.Quotient.mk_surjective
  haveI hfin : Module.Finite K (A ⧸ m) := Module.Finite.of_injective (Ideal.quotientMapₐ mB g le_rfl : A ⧸ m →ₐ[K] B ⧸ mB).toLinearMap hinj
  haveI : IsArtinianRing (A ⧸ m) := IsArtinianRing.of_finite K (A ⧸ m)
  haveI : m.IsMaximal := Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  refine ⟨m ^ k, isLocalRing_quot_pow m k (by omega), GlobalTheory.T.module_finite_quotient_maximal_pow m hfin k,
    (Ideal.pow_le_pow_right hjk).trans hj, fun a ha => ?_⟩
  exact RingHom.mem_ker.1 (hj (hk a ha))

theorem main : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (J : Ideal R) (d : R), (l : R) ∣ d → (∀ a, d * a ∈ J → a ∈ J) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B), J ≤ RingHom.ker f → ∃ (B' : Type) (_ : CommRing B') (_ : IsLocalRing B') (_ : Algebra ℚ_[l] B') (_ : Module.Finite ℚ_[l] B') (_ : Algebra O B') (_ : Algebra ℤ_[l] B') (_ : IsScalarTower ℤ_[l] O B') (_ : IsScalarTower ℤ_[l] ℚ_[l] B') (f' : R →ₐ[O] B') (q : B' →ₐ[ℚ_[l]] B), J ≤ RingHom.ker f' ∧ (∀ a, q (f' a) = f a) ∧ ∀ b, f' d * b = 0 → q b = 0 := by
  intro l hl O _ _ R _ _ _ J d _ hdJ B _ _ _ _ _ _ _ _ f hJf
  let x : R ⧸ J := Ideal.Quotient.mk J (l : R)
  let A := Localization.Away x
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (Submonoid.powers x) A inferInstance
  have hlA : IsUnit ((l : ℕ) : A) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := A) x
    simpa [x, map_natCast] using this
  let ψ₀ : ℤ_[l] →+* A := (algebraMap O A).comp (algebraMap ℤ_[l] O)
  have hψ₀ : ∀ y : nonZeroDivisors ℤ_[l], IsUnit (ψ₀ y) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    show IsUnit (ψ₀ y)
    rw [PadicInt.unitCoeff_spec hy0, map_mul, map_pow, map_natCast]
    exact ((Units.isUnit _).map ψ₀).mul (hlA.pow _)
  let ψ : ℚ_[l] →+* A := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) hψ₀
  letI algQA : Algebra ℚ_[l] A := ψ.toAlgebra
  let g₀ : R ⧸ J →+* B := Ideal.Quotient.lift J f.toRingHom (fun a ha => RingHom.mem_ker.1 (hJf ha))
  have hu : IsUnit (g₀ x) := by
    have h1 : g₀ x = algebraMap ℚ_[l] B (l : ℚ_[l]) := by
      simp [g₀, x, map_natCast]
    rw [h1]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hl.out.ne_zero)).map _
  let g : A →+* B := IsLocalization.Away.lift x hu
  have hg : ∀ w, g (algebraMap (R ⧸ J) A w) = g₀ w := fun w => IsLocalization.Away.lift_eq x hu w
  have hgO : ∀ z : O, g (algebraMap O A z) = algebraMap O B z := by
    intro z
    rw [IsScalarTower.algebraMap_apply O (R ⧸ J) A, hg]
    exact f.commutes z
  have hgψ : g.comp ψ = algebraMap ℚ_[l] B := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) ?_
    ext y
    simp only [RingHom.comp_apply, ψ, IsLocalization.lift_eq, ψ₀, hgO]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let gK : A →ₐ[ℚ_[l]] B := { g with commutes' := fun r => RingHom.congr_fun hgψ r }
  let δ : A := algebraMap (R ⧸ J) A (Ideal.Quotient.mk J d)
  have hδ : ∀ a, δ * a = 0 → a = 0 := by
    intro a ha
    obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) a
    change δ * IsLocalization.mk' A w s = 0 at ha
    change IsLocalization.mk' A w s = 0
    have e : δ = IsLocalization.mk' A (Ideal.Quotient.mk J d) (1 : Submonoid.powers x) :=
      (IsLocalization.mk'_one A _).symm
    rw [e, ← IsLocalization.mk'_mul, one_mul, IsLocalization.mk'_eq_zero_iff] at ha
    obtain ⟨c, hc⟩ := ha
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨c, ?_⟩
    obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (c : R ⧸ J)
    rw [← hc', ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hc
    rw [← hc', ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    apply hdJ
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  obtain ⟨I, hloc, hfin, hIker, hI⟩ := core δ hδ gK
  letI algZ : Algebra ℤ_[l] (A ⧸ I) := ((algebraMap ℚ_[l] (A ⧸ I)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  have tZO : IsScalarTower ℤ_[l] O (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun y => by
    show Ideal.Quotient.mk I (ψ (algebraMap ℤ_[l] ℚ_[l] y)) = Ideal.Quotient.mk I (algebraMap O A (algebraMap ℤ_[l] O y))
    rw [IsLocalization.lift_eq]
    rfl
  have tZQ : IsScalarTower ℤ_[l] ℚ_[l] (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f' : R →ₐ[O] A ⧸ I := (Ideal.Quotient.mkₐ O I).comp
    ((IsScalarTower.toAlgHom O (R ⧸ J) A).comp (Ideal.Quotient.mkₐ O J))
  have hf' : ∀ a, f' a = Ideal.Quotient.mk I (algebraMap (R ⧸ J) A (Ideal.Quotient.mk J a)) := fun _ => rfl
  let q : A ⧸ I →ₐ[ℚ_[l]] B := Ideal.Quotient.liftₐ I gK (fun a ha => RingHom.mem_ker.1 (hIker ha))
  have hq : ∀ a, q (Ideal.Quotient.mk I a) = g a := fun _ => rfl
  refine ⟨A ⧸ I, inferInstance, hloc, inferInstance, hfin, inferInstance, algZ, tZO, tZQ, f', q, ?_, ?_, ?_⟩
  · intro a ha
    rw [RingHom.mem_ker, hf', Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero, map_zero]
  · intro a
    rw [hf', hq, hg]
    rfl
  · intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hf', ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hb
    rw [hq]
    exact hI a hb

end GlobalTheory.ThickenSaturated
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_local_lift_of_saturated_ideal : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (J : Ideal R) (d : R), (l : R) ∣ d → (∀ a, d * a ∈ J → a ∈ J) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B), J ≤ RingHom.ker f → ∃ (B' : Type) (_ : CommRing B') (_ : IsLocalRing B') (_ : Algebra ℚ_[l] B') (_ : Module.Finite ℚ_[l] B') (_ : Algebra O B') (_ : Algebra ℤ_[l] B') (_ : IsScalarTower ℤ_[l] O B') (_ : IsScalarTower ℤ_[l] ℚ_[l] B') (f' : R →ₐ[O] B') (q : B' →ₐ[ℚ_[l]] B), J ≤ RingHom.ker f' ∧ (∀ a, q (f' a) = f a) ∧ ∀ b, f' d * b = 0 → q b = 0 := by
  intro l _ O _ _ R _ _ _ J d _ hreg B _ _ _ _ _ _ _ _ f hJf
  classical
  let M0 : Ideal R := (IsLocalRing.maximalIdeal B).comap f
  let RM := Localization.AtPrime M0
  have hgu : ∀ y : M0.primeCompl, IsUnit ((f : R →+* B) (y : R)) := by
    intro y
    have hy := Ideal.mem_primeCompl_iff.1 y.2
    by_contra h
    exact hy (show (y : R) ∈ M0 from (IsLocalRing.mem_maximalIdeal _).2 h)
  let g : RM →+* B := IsLocalization.lift (M := M0.primeCompl) (S := RM) (g := (f : R →+* B)) hgu
  have hg : ∀ r : R, g (algebraMap R RM r) = f r := fun r => IsLocalization.lift_eq hgu r
  let α : O →+* RM := (algebraMap R RM).comp (algebraMap O R)
  let ψ : ℤ_[l] →+* RM := α.comp (algebraMap ℤ_[l] O)
  have hfψ : ∀ y : ℤ_[l], g (ψ y) = algebraMap ℚ_[l] B (algebraMap ℤ_[l] ℚ_[l] y) := by
    intro y
    show g (algebraMap R RM (algebraMap O R (algebraMap ℤ_[l] O y))) = _
    rw [hg, f.commutes, ← IsScalarTower.algebraMap_apply ℤ_[l] O B y,
      ← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B y]
  have hψu : ∀ y : nonZeroDivisors ℤ_[l], IsUnit (ψ y) := by
    intro y
    have hy0 : algebraMap ℤ_[l] ℚ_[l] y ≠ 0 := by
      intro h
      exact nonZeroDivisors.coe_ne_zero y
        ((IsFractionRing.injective ℤ_[l] ℚ_[l]) (h.trans (map_zero _).symm))
    have hr : IsUnit (f (algebraMap O R (algebraMap ℤ_[l] O y))) := by
      rw [← hg]
      have := (isUnit_iff_ne_zero.2 hy0).map (algebraMap ℚ_[l] B)
      rw [← hfψ y] at this
      exact this
    exact (IsLocalization.AtPrime.isUnit_to_map_iff RM M0 _).2
      (Ideal.mem_primeCompl_iff.2 (fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) hr))
  let φ : ℚ_[l] →+* RM := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) (S := ℚ_[l]) hψu
  have hφ : ∀ y : ℤ_[l], φ (algebraMap ℤ_[l] ℚ_[l] y) = ψ y := fun y => IsLocalization.lift_eq hψu y
  have hgφ : g.comp φ = algebraMap ℚ_[l] B := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l])
    ext y
    simp only [RingHom.comp_apply, hφ, hfψ]
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  obtain ⟨N0, hN0⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).1 this
  have hmaxg : ∀ x ∈ IsLocalRing.maximalIdeal RM ^ N0, g x = 0 := by
    intro x hx
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M0 RM, ← Ideal.map_pow] at hx
    have hle : Ideal.map (algebraMap R RM) (M0 ^ N0) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hg]
      have h1 : f r ∈ (M0 ^ N0).map f := Ideal.mem_map_of_mem f hr
      rw [Ideal.map_pow] at h1
      have h2 : (M0.map f) ^ N0 ≤ IsLocalRing.maximalIdeal B ^ N0 :=
        Ideal.pow_right_mono Ideal.map_comap_le N0
      have h3 := h2 h1
      rw [hN0, Submodule.zero_eq_bot, Ideal.mem_bot] at h3
      exact h3
    exact RingHom.mem_ker.1 (hle hx)
  let J' : Ideal RM := J.map (algebraMap R RM)
  have hJg : ∀ x ∈ J', g x = 0 := by
    intro x hx
    have hle : J' ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hg]
      exact RingHom.mem_ker.1 (hJf hr)
    exact RingHom.mem_ker.1 (hle hx)
  have hreg' : ∀ a : RM, algebraMap R RM d * a ∈ J' → a ∈ J' := by
    intro a ha
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M0.primeCompl a
    simp only at ha ⊢
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mem_map_algebraMap_iff] at ha
    obtain ⟨t, ht, htJ⟩ := ha
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    refine ⟨t, ht, hreg _ ?_⟩
    rw [mul_left_comm]
    exact htJ
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal RM)
    (Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)})
  have hkey : ∀ c : RM, algebraMap R RM d * c ∈ J' ⊔ IsLocalRing.maximalIdeal RM ^ (N0 + k) →
      g c = 0 := by
    intro c hc
    obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 hc
    have hx1 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        (IsLocalRing.maximalIdeal RM ^ (N0 + k)) • (⊤ : Submodule RM (RM ⧸ J')) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hjy, map_add,
        Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add]
      exact Ideal.mem_map_of_mem _ hy
    have hx2 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)} := by
      have : Ideal.Quotient.mk J' (algebraMap R RM d * c) =
          c • Ideal.Quotient.mk J' (algebraMap R RM d) := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm c]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hx3 := hk (N0 + k) (by omega)
    have h5 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈
        IsLocalRing.maximalIdeal RM ^ (N0 + k - k) • (IsLocalRing.maximalIdeal RM ^ k • ⊤ ⊓
          Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)}) := by
      rw [← hx3]
      exact Submodule.mem_inf.2 ⟨hx1, hx2⟩
    rw [Nat.add_sub_cancel] at h5
    have hx4 : Ideal.Quotient.mk J' (algebraMap R RM d * c) ∈ IsLocalRing.maximalIdeal RM ^ N0 •
        Submodule.span RM {Ideal.Quotient.mk J' (algebraMap R RM d)} :=
      Submodule.smul_mono le_rfl inf_le_right h5
    obtain ⟨a, ha, hav⟩ := Submodule.mem_smul_span_singleton.1 hx4
    have hdiff : algebraMap R RM d * (c - a) ∈ J' := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, mul_sub, map_sub, ← hav, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, mul_comm a, sub_self]
    have hca : c - a ∈ J' := hreg' _ hdiff
    have hc : c = (c - a) + a := by ring
    rw [hc, map_add, hJg _ hca, hmaxg _ ha, add_zero]
  let I : Ideal RM := J' ⊔ IsLocalRing.maximalIdeal RM ^ (N0 + k)
  have hIg : ∀ x ∈ I, g x = 0 := by
    intro x hx
    obtain ⟨j, hj, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hJg _ hj, hmaxg _ (Ideal.pow_le_pow_right (by omega) hy), add_zero]
  have hIne : I ≠ ⊤ := by
    intro h
    have h1 : (1 : RM) ∈ I := by rw [h]; exact Submodule.mem_top
    have := hIg 1 h1
    simp at this
  haveI : Nontrivial (RM ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIne
  haveI hloc : IsLocalRing (RM ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI aQ : Algebra ℚ_[l] (RM ⧸ I) := ((Ideal.Quotient.mk I).comp φ).toAlgebra
  letI aO : Algebra O (RM ⧸ I) := ((Ideal.Quotient.mk I).comp α).toAlgebra
  letI aZ : Algebra ℤ_[l] (RM ⧸ I) := ((Ideal.Quotient.mk I).comp ψ).toAlgebra
  haveI t1 : @IsScalarTower ℤ_[l] O (RM ⧸ I) _ aO.toSMul aZ.toSMul := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI t2 : IsScalarTower ℤ_[l] ℚ_[l] (RM ⧸ I) := IsScalarTower.of_algebraMap_eq (fun x => by
    show Ideal.Quotient.mk I (ψ x) = Ideal.Quotient.mk I (φ (algebraMap ℤ_[l] ℚ_[l] x))
    rw [hφ])
  let f' : R →ₐ[O] (RM ⧸ I) :=
    { (Ideal.Quotient.mk I).comp (algebraMap R RM) with commutes' := fun o => rfl }
  let q : (RM ⧸ I) →ₐ[ℚ_[l]] B :=
    { Ideal.Quotient.lift I g hIg with
      commutes' := fun c => by
        show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I (φ c)) = algebraMap ℚ_[l] B c
        rw [Ideal.Quotient.lift_mk]
        exact RingHom.congr_fun hgφ c }
  have hmaxQ : IsLocalRing.maximalIdeal (RM ⧸ I) ≤
      (IsLocalRing.maximalIdeal RM).map (Ideal.Quotient.mk I) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    by_contra hy
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hx hy
    exact hx (hy.map _)
  have hnil : IsLocalRing.maximalIdeal (RM ⧸ I) ^ (N0 + k) = ⊥ := by
    rw [eq_bot_iff]
    calc IsLocalRing.maximalIdeal (RM ⧸ I) ^ (N0 + k)
        ≤ ((IsLocalRing.maximalIdeal RM).map (Ideal.Quotient.mk I)) ^ (N0 + k) :=
          Ideal.pow_right_mono hmaxQ _
      _ = (IsLocalRing.maximalIdeal RM ^ (N0 + k)).map (Ideal.Quotient.mk I) :=
          (Ideal.map_pow _ _ _).symm
      _ ≤ I.map (Ideal.Quotient.mk I) := Ideal.map_mono le_sup_right
      _ = ⊥ := Ideal.map_quotient_self I
  haveI hart : IsArtinianRing (RM ⧸ I) := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
    exact ⟨N0 + k, by rw [hnil]; rfl⟩
  have hfin : Module.Finite ℚ_[l] (RM ⧸ I) := by
    haveI : Module.Finite ℚ_[l] ((RM ⧸ I) ⧸ Ring.jacobson (RM ⧸ I)) := by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      have hle : IsLocalRing.maximalIdeal (RM ⧸ I) ≤ (IsLocalRing.maximalIdeal B).comap q := by
        intro x hx
        rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have hx0 : x ^ (N0 + k) = 0 := by
          have := Ideal.pow_mem_pow hx (N0 + k)
          rw [hnil] at this
          exact (Ideal.mem_bot).1 this
        have := hu.pow (N0 + k)
        rw [← map_pow, hx0, map_zero] at this
        exact not_isUnit_zero this
      have hcomap : (IsLocalRing.maximalIdeal B).comap (q : (RM ⧸ I) →+* B) ≤
          IsLocalRing.maximalIdeal (RM ⧸ I) :=
        IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
      have hinj : Function.Injective (Ideal.quotientMap (IsLocalRing.maximalIdeal B)
          (q : (RM ⧸ I) →+* B) hle) := Ideal.quotientMap_injective' hcomap
      haveI : Module.Finite ℚ_[l] (B ⧸ IsLocalRing.maximalIdeal B) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[l] (IsLocalRing.maximalIdeal B)).toLinearMap
          (Ideal.Quotient.mkₐ_surjective ℚ_[l] (IsLocalRing.maximalIdeal B))
      exact Module.Finite.of_injective
        (Ideal.quotientMapₐ (IsLocalRing.maximalIdeal B) q hle).toLinearMap hinj
    exact IsSemiprimaryRing.finite_of_isArtinian ℚ_[l] (RM ⧸ I) (RM ⧸ I)
  refine ⟨RM ⧸ I, inferInstance, hloc, aQ, hfin, aO, aZ, t1, t2, f', q, ?_, ?_, ?_⟩
  · intro x hx
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk I (algebraMap R RM x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)
  · intro a
    show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I (algebraMap R RM a)) = f a
    rw [Ideal.Quotient.lift_mk, hg]
  · intro b hb
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    show Ideal.Quotient.lift I g hIg (Ideal.Quotient.mk I c) = 0
    rw [Ideal.Quotient.lift_mk]
    apply hkey
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hb
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLocPt

theorem main : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] (f : U.R →ₐ[O] B), GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f → D.IsLCr (push f U.r.hom) := by
  intro hP l _ O _ _ _ _ _ _ _ D U B _ _ _ _ _ _ _ _ f hf

  have hord : GlobalTheory.OrdLoc.ordIdeal D U.r.hom ≤ GlobalTheory.OrdLoc.IY D U := fun a ha => ⟨0, by simpa using ha⟩
  have hdiv : (l : U.R) ∣ GlobalTheory.OrdLoc.del D U.r.hom :=
    ⟨GlobalTheory.OrdLoc.dd D U.r.hom 0 * GlobalTheory.OrdLoc.dd D U.r.hom 1, by unfold GlobalTheory.OrdLoc.del; ring⟩
  have hsat : ∀ a, GlobalTheory.OrdLoc.del D U.r.hom * a ∈ GlobalTheory.OrdLoc.IY D U → a ∈ GlobalTheory.OrdLoc.IY D U := by
    rintro a ⟨n, hn⟩
    exact ⟨n + 1, by rw [pow_succ, mul_assoc]; exact hn⟩
  obtain ⟨B', _, _, _, _, _, _, _, _, f', q, hJ, hqf, hkill⟩ :=
    GlobalTheory.T.exists_finite_local_lift_of_saturated_ideal U.R (GlobalTheory.OrdLoc.IY D U) (GlobalTheory.OrdLoc.del D U.r.hom) hdiv hsat B f hf
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalRing B' := IsModuleTopology.isTopologicalRing ℚ_[l] B'
  obtain ⟨hnat, -, hdel⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D f' U.r.hom
  have hzero : GlobalTheory.OrdLoc.ordIdeal D (push f' U.r.hom) = ⊥ := by
    rw [← hnat, Ideal.map_eq_bot_iff_le_ker]
    exact hord.trans hJ
  have hmult' : HasMult D.η (push f' U.r.hom) := fun g => U.r.hasMult g
  have hcont' : ∀ a b, QCont l fun g => (push f' U.r.hom g).mat a b := fun a b =>
    (ptCont U.R B' f').1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)
  obtain ⟨h, ρ, κ, x, y, z, hρ, hκc, hκI, hz, hρM, hx, hy, hσd⟩ :=
    GlobalTheory.T.triangular_conj_of_ordIdeal_eq_bot D B' (push f' U.r.hom) hmult' hcont' hzero
  obtain ⟨⟨hσ, hcl⟩, -⟩ := GlobalTheory.T.chosenFrobenius_isFrobenius D
  obtain ⟨-, -, hφ, -, -⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  obtain ⟨⟨v0, hv0⟩, ⟨v1, hv1⟩⟩ := hσd hσ
  have hdel' : f' (GlobalTheory.OrdLoc.del D U.r.hom) = (l : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 0 *
      GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 1 := hdel
  have hcr := GlobalTheory.T.triangular_rank_three_crystalline_after_push hP D.HL.subtype hφ q D.e D.e_pos κ hκc hκI x y z ρ hz hρM hx hy ⟨_, hσ⟩ hcl
    (fun b hb => hkill b (by
      have hb' : ((((κ 0 / κ 1) ⟨_, hσ⟩ : B'ˣ) : B') - (cycA l l B' (GlobalTheory.OrdLoc.fr D) : B')) * b = 0 := hb
      rw [hdel', hv0]
      linear_combination ((l : B') * (v0 : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 1) * hb'))
    (fun b hb => hkill b (by
      have hb' : ((((κ 1 / κ 2) ⟨_, hσ⟩ : B'ˣ) : B') - (cycA l l B' (GlobalTheory.OrdLoc.fr D) : B')) * b = 0 := hb
      rw [hdel', hv1]
      linear_combination ((l : B') * GlobalTheory.OrdLoc.dd D (push f' U.r.hom) 0 * (v1 : B')) * hb'))
  have hmult : HasMult D.η (push f U.r.hom) := fun g => U.r.hasMult g
  have hcont : ∀ a b, QCont l fun g => (push f U.r.hom g).mat a b := fun a b =>
    (ptCont U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)
  have hqf' : (q : B' →+* B).comp (f' : U.R →+* B') = (f : U.R →+* B) := RingHom.ext hqf
  refine GlobalTheory.T.isLCrystalline_conjBy_invariant D B (push f U.r.hom) (Matrix.GeneralLinearGroup.map (q : B' →+* B) h) hmult hcont
    ⟨(Matrix.GeneralLinearGroup.map (q : B' →+* B)).comp ρ, fun g => ?_, hcr⟩
  have e1 : GG.map (q : B' →+* B) (conjBy h (push f' U.r.hom) (g : GQ l)) =
      conjBy (Matrix.GeneralLinearGroup.map (q : B' →+* B) h) (push f U.r.hom) (g : GQ l) := by
    simp only [conjBy, push, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
      GG.map_map, hqf']
    congr 2 <;> simp [GG.ofGL, GG.map, SemidirectProduct.map_inl]
  rw [MonoidHom.comp_apply, hρ g, ← e1]
  rfl

end GlobalTheory.OrdLocPt
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLCrystalline_point_of_saturatedOrdIdeal : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [IsLocalRing B] (f : U.R →ₐ[O] B), GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f → D.IsLCr (push f U.r.hom) := by
  atlas_forward_decl GlobalTheory.OrdLocPt.main
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

def glPart {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G) (r : G →* GG m R)
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

theorem ptsCr_IY : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), GlobalTheory.OrdLoc.PtsCr D U (GlobalTheory.OrdLoc.IY D U) := by
  intro hP l _ O _ _ _ _ _ _ _ D U B _ _ _ _ _ _ _ f hf
  obtain ⟨-, -, hemb, -, -⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  have hright : ∀ g ∈ D.HL, (push f U.r.hom g).right = 1 := fun g hg => by
    rw [show (push f U.r.hom g).right = (U.r.hom g).right from rfl, U.r.hasMult g]
    exact hg.1
  let ρ := glPart D.HL (push f U.r.hom) hright
  refine ⟨ρ, fun _ => rfl, ?_⟩
  refine GlobalTheory.CrLocal.isCr_of_local D.HL.subtype hemb ρ (fun i j => ?_) ?_
  · have h := (ptCont (l := l) U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat i j) (U.r.cont i j)
    unfold QCont at h ⊢
    exact @Continuous.comp ↥D.HL (GQ l) B _ _ (moduleTopology ℚ_[l] B) Subtype.val (fun g => f ((U.r.hom g).mat i j)) h continuous_subtype_val
  · intro B' _ _ _ _ _ _
    letI : Algebra O B' := ((algebraMap B B').comp (algebraMap O B)).toAlgebra
    letI : Algebra ℤ_[l] B' := ((algebraMap B B').comp (algebraMap ℤ_[l] B)).toAlgebra
    haveI : IsScalarTower ℤ_[l] O B' := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B B' (algebraMap ℤ_[l] B x) = algebraMap B B' (algebraMap O B (algebraMap ℤ_[l] O x))
      rw [IsScalarTower.algebraMap_apply ℤ_[l] O B]
    haveI : IsScalarTower ℤ_[l] ℚ_[l] B' := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B B' (algebraMap ℤ_[l] B x) = algebraMap ℚ_[l] B' (algebraMap ℤ_[l] ℚ_[l] x)
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B, IsScalarTower.algebraMap_apply ℚ_[l] B B']
    let f' : U.R →ₐ[O] B' :=
      { toRingHom := (algebraMap B B').comp (f : U.R →+* B)
        commutes' := fun x => by
          change algebraMap B B' (f (algebraMap O U.R x)) = algebraMap B B' (algebraMap O B x)
          rw [f.commutes] }
    obtain ⟨ρ', hρ', hcr⟩ := GlobalTheory.T.isLCrystalline_point_of_saturatedOrdIdeal hP D U B' f' (fun a ha => by
      change algebraMap B B' (f a) = 0
      rw [show f a = 0 from hf ha, map_zero])
    have e : ρ' = (Matrix.GeneralLinearGroup.map (algebraMap B B')).comp ρ := by
      ext g i j
      rw [hρ' g]
      rfl
    exact e ▸ hcr

end GlobalTheory.OrdLoc
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturatedOrdIdeal_points_isLCrystalline : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), GlobalTheory.OrdLoc.PtsCr D U (GlobalTheory.OrdLoc.IY D U) := by
  atlas_forward_decl GlobalTheory.OrdLoc.ptsCr_IY
end
