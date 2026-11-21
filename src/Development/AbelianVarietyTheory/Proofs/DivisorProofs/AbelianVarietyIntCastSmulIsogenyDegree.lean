import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMul
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K) (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | exact GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open FiniteCover

theorem finrank_sec_pull_sandwich_flat : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (FiniteCover.basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_sections_pullback_finite_flat_degree_bounds : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  atlas_forward_decl GlobalTheory.finrank_sec_pull_sandwich_flat
end

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.ZV GlobalTheory.DegKer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbelianTower

theorem isFinite_pow {K : Type} [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G]
    (D : TorusExtension G) (N : ℕ) (hN : 1 ≤ N) : IsFinite ((𝟙 G) ^ N : G ⟶ G).left := by
  letI := D.addCommGroup
  letI := D.grpB
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_quasiCompact
  have := D.free
  have := D.finite
  have h1 : IsFinite ((𝟙 D.B) ^ N : D.B ⟶ D.B).left := GlobalTheory.MulFiniteAny.isFinite_mulA K D.B D.isAbelian N hN
  have hf : IsFinite (mulN (splitTorus (Sp K) D.X) N).left := Diag.isFinite_mulN _ D.X (by omega)
  rw [GrpTangent.mulN_eq_pow] at hf
  have := isAffineHom_descendsAlong_fpqc.{0}
  have hP := IsPullback.of_hasPullback D.q ((𝟙 D.B) ^ N)
  have w : ((𝟙 G) ^ N) ≫ D.q = D.q ≫ ((𝟙 D.B) ^ N) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have ha := hP.lift_fst _ _ w
  have hb := hP.lift_snd _ _ w
  have a2 : IsAffineHom (hP.lift _ _ w).left :=
    ExtensionMul.of_pow_kernel @IsAffineHom D.i D.q D.isKernel N hP ha hb inferInstance
  have a3 : UniversallyClosed (hP.lift _ _ w).left :=
    ExtensionMul.of_pow_kernel @UniversallyClosed D.i D.q D.isKernel N hP ha hb inferInstance
  have a4 : LocallyOfFiniteType (hP.lift _ _ w).left :=
    ExtensionMul.of_pow_kernel @LocallyOfFiniteType D.i D.q D.isKernel N hP ha hb inferInstance
  have a5 : IsFinite (hP.lift _ _ w).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  have hP' := (hP.map (Over.forget _)).flip
  have b1 : IsFinite (pullback.fst D.q ((𝟙 D.B) ^ N)).left := MorphismProperty.of_isPullback (P := @IsFinite) hP' h1
  rw [← ha, Over.comp_left]
  infer_instance

theorem mapDeg_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [IsFinite φ] [IsFinite ψ] [Surjective φ] [Surjective ψ] {D E : ℕ} (hD : MapDeg φ D) (hE : MapDeg ψ E) :
    MapDeg (φ ≫ ψ) (E * D) := by
  refine MapDeg.of_isFinite fun U hU hne => ?_
  obtain ⟨z, hz⟩ := hne
  obtain ⟨y, rfl⟩ := ψ.surjective z
  obtain ⟨x, rfl⟩ := φ.surjective y
  haveI : Nonempty U := ⟨⟨_, hz⟩⟩
  haveI : Nonempty (ψ ⁻¹ᵁ U) := ⟨⟨φ x, hz⟩⟩
  haveI : Nonempty (φ ⁻¹ᵁ ψ ⁻¹ᵁ U) := ⟨⟨x, hz⟩⟩
  letI := (ψ.app U).hom.toAlgebra
  letI := (φ.app (ψ ⁻¹ᵁ U)).hom.toAlgebra
  letI : Algebra Γ(Z, U) Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U) := ((φ ≫ ψ).app U).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Y, ψ ⁻¹ᵁ U) Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Γ(Z, U) Γ(Y, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
  haveI := IsSchemeTheoreticallyDominant.of_isDominant φ
  haveI := IsSchemeTheoreticallyDominant.of_isDominant ψ
  haveI : FaithfulSMul Γ(Z, U) Γ(Y, ψ ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (ψ.app_injective U)
  haveI : FaithfulSMul Γ(Y, ψ ⁻¹ᵁ U) Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (φ.app_injective _)
  rw [← hE.finrank_eq U hU ⟨_, hz⟩, ← hD.finrank_eq _ (hU.preimage ψ) ⟨φ x, hz⟩]
  exact (Module.finrank_mul_finrank' Γ(X, φ ⁻¹ᵁ ψ ⁻¹ᵁ U)).symm

theorem finrank_eq_of_mapDeg {X Y : Scheme.{0}} [IsIntegral Y] (φ : X ⟶ Y) [IsFinite φ] [Flat φ] {D : ℕ}
    (hD : MapDeg φ D) (y : Y) : φ.finrank y = D := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  letI := (φ.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := φ.finite_app U hU
  haveI : Module.Flat Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
    have := φ.flat_appLE hU (hU.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hp : IsPullback (hU.preimage φ).fromSpec (Spec.map (φ.app U)) φ hU.fromSpec :=
    (IsOpenImmersion.isPullback _ _ _ _ (by
      rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hU (hU.preimage φ)])
      (by simp)).flip
  obtain ⟨q, rfl⟩ : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hy
  rw [← hD.finrank_eq U hU ⟨_, hy⟩, ← FiniteCover.rankAtStalk_bot,
    Module.rankAtStalk_eq_of_le_of_finite_of_flat _ (p := ⊥) (q := q) bot_le,
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp q]
  exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) _

theorem mapDeg_eq_pow_mul_card (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G]
    [IsIntegral G.left] [LocallyOfFiniteType G.hom] (α : G ⟶ G) [IsMonHom α] [IsFinite α.left] :
    Finite {x : Out.baseOver (Sp K) ⟶ G // x ≫ α = 1} ∧
      ∃ e : ℕ, MapDeg α.left (ringExpChar K ^ e * Nat.card {x : Out.baseOver (Sp K) ⟶ G // x ≫ α = 1}) := by
  have hs := (flat_and_surjective_of_isFinite_grpEnd K G α).2
  obtain ⟨D, -, hD⟩ := exists_mapDeg_of_isFinite _ _ α.left inferInstance hs
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint G.left)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  have : Nonempty (α.left ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := α.left.surjective (genericPoint G.left)
    exact ⟨⟨x, show α.left x ∈ U from hx ▸ hξ⟩⟩
  letI := (α.left.app U).hom.toAlgebra
  have : Module.Finite Γ(G.left, U) Γ(G.left, α.left ⁻¹ᵁ U) := α.left.finite_app U hU
  have : IsSchemeTheoreticallyDominant α.left := .of_isDominant _
  have : FaithfulSMul Γ(G.left, U) Γ(G.left, α.left ⁻¹ᵁ U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (α.left.app_injective U)
  let c : K →+* Γ(G.left, U) :=
    (G.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have : ExpChar Γ(G.left, U) (ringExpChar K) := expChar_of_injective_ringHom c.injective _
  let Ω := AlgebraicClosure (FractionRing Γ(G.left, U))
  have : FaithfulSMul Γ(G.left, U) Ω := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq Γ(G.left, U) (FractionRing Γ(G.left, U)) Ω, RingHom.coe_comp]
    exact (RingHom.injective _).comp (IsFractionRing.injective _ _)
  obtain ⟨h0, e, he⟩ := finrank_eq_pow_mul_card Γ(G.left, U) Γ(G.left, α.left ⁻¹ᵁ U) Ω (ringExpChar K)
  rw [card_fibre_eq α.left hU Ω] at h0 he
  set z := Spec.map (CommRingCat.ofHom (algebraMap Γ(G.left, U) Ω)) ≫ hU.fromSpec with hz
  let z' : Over.mk (z ≫ G.hom) ⟶ G := Over.homMk z rfl
  have h1 : Nat.card {y : Over.mk (z ≫ G.hom) ⟶ G // y ≫ α = z'} =
      Nat.card {y : Spec (CommRingCat.of Ω) ⟶ G.left // y ≫ α.left = z} := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun y => ⟨y.1.left, congrArg CommaMorphism.left y.2⟩) ⟨?_, ?_⟩)
    · intro y y' h
      exact Subtype.ext (Over.OverMorphism.ext (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      refine ⟨⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩, rfl⟩
      change y ≫ G.hom = z ≫ G.hom
      rw [← hy, Category.assoc, Over.w α]
  rw [← h1] at h0 he
  have hne := (Nat.card_ne_zero.mp h0).1
  rw [← card_coset_eq G _ α z' hne, ← card_ker_eq G α Ω (z ≫ G.hom)] at h0 he
  refine ⟨(Nat.card_ne_zero.mp h0).2, e, ?_⟩
  rw [← he, hD.finrank_eq U hU ⟨_, hξ⟩]
  exact hD

theorem exists_finrank_torsion (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [IsAlgClosed K] (h0 : (p : K) = 0)
    (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [GeometricallyConnected G.hom]
    (D : TorusExtension G) : ∃ h : ℕ, ∀ (n : ℕ) (S : Type) [CommRing S] [Algebra K S] [Module.Finite K S]
      (y : SpAlg K S ⟶ G), IsPullback y.left (spMap (algebraMap K S)) (mulN G (p ^ n)).left η[G].left →
        Module.finrank K S = p ^ (n * h) := by
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ G.hom ‹_› ‹_›
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_subsingleton G.hom
  have hm : ∀ N, IsMonHom ((𝟙 G) ^ N : G ⟶ G) := fun N => GlobalTheory.AbLaw.MulN.isMonHom_mulA G N
  have hf : ∀ n, IsFinite ((𝟙 G) ^ p ^ n : G ⟶ G).left := fun n => isFinite_pow G D _ (Nat.one_le_pow _ _ hp.out.pos)
  have hl := fun n => (flat_and_surjective_of_isFinite_grpEnd K G ((𝟙 G) ^ p ^ n)).1
  have hs := fun n => (flat_and_surjective_of_isFinite_grpEnd K G ((𝟙 G) ^ p ^ n)).2
  obtain ⟨hfin, e, he⟩ := mapDeg_eq_pow_mul_card K G ((𝟙 G) ^ p ^ 1)
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 h0
  rw [ringExpChar.eq K p] at he
  let M : Subgroup (Out.baseOver (Sp K) ⟶ G) := (IsMonHom.monoidHom ((𝟙 G) ^ p ^ 1 : G ⟶ G) _).ker
  haveI : Finite M := hfin
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := M)).1 fun g => ⟨1, Subtype.ext (by
    have h : g.1 ≫ (𝟙 G) ^ p ^ 1 = 1 := g.2
    rw [MonObj.comp_pow, Category.comp_id] at h
    exact h)⟩
  have hd : ∀ n, MapDeg ((𝟙 G) ^ p ^ n : G ⟶ G).left (p ^ (n * (e + k))) := fun n => by
    induction n with
    | zero =>
      simp only [pow_zero, pow_one, zero_mul]
      exact MapDeg.id_one _
    | succ n ih =>
      have h := mapDeg_comp _ _ he ih
      rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ← pow_mul, ← pow_add,
        show Nat.card {x : Out.baseOver (Sp K) ⟶ G // x ≫ (𝟙 G) ^ p ^ 1 = 1} = p ^ k from hk, ← pow_add,
        ← pow_add, add_comm 1 n] at h
      rwa [add_mul, _root_.one_mul]
  refine ⟨e + k, fun n S _ _ _ y H => ?_⟩
  rw [GrpTangent.mulN_eq_pow] at H
  have h := Scheme.Hom.finrank_of_isPullback _ _ _ _ H (⊥ : PrimeSpectrum K)
  rw [finrank_eq_of_mapDeg _ (hd n)] at h
  rw [← h, ← FiniteCover.rankAtStalk_bot]
  exact (Scheme.Hom.finrank_SpecMap_algebraMap K S _).symm

theorem exists_tower : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A], IsSemiAbelian A → (∀ N, 1 ≤ N → IsFinite (torsion A N).hom ∧ Flat (torsion A N).hom) → ∃ G : PDivGroup p O, Nonempty (G.TorsionTower A) := by
  intro p hp O _ _ A _ hA hf
  by_cases h0 : (p : O) = 0
  swap
  · exact RaynaudPDiv.exists_tower p O h0 A hA hf
  have := hA.comm
  have := hA.smooth
  have := hA.geomConnected
  let K := AlgebraicClosure (FractionRing O)
  have hi : Function.Injective (algebraMap O K) :=
    (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O _)
  let B := (Over.pullback (spMap (algebraMap O K))).obj A
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom _))
  have : GeometricallyConnected B.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom _))
  choose R _ _ y h1 h2 H using fun n : ℕ => RaynaudPDiv.exists_isPullback_torsion O A (p ^ n)
    (hf _ (Nat.one_le_pow _ _ hp.out.pos)).1 (hf _ (Nat.one_le_pow _ _ hp.out.pos)).2
  have h := fun n => AbelianPDiv.isUnivTorsion_of_isPullback (y n) (H n)
  obtain ⟨D⟩ := hA.fibres K (spMap (algebraMap O K))
  obtain ⟨d, hd⟩ := exists_finrank_torsion p K (by rw [← map_natCast (algebraMap O K), h0, map_zero]) B D
  have hk : ∀ n, Module.finrank K (K ⊗[O] R n) = p ^ (n * d) := fun n => by
    obtain ⟨y', h'⟩ := AbelianPDiv.exists_isPullback_baseChange (y n) (H n) K
    exact hd n _ y' h'
  have hr : ∀ n (q : PrimeSpectrum O), Module.rankAtStalk (R n) q = p ^ (n * d) := fun n q => by
    rw [← Module.rankAtStalk_eq_of_le_of_finite_of_flat (R n)
        (p := PrimeSpectrum.comap (algebraMap O K) ⊥) (q := q) ?_, ← Module.rankAtStalk_baseChange,
      Module.rankAtStalk_eq_finrank_of_free, hk n]
    · rfl
    · intro a ha
      have ha' : algebraMap O K a = 0 := ha
      rw [(map_eq_zero_iff _ hi).1 ha']
      exact zero_mem _
  choose r r1 r2 r3 using fun n : ℕ =>
    (h n).exists_res (h (n + 1)) (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := d
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := hr
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

end GlobalTheory.SemiAbelianTower
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.MulDegree

theorem finrank_mul_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → n ≠ 0 → ∀ [IsFinite (𝟙 B ^ n : B ⟶ B).left] [Flat (𝟙 B ^ n : B ⟶ B).left], ∀ x : B.left, (𝟙 B ^ n : B ⟶ B).left.finrank x = n ^ (2 * g) := by
  intro k _ _ B _ g n hB hg hn0 _ _ x
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hq : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hn0)
  haveI : IsMonHom (𝟙 B ^ n : B ⟶ B) := GlobalTheory.AbLaw.MulN.isMonHom_mulA B n
  haveI : Surjective (𝟙 B ^ n : B ⟶ B).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_grpEnd k B (𝟙 B ^ n)).2
  obtain ⟨D, -, hD⟩ := GlobalTheory.DegKer.exists_mapDeg_of_isFinite _ _ (𝟙 B ^ n : B ⟶ B).left inferInstance inferInstance
  have hrank : ∀ y : B.left, (𝟙 B ^ n : B ⟶ B).left.finrank y = D :=
    fun y => GlobalTheory.SemiAbelianTower.finrank_eq_of_mapDeg _ hD y
  rw [hrank x]
  have hproj := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k B hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec B)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB).1 ⟨H, r, hH, hr⟩
    (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety hG k B hB hproj H hH) hsym
  have hiso : LBIso (AbLaw.pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (𝟙 B ^ n).left) := by
    have h := GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing k B M n
    rw [hM] at h
    rw [Nat.cast_pow]
    exact h
  have hφ : (𝟙 B ^ n).left ≫ B.hom = B.hom := Over.w _
  obtain ⟨hfin, hmono, c, C, hc1, hgrow⟩ :=
    GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k B.left B.hom g hg H m s hH hs
  have e := GlobalTheory.UU.TorsionCount.nonempty_secEquiv B.hom _ hφ hH (n ^ 2) hiso
  obtain ⟨a, ha⟩ := GlobalTheory.T.finrank_sections_pullback_finite_flat_degree_bounds k B.left B.left B.hom (𝟙 B ^ n).left H m s hH hs D hrank hfin fun t => by
    obtain ⟨e⟩ := e t
    haveI := hfin (n ^ 2 * t)
    exact Module.Finite.equiv e
  rw [pow_mul]
  refine GlobalTheory.UU.degree_eq_pow_of_growth (fun t : ℕ => Module.finrank k (SecOnR B.hom (AbLaw.pw H t) ⊤)) g c C a _ (n ^ 2)
    hc1 hq hmono hgrow fun t => ?_
  obtain ⟨e₁⟩ := e (t + a)
  obtain ⟨e₂⟩ := e t
  exact ⟨(ha t).1.trans e₁.finrank_eq.ge, e₂.finrank_eq.le.trans (ha t).2⟩

end GlobalTheory.UU.MulDegree
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulIsogeny

theorem bcMap_natCast_smul_id (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (n : ℕ) :
    bcMap L ((n : ℤ) • 𝟙 A) = (n : ℤ) • 𝟙 (baseChange L A) := by
  ext1
  simp only [bcMap, mk_hom, zsmul_hom, id_hom, zpow_natCast]
  exact GlobalTheory.MulFiniteFlat.pullback_map_mulA _ A.X n

theorem natCast_algClosed (k : Type) [Field k] [IsAlgClosed k] (A : AbVar k) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  have e : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X ^ n : A.X ⟶ A.X) := by
    rw [zsmul_hom, id_hom, zpow_natCast]
  obtain ⟨hfin, hfl⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul (Sp k) A.X A.ab n (Nat.one_le_iff_ne_zero.2 hn)
  have hmon : IsMonHom (𝟙 A.X ^ n : A.X ⟶ A.X) := e ▸ inferInstanceAs (IsMonHom ((n : ℤ) • 𝟙 A).hom)
  have hsurj : Surjective (𝟙 A.X ^ n : A.X ⟶ A.X).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A.X A.ab _ inferInstance hfin).2
  have hiso : IsIsogeny ((n : ℤ) • 𝟙 A) := by
    unfold IsIsogeny
    rw [e]
    exact ⟨hfin, hsurj⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso, e]
  exact GlobalTheory.UU.MulDegree.finrank_mul_eq k A.X A.dim n A.ab A.smooth hn _

theorem natCast (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  obtain ⟨h1, h2⟩ := natCast_algClosed (AlgebraicClosure K) (baseChange (AlgebraicClosure K) A) n hn
  obtain ⟨e1, e2⟩ := GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq K (AlgebraicClosure K) A A ((n : ℤ) • 𝟙 A)
  rw [bcMap_natCast_smul_id] at e1 e2
  exact ⟨e1.1 h1, e2.symm.trans h2⟩

theorem neg_one (K : Type) [Field K] (A : AbVar K) : IsIsogeny (-𝟙 A) ∧ deg (-𝟙 A) = 1 := by
  have hsq : (-𝟙 A) ≫ (-𝟙 A) = 𝟙 A := by simp
  have hsq' : (-𝟙 A).hom.left ≫ (-𝟙 A).hom.left = 𝟙 A.X.left := by
    rw [← Over.comp_left, ← comp_hom, hsq, id_hom, Over.id_left]
  haveI : IsIso (-𝟙 A).hom.left := ⟨⟨(-𝟙 A).hom.left, hsq', hsq'⟩⟩
  have hiso : IsIsogeny (-𝟙 A) := ⟨inferInstance, inferInstance⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

theorem mul_isogeny : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℤ), n ≠ 0 → IsIsogeny (n • 𝟙 A) ∧ deg (n • 𝟙 A) = n.natAbs ^ (2 * A.dim) := by
  intro K _ A n hn
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    exact natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
  · have e : n • 𝟙 A = ((n.natAbs : ℤ) • 𝟙 A) ≫ (-𝟙 A) := by
      rw [Preadditive.comp_neg, Category.comp_id, ← neg_smul, ← h]
    obtain ⟨h1, h2⟩ := natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
    obtain ⟨h3, h4⟩ := neg_one K A
    obtain ⟨h5, h6⟩ := GlobalTheory.T.isogeny_comp_and_degree_mul K A A A _ _ h1 h3
    rw [e]
    exact ⟨h5, by rw [h6, h2, h4, _root_.mul_one]⟩

end GlobalTheory.MulIsogeny
end
