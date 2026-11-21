import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectDeterminedOverArtinianPinch
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorsFunctionsInvertibleDerivs
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqOfMulEq

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegField

theorem classify : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K]
    (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ f : Sp K ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ β c hc
  haveI : Module.FaithfullyFlat K (AlgebraicClosure K) := inferInstance
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F K (AlgebraicClosure K) β c hc fun c' hpb => ?_
  have hc' : c'.Principal := GlobalTheory.SiegLevCalc.sRel_principal ((sRel_one_one_iff _ _ _).2 hpb) hc
  exact GlobalTheory.T.siegel_family_classifies_principal_algClosed g n hg hn hodd F (AlgebraicClosure K) ((algebraMap K (AlgebraicClosure K)).comp β) c' hc'

end GlobalTheory.SiegField
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_family_classifies_principal_any_field : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp K ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  atlas_forward_decl GlobalTheory.SiegField.classify
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangentBound

def acts (W : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ
  | .inl uv => Matrix.single uv.1 uv.2 1
  | .inr true => (W + W.transpose).adjugate * W
  | .inr false => (W + W.transpose).adjugate * W.transpose

theorem main : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  intro h n _ h3 hodd K _ _ r β c hc hun
  have hn : n ≠ 0 := by omega
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨W, hW, hbasAll⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hbasAll h
  have hζ : (cycBase hn).ζ ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, cycBase_ζ]
    exact Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one)
  have hdet : (W + W.transpose).det = 1 := hW.2
  have hw : (W + W.transpose) * acts W (.inr true) = W := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have hw' : (W + W.transpose) * acts W (.inr false) = W.transpose := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have he : ∀ u v : Fin 8, ∃ j, acts W j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c hodd h3 hζ hc
  refine GlobalTheory.PowerTangent.main L1 L2 GlobalTheory.Moduli.cube_of_isLB h (8 * h) W _ (acts W) bas hW hbas (.inr true) (.inr false)
    hw hw' n (cycAway n) (cycBase hn) K r β t c hc ht ?_
  intro lam t' m₁ m₂
  have hf : spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      spMap ((algebraMap K (DualNumber K)).comp β) ≫ spMap (RingHom.id (cycAway n)) := by
    rw [← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => by
      simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl])
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).1 c
  have hc'P := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).2.1 c c' hc' hc
  obtain ⟨t'', ht''⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c' hodd h3 hζ hc'P
  have m₃ : TMap t'' t (spMap (dirMap lam)) :=
    (GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
      (spMap (dirMap lam)) hc hc'P ht ht'').1 hc'
  have m₄ : TMap t'' t' (𝟙 _) :=
    ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₁).2 (by rwa [Category.id_comp])
  have m₅ : TMap t'' t (constPt (spMap (dirMap lam))) := by
    have := ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₂).1 m₄
    rwa [Category.id_comp] at this
  exact hun lam c' hc' ((GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
    _ hc hc'P ht ht'').2 he m₅)

end GlobalTheory.SiegelTangentBound
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_tangentBound_nonconstant : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  atlas_forward_decl GlobalTheory.SiegelTangentBound.main
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.TangentOrigin
open scoped CategoryTheory.Obj

namespace GlobalTheory.TanPt

theorem exists_coords_derivs' {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) :
    ∃ (x : Fin D → A) (d : Fin D → A →+ A),
      (∀ c a b, d c (a * b) = a * d c b + b * d c a) ∧
      (∀ a c, d c (x a) = if a = c then 1 else 0) ∧ ∀ c r, d c (α r) = 0 := by
  classical
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ιv, σv, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ιv
  letI := Fintype.ofFinite σv
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ιv) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  let B := P.basisKaehler.reindex e
  have hB : ∀ i, KaehlerDifferential.D k A (P.val (e.symm i)) = B i := fun i => by
    simp [B]
  refine ⟨fun i => P.val (e.symm i), fun c =>
    { toFun := fun s => B.coord c (KaehlerDifferential.D k A s)
      map_zero' := by simp
      map_add' := fun s t => by simp }, fun c a b => ?_, fun a c => ?_, fun c r => ?_⟩
  · change B.coord c (KaehlerDifferential.D k A (a * b)) =
      a * B.coord c (KaehlerDifferential.D k A b) + b * B.coord c (KaehlerDifferential.D k A a)
    rw [Derivation.leibniz, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · change B.coord c (KaehlerDifferential.D k A (P.val (e.symm a))) = _
    rw [hB, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  · change B.coord c (KaehlerDifferential.D k A (algebraMap k A r)) = 0
    rw [Derivation.map_algebraMap, map_zero]

def jetVec {A K : Type} [CommRing A] [Field K] {D : ℕ} (φ : A →+* K) (d : Fin D → A →+ A)
    (hd : ∀ c a b, d c (a * b) = a * d c b + b * d c a) : A →+* TrivSqZeroExt K (Fin D → K) where
  toFun s := (φ s, fun c => φ (d c s))
  map_one' := by
    refine TrivSqZeroExt.ext (map_one φ) ?_
    funext c
    have h1 : d c 1 = 0 := by simpa using hd c 1 1
    change φ (d c 1) = 0
    rw [h1, map_zero]
  map_zero' := by
    refine TrivSqZeroExt.ext (map_zero φ) ?_
    funext c
    change φ (d c 0) = 0
    rw [map_zero, map_zero]
  map_add' s t := by
    refine TrivSqZeroExt.ext (map_add φ s t) ?_
    funext c
    change φ (d c (s + t)) = φ (d c s) + φ (d c t)
    rw [map_add, map_add]
  map_mul' s t := by
    refine TrivSqZeroExt.ext (map_mul φ s t) ?_
    refine Eq.trans ?_ (TrivSqZeroExt.snd_mul _ _).symm
    funext c
    show φ (d c (s * t)) = (φ s • (fun c => φ (d c t)) + MulOpposite.op (φ t) • (fun c => φ (d c s))) c
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, hd c, map_add, map_mul, map_mul, mul_comm (φ (d c s))]

theorem evalPt_congr {R : Type} [CommRing R] {X : Scheme.{0}} {x y : Sp R ⟶ X} (e : x = y) (U : X.Opens)
    (hx : ⊤ ≤ x ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) : evalPt x U hx f = evalPt y U hy f := by
  subst e; rfl

end GlobalTheory.TanPt

namespace GlobalTheory.TanPt

theorem exists_tangent_point : ∀ {o : Type} [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (K : Type) [Field K] (β : o →+* K) (x₀ : Sp K ⟶ X), x₀ ≫ s = spMap β → ∃ y : Sp (TrivSqZeroExt K (Fin D → K)) ⟶ X, spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ y = x₀ ∧ y ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin D → K))).comp β) ∧ ∀ mu : (Fin D → K) →ₗ[K] K, spMap (dirMap mu) ≫ y = constPt (spMap (dirMap mu) ≫ y) → mu = 0 := by
  intro o _ Y p D hsm K _ β z hz
  haveI := hsm
  obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (GlobalTheory.Adelic.ptOf z))
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨S, hS, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (S : Set Γ(Y, V)), GlobalTheory.Adelic.ptOf z ∈ Y.basicOpen (t : Γ(Y, V)) :=
    TopologicalSpace.Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hS).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨x, d, hl, hd, h0⟩ := exists_coords_derivs' h₂
  have hO : IsAffineOpen (Y.basicOpen (t : Γ(Y, V))) := IsAffineOpen.basicOpen hV _
  have hzO : ⊤ ≤ z ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := (GlobalTheory.Adelic.le_iff_ptOf_mem z _).2 hxt
  obtain ⟨w, hw, he⟩ := exists_evalPt_eq hO (jetVec (evalPt z _ hzO) d hl)
  refine ⟨w, ?_, ?_, fun mu hmu => ?_⟩
  · have h' : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ w) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    refine ext_evalPt hO h' hzO (RingHom.ext fun f => ?_)
    refine (evalPt_spMap_comp _ w _ hw h' f).trans ?_
    rw [he]
    rfl
  · refine eq_spMap_of_evalPt _ _ fun a => ?_
    rw [← evalPt_constFn p w _ hw a, he]
    have hza : evalPt z _ hzO (constFn p (Y.basicOpen (t : Γ(Y, V))) a) = β a := by
      rw [evalPt_constFn]
      exact (evalPt_congr hz (⊤ : (Sp o).Opens) _ le_rfl _).trans (evalPt_spMap β a)
    refine TrivSqZeroExt.ext ?_ ?_
    · exact hza
    · funext c
      change evalPt z _ hzO (d c (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p _ a)) = _
      rw [h0 c a, map_zero]
      rfl
  · refine (Pi.basisFun K (Fin D)).ext fun a => ?_
    have h1 : ⊤ ≤ (spMap (dirMap mu) ≫ w) ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    have h2 : ⊤ ≤ (constPt (spMap (dirMap mu) ≫ w)) ⁻¹ᵁ Y.basicOpen (t : Γ(Y, V)) :=
      fun q _ => hw (Set.mem_univ _)
    have h3 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap mu) ≫ w) ⁻¹ᵁ
        Y.basicOpen (t : Γ(Y, V)) := fun q _ => hw (Set.mem_univ _)
    have e := congrArg TrivSqZeroExt.snd (evalPt_congr hmu _ h1 h2 (x a))
    have e2 : (evalPt (constPt (spMap (dirMap mu) ≫ w)) _ h2 (x a)).snd = 0 := by
      rw [evalPt_congr (show constPt (spMap (dirMap mu) ≫ w) = spMap (algebraMap K (DualNumber K)) ≫
        (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (dirMap mu) ≫ w) from rfl) _ h2 h2,
        evalPt_spMap_comp _ _ _ h3 h2]
      rfl
    rw [e2, evalPt_spMap_comp _ w _ hw h1, he] at e
    have hv : (fun c => evalPt z _ hzO (d c (x a))) = Pi.basisFun K (Fin D) a := by
      funext c
      rw [hd, Pi.basisFun_apply]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac, Pi.single_apply, Ne.symm hac]
    rw [LinearMap.zero_apply, ← hv]
    rw [dirMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.snd_map] at e
    exact e

end GlobalTheory.TanPt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_firstOrder_tangentPoint_smooth : ∀ {o : Type} [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (K : Type) [Field K] (β : o →+* K) (x₀ : Sp K ⟶ X), x₀ ≫ s = spMap β → ∃ y : Sp (TrivSqZeroExt K (Fin D → K)) ⟶ X, spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ y = x₀ ∧ y ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin D → K))).comp β) ∧ ∀ mu : (Fin D → K) →ₗ[K] K, spMap (dirMap mu) ≫ y = constPt (spMap (dirMap mu) ≫ y) → mu = 0 := by
  atlas_forward_decl GlobalTheory.TanPt.exists_tangent_point
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SqZeroPb

def liftHom {K : Type} [Field K] {V W₁ W₂ : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁]
    [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂]
    (e : V ≃ₗ[K] W₁ × W₂) {T : Type} [CommRing T]
    (a : T →+* TrivSqZeroExt K W₁) (b : T →+* TrivSqZeroExt K W₂)
    (h : ∀ t, (a t).fst = (b t).fst) : T →+* TrivSqZeroExt K V where
  toFun t := TrivSqZeroExt.inl (a t).fst + TrivSqZeroExt.inr (e.symm ((a t).snd, (b t).snd))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, zero_add, smul_eq_mul, op_smul_eq_smul, smul_zero]
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      ext <;> simp [h]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add]
      rw [show ((a x).snd + (a y).snd, (b x).snd + (b y).snd)
          = ((a x).snd, (b x).snd) + ((a y).snd, (b y).snd) from rfl, map_add]

end GlobalTheory.SqZeroPb

open GlobalTheory.SqZeroPb in
theorem GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt : ∀ (K : Type) [Field K] (V W₁ W₂ : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁] [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂] (p : V →ₗ[K] W₁) (q : V →ₗ[K] W₂), Function.Bijective (LinearMap.prod p q) → IsPullback (CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom) := by
  intro K _ V W₁ W₂ _ _ _ _ _ _ _ _ _ _ _ _ p q hpq
  let e := LinearEquiv.ofBijective (LinearMap.prod p q) hpq
  have he : ∀ v, e v = (p v, q v) := fun v => rfl
  have hw : CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom =
      CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom := by
    ext x; simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => CommRingCat.ofHom (liftHom e s.fst.hom s.snd.hom ?_)) ?_ ?_ ?_)
  · intro t
    have := congrArg (fun φ => φ.hom t) s.condition
    simpa using this
  · intro s
    ext t : 2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom]
    · simp [liftHom]
      exact congrArg Prod.fst (e.apply_symm_apply _)
  · intro s
    ext t : 2
    have hc := congrArg (fun φ => φ.hom t) s.condition
    simp at hc
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, hc]
    · simp [liftHom]
      exact congrArg Prod.snd (e.apply_symm_apply _)
  · intro s m hm1 hm2
    ext t : 2
    have h1 := congrArg (fun φ => φ.hom t) hm1
    have h2 := congrArg (fun φ => φ.hom t) hm2
    simp at h1 h2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, ← h1]
    · simp [liftHom, ← h1, ← h2]
      rw [LinearEquiv.eq_symm_apply]
      rfl
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_square_zero_extension_pullback : ∀ (K : Type) [Field K] (V W₁ W₂ : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁] [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂] (p : V →ₗ[K] W₁) (q : V →ₗ[K] W₂), Function.Bijective (LinearMap.prod p q) → IsPullback (CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom) := by
  atlas_forward_decl GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegTanShift

theorem spMap_comp_spMap' {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (g : A' →+* A) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem isLocalRing_sq (K : Type) [Field K] : IsLocalRing (TrivSqZeroExt K (K × K)) :=
  haveI : Nontrivial (TrivSqZeroExt K (K × K)) := TrivSqZeroExt.inl_injective.nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_sq (K : Type) [Field K] : IsArtinianRing (TrivSqZeroExt K (K × K)) := by
  haveI : Module.Finite K (TrivSqZeroExt K (K × K)) := inferInstanceAs (Module.Finite K (K × (K × K)))
  exact IsArtinianRing.of_finite K _

theorem pbEq {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c' : SiegPre h k ζ' s'} {c : SiegPre h k ζ s} {f f' : S' ⟶ S}
    (hc : SiegPB c' c f) (e : f = f') : SiegPB c' c f' := e ▸ hc

theorem shift : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] (r : ℕ) (β : cycAway n →+* K) (G : SiegPre g n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), G.Principal → ∀ (lam κ κ' : (Fin r → K) →ₗ[K] K) (t : K) (c₃ c₁ : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), κ = κ' + t • lam → SiegPB c₃ G (spMap (dirMap lam)) → SiegPB c₃ G (constPt (spMap (dirMap lam))) → SiegPB c₁ G (spMap (dirMap κ)) → SiegPB c₁ G (spMap (dirMap κ')) := by
  intro g n h3 hodd K _ r β G hG lam κ κ' t c₃ c₁ hκ h₁ h₂ h₃
  subst hκ
  have pull : ∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (cycAway n)) (s' : S' ⟶ Sp (cycAway n)) (f : S' ⟶ S), f ≫ s = s' →
      ∀ c : SiegPre g n (zetaAway n) s, c.Principal →
        ∃ c' : SiegPre g n (zetaAway n) s', SiegPB c' c f ∧ c'.Principal := by
    intro S S' s s' f hf c hc
    have hf' : f ≫ s = s' ≫ spMap (RingHom.id (cycAway n)) := by rw [spMap_id', Category.comp_id]; exact hf
    have pr := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) S S' s s' f rfl hf'
    obtain ⟨c', hcc⟩ := pr.1 c
    exact ⟨c', hcc, pr.2.1 c c' hcc hc⟩
  have base : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra K R] [Algebra K R'] (f : R →ₐ[K] R'),
      spMap f.toRingHom ≫ spMap ((algebraMap K R).comp β) = spMap ((algebraMap K R').comp β) := by
    intro R R' _ _ _ _ f
    rw [spMap_comp_spMap', ← RingHom.comp_assoc]
    congr 2
    ext x
    simp
  let Φ := TrivSqZeroExt.map (LinearMap.prod κ' (t • lam))
  let p₁ := TrivSqZeroExt.map (LinearMap.fst K K K)
  let p₂ := TrivSqZeroExt.map (LinearMap.snd K K K)
  let ι₁ := TrivSqZeroExt.map (LinearMap.inl K K K)
  let sm := TrivSqZeroExt.map (LinearMap.fst K K K + LinearMap.snd K K K)
  let mt := TrivSqZeroExt.map (t • LinearMap.id : K →ₗ[K] K)
  let cst : TrivSqZeroExt K (Fin r → K) →+* DualNumber K :=
    (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom
  let cD : DualNumber K →+* DualNumber K := (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have e1 : p₁.toRingHom.comp Φ.toRingHom = dirMap κ' := by
    ext x <;> simp [p₁, Φ, dirMap]
  have e2 : p₂.toRingHom.comp Φ.toRingHom = dirMap (t • lam) := by
    ext x <;> simp [p₂, Φ, dirMap]
  have e3 : mt.toRingHom.comp (dirMap lam) = dirMap (t • lam) := by
    ext x <;> simp [mt, dirMap]
  have e4 : mt.toRingHom.comp cst = cst := by
    ext x <;> simp [mt, cst]
  have e6 : p₁.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [p₁, ι₁]
  have e7 : p₂.toRingHom.comp ι₁.toRingHom = cD := by
    ext x <;> simp [p₂, ι₁, cD]
  have e8 : sm.toRingHom.comp Φ.toRingHom = dirMap (κ' + t • lam) := by
    ext x <;> simp [sm, Φ, dirMap]
  have e9 : sm.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [sm, ι₁]
  have e10 : cD.comp (dirMap κ') = cst := by
    ext x <;> simp [cD, cst, dirMap]
  have hconst : constPt (spMap (dirMap lam)) = spMap cst := by
    simp only [constPt, spMap_comp_spMap']
    congr 1
  obtain ⟨c', hc', hc'p⟩ := pull _ _ (spMap (dirMap κ')) (base (TrivSqZeroExt.map κ')) G hG
  obtain ⟨H, hH, hHp⟩ := pull _ _ (spMap Φ.toRingHom) (base Φ) G hG
  obtain ⟨H'', hH'', hH''p⟩ := pull _ _ (spMap ι₁.toRingHom) (base ι₁) c' hc'p
  obtain ⟨C1, hC1, -⟩ := pull _ (spMap p₁.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₁.toRingHom) rfl H hHp
  obtain ⟨C2, hC2, -⟩ := pull _ (spMap p₂.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₂.toRingHom) rfl H hHp
  have hC1G : SiegPB C1 G (spMap (dirMap κ')) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC1) (by rw [spMap_comp_spMap', e1])
  have hC1c' : SiegPB C1 c' (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq hC1G (by rw [Category.id_comp]))
  have hC1H'' : SiegPB C1 H'' (spMap p₁.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC1c' (by rw [spMap_comp_spMap', e6, spMap_id']))
  have hC2G : SiegPB C2 G (spMap (dirMap (t • lam))) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC2) (by rw [spMap_comp_spMap', e2])
  have h₂' : SiegPB c₃ G (spMap cst) := pbEq h₂ hconst
  have hC2m : SiegPB C2 c₃ (spMap mt.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel h₁ (pbEq hC2G (by rw [spMap_comp_spMap', e3]))
  have hC2Gc : SiegPB C2 G (spMap cst) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp h₂' hC2m) (by rw [spMap_comp_spMap', e4])
  have hC2c₃ : SiegPB C2 c₃ (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel h₂' (pbEq hC2Gc (by rw [Category.id_comp]))
  have hc₃c' : SiegPB c₃ c' (spMap cD) :=
    GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq h₂' (by rw [spMap_comp_spMap', e10]))
  have hC2c' : SiegPB C2 c' (spMap cD) := pbEq (GlobalTheory.SiegelPullComp.pb_comp hc₃c' hC2c₃) (by rw [Category.id_comp])
  have hC2H'' : SiegPB C2 H'' (spMap p₂.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC2c' (by rw [spMap_comp_spMap', e7]))
  have hpb := GlobalTheory.T.trivial_square_zero_extension_pullback K (K × K) K K (LinearMap.fst K K K) (LinearMap.snd K K K)
    ⟨fun a b hab => by simpa using hab, fun y => ⟨y, by simp⟩⟩
  have hsurj : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hHH : SiegPB H'' H (𝟙 _) :=
    GlobalTheory.T.principalSiegelObject_determined_over_artinianPinch g n h3 hodd (CommRingCat.of (TrivSqZeroExt K (K × K))) (CommRingCat.of (DualNumber K))
      (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _ hpb (isLocalRing_sq K) (isArtinianRing_sq K)
      hsurj hsurj (CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (K × K))).comp β)) H H'' C1 C2 hHp hH''p
      hC1 hC1H'' hC2 hC2H''
  have hc₁H : SiegPB c₁ H (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH (pbEq h₃ (by rw [spMap_comp_spMap', e8]))
  have hc₁H'' : SiegPB c₁ H'' (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hHH (pbEq hc₁H (by rw [Category.comp_id]))
  have hc₁c' : SiegPB c₁ c' (𝟙 _) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH'' hc₁H'') (by rw [spMap_comp_spMap', e9, spMap_id'])
  exact pbEq (GlobalTheory.SiegelPullComp.pb_comp hc' hc₁c') (by rw [Category.id_comp])

end GlobalTheory.SiegTanShift
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObject_tangentShift_constancy_direction_iso : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] (r : ℕ) (β : cycAway n →+* K) (G : SiegPre g n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), G.Principal → ∀ (lam κ κ' : (Fin r → K) →ₗ[K] K) (t : K) (c₃ c₁ : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), κ = κ' + t • lam → SiegPB c₃ G (spMap (dirMap lam)) → SiegPB c₃ G (constPt (spMap (dirMap lam))) → SiegPB c₁ G (spMap (dirMap κ)) → SiegPB c₁ G (spMap (dirMap κ')) := by
  atlas_forward_decl GlobalTheory.SiegTanShift.shift
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.FirstOrderSiegel

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

variable {h k : ℕ}

theorem isLocalRing_tsze (K : Type) [Field K] (r : ℕ) : IsLocalRing (TrivSqZeroExt K (Fin r → K)) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_tsze (K : Type) [Field K] (r : ℕ) : IsArtinianRing (TrivSqZeroExt K (Fin r → K)) :=
  haveI : Module.Finite K (TrivSqZeroExt K (Fin r → K)) := inferInstanceAs (Module.Finite K (K × (Fin r → K)))
  IsArtinianRing.of_finite K _

theorem pull_exists {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre h k ζ s) :
    ∃ c' : SiegPre h k ζ s', SiegPB c' c f ∧ (c.Principal → c'.Principal) := by
  have e : f ≫ s = s' ≫ spMap (RingHom.id B) := by
    rw [hf]
    simp [spMap]
  have H := siegPre_pull_ringChange h k B B ζ ζ (RingHom.id B) S S' s s' f rfl e
  obtain ⟨c', hc'⟩ := H.1 c
  exact ⟨c', hc', H.2.1 c c' hc'⟩

theorem pb_symm {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S ⟶ Sp B'} {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} (m : SiegPB c' c (𝟙 S)) : SiegPB c c' (𝟙 S) :=
  pb_cancel m (by rw [Category.comp_id]; exact pb_id c)

theorem constPt_comp {K : Type} [Field K] {X Y : Scheme.{0}} (x : Sp (DualNumber K) ⟶ X) (z : X ⟶ Y) :
    constPt (x ≫ z) = constPt x ≫ z := by
  unfold constPt
  simp only [Category.assoc]

theorem base_map {K o V W : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] (β : o →+* K)
    (L : V →ₗ[K] W) : spMap (TrivSqZeroExt.map L).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) =
      spMap ((algebraMap K (TrivSqZeroExt K W)).comp β) := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.map L).commutes (β z)

theorem fst_base {K o V : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] (β : o →+* K) :
    spMap (TrivSqZeroExt.fstHom K K V).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) = spMap β := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.fstHom K K V).commutes (β z)

theorem constPt_base {K o : Type} [Field K] [CommRing o] {X : Scheme.{0}} (β : o →+* K) (x : Sp (DualNumber K) ⟶ X)
    (s : X ⟶ Sp o) (hx : x ≫ s = spMap ((algebraMap K (DualNumber K)).comp β)) :
    constPt x ≫ s = x ≫ s := by
  unfold constPt
  rw [Category.assoc, Category.assoc, hx, fst_base, ← spMap_comp']

theorem dirMap_comp {K : Type} [Field K] {r m : ℕ} (mu : (Fin m → K) →ₗ[K] K) (L : (Fin r → K) →ₗ[K] (Fin m → K)) :
    spMap (dirMap (mu ∘ₗ L)) = spMap (dirMap mu) ≫ spMap (TrivSqZeroExt.map L).toRingHom := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dirMap]) (by simp [dirMap])

def drop (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) := GlobalTheory.InnerAutomorphism.dropLast K d

def lastC (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] K := LinearMap.proj (Fin.last d)

def incl (K : Type) [Field K] (d : ℕ) : (Fin d → K) →ₗ[K] (Fin (d + 1) → K) where
  toFun w := Fin.snoc w 0
  map_add' w w' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' a w := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem bij_drop_last (K : Type) [Field K] (d : ℕ) : Function.Bijective ((drop K d).prod (lastC K d)) := by
  refine ⟨fun v w hvw => ?_, fun p => ⟨Fin.snoc p.1 p.2, ?_⟩⟩
  · have h1 := congrArg Prod.fst hvw
    have h2 := congrArg Prod.snd hvw
    simp only [LinearMap.prod_apply, Pi.prod] at h1 h2
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h2
    · exact congrFun h1 j
  · ext j <;> simp [drop, lastC]

theorem lam_decomp (K : Type) [Field K] (d : ℕ) (lam : (Fin (d + 1) → K) →ₗ[K] K) :
    lam = (lam ∘ₗ incl K d) ∘ₗ drop K d + lam (Pi.single (Fin.last d) 1) • lastC K d := by
  refine LinearMap.ext fun v => ?_
  have hv : v = incl K d (drop K d v) + v (Fin.last d) • Pi.single (Fin.last d) 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [incl]
    · simp [incl, drop, Pi.single_apply, Fin.castSucc_ne_last]
  conv_lhs => rw [hv]
  simp [lastC, mul_comm]

theorem classified_dualNumber_of_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β₀ : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ _ β₀ c hc

  obtain ⟨c₀, hc₀, hc₀p⟩ := pull_exists (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (fst_base β₀) c
  obtain ⟨x₀, hx₀s, hx₀⟩ := GlobalTheory.T.siegel_family_classifies_principal_algClosed g n hg hn hodd F K β₀ c₀ (hc₀p hc)

  obtain ⟨y, hy₀, hys, hyinj⟩ := GlobalTheory.T.exists_firstOrder_tangentPoint_smooth F.X F.s (g * (g + 1) / 2) F.smooth K β₀ x₀ hx₀s
  obtain ⟨cy, hcy, hcyp⟩ := pull_exists y hys F.univ
  have h0y : SiegPB c₀ cy (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) :=
    pb_cancel hcy (by rw [hy₀]; exact hx₀)

  have hsq := GlobalTheory.T.trivial_square_zero_extension_pullback K (Fin (g * (g + 1) / 2 + 1) → K) (Fin (g * (g + 1) / 2) → K) K (drop K _) (lastC K _)
    (bij_drop_last K _)
  let β : CommRingCat.of (cycAway n) ⟶ CommRingCat.of (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K)) :=
    CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K))).comp β₀)
  obtain ⟨c₁, hc₁, hc₁p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) cy
  obtain ⟨c₂, hc₂, hc₂p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (lastC K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) c
  obtain ⟨c₀', hc₀', -⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by
      rw [Category.id_comp]
      exact ((congrArg (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom ≫ ·)
        (base_map β₀ (drop K _))).trans (fst_base β₀)).symm) c₀
  have h01 : SiegPB c₀' c₁ (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₁) h0y) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  have h02 : SiegPB c₀' c₂ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₂) hc₀) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  obtain ⟨G, hGp, hG1, hG2⟩ := GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct g n hn hodd _ _ (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _
    hsq (isLocalRing_tsze K _) (isArtinianRing_tsze K _) (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) β c₁ c₂ (hc₁p (hcyp F.princ)) (hc₂p hc) ⟨c₀', h01, h02⟩
  have hGy : SiegPB cy G (spMap (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) := by
    have := pb_comp hG1 (pb_symm hc₁)
    rwa [Category.id_comp] at this
  have hGc : SiegPB c G (spMap (dirMap (lastC K (g * (g + 1) / 2)))) := by
    have := pb_comp hG2 (pb_symm hc₂)
    rwa [Category.id_comp] at this

  have htb := GlobalTheory.T.siegelFamily_tangentBound_nonconstant g n hg hn hodd K (g * (g + 1) / 2 + 1) β₀ G hGp
  obtain ⟨lam, c', h1, h2, hlam⟩ : ∃ (lam : (Fin (g * (g + 1) / 2 + 1) → K) →ₗ[K] K)
      (c' : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))),
      SiegPB c' G (spMap (dirMap lam)) ∧ SiegPB c' G (constPt (spMap (dirMap lam))) ∧ lam ≠ 0 := by
    by_contra hne
    push_neg at hne
    have := htb fun lam c' h1 h2 => hne lam c' h1 h2
    omega
  obtain ⟨mu, a, hdec⟩ : ∃ (mu : (Fin (g * (g + 1) / 2) → K) →ₗ[K] K) (a : K),
      lam = mu ∘ₗ drop K _ + a • lastC K _ := ⟨_, _, lam_decomp K _ lam⟩
  by_cases ha : a = 0
  ·
    exfalso
    rw [ha, zero_smul, add_zero] at hdec
    subst hdec
    rw [dirMap_comp] at h1 h2
    rw [constPt_comp] at h2
    have k1 : SiegPB c' F.univ (spMap (dirMap mu) ≫ y) := pb_comp hcy (pb_cancel hGy h1)
    have k2 : SiegPB c' F.univ (constPt (spMap (dirMap mu) ≫ y)) := by
      rw [constPt_comp]
      exact pb_comp hcy (pb_cancel hGy h2)
    have hxs : (spMap (dirMap mu) ≫ y) ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) := by
      rw [Category.assoc, hys]
      exact base_map β₀ mu
    obtain ⟨c'', hc'', -⟩ := pull_exists (𝟙 _) (s' := (spMap (dirMap mu) ≫ y) ≫ F.s)
      (by rw [Category.id_comp, hxs]) c'
    have e := F.eq_constPt K (spMap (dirMap mu) ≫ y) c'' (constPt_base β₀ _ _ hxs).symm
      (by have := pb_comp k1 hc''; rwa [Category.id_comp] at this)
      (by have := pb_comp k2 hc''; rwa [Category.id_comp] at this)
    have := hyinj mu e
    subst this
    exact hlam (by simp)
  ·
    have hκ : lastC K (g * (g + 1) / 2) = ((-a⁻¹) • mu) ∘ₗ drop K _ + a⁻¹ • lam := by
      rw [hdec]
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, neg_mul]
      field_simp
      ring
    have k := GlobalTheory.T.siegelObject_tangentShift_constancy_direction_iso g n hn hodd K _ β₀ G hGp lam _ _ a⁻¹ c' c hκ h1 h2 hGc
    rw [dirMap_comp] at k
    refine ⟨spMap (dirMap ((-a⁻¹) • mu)) ≫ y, ?_, pb_comp hcy (pb_cancel hGy k)⟩
    rw [Category.assoc, hys]
    exact base_map β₀ _

end GlobalTheory.FirstOrderSiegel

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_point_lifts_to_dual_numbers : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β₀ : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) ∧ SiegPB c F.univ f := by
  atlas_forward_decl GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangent

theorem cycAway_dualNumber_factor {n : ℕ} (hn : n ≠ 0) (K : Type) [Field K] (β : cycAway n →+* DualNumber K) :
    ∃ β₀ : cycAway n →+* K, β = (algebraMap K (DualNumber K)).comp β₀ := by
  let π : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  have hnK : (n : K) ≠ 0 := by
    have := ((isUnit_natCast hn).map (π.comp β)).ne_zero
    simpa using this
  let S : Subring (cycAway n) :=
    { carrier := {x | TrivSqZeroExt.snd (β x) = 0}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, TrivSqZeroExt.snd_mul] at *
        simp [ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add, TrivSqZeroExt.snd_add] at *
        simp [ha, hb]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_neg, TrivSqZeroExt.snd_neg] at *
        simp [ha] }
  have hζ : zetaAway n ∈ S := by
    have hz : zetaAway n ^ n = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one
    have h1 : β (zetaAway n) ^ n = 1 := by rw [← map_pow, hz, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    have h3 := congrArg TrivSqZeroExt.fst h1
    rw [TrivSqZeroExt.snd_pow] at h2
    rw [TrivSqZeroExt.fst_pow] at h3
    simp only [TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one] at h2 h3
    have ha : TrivSqZeroExt.fst (β (zetaAway n)) ≠ 0 := by
      intro h0; rw [h0, zero_pow hn] at h3; exact zero_ne_one h3
    show TrivSqZeroExt.snd (β (zetaAway n)) = 0
    rw [nsmul_eq_mul, smul_eq_mul] at h2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' (pow_ne_zero _ ha)
      · exact h'
  have hinv : (⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway n) ∈ S := by
    set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
    have hu : (n : cycAway n) * u = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
    have h1 : (n : DualNumber K) * β u = 1 := by rw [← map_natCast β, ← map_mul, hu, map_one]
    have h2 := congrArg TrivSqZeroExt.snd h1
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_natCast,
      TrivSqZeroExt.snd_natCast, smul_zero, add_zero, smul_eq_mul] at h2
    show TrivSqZeroExt.snd (β u) = 0
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hnK
    · exact h
  have hall : ∀ x : cycAway n, x ∈ S := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact hζ
      · exact hinv
    | zero => exact S.zero_mem
    | one => exact S.one_mem
    | add y z _ _ hy hz => exact S.add_mem hy hz
    | neg y _ hy => exact S.neg_mem hy
    | mul y z _ _ hy hz => exact S.mul_mem hy hz
  refine ⟨π.comp β, RingHom.ext fun x => ?_⟩
  ext
  · rfl
  · exact (hall x).trans (TrivSqZeroExt.snd_inl _ _).symm

theorem classified_dualNumber : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K]
    (β : cycAway n →+* DualNumber K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal →
    ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ β c hc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨β₀, rfl⟩ := cycAway_dualNumber_factor hn0 K β
  let L := AlgebraicClosure K
  obtain ⟨ψ, h1, -, hfl, hsurj⟩ := GlobalTheory.DualOpen.dualNumber_map_flat_surjective K L (algebraMap K L)
  have hff : ψ.FaithfullyFlat := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom ψ)).1 ⟨hfl, hsurj⟩
  letI : Algebra (DualNumber K) (DualNumber L) := ψ.toAlgebra
  haveI : Module.FaithfullyFlat (DualNumber K) (DualNumber L) := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  refine GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat g n hg hn hodd F (DualNumber K) (DualNumber L) _ c hc ?_
  intro c' hc'
  have hp : c'.Principal := by
    refine (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) _ _ (spMap ((algebraMap K (DualNumber K)).comp β₀))
      (spMap ((algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀)))
      (spMap (algebraMap (DualNumber K) (DualNumber L))) rfl ?_).2.1 c c' hc' hc
    rw [GlobalTheory.SiegelRingChange.spMap_comp']
    simp [spMap]
  have e : (algebraMap (DualNumber K) (DualNumber L)).comp ((algebraMap K (DualNumber K)).comp β₀) =
      (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    exact congrArg (fun q => q.comp β₀) h1
  have key : ∀ b : cycAway n →+* DualNumber L, b = (algebraMap L (DualNumber L)).comp ((algebraMap K L).comp β₀) →
      ∀ c' : SiegPre g n (zetaAway n) (spMap b), c'.Principal →
      ∃ f : Sp (DualNumber L) ⟶ F.X, f ≫ F.s = spMap b ∧ SiegPB c' F.univ f := by
    rintro b rfl c' hc'
    exact GlobalTheory.T.siegel_point_lifts_to_dual_numbers g n hg hn hodd F L ((algebraMap K L).comp β₀) c' hc'
  exact key _ e c' hp

end GlobalTheory.SiegelTangent
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelObject_dualNumber_classified : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] (β : cycAway n →+* DualNumber K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  atlas_forward_decl GlobalTheory.SiegelTangent.classified_dualNumber
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.SmallGlue
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem spec_localArtinian_point_eq (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P]
    (x y : Spec P) : x = y := by
  apply PrimeSpectrum.ext
  haveI := x.isPrime
  haveI := y.isPrime
  rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime x.asIdeal),
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime y.asIdeal)]

theorem spec_map_injective_of_surjective {R S : CommRingCat.{0}} (f : R ⟶ S) (hf : Function.Surjective f) :
    Function.Injective (Spec.map f) := fun x y h =>
  PrimeSpectrum.comap_injective_of_surjective f.hom hf h

theorem spec_pullback_localArtinian_glue_existsUnique : ∀ (P B₁ B₂ B₀ : CommRingCat.{0}) (f₁ : P ⟶ B₁) (f₂ : P ⟶ B₂) (g₁ : B₁ ⟶ B₀) (g₂ : B₂ ⟶ B₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective f₁ → Function.Surjective f₂ → Nontrivial B₀ → ∀ (Z : Scheme.{0}) (a : Spec B₁ ⟶ Z) (b : Spec B₂ ⟶ Z), Spec.map g₁ ≫ a = Spec.map g₂ ≫ b → ∃! w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a ∧ Spec.map f₂ ≫ w = b := by
  intro P B₁ B₂ B₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ hnt Z a b hab
  have hnt₁ : Nontrivial B₁ := RingHom.domain_nontrivial g₁.hom
  have hnt₂ : Nontrivial B₂ := RingHom.domain_nontrivial g₂.hom
  obtain ⟨y₀⟩ : Nonempty (Spec B₀) := inferInstanceAs (Nonempty (PrimeSpectrum B₀))
  have hone₁ : ∀ y y' : Spec B₁, y = y' := fun y y' =>
    spec_map_injective_of_surjective f₁ hs₁ (spec_localArtinian_point_eq P _ _)
  have hone₂ : ∀ y y' : Spec B₂, y = y' := fun y y' =>
    spec_map_injective_of_surjective f₂ hs₂ (spec_localArtinian_point_eq P _ _)
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := a (Spec.map g₁ y₀)) trivial
  have hza : Set.range a ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩; rw [hV.range_fromSpec, hone₁ y (Spec.map g₁ y₀)]; exact hzV
  have hzb : Set.range b ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    rw [hV.range_fromSpec, hone₂ y (Spec.map g₂ y₀)]
    have : b (Spec.map g₂ y₀) = a (Spec.map g₁ y₀) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hab]
    rw [this]; exact hzV
  haveI := hV.isOpenImmersion_fromSpec
  set φ₁ := Spec.preimage (IsOpenImmersion.lift hV.fromSpec a hza) with hφ₁
  set φ₂ := Spec.preimage (IsOpenImmersion.lift hV.fromSpec b hzb) with hφ₂
  have ha : Spec.map φ₁ ≫ hV.fromSpec = a := by
    rw [hφ₁, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hb : Spec.map φ₂ ≫ hV.fromSpec = b := by
    rw [hφ₂, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hφ : φ₁ ≫ g₁ = φ₂ ≫ g₂ := by
    apply Spec.map_injective
    rw [← cancel_mono hV.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha, hb, hab]
  have key : ∀ w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a → Spec.map f₂ ≫ w = b →
      w = Spec.map (hP.lift φ₁ φ₂ hφ) ≫ hV.fromSpec := by
    intro w hw₁ hw₂
    have hr : Set.range w ⊆ Set.range hV.fromSpec := by
      rintro _ ⟨x, rfl⟩
      rw [spec_localArtinian_point_eq P x (Spec.map f₁ (Spec.map g₁ y₀)), ← Scheme.Hom.comp_apply, hw₁]
      exact hza ⟨_, rfl⟩
    rw [← IsOpenImmersion.lift_fac hV.fromSpec w hr, ← Spec.map_preimage (IsOpenImmersion.lift hV.fromSpec w hr)]
    congr 2
    apply hP.hom_ext
    · rw [IsPullback.lift_fst]
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
        IsOpenImmersion.lift_fac, hw₁, ha]
    · rw [IsPullback.lift_snd]
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
        IsOpenImmersion.lift_fac, hw₂, hb]
  refine ⟨Spec.map (hP.lift φ₁ φ₂ hφ) ≫ hV.fromSpec, ⟨?_, ?_⟩, fun w hw => key w hw.1 hw.2⟩
  · rw [← Category.assoc, ← Spec.map_comp, IsPullback.lift_fst, ha]
  · rw [← Category.assoc, ← Spec.map_comp, IsPullback.lift_snd, hb]

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.SmallGlue
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_fibreProduct_localArtinian_glue_existsUnique : ∀ (P B₁ B₂ B₀ : CommRingCat.{0}) (f₁ : P ⟶ B₁) (f₂ : P ⟶ B₂) (g₁ : B₁ ⟶ B₀) (g₂ : B₂ ⟶ B₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective f₁ → Function.Surjective f₂ → Nontrivial B₀ → ∀ (Z : Scheme.{0}) (a : Spec B₁ ⟶ Z) (b : Spec B₂ ⟶ Z), Spec.map g₁ ≫ a = Spec.map g₂ ≫ b → ∃! w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a ∧ Spec.map f₂ ≫ w = b := by
  atlas_forward_decl GlobalTheory.spec_pullback_localArtinian_glue_existsUnique
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SmallClassify

theorem lift_lemma : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (d : ℕ), SmoothOfRelativeDimension d s → ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e * e = 0 → ∀ (β : R →+* C) (x₀ : Sp (C ⧸ Ideal.span {e}) ⟶ X), x₀ ≫ s = spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β) → ∃ x₁ : Sp C ⟶ X, x₁ ≫ s = spMap β ∧ spMap (Ideal.Quotient.mk (Ideal.span {e})) ≫ x₁ = x₀ := by
  intro R _ X s d hs C _ _ e hee β x₀ hx₀
  haveI : Smooth s := hs.smooth
  let πC : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ Ideal.span {e}) := CommRingCat.ofHom (Ideal.Quotient.mk _)
  have hsurj : Function.Surjective πC := Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion (Spec.map πC) := IsClosedImmersion.spec_of_surjective _ hsurj
  have hnil : IsNilpotent (RingHom.ker πC.hom) := by
    refine ⟨2, ?_⟩
    show (RingHom.ker (Ideal.Quotient.mk (Ideal.span {e}))) ^ 2 = ⊥
    rw [Ideal.mk_ker, pow_two, Ideal.span_singleton_mul_span_singleton, hee, Ideal.span_singleton_eq_bot.2 rfl]
  have hw : x₀ ≫ s = Spec.map πC ≫ spMap β := by
    rw [hx₀, GlobalTheory.SiegelRingChange.spMap_comp']
  obtain ⟨W, hW, l, hl, hl'⟩ := GlobalTheory.exists_local_lift_of_smooth s (Spec.map πC) (GlobalTheory.isNilpotent_ker_specMap πC hnil)
    x₀ (spMap β) hw (IsLocalRing.closedPoint (CommRingCat.of C))
  have hWt : W = ⊤ := (IsLocalRing.closed_point_mem_iff (R := CommRingCat.of C) (U := W)).mp hW
  subst hWt
  haveI : IsIso (⊤ : (Sp C).Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have hU : IsIso ((Spec.map πC) ⁻¹ᵁ (⊤ : (Sp C).Opens)).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  refine ⟨inv (⊤ : (Sp C).Opens).ι ≫ l, by rw [Category.assoc, hl, IsIso.inv_hom_id_assoc], ?_⟩
  rw [← cancel_epi ((Spec.map πC) ⁻¹ᵁ (⊤ : (Sp C).Opens)).ι, ← hl', ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (⊤ : (Sp C).Opens).ι, Category.assoc, IsIso.inv_hom_id, Category.comp_id, morphismRestrict_ι]

theorem isPullback_of_bij {P A B D : CommRingCat.{0}} (f₁ : P ⟶ A) (f₂ : P ⟶ B) (g₁ : A ⟶ D) (g₂ : B ⟶ D)
    (w : f₁ ≫ g₁ = f₂ ≫ g₂) (hinj : ∀ x, f₁ x = 0 → f₂ x = 0 → x = 0)
    (hsurj : ∀ a b, g₁ a = g₂ b → ∃ x, f₁ x = a ∧ f₂ x = b) : IsPullback f₁ f₂ g₁ g₂ := by
  have hw : ∀ x, g₁ (f₁ x) = g₂ (f₂ x) := fun x => by
    have := congrArg (fun h : P ⟶ D => h x) w
    simpa using this
  let Q := RingHom.eqLocus (g₁.hom.comp (RingHom.fst A B)) (g₂.hom.comp (RingHom.snd A B))
  let φ : P →+* Q := (f₁.hom.prod f₂.hom).codRestrict Q (fun x => hw x)
  have hφ : Function.Bijective φ := by
    refine ⟨(injective_iff_map_eq_zero φ).2 fun x hx => hinj x ?_ ?_, fun y => ?_⟩
    · exact congrArg (fun z : Q => (z : A × B).1) hx
    · exact congrArg (fun z : Q => (z : A × B).2) hx
    · obtain ⟨x, h1, h2⟩ := hsurj (y : A × B).1 (y : A × B).2 y.2
      exact ⟨x, Subtype.ext (Prod.ext h1 h2)⟩
  let E : P ≅ CommRingCat.of Q := (RingEquiv.ofBijective φ hφ).toCommRingCatIso
  have h0 := IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit g₁ g₂)
  refine IsPullback.of_iso h0 E.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · ext y
    obtain ⟨x, rfl⟩ := hφ.2 y
    have : E.inv (φ x) = x := (RingEquiv.ofBijective φ hφ).symm_apply_apply x
    change (φ x : A × B).1 = f₁ (E.inv (φ x))
    rw [this]; rfl
  · ext y
    obtain ⟨x, rfl⟩ := hφ.2 y
    have : E.inv (φ x) = x := (RingEquiv.ofBijective φ hφ).symm_apply_apply x
    change (φ x : A × B).2 = f₂ (E.inv (φ x))
    rw [this]; rfl

open IsLocalRing in

theorem ring_lemma : ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∃ (P : CommRingCat.{0}) (i : CommRingCat.of C ⟶ P) (p σ : P ⟶ CommRingCat.of C) (q : P ⟶ CommRingCat.of (DualNumber (IsLocalRing.ResidueField C))), i ≫ p = 𝟙 _ ∧ i ≫ σ = 𝟙 _ ∧ IsPullback p σ (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ∧ IsPullback p q (CommRingCat.ofHom (IsLocalRing.residue C)) (CommRingCat.ofHom (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField C) (IsLocalRing.ResidueField C)).toRingHom) ∧ IsLocalRing P ∧ IsArtinianRing P ∧ Function.Surjective p ∧ Function.Surjective q := by
  intro C _ _ _ e he hm hne
  have hee : e * e = 0 := hm e he
  obtain ⟨φ, hφ⟩ : ∃ φ : ResidueField C →+ C, ∀ c, φ (residue C c) = c * e := by
    refine ⟨(Submodule.liftQ (maximalIdeal C) (LinearMap.toSpanSingleton C C e) ?_).toAddMonoidHom, fun c ↦ ?_⟩
    · intro a ha
      simpa using hm a ha
    · rfl
  have hφ0 : ∀ x, φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ] at hx
    rw [residue_eq_zero_iff]
    by_contra hc
    have hu : IsUnit c := by simpa using hc
    exact hne (hu.mul_right_eq_zero.mp hx)
  let dF : DualNumber (ResidueField C) →+* ResidueField C :=
    (TrivSqZeroExt.fstHom (ResidueField C) (ResidueField C) (ResidueField C)).toRingHom
  let Ps : Subring (C × DualNumber (ResidueField C)) :=
    RingHom.eqLocus ((residue C).comp (RingHom.fst _ _)) (dF.comp (RingHom.snd _ _))
  let p : Ps →+* C := (RingHom.fst _ _).comp Ps.subtype
  let q : Ps →+* DualNumber (ResidueField C) := (RingHom.snd _ _).comp Ps.subtype
  let i : C →+* Ps := RingHom.codRestrict ((RingHom.id C).prod
    ((algebraMap (ResidueField C) (DualNumber (ResidueField C))).comp (residue C))) Ps (fun c ↦ rfl)
  let σ : Ps →+* C :=
    { toFun := fun x ↦ x.1.1 + φ x.1.2.snd
      map_one' := by simp
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add, TrivSqZeroExt.snd_add, map_add]
        ring
      map_mul' := by
        rintro ⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩
        have hx' : residue C a = x.fst := hx
        have hy' : residue C b = y.fst := hy
        obtain ⟨c, hc⟩ := residue_surjective (R := C) x.snd
        obtain ⟨d, hd⟩ := residue_surjective (R := C) y.snd
        show a * b + φ (x * y).snd = (a + φ x.snd) * (b + φ y.snd)
        rw [DualNumber.snd_mul, ← hx', ← hy', ← hc, ← hd, ← map_mul, ← map_mul, ← map_add, hφ, hφ, hφ]
        linear_combination (-(c * d)) * hee }
  have hσi : σ.comp i = RingHom.id C := by
    ext c
    show c + φ (TrivSqZeroExt.inl (residue C c) : DualNumber _).snd = c
    simp
  have hφmem : ∀ x, φ x ∈ Ideal.span {e} := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ]
    exact Ideal.mem_span_singleton'.2 ⟨c, rfl⟩

  have hunit : ∀ x : Ps, IsUnit (x : C × DualNumber (ResidueField C)).1 → IsUnit x := by
    rintro ⟨⟨a, y⟩, hx⟩ ha
    have hx' : residue C a = y.fst := hx
    have hy : IsUnit y := by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, ← hx']
      exact ha.map _
    obtain ⟨u, hu⟩ := (Prod.isUnit_iff (x := (a, y))).2 ⟨ha, hy⟩
    have hmem : ((u⁻¹ : (C × DualNumber (ResidueField C))ˣ) : C × DualNumber (ResidueField C)) ∈ Ps := by
      show ((residue C).comp (RingHom.fst _ _)) _ = (dF.comp (RingHom.snd _ _)) _
      rw [map_units_inv, map_units_inv, hu]
      exact congrArg (·⁻¹) hx
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    show (a, y) * _ = 1
    rw [← hu, Units.mul_inv]
  haveI : Nontrivial Ps := nontrivial_of_ne 0 1 (fun h ↦ zero_ne_one (α := C) (congrArg (fun z : Ps ↦ (z : C × DualNumber (ResidueField C)).1) h))
  have hloc : IsLocalRing Ps := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (x : C × DualNumber (ResidueField C)).1).imp (hunit x) (fun h ↦ hunit (1 - x) (by simpa using h))

  letI : Algebra C Ps := i.toAlgebra
  let ε' : Ps := ⟨(0, TrivSqZeroExt.inr 1), by show residue C 0 = (0 : ResidueField C); simp⟩
  have hfin : Module.Finite C Ps := by
    classical
    refine ⟨⟨({1, ε'} : Finset Ps), eq_top_iff.2 fun x _ ↦ ?_⟩⟩
    obtain ⟨⟨a, y⟩, hx⟩ := x
    have hx' : residue C a = y.fst := hx
    obtain ⟨c, hc⟩ := residue_surjective (R := C) y.snd
    have : (⟨(a, y), hx⟩ : Ps) = a • (1 : Ps) + c • ε' := by
      rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one]
      refine Subtype.ext (Prod.ext ?_ ?_)
      · show a = a + c * 0
        ring
      · show y = TrivSqZeroExt.inl (residue C a) + TrivSqZeroExt.inl (residue C c) * TrivSqZeroExt.inr 1
        rw [TrivSqZeroExt.inl_mul_inr]
        ext
        · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, hx']
        · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, zero_add, TrivSqZeroExt.snd_inr,
            smul_eq_mul, _root_.mul_one, hc]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hart : IsArtinianRing Ps := IsArtinianRing.of_finite C Ps
  refine ⟨CommRingCat.of Ps, CommRingCat.ofHom i, CommRingCat.ofHom p, CommRingCat.ofHom σ, CommRingCat.ofHom q,
    by ext c; rfl, by ext c; exact RingHom.congr_fun hσi c, ?_, ?_, hloc, hart, fun c ↦ ⟨i c, rfl⟩, fun y ↦ ?_⟩
  · refine isPullback_of_bij _ _ _ _ ?_ ?_ ?_
    · ext x
      show Ideal.Quotient.mk _ x.1.1 = Ideal.Quotient.mk _ (x.1.1 + φ x.1.2.snd)
      refine (Ideal.Quotient.eq.2 ?_).symm
      simpa using hφmem _
    · rintro ⟨⟨a, x⟩, hx⟩ h1 h2
      have hx' : residue C a = x.fst := hx
      have h1' : a = 0 := h1
      have h2' : a + φ x.snd = 0 := h2
      subst h1'
      rw [zero_add] at h2'
      refine Subtype.ext (Prod.ext rfl ?_)
      show x = 0
      ext
      · simp [← hx']
      · simpa using hφ0 _ h2'
    · intro a b hab
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hab.symm)
      refine ⟨⟨(a, ⟨residue C a, residue C c⟩), rfl⟩, rfl, ?_⟩
      show a + φ (residue C c) = b
      rw [hφ, hc]
      ring
  · refine isPullback_of_bij _ _ _ _ ?_ ?_ ?_
    · ext x
      exact x.2
    · intro x h1 h2
      exact Subtype.ext (Prod.ext h1 h2)
    · intro a b hab
      exact ⟨⟨(a, b), hab⟩, rfl, rfl⟩
  · obtain ⟨a, ha⟩ := residue_surjective (R := C) y.fst
    exact ⟨⟨(a, y), ha⟩, rfl⟩

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem pull_ex {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre g n ζ s) :
    ∃ c' : SiegPre g n ζ s', SiegPB c' c f ∧ (c.Principal → c'.Principal) := by
  have hf' : f ≫ s = s' ≫ spMap (RingHom.id B) := by
    rw [hf, show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  have H := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n B B ζ ζ (RingHom.id B) S S' s s' f rfl hf'
  obtain ⟨c', hc'⟩ := H.1 c
  exact ⟨c', hc', H.2.1 c c' hc'⟩

theorem classified_of_small : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c₀ : SiegPre g n (zetaAway n) (spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β)), SiegPB c₀ c (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → ∃ f : Sp (C ⧸ Ideal.span {e}) ⟶ F.X, f ≫ F.s = spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β) ∧ SiegPB c₀ F.univ f) → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F C _ _ _ e he hme β c hc hcl
  set π := Ideal.Quotient.mk (Ideal.span {e}) with hπ
  obtain ⟨c₀, hc₀, -⟩ := pull_ex (s := spMap β) (s' := spMap (π.comp β)) (spMap π) (spMap_comp' β π).symm c
  obtain ⟨x₀, hx₀s, hx₀⟩ := hcl c₀ hc₀
  by_cases he0 : e = 0
  · have hker : ∀ a ∈ Ideal.span {e}, (RingHom.id C) a = 0 := by
      intro a ha
      rw [he0] at ha
      simpa using Ideal.mem_span_singleton.1 ha
    let ψ : C ⧸ Ideal.span {e} →+* C := Ideal.Quotient.lift _ (RingHom.id C) hker
    have hψπ : ψ.comp π = RingHom.id C := RingHom.ext fun a => by
      show ψ (π a) = a
      exact Ideal.Quotient.lift_mk _ _ _
    refine ⟨spMap ψ ≫ x₀, ?_, ?_⟩
    · rw [Category.assoc, hx₀s, ← spMap_comp', ← RingHom.comp_assoc, hψπ, RingHom.id_comp]
    · have h1 : SiegPB c c₀ (spMap ψ) := pb_cancel hc₀ (by
        rw [← spMap_comp', hψπ, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]; exact pb_id c)
      exact pb_comp hx₀ h1
  obtain ⟨x₁, hx₁s, hx₁⟩ := lift_lemma _ F.X F.s _ F.smooth C e (hme e he) β x₀ hx₀s
  obtain ⟨P, i, p, σ, q, hip, hiσ, sq1, sq2, hPl, hPa, hps, hqs⟩ := ring_lemma C e he hme he0
  let βP : CommRingCat.of (cycAway n) ⟶ P := CommRingCat.ofHom β ≫ i
  have hpβ : Spec.map p ≫ Spec.map βP = spMap β := by
    rw [Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hip, Spec.map_id, Category.id_comp]
  have hσβ : Spec.map σ ≫ Spec.map βP = spMap β := by
    rw [Spec.map_comp, ← Category.assoc, ← Spec.map_comp, hiσ, Spec.map_id, Category.id_comp]
  let k := IsLocalRing.ResidueField C
  let β' : cycAway n →+* DualNumber k := (βP ≫ q).hom
  have hqβ : Spec.map q ≫ Spec.map βP = spMap β' := by
    rw [← Spec.map_comp]; rfl
  let πC : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ Ideal.span {e}) := CommRingCat.ofHom π
  obtain ⟨c₁, hc₁, hc₁p⟩ := pull_ex (s' := Spec.map p ≫ Spec.map βP) x₁ (by rw [hx₁s, hpβ]) F.univ
  obtain ⟨c₂, hc₂, hc₂p⟩ := pull_ex (s' := Spec.map σ ≫ Spec.map βP) (𝟙 _) (by rw [Category.id_comp, hσβ]) c
  obtain ⟨c₀', hc₀', -⟩ := pull_ex (s' := Spec.map πC ≫ Spec.map p ≫ Spec.map βP) x₀
    (by rw [hx₀s, hpβ, spMap_comp']) F.univ
  have h01 : SiegPB c₀' c₁ (spMap π) := pb_cancel hc₁ (by rw [hx₁]; exact hc₀')
  have h0c : SiegPB c₀' c₀ (𝟙 _) := pb_cancel hx₀ (by rw [Category.id_comp]; exact hc₀')
  have h0c' : SiegPB c₀' c (spMap π) := by simpa using pb_comp hc₀ h0c
  have h02 : SiegPB c₀' c₂ (spMap π) := pb_cancel hc₂ (by rw [Category.comp_id]; exact h0c')
  obtain ⟨e', he'p, he'1, he'2⟩ := GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct g n hn hodd P (CommRingCat.of C) (CommRingCat.of C)
    (CommRingCat.of (C ⧸ Ideal.span {e})) p σ πC πC sq1 hPl hPa Ideal.Quotient.mk_surjective
    Ideal.Quotient.mk_surjective βP c₁ c₂ (hc₁p F.princ) (hc₂p hc) ⟨c₀', h01, h02⟩
  obtain ⟨eε, heε, heεp⟩ := pull_ex (s' := Spec.map q ≫ Spec.map βP) (Spec.map q) rfl e'
  obtain ⟨eε', heε', heε'p⟩ := pull_ex (s' := spMap β') (𝟙 _) (by rw [Category.id_comp, hqβ]) eε
  obtain ⟨v, hvs, hv₀⟩ := GlobalTheory.T.siegelObject_dualNumber_classified g n hg hn hodd F k β' eε' (heε'p (heεp he'p))
  have hεε : SiegPB eε eε' (𝟙 _) := pb_cancel heε' (by rw [Category.id_comp]; exact pb_id eε)
  have hv : SiegPB eε F.univ v := by simpa using pb_comp hv₀ hεε
  let ρ : CommRingCat.of C ⟶ CommRingCat.of k := CommRingCat.ofHom (IsLocalRing.residue C)
  let ε₀ : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hw : Spec.map ρ ≫ Spec.map p = Spec.map ε₀ ≫ Spec.map q := by
    rw [← Spec.map_comp, ← Spec.map_comp, sq2.w]
  obtain ⟨ck, hck, -⟩ := pull_ex (s' := Spec.map ρ ≫ Spec.map p ≫ Spec.map βP) (Spec.map ρ) rfl c₁
  have hk1 : SiegPB ck F.univ (Spec.map ρ ≫ x₁) := pb_comp hc₁ hck
  have hk2 : SiegPB ck eε (Spec.map ε₀) := pb_cancel heε (by rw [← hw]; exact pb_comp he'1 hck)
  have hk3 : SiegPB ck F.univ (Spec.map ε₀ ≫ v) := pb_comp hv hk2
  have hglue : Spec.map ρ ≫ x₁ = Spec.map ε₀ ≫ v := by
    refine F.inj k _ _ _ ck ?_ hk1 hk3
    rw [Category.assoc, Category.assoc, hx₁s, hvs, ← hpβ, ← hqβ, ← Category.assoc, hw, Category.assoc]
  have hsq := GlobalTheory.T.spec_fibreProduct_localArtinian_glue_existsUnique P (CommRingCat.of C) (CommRingCat.of (DualNumber k)) (CommRingCat.of k) p q ρ ε₀ sq2
    hPl hPa hps hqs inferInstance
  obtain ⟨w, ⟨hw1, hw2⟩, -⟩ := hsq F.X x₁ v hglue
  have hws : w ≫ F.s = Spec.map βP := by
    obtain ⟨w', -, hu⟩ := hsq (Sp (cycAway n)) (x₁ ≫ F.s) (v ≫ F.s) (by
      rw [← Category.assoc, hglue, Category.assoc])
    have a1 := hu (w ≫ F.s) ⟨by rw [← Category.assoc, hw1], by rw [← Category.assoc, hw2]⟩
    have a2 := hu (Spec.map βP) ⟨by rw [hpβ, hx₁s], by rw [hqβ, hvs]⟩
    rw [a1, a2]
  obtain ⟨e'', he'', he''p⟩ := pull_ex (s' := Spec.map βP) w hws F.univ
  have hq1 : SiegPB c₁ e'' (Spec.map p) := pb_cancel he'' (by rw [hw1]; exact hc₁)
  have hq2 : SiegPB eε e'' (Spec.map q) := pb_cancel he'' (by rw [hw2]; exact hv)
  have hiso : SiegPB e' e'' (𝟙 _) := GlobalTheory.T.principalSiegelObject_determined_over_artinianPinch g n hn hodd P (CommRingCat.of C) (CommRingCat.of (DualNumber k))
    (CommRingCat.of k) p q ρ ε₀ sq2 hPl hPa IsLocalRing.residue_surjective (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩)
    βP e'' e' c₁ eε (he''p F.princ) he'p hq1 he'1 hq2 heε
  refine ⟨Spec.map σ ≫ w, by rw [Category.assoc, hws, hσβ], ?_⟩
  have hcc2 : SiegPB c c₂ (𝟙 _) := pb_cancel hc₂ (by rw [Category.id_comp]; exact pb_id c)
  have := pb_comp he'' (pb_comp hiso (pb_comp he'2 hcc2))
  simpa using this

end GlobalTheory.SmallClassify
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegPB_lift_of_quotient_lift : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c₀ : SiegPre g n (zetaAway n) (spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β)), SiegPB c₀ c (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → ∃ f : Sp (C ⧸ Ideal.span {e}) ⟶ F.X, f ≫ F.s = spMap ((Ideal.Quotient.mk (Ideal.span {e})).comp β) ∧ SiegPB c₀ F.univ f) → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  atlas_forward_decl GlobalTheory.SmallClassify.classified_of_small
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelArtin

theorem exists_socle (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    (hm : IsLocalRing.maximalIdeal C ≠ ⊥) :
    ∃ e : C, e ≠ 0 ∧ e ∈ IsLocalRing.maximalIdeal C ∧ ∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0 := by
  set m := IsLocalRing.maximalIdeal C
  have hnil : IsNilpotent m := (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp inferInstance
  have hex : ∃ k, m ^ k = ⊥ := by
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [hk]; rfl⟩
  classical
  let k := Nat.find hex
  have hk : m ^ k = ⊥ := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    have : m ^ k = ⊤ := by rw [h0, pow_zero, Ideal.one_eq_top]
    rw [this] at hk
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (top_le_iff.mp (hk ▸ bot_le))
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hk
    exact hm hk
  have hprev : m ^ (k - 1) ≠ ⊥ := Nat.find_min hex (by omega)
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprev
  refine ⟨e, he0, ?_, ?_⟩
  · exact Ideal.pow_le_self (by omega) he
  · intro a ha
    have : a * e ∈ m ^ k := by
      have hk' : k = (k - 1) + 1 := by omega
      rw [hk', pow_succ']
      exact Ideal.mul_mem_mul ha he
    rw [hk] at this
    simpa using this

theorem main : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F
  suffices H : ∀ (N : ℕ) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C],
      Module.length C C = N → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)),
      c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f by
    intro C _ _ _ β c hc
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top (R := C) (M := C))
    exact H N C hN.symm β c hc
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C _ _ _ hN β c hc
  by_cases hm : IsLocalRing.maximalIdeal C = ⊥
  · letI : Field C := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
    exact GlobalTheory.T.siegel_family_classifies_principal_any_field g n hg hn hodd F C β c hc
  obtain ⟨e, he0, hem, hann⟩ := exists_socle C hm
  set I : Ideal C := Ideal.span {e}
  have hIt : I ≠ ⊤ := by
    intro h
    have : I ≤ IsLocalRing.maximalIdeal C := (Ideal.span_singleton_le_iff_mem _).mpr hem
    rw [h] at this
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (top_le_iff.mp this)
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIt
  haveI : IsLocalRing (C ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

  have hlenQ : Module.length C (C ⧸ I) = Module.length (C ⧸ I) (C ⧸ I) :=
    Module.length_eq_of_surjective (R := C ⧸ I) (S := C) (M := C ⧸ I) Ideal.Quotient.mk_surjective
  have hsum : Module.length C C = Module.length C I + Module.length C (C ⧸ I) :=
    Module.length_eq_add_of_exact I.subtype I.mkQ I.injective_subtype I.mkQ_surjective
      (LinearMap.exact_subtype_mkQ I)
  haveI : Nontrivial I := ⟨⟨⟨e, Ideal.subset_span rfl⟩, 0, fun h => he0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.length C I := Module.length_pos
  rw [hN, hlenQ] at hsum
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (show Module.length C I ≠ ⊤ from fun h => by
    rw [h, top_add] at hsum; exact ENat.natCast_ne_top _ hsum)
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (show Module.length (C ⧸ I) (C ⧸ I) ≠ ⊤ from fun h => by
    rw [h, add_top] at hsum; exact ENat.natCast_ne_top _ hsum)
  rw [← hb, ← hM] at hsum
  rw [← hb] at hpos
  have hb0 : 0 < b := by exact_mod_cast hpos
  have hNM : N = b + M := by exact_mod_cast hsum
  have hlt : M < N := by omega
  refine GlobalTheory.T.exists_siegPB_lift_of_quotient_lift g n hg hn hodd F C e hem hann β c hc ?_
  intro c₀ hpb
  have hcomm : spMap (Ideal.Quotient.mk I) ≫ spMap β = spMap ((Ideal.Quotient.mk I).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hc₀ : c₀.Principal :=
    (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp C) (Sp (C ⧸ I)) (spMap β)
      (spMap ((Ideal.Quotient.mk I).comp β)) (spMap (Ideal.Quotient.mk I)) c hcomm).2 c₀ hpb hc
  exact ih M hlt (C ⧸ I) hM.symm _ c₀ hc₀

end GlobalTheory.SiegelArtin
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_point_lifts_to_artinian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  atlas_forward_decl GlobalTheory.SiegelArtin.main
end
