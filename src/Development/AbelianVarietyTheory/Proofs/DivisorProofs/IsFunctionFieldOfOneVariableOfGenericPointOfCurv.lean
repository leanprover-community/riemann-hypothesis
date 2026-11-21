import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegFunctionFieldEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndE

section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.FGFun

theorem fg_functionField : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (sG : G ⟶ Sp F), IsProjOver sG → ∀ (P Ω : Type) [Field P] [Field Ω] (φ : P →+* G.functionField) (t : Sp P ⟶ Sp F) (ι : G.functionField →+* Ω), spMap ι ≫ G.fromSpecStalk (genericPoint G) ≫ sG = spMap ι ≫ spMap φ ≫ t → (letI := φ.toAlgebra; (⊤ : IntermediateField P G.functionField).FG) := by
  intro F _ G _ sG hproj P Ω _ _ φ t ι h
  letI := φ.toAlgebra
  obtain ⟨τ, rfl⟩ := Spec.map_surjective t
  obtain ⟨β, hβ⟩ := Spec.map_surjective (G.fromSpecStalk (genericPoint G) ≫ sG)
  have hβτ : ∀ c : F, β.hom c = φ (τ.hom c) := by
    rw [← hβ] at h
    simp only [← Spec.map_comp] at h
    have h' := Spec.map_injective h
    intro c
    apply ι.injective
    have := congrArg (fun f => f.hom c) h'
    simpa using this
  have hft : LocallyOfFiniteType sG := by
    obtain ⟨N, i, hi, rfl⟩ := hproj
    haveI := isProper_str F N
    infer_instance
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 G.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint G))
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  have e : U ≤ sG ⁻¹ᵁ ⊤ := by simp
  have hfin := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) sG hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e
  have key : sG.appLE ⊤ U e ≫ G.presheaf.germ U _ hx = (Scheme.ΓSpecIso (.of F)).hom ≫ β := by
    rw [← Scheme.ΓSpecIso_naturality, hβ, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
      Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have h3 : (Spec (G.presheaf.stalk (genericPoint G))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (G.presheaf.stalk (genericPoint G))).Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
    rw [h3]
    simp
  classical
  letI : Algebra Γ(Sp F, ⊤) Γ(G, U) := (sG.appLE ⊤ U e).hom.toAlgebra
  have hfin' : Algebra.FiniteType Γ(Sp F, ⊤) Γ(G, U) := hfin
  obtain ⟨s, hs⟩ := hfin'.out
  have hmem : ∀ a : Γ(G, U), (G.presheaf.germ U _ hx).hom a ∈
      IntermediateField.adjoin P ((s.image (G.presheaf.germ U _ hx).hom : Finset _) : Set G.functionField) := by
    intro a
    have ha : a ∈ Algebra.adjoin Γ(Sp F, ⊤) (s : Set Γ(G, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx' =>
      exact IntermediateField.subset_adjoin _ _ (by rw [Finset.coe_image]; exact ⟨x, hx', rfl⟩)
    | algebraMap r =>
      have := congrArg (fun f => f.hom r) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [RingHom.algebraMap_toAlgebra, this, hβτ]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨s.image (G.presheaf.germ U _ hx).hom, eq_top_iff.2 fun f _ => ?_⟩
  have := functionField_isFractionRing_of_isAffineOpen G U hU
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(G, U)) f
  exact div_mem (hmem a) (hmem b)

end GlobalTheory.FGFun
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc IntermediateField

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef.CurveFF

theorem isFF_of_trdeg_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (h : Algebra.trdeg k F = 1) : IsFF k F := by
  have hna : ¬ Algebra.IsAlgebraic k F := fun ha => by
    rw [trdeg_eq_zero_iff.mpr ha] at h; exact zero_ne_one h
  obtain ⟨x, hx⟩ : ∃ x : F, Transcendental k x := by
    by_contra hc
    push_neg at hc
    exact hna ⟨fun x => by simpa [Transcendental] using hc x⟩
  exact ⟨x, hx, finiteDimensional_adjoin_of_trdeg_le_one h.le x hx⟩

theorem isFF_of_stalk (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0}) [IsIntegral C]
    [Algebra k Γ(C, ⊤)] (hp : IsProjOver (strHom k C)) (hd : topologicalKrullDim C = 1)
    (y : C) (hy : y = genericPoint C) (ψ : C.presheaf.stalk y ⟶ CommRingCat.of K)
    (hψ : Function.Surjective ψ.hom)
    (hc : Spec.map ψ ≫ C.fromSpecStalk y ≫ strHom k C = spMap (algebraMap k K)) : IsFF k K := by
  subst hy
  let φ : k →+* C.functionField := (Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ strHom k C)).hom
  have hφ : C.fromSpecStalk (genericPoint C) ≫ strHom k C = spMap φ := (Spec.map_preimage _).symm
  letI : Algebra k C.functionField := φ.toAlgebra
  have htr : Algebra.trdeg k C.functionField = 1 := by
    have := FunctionFieldTrdeg.trdeg_functionField_eq k C (strHom k C) 1 hp (by simpa using hd) φ hφ
    simpa using this
  have hfg : (⊤ : IntermediateField k C.functionField).FG :=
    FGFun.fg_functionField k C (strHom k C) hp k C.functionField φ (𝟙 _) (RingHom.id _) (by simp [hφ])
  haveI : Algebra.EssFiniteType k C.functionField := IntermediateField.fg_top_iff.mp hfg
  let ψ' : C.functionField →+* K := ψ.hom
  have hinj : Function.Injective ψ' := ψ'.injective
  have hcomm : ∀ c : k, ψ' (φ c) = algebraMap k K c := by
    rw [hφ] at hc
    have h1 : Spec.map (CommRingCat.ofHom φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      rw [Spec.map_comp]; exact hc
    have h2 := Spec.map_injective h1
    intro c
    exact congrArg (fun f => f.hom c) h2
  let e : C.functionField ≃ₐ[k] K :=
    AlgEquiv.ofBijective { ψ' with commutes' := hcomm } ⟨hinj, hψ⟩
  haveI : Algebra.EssFiniteType k K := (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  exact isFF_of_trdeg_eq_one (e.trdeg_eq ▸ htr)

theorem isFF_of_isGenOver : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  IsFF k K := by
  intro k K _ _ _ _ _ C _ x hx
  obtain ⟨⟨hs, hp, hg⟩, ⟨hdom, hpre⟩, hxs⟩ := hx
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hs hg
  let p : Sp K := IsLocalRing.closedPoint (CommRingCat.of K)
  haveI : Nonempty C := ⟨x p⟩
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hs
  have hgen : x p = genericPoint C := by
    have hr : Set.range x = {x p} := by
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        rw [Set.mem_singleton_iff, Subsingleton.elim v p]
      · rintro rfl
        exact ⟨p, rfl⟩
    refine ((genericPoint_spec C).eq ?_).symm
    rw [isGenericPoint_def, ← hr]
    exact x.denseRange.closure_range
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp
      (x.stalkMap_surjective _)
  refine isFF_of_stalk k K C hp hd _ hgen (Scheme.stalkClosedPointTo x) hsurj ?_
  rw [← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hxs]

end GlobalTheory.Nef.CurveFF
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  IsFF k K := by
  atlas_forward_decl GlobalTheory.Nef.CurveFF.isFF_of_isGenOver
end
