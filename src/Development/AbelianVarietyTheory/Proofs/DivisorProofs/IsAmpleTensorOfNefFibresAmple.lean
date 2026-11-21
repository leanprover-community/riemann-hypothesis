import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAmpleLBOfFibres
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreDimensionLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePreimmersionIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianOfCombinationMetricLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralLinearRelationZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionCycleFormulaProjectiveStatement

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleFibre

theorem isAmpleLB_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → ∀ (l : ℕ) [Fact l.Prime], IsAmpleLB ((L.tens A).B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))))) := by
  intro k _ X _ p D hX L A hL hA l _
  haveI := hX.finite
  have hc := GlobalTheory.NefFibPrime.isClosedImmersion_spMap_zmod l
  haveI : IsClosedImmersion (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip hc
  set f := Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hf
  set g := Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hg
  letI := GlobalTheory.algebraΓOfHom g
  have hproj : IsProjOver g := by
    have h := GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver l f
    rwa [GlobalTheory.strHom_eq (f := g) fun _ => rfl] at h
  have hN : IsNef (ZMod l) (L.B.pull f) :=
    GlobalTheory.FibreNef.isNef_pull_of_nefOver l f L ((GlobalTheory.VertForm.nefFib_iff L).1 hL l Fact.out)
  have hAf : IsAmpleLB (A.B.pull f) := hA.pull_of_isClosedImmersion f
  have hK := IsAmpleLB.tens_of_isNef GlobalTheory.nefNumerics_outright (ZMod l) _ g hproj _ _ hAf hN
  refine hK.of_lbIso (LB.isLB_pull (L.tens A).isLB f) ?_
  refine (CechPic.cls_eq_iff (LB.isLB_pull (L.tens A).isLB f)
    (CechPic.isLB_tens (LB.isLB_pull A.isLB f) (LB.isLB_pull L.isLB f))).1 ?_
  show CechPic.pull f (CechPic.cls L.B L.isLB + CechPic.cls A.B A.isLB) =
    CechPic.pull f (CechPic.cls A.B A.isLB) + CechPic.pull f (CechPic.cls L.B L.isLB)
  rw [map_add, add_comm]

end GlobalTheory.AmpleFibre
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_nef_ample_finiteFieldFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → ∀ (l : ℕ) [Fact l.Prime], IsAmpleLB ((L.tens A).B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))))) := by
  atlas_forward_decl GlobalTheory.AmpleFibre.isAmpleLB_fibre
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_subscheme_mod_l_projective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) Z) := by
  first | exact @GlobalTheory.VertProj.isProjOver_strHom_zmod | exact GlobalTheory.VertProj.isProjOver_strHom_zmod | (intros; apply GlobalTheory.VertProj.isProjOver_strHom_zmod <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

namespace GlobalTheory.FibreProj

theorem pol_topSelf_comb_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (κ : Type) [Field κ] (Z : Scheme.{0}) [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → ∀ (ι : Type) [Fintype ι] (D : ℕ), Fintype.card ι = D → topologicalKrullDim Z ≤ D → ∀ (i : Z ⟶ X) (N : ι → HermLB p), pol (fun n : ι → ℤ => (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ)) = D.factorial * (interNum κ (structureModule Z) (fun a => (N a).B.pull i) : ℝ) := by
  intro k _ X p κ _ Z _ hp ι _ D hcard hdim i N
  classical
  have HD := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ Z) (structureModule Z) hp (d := D)
    (by rw [QCoh.suppDim_structureModule]; exact hdim)
  have hL : ∀ a, ((N a).B.pull i).IsLB := fun a => LB.isLB_pull (N a).isLB i
  let c : ι → CechPic.Pic Z := fun a => CechPic.cls ((N a).B.pull i) (hL a)
  let g : (ι → ℤ) →+ CechPic.Pic Z := AddMonoidHom.mk' (fun n => ∑ a, n a • c a) fun u v => by
    simp [add_smul, Finset.sum_add_distrib]
  have hg (a : ι) : g (Pi.single a 1) = c a := by
    simp [g, Pi.single_apply, Finset.sum_ite_eq']
  have key : (fun n : ι → ℤ => (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ)) =
      (Int.castAddHom ℝ) ∘ ((fun y => HD.form fun _ => y) ∘ g) := by
    funext n
    rw [topSelf_def, ← HD.form_cls (P := fun _ => (comb N n).B.pull i) (fun _ => LB.isLB_pull (comb N n).isLB i)]
    simp only [Function.comp_apply, Int.coe_castAddHom]
    congr 2
    funext j
    rw [CechPic.cls_pull (comb N n).isLB, GenFibreSecs.cls_comb, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul]
    simp only [c]
    rw [CechPic.cls_pull (N a).isLB]
  let e : Fin D ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  have h₁ := congrFun (multiDiff_comap g (fun a => (Pi.single a 1 : ι → ℤ)) (fun y => HD.form fun _ => y)) 0
  have h₂ := congrFun (multiDiff_map (Int.castAddHom ℝ) (fun a => (Pi.single a 1 : ι → ℤ))
    ((fun y => HD.form fun _ => y) ∘ g)) 0
  rw [key, pol_eq_multiDiff]
  refine h₂.trans ?_
  have hc : (g ∘ fun a => (Pi.single a 1 : ι → ℤ)) = c := funext hg
  rw [Function.comp_apply, h₁, Function.comp_apply, hc, ← multiDiff_comp_equiv e, HD.multiDiff_form_diag,
    show c ∘ e = fun j => CechPic.cls ((N (e j)).B.pull i) (hL (e j)) from rfl, HD.form_cls (P := fun j => (N (e j)).B.pull i) (fun j => hL (e j)),
    ← interNum_comp_equiv κ (structureModule Z) (L := fun a => (N a).B.pull i) hL e]
  simp [Function.comp_def]

end GlobalTheory.FibreProj
end

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_top_self_intersection : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (κ : Type) [Field κ] (Z : Scheme.{0}) [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → ∀ (ι : Type) [Fintype ι] (D : ℕ), Fintype.card ι = D → topologicalKrullDim Z ≤ D → ∀ (i : Z ⟶ X) (N : ι → HermLB p), pol (fun n : ι → ℤ => (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ)) = D.factorial * (interNum κ (structureModule Z) (fun a => (N a).B.pull i) : ℝ) := by
  atlas_forward_decl GlobalTheory.FibreProj.pol_topSelf_comb_pull
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.codim_one_integral_subscheme_dim : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z], Order.coheight (i (genericPoint Z)) = 1 → topologicalKrullDim Z = D := by
  first | exact @GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one | exact GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one | (intros; apply GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericFibreDegree

theorem chi_eq_residueDegree : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (f : Y ⟶ B)
    (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField),
    IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsProjOver s →
    topologicalKrullDim G ≤ (0 : ℕ) → Nonempty G → f.residueDegree (genericPoint Y) ≠ 0 ∧
      (letI := algebraΓOfHom s; chi B.functionField (structureModule G)) =
        f.residueDegree (genericPoint Y) := by
  intro B Y _ _ f G j s hpb hP hd hne
  obtain ⟨hpre, -, -, hint⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hpb
  obtain ⟨hGint, hjη⟩ := hint hne

  have hu (w : G) : w = genericPoint G := by
    have h0 : Order.krullDim (IrreducibleCloseds G) ≤ 0 := (by simpa using hd : topologicalKrullDim G ≤ 0)
    have := Order.krullDim_nonpos_iff_forall_isMax.1 h0
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ G, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec G)

  haveI : IsAffine G := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := G) (x := genericPoint G)
      (U := ⊤) trivial
    have hUt : U = ⊤ := by
      ext w
      exact ⟨fun _ => trivial, fun _ => by rw [hu w]; exact hxU⟩
    subst hUt
    haveI : IsAffine (⊤ : G.Opens).toScheme := hU
    exact IsAffine.of_isIso G.topIso.inv
  haveI : IsProper s := CommonModel.isProper_of_isProjOver hP
  haveI : IsFinite s := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hsη : s (genericPoint G) = genericPoint (Sp B.functionField) := Subsingleton.elim _ _
  have h1 := GlobalTheory.ProjFin.finrank_app_eq_residueDegree s hsη (U := ⊤) (isAffineOpen_top _) trivial

  have h2 : f.residueDegree (genericPoint Y) = s.residueDegree (genericPoint G) := by
    have e := congrArg (fun h => Scheme.Hom.residueDegree h (genericPoint G)) hpb.w
    simp only [CurveDegreesCompare.residueDegree_comp] at e
    rw [CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks j,
      CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks (B.fromSpecStalk (genericPoint B)),
      mul_one, one_mul, hjη] at e
    exact e
  letI := algebraΓOfHom s

  have h3 : Module.finrank B.functionField Γ(G, ⊤) = s.residueDegree (genericPoint G) := by
    refine Eq.trans ?_ h1
    letI := (s.app ⊤).hom.toAlgebra
    exact Algebra.finrank_eq_of_equiv_equiv
      (Scheme.ΓSpecIso (CommRingCat.of B.functionField)).symm.commRingCatIsoToRingEquiv
      (RingEquiv.refl _) rfl
  haveI hfin : Module.Finite B.functionField Γ(G, ⊤) := by
    have hf : (s.app ⊤).hom.Finite := IsFinite.finite_app s ⊤ (isAffineOpen_top _)
    have hi : ((Scheme.ΓSpecIso (CommRingCat.of B.functionField)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B.functionField)).inv).2
    exact hf.comp hi
  haveI : Nontrivial Γ(G, ⊤) := inferInstance
  refine ⟨?_, ?_⟩
  · rw [h2, ← h3]
    exact Module.finrank_pos.ne'
  · rw [chi_structureModule_of_isAffine, h3, h2]

end GlobalTheory.GenericFibreDegree
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_degree_eq_euler_characteristic : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsProjOver s → topologicalKrullDim G ≤ (0 : ℕ) → Nonempty G → f.residueDegree (genericPoint Y) ≠ 0 ∧ (letI := algebraΓOfHom s; chi B.functionField (structureModule G)) = f.residueDegree (genericPoint Y) := by
  atlas_forward_decl GlobalTheory.GenericFibreDegree.chi_eq_residueDegree
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

namespace GlobalTheory.FibreProj.DetPol

open Classical in

theorem pol_eq_zero_of_indep {ι : Type} [Fintype ι] (φ : (ι → ℤ) → ℝ) (i : ι)
    (h : ∀ n v, φ (Function.update n i v) = φ n) : pol φ = 0 := by
  unfold pol
  refine Finset.sum_involution (fun S _ => if i ∈ S then S.erase i else insert i S) ?_ ?_
    (fun _ _ => Finset.mem_univ _) ?_
  · intro S _
    have hpt : ∀ T : Finset ι, (i ∈ T ↔ i ∉ S) → (∀ j, j ≠ i → (j ∈ T ↔ j ∈ S)) →
        (fun j => if j ∈ T then (-1 : ℤ) else 0) =
          Function.update (fun j => if j ∈ S then (-1 : ℤ) else 0) i (if i ∈ T then -1 else 0) := by
      intro T _ hT
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]
        by_cases hS : j ∈ S
        · simp [hS, (hT j hj).2 hS]
        · have : j ∉ T := fun h' => hS ((hT j hj).1 h')
          simp [hS, this]
    by_cases hS : i ∈ S
    · simp only [hS, if_true]
      rw [hpt (S.erase i) (by simp [hS]) (fun j hj => by simp [hj]), h]
      have hc := Finset.card_erase_add_one hS
      rw [← hc, pow_succ]
      ring
    · simp only [hS, if_false]
      rw [hpt (insert i S) (by simp [hS]) (fun j hj => by simp [hj]), h]
      rw [Finset.card_insert_of_notMem hS, pow_succ]
      ring
  · intro S _ _ heq
    by_cases hS : i ∈ S
    · simp only [hS, if_true] at heq
      have hn := Finset.notMem_erase i S
      rw [heq] at hn
      exact hn hS
    · simp only [hS, if_false] at heq
      have hm := Finset.mem_insert_self i S
      rw [heq] at hm
      exact hS hm
  · intro S _
    by_cases hS : i ∈ S
    · simp [hS, Finset.insert_erase hS]
    · simp [hS, Finset.erase_insert hS]

variable (α β : Type) [Fintype α] [Fintype β]

def DepOn (T : Finset β) (g : (α ⊕ β → ℤ) → ℂ) : Prop :=
  ∀ n n' : α ⊕ β → ℤ, (∀ a, n (Sum.inl a) = n' (Sum.inl a)) →
    (∀ b ∈ T, n (Sum.inr b) = n' (Sum.inr b)) → g n = g n'

def lowDeg (k : ℕ) : Submodule ℂ ((α ⊕ β → ℤ) → ℂ) :=
  Submodule.span ℂ {g | ∃ T : Finset β, T.card ≤ k ∧ DepOn α β T g}

variable {α β}

theorem mem_lowDeg_of_depOn {k : ℕ} (T : Finset β) (hT : T.card ≤ k) (g : (α ⊕ β → ℤ) → ℂ)
    (hg : DepOn α β T g) : g ∈ lowDeg α β k :=
  Submodule.subset_span ⟨T, hT, hg⟩

theorem lowDeg_mono {k l : ℕ} (h : k ≤ l) : lowDeg α β k ≤ lowDeg α β l :=
  Submodule.span_mono fun _ ⟨T, hT, hg⟩ => ⟨T, hT.trans h, hg⟩

theorem mul_mem_lowDeg {k l : ℕ} {f g : (α ⊕ β → ℤ) → ℂ} (hf : f ∈ lowDeg α β k)
    (hg : g ∈ lowDeg α β l) : f * g ∈ lowDeg α β (k + l) := by
  classical
  have gen : ∀ f, (∃ T : Finset β, T.card ≤ k ∧ DepOn α β T f) → ∀ g, g ∈ lowDeg α β l →
      f * g ∈ lowDeg α β (k + l) := by
    intro f ⟨T, hT, hfT⟩ g hg
    induction hg using Submodule.span_induction with
    | mem g hg' =>
      obtain ⟨T', hT', hgT⟩ := hg'
      refine mem_lowDeg_of_depOn (T ∪ T') ((Finset.card_union_le _ _).trans (by omega)) _ ?_
      intro n n' ha hb
      simp only [Pi.mul_apply]
      rw [hfT n n' ha (fun b hb' => hb b (Finset.mem_union_left _ hb')),
        hgT n n' ha (fun b hb' => hb b (Finset.mem_union_right _ hb'))]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  induction hf using Submodule.span_induction with
  | mem f hf' => exact gen f hf' g hg
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem prod_mem_lowDeg {ι : Type} (s : Finset ι) (f : ι → (α ⊕ β → ℤ) → ℂ) (k : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ lowDeg α β (k i)) : ∏ i ∈ s, f i ∈ lowDeg α β (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact mem_lowDeg_of_depOn ∅ le_rfl _ fun _ _ _ _ => rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_lowDeg (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem pol_eq_zero_of_mem_lowDeg {k : ℕ} (hk : k < Fintype.card β) {g : (α ⊕ β → ℤ) → ℂ}
    (hg : g ∈ lowDeg α β k) : ∀ L : ℂ →ₗ[ℝ] ℝ, pol (fun n => L (g n)) = 0 := by
  classical
  induction hg using Submodule.span_induction with
  | mem g hg' =>
    obtain ⟨T, hT, hgT⟩ := hg'
    intro L
    obtain ⟨b, hb⟩ : ∃ b, b ∉ T := by
      by_contra hc
      push_neg at hc
      have := Finset.card_le_card (fun b _ => hc b : (Finset.univ : Finset β) ⊆ T)
      rw [Finset.card_univ] at this
      omega
    refine pol_eq_zero_of_indep _ (Sum.inr b) fun n v => ?_
    congr 1
    refine hgT _ _ (fun a => by simp) fun b' hb' => ?_
    have : b' ≠ b := fun h => hb (h ▸ hb')
    simp [Function.update_apply, this]
  | zero => intro L; simp [pol]
  | add x y _ _ hx hy =>
    intro L
    have h1 := hx L
    have h2 := hy L
    simp only [pol] at h1 h2 ⊢
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
  | smul c x _ hx =>
    intro L
    have := hx (L ∘ₗ LinearMap.mulLeft ℝ c)
    simpa [smul_eq_mul] using this

end GlobalTheory.FibreProj.DetPol

namespace GlobalTheory.FibreProj.DetPol

theorem det_add_perturb_eq {D d : ℕ} {β : Type} [Fintype β] (A : Matrix (Fin D) (Fin D) ℂ)
    (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ) (K : β → Matrix (Fin d) (Fin d) ℂ)
    (c : β → ℂ) :
    Matrix.det (A + ∑ b, c b • (P * K b * Q)) =
      Matrix.det (Matrix.fromBlocks A (-(P * ∑ b, c b • K b)) Q 1) := by
  rw [Matrix.det_fromBlocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]
  congr 2
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem pol_det_perturb_eq_zero : ∀ (D d : ℕ) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β →
    ∀ (H : α → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ)
      (K : β → Matrix (Fin d) (Fin d) ℂ),
    pol (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a +
      ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) = 0 := by
  intro D d α β _ _ hd H P Q K
  classical
  let M : (α ⊕ β → ℤ) → Matrix (Fin D ⊕ Fin d) (Fin D ⊕ Fin d) ℂ := fun n =>
    Matrix.fromBlocks (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a)
      (-(P * ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • K b)) Q 1
  have hfun : (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a +
      ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) =
      fun n => Complex.reLm ((M n).det) := by
    funext n
    rw [det_add_perturb_eq]
    rfl
  rw [hfun]
  refine pol_eq_zero_of_mem_lowDeg hd ?_ Complex.reLm
  have hentry : ∀ r c : Fin D ⊕ Fin d,
      (fun n => M n r c) ∈ lowDeg α β (Sum.elim (fun _ => 0) (fun _ => 1) c) := by
    intro r c
    rcases c with j | j
    · refine mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' ha _ => ?_
      rcases r with r | r
      · simp [M, ha]
      · simp [M]
    · rcases r with r | r
      · have : (fun n => M n (Sum.inl r) (Sum.inr j)) =
            ∑ b, (-(P * K b) r j) • (fun n : α ⊕ β → ℤ => ((n (Sum.inr b) : ℝ) : ℂ)) := by
          funext n
          simp [M, Matrix.mul_sum, Matrix.sum_apply, Matrix.mul_smul, Finset.sum_apply, mul_comm]
        rw [this]
        refine Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
        refine mem_lowDeg_of_depOn {b} (by simp) _ fun n n' _ hb => ?_
        simp [hb b (Finset.mem_singleton_self b)]
      · exact lowDeg_mono (Nat.zero_le 1)
          (mem_lowDeg_of_depOn ∅ (by simp) _ fun n n' _ _ => by simp [M])
  have hdet : (fun n => (M n).det) =
      ∑ σ : Equiv.Perm (Fin D ⊕ Fin d), Equiv.Perm.sign σ • ∏ i, (fun n => M n (σ i) i) := by
    funext n
    simp [Matrix.det_apply, Finset.sum_apply, Finset.prod_apply]
  rw [show (fun n => (M n).det) = _ from hdet]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  have := prod_mem_lowDeg Finset.univ (fun i => fun n => M n (σ i) i)
    (fun i => Sum.elim (fun _ => 0) (fun _ => 1) i) (fun i _ => hentry (σ i) i)
  simpa [Fintype.sum_sum_type] using this

end GlobalTheory.FibreProj.DetPol
end

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_det_hermitian_sum_zero : ∀ (D d : ℕ) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β → ∀ (H : α → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ) (K : β → Matrix (Fin d) (Fin d) ℂ), pol (fun n : α ⊕ β → ℤ => (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • H a + ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re) = 0 := by
  atlas_forward_decl GlobalTheory.FibreProj.DetPol.pol_det_perturb_eq_zero
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_chart_metric_block_form : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (f : Y ⟶ B) (w : f ≫ q = p) (σ : k →+* ℂ) (D d : ℕ) (c : AlgChart p σ D) (c' : AlgChart q σ d) (y : CxPts p σ), y ∈ c.e.source → PtsOver.map f w (spMap σ) y ∈ c'.e.source → ∃ (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ), ∀ (A : HermLB q) (i : (A.pull f w).B.ι), y ∈ ptsIn p σ ((A.pull f w).B.U i) → ∃ K : Matrix (Fin d) (Fin d) ℂ, c.hess ((A.pull f w).φ σ) i y = P * K * Q := by
  first | exact @GlobalTheory.HessPull.hess_pull_factor | exact GlobalTheory.HessPull.hess_pull_factor | (intros; apply GlobalTheory.HessPull.hess_pull_factor <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_integral_linear_relation_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (N : J → HermLB p), (∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, ∑ j, a j * c.chernDens ((N j).φ σ) y = 0) → ∀ (S : Set (CxPts p σ)) (g : CxPts p σ → ℝ), (∀ j, ((N j).φ σ).ChernIntegrableOn D S g) → ∑ j, a j * ((N j).φ σ).chernInt D S g = 0 := by
  first | exact @GlobalTheory.ChernLinRel.sum_chernInt_eq_zero | exact GlobalTheory.ChernLinRel.sum_chernInt_eq_zero | (intros; apply GlobalTheory.ChernLinRel.sum_chernInt_eq_zero <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreProj

theorem pol_archInt_pull_eq_zero : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), GenSmooth q d → IsArithVar p D → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β → ∀ (L : α → HermLB p) (A : β → HermLB q) (M : HermLB p) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb (Sum.elim L fun a => (A a).pull f w) n).ArchIntegrable M D hr) → pol (fun n => (comb (Sum.elim L fun a => (A a).pull f w) n).archInt M D hr) = 0 := by
  classical
  intro k _ B Y _ q p d D hB hX f w α β _ _ hd L A M r hr hint
  set F : α ⊕ β → HermLB p := Sum.elim L fun a => (A a).pull f w with hF
  haveI := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  simp only [HermLB.archInt, finsum_eq_sum_of_fintype]
  rw [pol_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  unfold pol
  refine GlobalTheory.T.chern_integral_linear_relation_zero k Y p hX.isProjOver σ D (Finset (α ⊕ β)) _ _ ?_ _ _ fun S => hint _ σ
  intro c y hy
  obtain ⟨R⟩ := hB σ
  obtain ⟨i, hi⟩ := R.cover (PtsOver.map f w (spMap σ) y)
  obtain ⟨P, Q, hPQ⟩ := GlobalTheory.T.pullback_chart_metric_block_form k B Y q p f w σ D d c (R.chart i) y hy hi
  choose K hK using fun b => hPQ (A b) (pick (((A b).pull f w).φ σ).isLB y) (mem_pick _ y)
  set m : ∀ l, (F l).B.ι := fun l => pick ((F l).φ σ).isLB y with hm
  have hK' : ∀ b, c.hess ((F (Sum.inr b)).φ σ) (m (Sum.inr b)) y = P * K b * Q := hK
  have key : ∀ n : α ⊕ β → ℤ, c.chernDens ((comb F n).φ σ) y = D.factorial / Real.pi ^ D *
      (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • c.hess ((F (Sum.inl a)).φ σ) (m (Sum.inl a)) y +
        ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re := by
    intro n
    rw [AlgChart.chernDens, GlobalTheory.Mean4O.ReadsProj.hess_comb F n σ c hy _ (mem_pick _ y) m
      (fun l => mem_pick _ y), Fintype.sum_sum_type]
    simp only [hK']
  simp only [key]
  have h0 := pol_const_mul (D.factorial / Real.pi ^ D) (fun n : α ⊕ β → ℤ =>
      (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • c.hess ((F (Sum.inl a)).φ σ) (m (Sum.inl a)) y +
        ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re)
  rw [GlobalTheory.T.polynomial_det_hermitian_sum_zero D d α β hd, mul_zero] at h0
  unfold pol at h0
  exact h0

end GlobalTheory.FibreProj
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_integrable_polynomial_vanishing : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), GenSmooth q d → IsArithVar p D → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β → ∀ (L : α → HermLB p) (A : β → HermLB q) (M : HermLB p) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb (Sum.elim L fun a => (A a).pull f w) n).ArchIntegrable M D hr) → pol (fun n => (comb (Sum.elim L fun a => (A a).pull f w) n).archInt M D hr) = 0 := by
  atlas_forward_decl GlobalTheory.FibreProj.pol_archInt_pull_eq_zero
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_zero_small_image : ∀ (κ : Type) [Field κ] (e r : ℕ) (Z W : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → topologicalKrullDim Z ≤ (e + r : ℕ) → ∀ g : Z ⟶ W, topologicalKrullDim (closure ({g (genericPoint Z)} : Set W)) < (r : ℕ) → ∀ (P : Fin e → LB Z), (∀ i, (P i).IsLB) → ∀ (A : Fin r → LB W), (∀ i, (A i).IsLB) → interNum κ (structureModule Z) (Sum.elim P fun a => (A a).pull g) = 0 := by
  first | exact @GlobalTheory.PullVanish.interNum_pull_eq_zero | exact GlobalTheory.PullVanish.interNum_pull_eq_zero | (intros; apply GlobalTheory.PullVanish.interNum_pull_eq_zero <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.FibreClosure

theorem interNum_genericFibre_eq_interNumRed : ∀ (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (x : G) (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = j x → ∀ (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB Y), (∀ a, (P a).IsLB) → (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a => ((P a).pull i).pull j')) = (letI := algebraΓOfHom s; interNumRed B.functionField (⟨closure {x}, isClosed_closure⟩ : Closeds _) (fun a => (P a).pull j)) := by
  intro B Y _ f G j s hG x Z i _ _ hx G' j' s' hG' ι _ P hP
  obtain ⟨hj, hrj, -, -⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hG
  obtain ⟨-, hrj', -, hint'⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Z (i ≫ f) G' j' s' hG'

  let u : G' ⟶ G := hG.lift (j' ≫ i) s' (by rw [Category.assoc]; exact hG'.w)
  have hu₁ : u ≫ j = j' ≫ i := hG.lift_fst _ _ _
  have hu₂ : u ≫ s = s' := hG.lift_snd _ _ _
  have hsq : IsPullback j' u i j := IsPullback.of_bot (by rw [hu₂]; exact hG') hu₁.symm hG
  have : IsClosedImmersion u := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq ‹_›

  have hη : (i ≫ f) (genericPoint Z) = genericPoint B := by
    have : j x ∈ Set.range j := ⟨x, rfl⟩
    rw [hrj] at this
    rw [Scheme.Hom.comp_apply, hx]
    exact this
  have hne : Nonempty G' := by
    have : genericPoint Z ∈ (i ≫ f) ⁻¹' {genericPoint B} := hη
    rw [← hrj'] at this
    obtain ⟨y, -⟩ := this
    exact ⟨y⟩
  obtain ⟨_, hgen⟩ := hint' hne
  have hux : u (genericPoint G') = x := by
    apply (Scheme.Hom.isEmbedding j).injective
    rw [← Scheme.Hom.comp_apply, hu₁, Scheme.Hom.comp_apply, hgen, hx]
  have hrange : Set.range u = closure {x} := by
    apply subset_antisymm
    · rintro _ ⟨y, rfl⟩
      have hy : y ∈ closure {genericPoint G'} := by
        rw [(genericPoint_spec G').def]; trivial
      have := image_closure_subset_closure_image (f := u) u.continuous ⟨y, hy, rfl⟩
      rwa [Set.image_singleton, hux] at this
    · exact (Scheme.Hom.isClosedEmbedding u).isClosed_range.closure_subset_iff.2
        (Set.singleton_subset_iff.2 ⟨_, hux⟩)
  letI := algebraΓOfHom s'
  letI := algebraΓOfHom s
  rw [GlobalTheory.InterModel.interNumRed_eq_interNumOn _ u _ hrange,
    interNumOn_eq_interNum_pull (appTop_algebraΓOfHom u s hu₂) (fun a => pull_isLB (hP a) j)]
  refine interNum_congr_lbIso _ _ (fun a => pull_isLB (pull_isLB (hP a) i) j')
    (fun a => pull_isLB (pull_isLB (hP a) j) u) fun a => ?_
  exact LBIso.trans (pull_isLB (pull_isLB (hP a) i) j') (pull_isLB (hP a) (u ≫ j))
    (pull_isLB (pull_isLB (hP a) j) u)
    (GlobalTheory.GenSpread.lbIso_pull_pull (hP a) j' hu₁).symm
    (GlobalTheory.GenSpread.lbIso_pull_pull (hP a) u rfl)

end GlobalTheory.FibreClosure
end

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_closed_subvariety : ∀ (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (x : G) (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = j x → ∀ (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB Y), (∀ a, (P a).IsLB) → (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a => ((P a).pull i).pull j')) = (letI := algebraΓOfHom s; interNumRed B.functionField (⟨closure {x}, isClosed_closure⟩ : Closeds _) (fun a => (P a).pull j)) := by
  atlas_forward_decl GlobalTheory.FibreClosure.interNum_genericFibre_eq_interNumRed
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_divisor_pullback_generic : ∀ (G Y : Scheme.{0}) [IsIntegral G] [IsIntegral Y] [IsLocallyNoetherian G] [IsLocallyNoetherian Y] (j : G ⟶ Y), j (genericPoint G) = genericPoint Y → (∀ x : G, IsIso (j.stalkMap x)) → ∀ (M : LB Y) (hM : M.IsLB) (r : M.ι → Y.functionFieldˣ) (hr : IsRatSec M r), ∃ (r' : (M.pull j).ι → G.functionFieldˣ) (hr' : IsRatSec (M.pull j) r'), ∀ x : G, (divOfRatSec (LB.isLB_pull hM j) hr').mult x = (divOfRatSec hM hr).mult (j x) := by
  first | exact @GlobalTheory.MultPull.exists_isRatSec_pull_mult | exact GlobalTheory.MultPull.exists_isRatSec_pull_mult | (intros; apply GlobalTheory.MultPull.exists_isRatSec_pull_mult <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

noncomputable section

namespace GlobalTheory.GenFibreDegree

theorem interNum_eq_zero_of_not_generic (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (z : Y)
    (hz : f z ≠ genericPoint B) (Z : Scheme.{0}) (i : Z ⟶ Y) [IsIntegral Z]
    (hi : i (genericPoint Z) = z) (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField)
    (hG' : IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)))
    {ι : Type} [Fintype ι] (P : ι → LB Z) (hP : ∀ a, (P a).IsLB) :
    (letI := algebraΓOfHom s'
     interNum B.functionField (structureModule G') (fun a => (P a).pull j')) = 0 := by
  have hE : IsEmpty G' := by
    refine ⟨fun g => hz ?_⟩
    obtain ⟨_, hr, _, h4⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Z (i ≫ f) G' j' s' hG'
    obtain ⟨hGi, hη⟩ := h4 ⟨g⟩
    have hmem : j' (genericPoint G') ∈ Set.range j' := ⟨_, rfl⟩
    rw [hr, hη] at hmem
    simpa [← hi] using hmem
  letI := algebraΓOfHom s'
  exact interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _)
    (fun a => LB.isLB_pull (hP a) j')

theorem degree_genericFibre_ratSec : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsLocallyNoetherian Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d e : ℕ), IsArithVar q d → IsArithVar p (d + (e + 1)) → ∀ (f : Y ⟶ B), f ≫ q = p → ∀ (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (L : Fin (e + 1) → LB Y) (hL : ∀ a, (L a).IsLB) (r : (L 0).ι → Y.functionFieldˣ) (hr : IsRatSec (L 0) r) (γ : Y → ℤ), (∀ z, (divOfRatSec (hL 0) hr).mult z ≠ 0 → ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), i (genericPoint Z) = z ∧ IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) ∧ γ z = (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a : Fin e => ((L a.succ).pull i).pull j'))) → (letI := algebraΓOfHom s; interNum B.functionField (structureModule G) (fun a => (L a).pull j)) = ∑ᶠ z, (divOfRatSec (hL 0) hr).mult z * γ z := by
  intro k _ B Y _ _ _ q p d e hq hp f hfq G j s hpb L hL r hr γ hγ
  obtain ⟨hpre, hrange, hstalk, hint⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hpb
  set F : Y → ℤ := fun z => (divOfRatSec (hL 0) hr).mult z * γ z with hF
  have hoff : ∀ z, z ∉ Set.range j → F z = 0 := by
    intro z hz
    by_cases hm : (divOfRatSec (hL 0) hr).mult z = 0
    · simp [hF, hm]
    obtain ⟨Z, i, _, _, G', j', s', hi, hpb', hγz⟩ := hγ z hm
    have hfz : f z ≠ genericPoint B := by
      intro h
      exact hz (hrange ▸ (show z ∈ f ⁻¹' {genericPoint B} from h))
    simp only [hF]
    rw [hγz, interNum_eq_zero_of_not_generic B Y f z hfz Z i hi G' j' s' hpb'
      (fun a : Fin e => (L a.succ).pull i) (fun a => LB.isLB_pull (hL a.succ) i), mul_zero]
  have hinj : Function.Injective j := j.isEmbedding.injective
  have hs : Function.support F ⊆ Set.range j := fun z hz => by
    by_contra h
    exact hz (hoff z h)
  have hre : ∑ᶠ w, F (j w) = ∑ᶠ z, F z := by
    rw [← finsum_mem_range hinj, ← finsum_mem_inter_support, Set.inter_eq_right.2 hs,
      finsum_mem_support]
  rw [← hre]
  rcases isEmpty_or_nonempty G with hG | hG
  · letI := algebraΓOfHom s
    rw [interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _)
      (fun a => LB.isLB_pull (hL a) j)]
    exact (finsum_of_isEmpty _).symm
  · obtain ⟨hGi, hη⟩ := hint hG
    letI := algebraΓOfHom s
    have hsproj : IsProjOver s :=
      GlobalTheory.T.generic_fibre_projective k B Y q p hq.isProjOver hp.isProjOver f hfq G j s hpb
    have hstr : strHom B.functionField G = s := strHom_eq fun _ => rfl
    haveI : AlgebraicGeometry.IsNoetherian G := isNoetherian_of_isProjOver hsproj
    haveI : IsProper q := CommonModel.isProper_of_isProjOver hq.isProjOver
    haveI : IsProper (f ≫ q) := by rw [hfq]; exact CommonModel.isProper_of_isProjOver hp.isProjOver
    haveI : IsProper f := IsProper.of_comp f q
    have hdim : topologicalKrullDim G ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
      GlobalTheory.T.generic_fibre_dimension_le B Y (d + 1) (e + 1) hq.dim_eq
        (by rw [hp.dim_eq]; exact le_of_eq (congrArg _ (by omega))) f G j s hpb
    obtain ⟨r', hr', hmult⟩ := GlobalTheory.T.rational_section_divisor_pullback_generic G Y j hη hstalk (L 0) (hL 0) r hr
    have hcyc := GlobalTheory.T.rational_section_cycle_formula_projective B.functionField G (by rw [hstr]; exact hsproj) e hdim
      ((L 0).pull j) (LB.isLB_pull (hL 0) j) (fun a => (L a.succ).pull j)
      (fun a => LB.isLB_pull (hL a.succ) j) r' hr'
    have hcons : (Fin.cons ((L 0).pull j) (fun a : Fin e => (L a.succ).pull j) :
        Fin (e + 1) → LB G) = fun a => (L a).pull j := by
      funext a
      exact Fin.cases rfl (fun b => rfl) a
    rw [hcons] at hcyc
    rw [hcyc]
    congr 1
    funext w
    simp only [hF]
    rw [hmult w]
    by_cases hm : (divOfRatSec (hL 0) hr).mult (j w) = 0
    · simp [hm]
    obtain ⟨Z, i, _, _, G', j', s', hi, hpb', hγz⟩ := hγ (j w) hm
    rw [hγz, GlobalTheory.T.generic_fibre_closed_subvariety B Y f G j s hpb w Z i hi G' j' s' hpb' (Fin e) (fun a => L a.succ)
      (fun a => hL a.succ)]

end GlobalTheory.GenFibreDegree
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_intersection_formula : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsLocallyNoetherian Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d e : ℕ), IsArithVar q d → IsArithVar p (d + (e + 1)) → ∀ (f : Y ⟶ B), f ≫ q = p → ∀ (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (L : Fin (e + 1) → LB Y) (hL : ∀ a, (L a).IsLB) (r : (L 0).ι → Y.functionFieldˣ) (hr : IsRatSec (L 0) r) (γ : Y → ℤ), (∀ z, (divOfRatSec (hL 0) hr).mult z ≠ 0 → ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), i (genericPoint Z) = z ∧ IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) ∧ γ z = (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a : Fin e => ((L a.succ).pull i).pull j'))) → (letI := algebraΓOfHom s; interNum B.functionField (structureModule G) (fun a => (L a).pull j)) = ∑ᶠ z, (divOfRatSec (hL 0) hr).mult z * γ z := by
  atlas_forward_decl GlobalTheory.GenFibreDegree.degree_genericFibre_ratSec
end

section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.Published
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier

namespace GlobalTheory.FibreProj

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

theorem dim_closure_lt (hB : IsArithVar q d) {b : B} (hb : b ≠ genericPoint B) :
    topologicalKrullDim (closure ({b} : Set B)) < ((d + 1 : ℕ) : WithBot ℕ∞) := by
  have hgen : genericPoint B ∉ closure ({b} : Set B) := fun h =>
    hb ((genericPoint_specializes b).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
  have h1 : topologicalKrullDim (Set.univ : Set B) = (d + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hB.dim_eq
  have hup : topologicalKrullDim (closure ({b} : Set B)) + 1 ≤ (d + 1 : ℕ) :=
    h1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x _ => ⟨genericPoint B, trivial, hgen, genericPoint_specializes x⟩
  by_contra h
  have := (add_le_add_left (not_lt.1 h) 1).trans hup
  norm_cast at this
  omega

theorem interNum_eq_zero_of_ne [IsIntegral Y] {f : Y ⟶ B} {G : Scheme.{0}} {j : G ⟶ Y} {s : G ⟶ Sp B.functionField}
    (h : IsPullback j s f (B.fromSpecStalk (genericPoint B))) (hf : f (genericPoint Y) ≠ genericPoint B)
    {ι : Type} [Fintype ι] {P : ι → LB G} (hP : ∀ i, (P i).IsLB) :
    (letI := algebraΓOfHom s; interNum B.functionField (structureModule G) P) = 0 := by
  obtain ⟨-, h₂, -, h₄⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s h
  have : IsEmpty G := not_nonempty_iff.1 fun hG => by
    obtain ⟨_, e⟩ := h₄ hG
    exact hf (h₂.le ⟨_, e⟩)
  letI := algebraΓOfHom s
  exact interNum_eq_zero_of_isZero _ (InterModel.isZero_of_isEmpty _) hP

theorem ne_genericPoint_of_vertical (hB : IsArithVar q d) {Z : Scheme.{0}} (g : Z ⟶ B) (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)] (z : Z) : g z ≠ genericPoint B := fun e => by
  have := hB.charZero
  have h₁ : genericPoint B ∈ B.basicOpen (l : Γ(B, ⊤)) :=
    (unitAt_fnOf_iff (Opens.mem_top _) (Opens.mem_top _) _).1 (unitAt_genericPoint
      ((map_ne_zero_iff _ (fnOf_injective ⊤ (Opens.mem_top _))).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)))
  have h₂ : z ∈ g ⁻¹ᵁ B.basicOpen (l : Γ(B, ⊤)) := show g z ∈ _ from e ▸ h₁
  rw [Scheme.preimage_basicOpen_top, map_natCast, ← map_natCast (algebraMap (ZMod l) Γ(Z, ⊤)), ZMod.natCast_self, map_zero,
    Scheme.basicOpen_zero] at h₂
  exact h₂

theorem isProper_of_isArithVar {D : ℕ} (h : IsArithVar p D) : IsProper p := by
  obtain ⟨N, j, _, hj⟩ := h.isProjOver
  have := isProper_str k N
  exact hj ▸ inferInstance

theorem isArFun_pull (H : ArCalc) [IsIntegral Y] (hB : IsArithVar q d) (hY : IsArithVar p d) (f : Y ⟶ B) (w : f ≫ q = p)
    {G : Scheme.{0}} {j : G ⟶ Y} {s : G ⟶ Sp B.functionField}
    (h : IsPullback j s f (B.fromSpecStalk (genericPoint B))) {κ : Type} [Fintype κ] {A : κ → HermLB q}
    {Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun A d Φ) {ι : Type} [Fintype ι] [IsEmpty ι] (P : ι → LB G) :
    IsArFun (fun a => (A a).pull f w) d
      (((letI := algebraΓOfHom s; interNum B.functionField (structureModule G) P : ℤ) : ℝ) • Φ) := by
  by_cases hf : f (genericPoint Y) = genericPoint B
  · obtain ⟨-, h₂, -, -⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s h
    obtain ⟨x, -⟩ : genericPoint Y ∈ Set.range j := h₂.ge hf
    have := isProper_of_isArithVar hB
    have : IsProper (f ≫ q) := w ▸ isProper_of_isArithVar hY
    have : IsProper f := IsProper.of_comp f q
    obtain ⟨h₃, h₄⟩ := GlobalTheory.T.residue_degree_eq_euler_characteristic B Y f G j s h (GlobalTheory.T.generic_fibre_projective k B Y q p hB.isProjOver hY.isProjOver f w G j s h)
      (GlobalTheory.T.generic_fibre_dimension_le B Y (d + 1) 0 hB.dim_eq hY.dim_eq.le f G j s h) ⟨x⟩
    letI := algebraΓOfHom s
    rw [interNum_of_isEmpty, h₄]
    exact (H.arProj k B Y q p d hB hY f w hf h₃).2 κ A Φ hΦ
  · rw [interNum_eq_zero_of_ne h hf isEmptyElim, Int.cast_zero, zero_smul]
    refine ⟨fun n => ?_, fun _ _ _ _ => rfl⟩
    obtain ⟨t, ht, e⟩ := ProjDrop.isSelfInter_zero_of_dim_lt H k B Y q p d d hB hY f w (dim_closure_lt hB hf) (comb A n)
    exact ⟨t, (H.arIso k Y p d hY).1 _ _ t (isometric_comb_pull A n f w).symm ht, e⟩

omit [IsIntegral B] in

theorem isometric_pull_pull {Z : Scheme.{0}} (L : HermLB q) (f : Y ⟶ B) (w : f ≫ q = p) (i : Z ⟶ Y)
    (h : (i ≫ f) ≫ q = i ≫ p) : ((L.pull f w).pull i rfl).Isometric (L.pull (i ≫ f) h) :=
  have R := L.refines_pull_pull f w i rfl h
  HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy => ((R.φ σ c y hy).trans (add_zero _)).symm

theorem pol_vertical {D e : ℕ} (hB : IsArithVar q d) (hY : IsArithVar p D) (hD : e + (d + 1) = D) (f : Y ⟶ B) (w : f ≫ q = p)
    (L : Fin e → HermLB p) (A : Fin (d + 1) → HermLB q) {h : (Fin e ⊕ Fin (d + 1) → ℤ) → Y → ℝ}
    (hh : ∀ n, (comb (Sum.elim L fun a => (A a).pull f w) n).IsArithHeight (h n)) {Z : Scheme.{0}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [IsIntegral Z] (hZ : topologicalKrullDim Z = D) (l : ℕ) [Fact l.Prime]
    [Algebra (ZMod l) Γ(Z, ⊤)] : pol (fun n => h n (i (genericPoint Z))) = 0 := by
  have hp : IsProjOver (strHom (ZMod l) Z) := GlobalTheory.T.closed_subscheme_mod_l_projective k Y p D hY Z i l
  have h₁ := GlobalTheory.T.intersection_number_zero_small_image (ZMod l) e (d + 1) Z B hp (hD ▸ hZ.le) (i ≫ f)
    (dim_closure_lt hB (ne_genericPoint_of_vertical hB _ l _)) (fun a => (L a).B.pull i)
    (fun a => LB.isLB_pull (L a).isLB i) (fun a => (A a).B) fun a => (A a).isLB
  have h₂ : interNum (ZMod l) (structureModule Z)
      (fun a => ((Sum.elim L fun a => (A a).pull f w) a).B.pull i) = 0 := by
    refine (interNum_congr_lbIso _ _ (fun a => LB.isLB_pull (HermLB.isLB _) i) ?_ ?_).trans h₁
    · rintro (a | a)
      · exact LB.isLB_pull (L a).isLB i
      · exact LB.isLB_pull (A a).isLB _
    · rintro (a | a)
      · exact (CechPic.cls_eq_iff (LB.isLB_pull (L a).isLB i) (LB.isLB_pull (L a).isLB i)).1 rfl
      · exact ((A a).refines_pull_pull f w i rfl (by rw [Category.assoc, w])).lbIso
  simp only [fun n => (hh n).vertical Z i (ZMod l) D hZ]
  rw [pol_mul_const, GlobalTheory.T.polynomial_top_self_intersection k Y p (ZMod l) Z hp _ D (by simpa using hD) hZ.le i, h₂]
  simp

theorem arFun_prod (H : ArCalc) (hB : IsArithVar q d) (hs : GenSmooth q d) {A : Fin (d + 1) → HermLB q}
    {Φ : MvPolynomial (Fin (d + 1)) ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun A d Φ) (e : ℕ) :
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k), IsArithVar p (d + e) → ∀ (f : Y ⟶ B) (w : f ≫ q = p)
      (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) →
      ∀ (L : Fin e → HermLB p) (Ψ : MvPolynomial (Fin e ⊕ Fin (d + 1)) ℝ →ₗ[ℝ] ℝ),
        IsArFun (Sum.elim L fun a => (A a).pull f w) (d + e) Ψ → Ψ (∏ o, X o) =
          (letI := algebraΓOfHom s; (interNum B.functionField (structureModule G) (fun i => (L i).B.pull j) : ℝ)) *
            Φ (∏ a, X a) := by
  induction e with
  | zero =>
    intro Y _ p hY f w G j s h L Ψ hΨ
    have e := DFunLike.congr_fun (VertForm.FormEx.arFun_eq_rename H hY
      (isArFun_pull H hB hY f w h hΦ fun i => (L i).B.pull j) hΨ Sum.inr fun _ => rfl) (∏ a, X a)
    simpa [Fintype.prod_sum_type] using e.symm
  | succ e ih =>
    intro Y _ p hY f w G j s hG L Ψ hΨ
    have := hY.isNoetherian
    let N : Fin e ⊕ Fin (d + 1) → HermLB p := Sum.elim (fun a => L a.succ) fun a => (A a).pull f w
    have hc : Fintype.card (Fin e ⊕ Fin (d + 1)) = d + (e + 1) := by simp; omega
    obtain ⟨Φ', hΦ'⟩ := ((H.arExists k Y p _ hY).2 _ fun o : Option _ => o.elim (L 0) N).1
    choose h hh using fun n => (H.arExists k Y p _ hY).1 (comb N n)
    obtain ⟨r, hr⟩ := exists_isRatSec (L 0).isLB
    have hm := fun n => H.arMix k Y p _ hY _ (L 0) N Φ' hΦ' n (h n) (hh n) r hr
    have ha := GlobalTheory.T.arch_integrable_polynomial_vanishing k B Y q p d _ hs hY f w _ _ (by simp) (fun a : Fin e => L a.succ) A (L 0) r hr fun n => (hm n).1
    have key (z : Y) : ∃ c : ℤ, ((L 0).div hr).mult z ≠ 0 →
        pol (fun n => h n z) = (d + (e + 1)).factorial * (c * Φ (∏ a, X a)) ∧
        ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (G' : Scheme.{0}) (j' : G' ⟶ Z)
          (s' : G' ⟶ Sp B.functionField), i (genericPoint Z) = z ∧
          IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) ∧
          c = (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G')
            (fun a : Fin e => ((L a.succ).B.pull i).pull j')) := by
      obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
      have hP := IsPullback.of_hasPullback (i ≫ f) (B.fromSpecStalk (genericPoint B))
      refine ⟨_, fun hz => ⟨?_, Z, i, ‹_›, ‹_›, _, _, _, rfl, hP, rfl⟩⟩
      have hZ := GlobalTheory.T.codim_one_integral_subscheme_dim k Y p _ hY Z i (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
      rcases hY.vertical_or_horizontal i with ⟨l, _, ⟨_⟩⟩ | ⟨hc0, -⟩
      · rw [pol_vertical hB hY (by omega) f w _ A hh i hZ l, interNum_eq_zero_of_ne hP
          (ne_genericPoint_of_vertical hB _ l _) fun a : Fin e => LB.isLB_pull (LB.isLB_pull (L a.succ).isLB i) _]
        simp
      · have hZ' : IsArithVar (i ≫ p) (d + e) := hY.of_isClosedImmersion i hc0 hZ
        have w' : (i ≫ f) ≫ q = i ≫ p := by rw [Category.assoc, w]
        obtain ⟨Ψ', hΨ'⟩ := ((H.arExists k Z _ _ hZ').2 _ fun o => (N o).pull i rfl).1
        have e₁ (n) : h n (i (genericPoint Z)) = Ψ' (lin (fun o => (n o : ℝ)) ^ (d + (e + 1))) := by
          obtain ⟨t, ht, e₂⟩ := hΨ'.1 n
          exact ((hh n).isSelfInter_restrict hY i rfl).unique hZ'
            ⟨t, (H.arIso k Z _ _ hZ').1 _ _ t (isometric_comb_pull N n i rfl) ht, e₂⟩
        have hΨ'' := ((H.arIso k Z _ _ hZ').2 _ _ Ψ' hΨ').2.1
          (Sum.elim (fun a : Fin e => (L a.succ).pull i rfl) fun a => (A a).pull (i ≫ f) w') (by
            rintro (a | a)
            · exact .refl _
            · exact isometric_pull_pull _ f w i w')
        simp only [e₁]
        rw [pol_lin_pow Ψ' hc, ih Z _ hZ' _ w' _ _ _ hP _ Ψ' hΨ'']
        rfl
    choose γ hγ using key
    have hg := GlobalTheory.T.generic_fibre_intersection_formula k B Y q p d e hB hY f w G j s hG (fun a => (L a).B) (fun a => (L a).isLB) r hr γ
      fun z hz => (hγ z hz).2
    have hT := ((L 0).div hr).finite_support_mult
    have e₃ (u : Y → ℝ) : ∑ᶠ z, (((L 0).div hr).mult z : ℝ) * u z =
        ∑ z ∈ hT.toFinset, (((L 0).div hr).mult z : ℝ) * u z :=
      finsum_eq_sum_of_support_subset _ fun z hz => by
        simpa using left_ne_zero_of_mul hz
    have e₄ : ∑ᶠ z, ((L 0).div hr).mult z * γ z = ∑ z ∈ hT.toFinset, ((L 0).div hr).mult z * γ z :=
      finsum_eq_sum_of_support_subset _ fun z hz => by
        simpa using left_ne_zero_of_mul hz
    have e₅ := pol_mix Φ' hc
    simp only [fun n => (hm n).2, e₃] at e₅
    rw [pol_sub, ha, sub_zero, pol_sum, Finset.sum_congr rfl fun z hz => by
      rw [pol_const_mul, (hγ z (by simpa using hz)).1]] at e₅
    have e₆ := DFunLike.congr_fun (VertForm.FormEx.arFun_eq_rename H hY hΦ' hΨ
      (fun o => o.elim (.inl 0) (Sum.map Fin.succ id)) (by rintro (_ | a | a) <;> rfl)) (∏ o, X o)
    have e₇ : Φ' (∏ o, X o) = Ψ (∏ o, X o) := by
      simpa [Fintype.prod_option, Fintype.prod_sum_type, Fin.prod_univ_succ, mul_assoc] using e₆
    rw [hg, e₄, ← e₇]
    refine mul_left_cancel₀ (a := ((d + (e + 1)).factorial : ℝ)) (by positivity) (e₅.symm.trans ?_)
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring

theorem exists_monomial_eq_prod {κ : Type} (n : ℕ) (m : κ →₀ ℕ) (hm : m.degree = n) :
    ∃ r : Fin n → κ, (monomial m 1 : MvPolynomial κ ℝ) = ∏ a, X (r a) := by
  subst hm
  have hl : m.toMultiset.toList.length = m.degree := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    rfl
  refine ⟨fun a => m.toMultiset.toList.get (a.cast hl.symm), ?_⟩
  refine Eq.trans ?_ ((finCongr hl.symm).prod_comp (fun a => (X (m.toMultiset.toList.get a) : MvPolynomial κ ℝ)) |>.trans
    (Fin.prod_univ_fun_getElem m.toMultiset.toList fun a => (X a : MvPolynomial κ ℝ))).symm
  rw [Multiset.prod_map_toList, ← prod_X_pow_eq_monomial, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by simp [pow_add])]
  rfl

open scoped Classical in

theorem arFun_mul_pull : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d e : ℕ), IsArithVar q d → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) → IsArithVar p (d + e) → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (L : Fin e → HermLB p) (κ : Type) [Fintype κ] (A : κ → HermLB q) (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial (Fin e ⊕ κ) ℝ →ₗ[ℝ] ℝ), IsArFun A d Φ → IsArFun (Sum.elim L fun a => (A a).pull f w) (d + e) Ψ → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous (d + 1) → Ψ ((∏ i : Fin e, MvPolynomial.X (Sum.inl i)) * rename Sum.inr P) = (letI := algebraΓOfHom s; (interNum B.functionField (structureModule G) (fun i => (L i).B.pull j) : ℝ)) * Φ P := by
  intro H k _ B Y _ _ q p d e hB hr hY f w G j s hG L κ _ A Φ Ψ hΦ hΨ P hP
  rw [P.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨r, e₀⟩ := exists_monomial_eq_prod (d + 1) m (by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (mem_support_iff.1 hm))
  obtain ⟨Φ', hΦ'⟩ := ((H.arExists k B q d hB).2 _ fun a => A (r a)).1
  obtain ⟨Ψ', hΨ'⟩ := ((H.arExists k Y p _ hY).2 _ (Sum.elim L fun a => (A (r a)).pull f w)).1
  have e₁ := arFun_prod H hB (RegGenSmooth.genSmooth hB hr) hΦ' e Y p hY f w G j s hG L Ψ' hΨ'
  rw [VertForm.FormEx.arFun_eq_rename H hB hΦ' hΦ r fun _ => rfl,
    VertForm.FormEx.arFun_eq_rename H hY hΨ' hΨ (Sum.map id r) (by rintro (a | a) <;> rfl)] at e₁
  rw [show monomial m (coeff m P) = coeff m P • monomial m 1 by rw [smul_monomial, smul_eq_mul, mul_one], e₀, map_smul, mul_smul_comm, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul, mul_left_comm]
  congr 1
  simpa [Fintype.prod_sum_type] using e₁

end GlobalTheory.FibreProj
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleNefFibZ

theorem exists_prime_le (P : Ideal ℤ) [P.IsPrime] :
    ∃ l : ℕ, l.Prime ∧ ∀ r : ℤ, r ∉ Ideal.span {(l : ℤ)} → r ∉ P := by
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P (Ideal.IsPrime.ne_top ‹_›)
  set m := Submodule.IsPrincipal.generator M
  have hmM : Ideal.span {m} = M := Submodule.IsPrincipal.span_singleton_generator M
  have hm0 : m ≠ 0 := by
    rintro h
    have := Ideal.bot_lt_of_maximal M Int.not_isField
    rw [← hmM, h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact lt_irrefl _ this
  have hmp : Prime m := (Ideal.span_singleton_prime hm0).1 (hmM ▸ hM.isPrime)
  refine ⟨m.natAbs, Int.prime_iff_natAbs_prime.1 hmp, fun r hr hrP => hr ?_⟩
  rw [Ideal.mem_span_singleton, Int.natAbs_dvd]
  rw [← Ideal.mem_span_singleton, hmM]
  exact hPM hrP

theorem isAmpleLB_tens_of_nefFib : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → IsAmpleLB (L.tens A).B := by
  intro k _ X _ p D hX L A hL hA
  haveI : Module.Finite ℤ k := hX.finite
  set s : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k) with hs_def
  have hsZ : s = ShFam.Pad.toSpZ X := specZIsTerminal.hom_ext _ _
  have hP : IsProjOver s := hsZ ▸ ShFam.Pad.isProjOver_toSpZ hX.isProjOver
  have hPB : AbLaw.IsProjBy s := (ProjSpace.isProjBy_iff_isProjOver s).2 hP
  haveI : IsProper s := hsZ ▸ FibreProj.isProper_of_isArithVar (ShFam.Pad.isArithVar_toSpZ hX)
  have hM : (L.tens A).B.IsLB := (L.tens A).isLB
  haveI : IsProper (Over.mk s).hom := ‹IsProper s›
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk s) hM).1 ?_
  refine AmpleLocal.relAmple_of_locally _ (Over.mk s) _ hM inferInstance inferInstance fun P => ?_
  obtain ⟨l, hl, hlP⟩ := @exists_prime_le P.asIdeal P.isPrime
  haveI : Fact l.Prime := ⟨hl⟩
  have F := GlobalTheory.T.isAmple_tensor_nef_ample_finiteFieldFibre k X p D hX L A hL hA l
  have hFib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s))
      ((L.tens A).B.pull (pullback.fst s (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l)))))) := by
    haveI : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s)).hom :=
      inferInstanceAs (IsProper (pullback.snd s _))
    exact (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2 F
  have hfrac : ∀ y : ZMod l, ∃ a b : ℤ, Int.castRingHom (ZMod l) b ≠ 0 ∧
      y * Int.castRingHom (ZMod l) b = Int.castRingHom (ZMod l) a :=
    fun y => ⟨(y.val : ℤ), 1, by simp, by simp⟩
  obtain ⟨r, hr, hA'⟩ := AmpleNear.relAmple_near_fibre ℤ (Over.mk s) (L.tens A).B hX.flat hPB hM (ZMod l)
    (Int.castRingHom (ZMod l)) hfrac hFib
  have hrl : r ∉ Ideal.span {(l : ℤ)} := by
    rw [Ideal.mem_span_singleton]
    intro h
    exact hr ((ZMod.intCast_zmod_eq_zero_iff_dvd r l).2 h)
  let U : (Spec (CommRingCat.of ℤ)).Opens := PrimeSpectrum.basicOpen r
  haveI : IsAffine U.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of ℤ) r
  exact ⟨U, hlP r hrl, AmpleFibres.relAmple_restrict U (Over.mk s) hM hA'⟩

end GlobalTheory.AmpleNefFibZ
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → IsAmpleLB (L.tens A).B := by
  atlas_forward_decl GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib
end
