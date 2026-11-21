import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtIffForallSpecializesStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DivisorPointProperLift
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.DiscrepancyFormulaDivisor
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FormOrderBirationalPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorCentreThroughImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsRoundedDownDivisor
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolutionBigBundle
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistAmple
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChart
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientSpanRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentCotangentOfIsTopFormFrameOfVani
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyFormulaDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorBirationalCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackBijectiveBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorCenterProperLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.BadOpen

theorem exists_affine_nhds_avoid : ∀ (X Y : Scheme.{0}) [IsIntegral X] (s : Y ⟶ X) [IsProper s] (T : Set Y) (σ : Y) (y : X) (N : CartierDiv X), T.Finite → (∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → ¬ s w ⤳ y) → ∃ (U : X.Opens) (e : X.functionFieldˣ), IsAffineOpen U ∧ y ∈ U ∧ (∀ x ∈ U, N.IsEqn x e) ∧ ∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → s w ∉ U := by
  intro X Y _ s _ T σ y N hT hbad
  obtain ⟨g, hg⟩ := N.exists_isEqn y
  obtain ⟨U₁, hyU₁, hU₁⟩ := hg.exists_nhds
  set C : Set X := ⋃ v ∈ T, s.base '' (closure {v} ∩ closure {σ}) with hC
  have hCc : IsClosed C := by
    refine hT.isClosed_biUnion fun v _ => ?_
    exact s.isClosedMap _ (isClosed_closure.inter isClosed_closure)
  have hyC : y ∉ C := by
    simp only [hC, Set.mem_iUnion, Set.mem_image, not_exists, not_and]
    intro v hv w hw hwy
    exact hbad v hv w (specializes_iff_mem_closure.2 hw.1) (specializes_iff_mem_closure.2 hw.2)
      (hwy ▸ specializes_rfl)
  let V : X.Opens := U₁ ⊓ ⟨Cᶜ, hCc.isOpen_compl⟩
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := y) ⟨hyU₁, hyC⟩
  refine ⟨W, g, hW, hyW, fun x hx => hU₁ x (hWV hx).1, fun v hv w hvw hσw hw => ?_⟩
  have := (hWV hw).2
  apply this
  simp only [hC, Set.mem_iUnion, Set.mem_image]
  exact ⟨v, hv, w, ⟨specializes_iff_mem_closure.1 hvw, specializes_iff_mem_closure.1 hσw⟩, rfl⟩

end GlobalTheory.BadOpen
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nhds_avoiding_images_of_specializations : ∀ (X Y : Scheme.{0}) [IsIntegral X] (s : Y ⟶ X) [IsProper s] (T : Set Y) (σ : Y) (y : X) (N : CartierDiv X), T.Finite → (∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → ¬ s w ⤳ y) → ∃ (U : X.Opens) (e : X.functionFieldˣ), IsAffineOpen U ∧ y ∈ U ∧ (∀ x ∈ U, N.IsEqn x e) ∧ ∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → s w ∉ U := by
  atlas_forward_decl GlobalTheory.BadOpen.exists_affine_nhds_avoid
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open Opposite

namespace GlobalTheory.TwoOpens

theorem sections_inter_eq_sub_of_subsingleton_cohOn : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  intro Y F W₁ W₂ h t
  let A := (toAbSheaf Y).obj F
  let S := Flasque.injectiveShortComplex A
  have hS : S.ShortExact := Flasque.injectiveShortComplex_shortExact A
  have hfl : TopCat.Sheaf.IsFlasque S.X₂ := Flasque.isFlasque_injectiveShortComplex_X₂ A
  have hinj : ∀ W : Y.Opens, Function.Injective (S.f.hom.app (op W)) := by
    intro W x y hxy
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective x
    obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
    rw [← SheafLES.equivZero_map, ← SheafLES.equivZero_map] at hxy
    rw [SheafLES.injective_zero hS W ((SheafLES.equivZero.{0} S.X₂ W).injective hxy)]
  have hex : ∀ W : Y.Opens, Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) := by
    intro W x
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₂ W).surjective x
    rw [← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (SheafLES.equivZero_map S.f W y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
      exact ⟨y, (SheafLES.equivZero.{0} S.X₂ W).injective
        ((SheafLES.equivZero_map S.f W y).trans hy)⟩

  have natf : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.f.hom.app (op V) (S.X₁.obj.map (homOfLE hUV).op x) =
        S.X₂.obj.map (homOfLE hUV).op (S.f.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.f.hom (homOfLE hUV).op x
  have natg : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hUV).op x) =
        S.X₃.obj.map (homOfLE hUV).op (S.g.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.g.hom (homOfLE hUV).op x
  have resres : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₂.obj.map (homOfLE h₂).op (S.X₂.obj.map (homOfLE h₁).op x) =
        S.X₂.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have resres3 : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₃.obj.map (homOfLE h₂).op (S.X₃.obj.map (homOfLE h₁).op x) =
        S.X₃.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

  obtain ⟨b', hb'⟩ := (AddCommGrpCat.epi_iff_surjective
    (S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op)).1 (hfl.epi _)
    (S.f.hom.app (op (W₁ ⊓ W₂)) (sectionsOn.toΓ F _ t))

  let U : Bool → Y.Opens := fun b => cond b W₂ W₁
  let sf : ∀ b : Bool, ToType (S.X₃.obj.obj (op (U b))) := fun b =>
    match b with
    | true => S.g.hom.app (op W₂) b'
    | false => 0
  have h0 : S.X₃.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    rw [← natg, hb']
    exact (hex _).apply_apply_eq_zero _
  have h0' : S.X₃.obj.map (homOfLE (inf_le_left : W₂ ⊓ W₁ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    have e := resres3 (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (inf_comm W₂ W₁).le (S.g.hom.app (op W₂) b')
    rw [h0, map_zero] at e
    exact e.symm
  have hcomp : TopCat.Presheaf.IsCompatible S.X₃.obj U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (map_zero _).trans h0.symm
    · exact h0'.trans (map_zero _).symm
    · rfl
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := Y.toPresheafedSpace.carrier) S.X₃ U (W₁ ⊔ W₂)
    (fun b => homOfLE (by cases b; exacts [le_sup_left, le_sup_right]))
    (sup_le (le_iSup U false) (le_iSup U true)) sf hcomp

  obtain ⟨i, hi⟩ := SheafLES.sections_surjective_of_subsingleton.{0} hS (W₁ ⊔ W₂) h q
  obtain ⟨bb, hbb⟩ := (hex W₂ (b' - S.X₂.obj.map (homOfLE (le_sup_right : W₂ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_sub, natg, hi]
    exact sub_eq_zero.2 (hq true).symm)
  obtain ⟨aa, haa⟩ := (hex W₁ (- S.X₂.obj.map (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_neg, natg, hi]
    exact neg_eq_zero.2 (hq false))
  refine ⟨(sectionsOn.toΓ F W₁).symm aa, (sectionsOn.toΓ F W₂).symm bb, ?_⟩
  apply (sectionsOn.toΓ F _).injective
  rw [map_sub, sectionsOn.toΓ_res, sectionsOn.toΓ_res]
  simp only [AddEquiv.apply_symm_apply]
  apply hinj
  change _ = S.f.hom.app _ (S.X₁.obj.map _ bb - S.X₁.obj.map _ aa)
  erw [map_sub]
  rw [natf, natf, hbb, haa, map_sub, map_neg, resres, resres, hb']
  abel

end GlobalTheory.TwoOpens
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayer_vietoris_sections_split : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  atlas_forward_decl GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

def chartEqn {D : CartierDiv Y} (i : (toLB D).ι) : Y.functionFieldˣ := (show EqnChart D from i).1.2

theorem gen_mem_chart {D : CartierDiv Y} (i : (toLB D).ι) : genericPoint Y ∈ (toLB D).U i :=
  (show EqnChart D from i).2.1

theorem isEqn_chartEqn {D : CartierDiv Y} (i : (toLB D).ι) {x : Y} (hx : x ∈ (toLB D).U i) :
    D.IsEqn x (chartEqn i) :=
  (show EqnChart D from i).2.2 x hx

theorem fnOf_g_chart {D : CartierDiv Y} (i j : (toLB D).ι) (h) :
    fnOf _ h ((toLB D).g i j).val = (chartEqn i : Y.functionField) / (chartEqn j : Y.functionField) :=
  fnOf_toLB_g i j h

def genChart (D : CartierDiv Y) : (toLB D).ι :=
  (exists_chart (isLB_toLB D) (genericPoint Y)).choose

def coordFn {D : CartierDiv Y} {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    Γ(Y, W ⊓ (toLB D).U i) :=
  Twist.coord (sectionsOn.toΓ _ _ a) i

theorem coordFn_zero {D : CartierDiv Y} {W : Y.Opens} (i : (toLB D).ι) :
    coordFn (0 : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) i = 0 := rfl

theorem coordFn_add {D : CartierDiv Y} {W : Y.Opens}
    (a b : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    coordFn (a + b) i = coordFn a i + coordFn b i := rfl

open Classical in

def ratOn (D : CartierDiv Y) (W : Y.Opens) :
    sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField where
  toFun a := if h : genericPoint Y ∈ W then
      fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
        (chartEqn (genChart D) : Y.functionField)
    else 0
  map_zero' := by
    split_ifs with h
    · rw [coordFn_zero, map_zero, zero_div]
    · rfl
  map_add' a b := by
    split_ifs with h
    · rw [coordFn_add, map_add, add_div]
    · rw [add_zero]

theorem ratOn_apply (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) :
    ratOn D W a = fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
      (chartEqn (genChart D) : Y.functionField) :=
  dif_pos h

theorem ratOn_mul (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    ratOn D W a * chartEqn i = fnOf _ (memInf h (gen_mem_chart i)) (coordFn a i) := by
  set j := genChart D
  have hij : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U j :=
    memInf (memInf h (gen_mem_chart i)) (gen_mem_chart j)
  have e0 : resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (coordFn a i) =
      resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
        resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (coordFn a j) :=
    Twist.coord_rel (sectionsOn.toΓ _ _ a) i j _ _ _
  have e := congrArg (fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij) e0
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, fnOf_g_chart] at e
  rw [ratOn_apply D h, e]
  have := (chartEqn j).ne_zero
  field_simp
  exact mul_comm _ _

end GlobalTheory.Cartier

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem ratOn_regularAt (D : CartierDiv Y) {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) {y : Y} (hy : y ∈ W) :
    D.RegularAt y (ratOn D W a) := by
  obtain ⟨i, hi⟩ : ∃ i, y ∈ (toLB D).U i := exists_chart (isLB_toLB D) y
  refine ⟨chartEqn i, isEqn_chartEqn i hi, ?_⟩
  rw [ratOn_mul D (gen_mem hy) a i]
  exact regAt_fnOf (memInf hy hi) _ _

theorem exists_ratOn_eq (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    {f : Y.functionField} (hf : ∀ y ∈ W, D.RegularAt y f) :
    ∃ a, ratOn D W a = f := by
  have key (i : (toLB D).ι) : ∃ b : Γ(Y, W ⊓ (toLB D).U i),
      fnOf _ (memInf h (gen_mem_chart i)) b = f * chartEqn i :=
    exists_fnOf_eq _ fun x hx => (isEqn_chartEqn i hx.2).regularAt_iff.1 (hf x hx.1)
  choose b hb using key
  have hmem : b ∈ Twist.secGroup (GlobalTheory.structureModule Y) (toLB D) W := fun i j =>
    fn_ext (U := W ⊓ (toLB D).U i ⊓ (toLB D).U j) fun hij => by
      show fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (b i)) =
        fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
            resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (b j))
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hb, hb, fnOf_g_chart]
      have := (chartEqn j).ne_zero
      field_simp
  refine ⟨(sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem), ?_⟩
  have e := ratOn_mul D h ((sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem)) (genChart D)
  exact mul_right_cancel₀ (chartEqn (genChart D)).ne_zero (e.trans (hb _))

theorem ratOn_res (D : CartierDiv Y) {W W' : Y.Opens} (hle : W' ≤ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (h : genericPoint Y ∈ W') :
    ratOn D W' (sectionsOn.res Γ(Y, ⊤) _ hle a) = ratOn D W a := by
  rw [ratOn_apply D h, ratOn_apply D (hle h)]
  have e : coordFn (sectionsOn.res Γ(Y, ⊤) _ hle a) (genChart D) =
      resG Y (inf_le_inf_right _ hle) (coordFn a (genChart D)) := rfl
  rw [e, fnOf_resG]

theorem exists_ratOn_twist : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y), ∃ ρ : ∀ W : Y.Opens, sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField, (∀ (W : Y.Opens) (a), ∀ y ∈ W, D.RegularAt y (ρ W a)) ∧ (∀ (W : Y.Opens) (f : Y.functionField), genericPoint Y ∈ W → (∀ y ∈ W, D.RegularAt y f) → ∃ a, ρ W a = f) ∧ ∀ (W W' : Y.Opens) (h : W' ≤ W) (a), genericPoint Y ∈ W' → ρ W' (sectionsOn.res Γ(Y, ⊤) _ h a) = ρ W a :=
  fun Y _ D => ⟨ratOn D, fun _ a _ hy => ratOn_regularAt D a hy,
    fun _ _ h hf => exists_ratOn_eq D h hf, fun _ _ hle a h => ratOn_res D hle a h⟩

end GlobalTheory.Cartier
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalFunction_maps_of_cartierTwistSections : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y), ∃ ρ : ∀ W : Y.Opens, sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField, (∀ (W : Y.Opens) (a), ∀ y ∈ W, D.RegularAt y (ρ W a)) ∧ (∀ (W : Y.Opens) (f : Y.functionField), genericPoint Y ∈ W → (∀ y ∈ W, D.RegularAt y f) → ∃ a, ρ W a = f) ∧ ∀ (W W' : Y.Opens) (h : W' ≤ W) (a), genericPoint Y ∈ W' → ρ W' (sectionsOn.res Γ(Y, ⊤) _ h a) = ρ W a := by
  atlas_forward_decl GlobalTheory.Cartier.exists_ratOn_twist
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem genericPoint_mem_of_mem_opens (Y : Scheme.{0}) [IsIntegral Y] (W : Y.Opens) {y : Y}
    (hy : y ∈ W) : genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨y, trivial, hy⟩

theorem ratsec_split_of_H1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens),
    Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) →
    ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) →
    ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧
      ∀ y ∈ W₂, D.RegularAt y h₂ := by
  intro Y _ D W₁ W₂ hH f hf
  obtain ⟨ρ, hreg, hsurj, hres⟩ := GlobalTheory.T.exists_rationalFunction_maps_of_cartierTwistSections Y D
  by_cases g1 : genericPoint Y ∈ W₁
  · by_cases g2 : genericPoint Y ∈ W₂
    · have g12 : genericPoint Y ∈ W₁ ⊓ W₂ := ⟨g1, g2⟩
      obtain ⟨t, ht⟩ := hsurj (W₁ ⊓ W₂) f g12 hf
      obtain ⟨a, b, hab⟩ := GlobalTheory.T.mayer_vietoris_sections_split Y _ W₁ W₂ hH t
      refine ⟨ρ W₁ a, ρ W₂ b, ?_, fun y hy => hreg W₁ a y hy, fun y hy => hreg W₂ b y hy⟩
      rw [← ht, hab, map_sub, hres W₂ (W₁ ⊓ W₂) inf_le_right b g12,
        hres W₁ (W₁ ⊓ W₂) inf_le_left a g12]
    · refine ⟨ρ W₁ 0, f, by simp, fun y hy => hreg W₁ 0 y hy, fun y hy => ?_⟩
      exact absurd (genericPoint_mem_of_mem_opens Y W₂ hy) g2
  · refine ⟨-f, ρ W₂ 0, by simp, fun y hy => ?_, fun y hy => hreg W₂ 0 y hy⟩
    exact absurd (genericPoint_mem_of_mem_opens Y W₁ hy) g1

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_function_split_regular_divisor : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens), Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) → ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) → ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧ ∀ y ∈ W₂, D.RegularAt y h₂ := by
  atlas_forward_decl GlobalTheory.ratsec_split_of_H1
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep.LiftFn

variable {Y : Scheme.{0}}

theorem eq_of_specializes_of_coheight {v w : Y} (h : v ⤳ w) (hv : Order.coheight v = 1)
    (hw : Order.coheight w = 1) : v = w := by
  by_contra hne
  have hlt : w < v := lt_of_le_not_ge h fun e => hne (Specializes.antisymm h e).eq
  have h₃ := Order.coheight_add_one_le hlt
  rw [hv, hw] at h₃
  exact absurd h₃ (by decide)

variable [IsIntegral Y] [IsLocallyNoetherian Y]

theorem mult_neg (F : CartierDiv Y) (z : Y) : (-F).mult z = -F.mult z := by
  have e := CartierDiv.mult_add F (-F) z
  rw [add_neg_cancel, (CartierDiv.isEqn_zero (X := Y) z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero] at e
  omega

end GlobalTheory.PairStep.LiftFn

namespace GlobalTheory.PairStep

open LiftFn in

theorem exists_lifted_fn : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), IsLogRes p n η m G s K B → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → F.mult v ≤ 0) → s σ ⤳ y → Order.coheight σ = 1 → ∃ h : Y.functionField, (-F).RegularAt σ (h - 1) ∧ ∀ v : Y, v ≠ σ → Order.coheight v = 1 → s v ⤳ y → (-F).RegularAt v h := by
  intro X _ _ p n hp _ η m G N Y _ _ s _ K B F hres hcoh y σ hF hσy hσ
  have hpr : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hspr : IsProper (s ≫ p) :=
    ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper s := IsProper.of_comp s p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  haveI := hres.smooth
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth (s ≫ p)

  set T : Set Y := {v | v ≠ σ ∧ 0 < F.mult v} with hTdef
  have hT : T.Finite := F.finite_support_mult.subset fun v hv => hv.2.ne'
  obtain ⟨U, e, hUa, hyU, hNe, hav⟩ := GlobalTheory.T.exists_affine_nhds_avoiding_images_of_specializations X Y s T σ y N hT
    fun v hv w hvw hσw hwy => not_le.2 hv.2 (hF v w hv.1 hvw hσw hwy)
  have hTc : IsClosed (⋃ v ∈ T, closure ({v} : Set Y)) :=
    hT.isClosed_biUnion fun _ _ => isClosed_closure
  set W₁ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, hTc.isOpen_compl⟩ with hW₁
  set W₂ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, (isClosed_closure (s := ({σ} : Set Y))).isOpen_compl⟩ with hW₂
  have hW : W₁ ⊔ W₂ = s ⁻¹ᵁ U := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
    by_cases hwσ : w ∈ closure ({σ} : Set Y)
    · refine Or.inl ⟨hw, fun hwT => ?_⟩
      obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.1 hwT
      exact hav v hv w (specializes_iff_mem_closure.2 hwv) (specializes_iff_mem_closure.2 hwσ) hw
    · exact Or.inr ⟨hw, hwσ⟩
  have hc := hcoh U hUa
  rw [← hW] at hc
  set e' : Y.functionFieldˣ := fnPull s e with he'
  have key : ∀ w ∈ s ⁻¹ᵁ U, ∀ f : Y.functionField,
      (pullCart s N - F).RegularAt w f ↔ (-F).RegularAt w (f * e') := by
    intro w hw f
    obtain ⟨g, hg⟩ := F.exists_isEqn w
    rw [((isEqn_pullCart s (hNe _ hw)).sub hg).regularAt_iff, hg.neg.regularAt_iff]
    have : f * ((fnPull s e / g : Y.functionFieldˣ) : Y.functionField) =
        f * (e' : Y.functionField) * ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      rw [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, he']
      ring
    rw [this]
  have hinv : ∀ x ∈ W₁ ⊓ W₂, (pullCart s N - F).RegularAt x (e' : Y.functionField)⁻¹ := by
    intro x hx
    rw [key x hx.1.1, inv_mul_cancel₀ e'.ne_zero]
    have h1 := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg Y (-F) x 1).2
    rw [Units.val_one] at h1
    refine h1 fun z hzx => ?_
    rw [(unitAt_one z).ord_eq_zero, zero_add, mult_neg]
    refine neg_nonneg.2 (not_lt.1 fun hz => ?_)
    by_cases hzσ : z = σ
    · subst hzσ
      exact hx.2.2 (specializes_iff_mem_closure.1 hzx)
    · exact hx.1.2 (Set.mem_iUnion₂.2 ⟨z, ⟨hzσ, hz⟩, specializes_iff_mem_closure.1 hzx⟩)
  obtain ⟨h₁, h₂, hsplit, hh₁, hh₂⟩ :=
    GlobalTheory.T.rational_function_split_regular_divisor Y (pullCart s N - F) W₁ W₂ hc (e' : Y.functionField)⁻¹ hinv
  have hσU : σ ∈ s ⁻¹ᵁ U := hσy.mem_open U.isOpen hyU
  refine ⟨h₂ * e', ?_, fun v hvσ hv hvy => ?_⟩
  · have hσW : σ ∈ W₁ := ⟨hσU, fun hσT => by
      obtain ⟨v, hv, hσv⟩ := Set.mem_iUnion₂.1 hσT
      exact hv.1 (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hσv)
        (CartierDiv.coheight_eq_one_of_mult_ne_zero hv.2.ne') hσ)⟩
    have e₁ : h₂ * (e' : Y.functionField) - 1 = h₁ * e' := by
      rw [show h₂ = (e' : Y.functionField)⁻¹ + h₁ by rw [hsplit]; ring, add_mul,
        inv_mul_cancel₀ e'.ne_zero]
      ring
    rw [e₁]
    exact (key σ hσU h₁).1 (hh₁ σ hσW)
  · have hvU : v ∈ s ⁻¹ᵁ U := hvy.mem_open U.isOpen hyU
    have hvW : v ∈ W₂ := ⟨hvU, fun hvσ' =>
      hvσ (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hvσ') hσ hv).symm⟩
    exact (key v hvU h₂).1 (hh₂ v hvW)

end GlobalTheory.PairStep
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifted_function_on_logResolution : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), IsLogRes p n η m G s K B → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → F.mult v ≤ 0) → s σ ⤳ y → Order.coheight σ = 1 → ∃ h : Y.functionField, (-F).RegularAt σ (h - 1) ∧ ∀ v : Y, v ≠ σ → Order.coheight v = 1 → s v ⤳ y → (-F).RegularAt v h := by
  atlas_forward_decl GlobalTheory.PairStep.exists_lifted_fn
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem regAt_of_isIntegrallyClosed_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) → ∀ f : X.functionField, (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → f ∈ E.ring) → RegAt y f := by
  intro X _ _ p hp y hy f hf
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨y, hx⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨y, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hx⟩
  refine (mem_range_algebraMap_iff_forall_height_eq_one (A := X.presheaf.stalk y) f).2
    fun q hq h1 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q.comap (algebraMap _ (X.presheaf.stalk y)), inferInstance⟩
  have hP1 : P.asIdeal.height = 1 :=
    (IsLocalization.height_comap (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl q).trans h1
  have hPQ : P ≤ hU.primeIdealOf ⟨y, hx⟩ := fun s hs => by_contra fun hs' =>
    hq.ne_top (q.eq_top_of_isUnit_mem hs (IsLocalization.map_units (X.presheaf.stalk y)
      (⟨s, hs'⟩ : (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl)))
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ y := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨y, hx⟩)).mp hPQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨y, hx⟩] at h
  clear_value z
  haveI := hU.isLocalization_stalk z
  have hc : Order.coheight (z : X) = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
      (X.presheaf.stalk (z : X))
    rw [ringKrullDim_stalk_eq_coheight, hP, hP1] at this
    exact_mod_cast this

  haveI hT : IsLocalization.AtPrime (Localization.AtPrime q) P.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl (Localization.AtPrime q) q
  haveI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hs : (hU.primeIdealOf z).asIdeal.primeCompl = P.asIdeal.primeCompl := by
    ext s; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hP]
  haveI hZ : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (z : X)) := by
    rw [← hs]; exact hU.isLocalization_stalk z
  let e : X.presheaf.stalk (z : X) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv P.asIdeal.primeCompl (X.presheaf.stalk (z : X))
      (Localization.AtPrime q)).toRingEquiv
  haveI : IsIntegrallyClosed (X.presheaf.stalk (z : X)) :=
    ((IsNormalScheme.isDomain_and_isIntegrallyClosed_iff_of_ringEquiv e).2
      ⟨inferInstance, inferInstance⟩).2
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := by
    have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk (z : X)) := krullDimLE_of_coheight_le hc.le
    have hf : ¬ IsField (X.presheaf.stalk (z : X)) := fun h => by
      have := ringKrullDim_eq_zero_of_isField h
      rw [ringKrullDim_stalk_eq_coheight, hc] at this
      simp at this
    have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
    have h3 : IsIntegrallyClosed (X.presheaf.stalk (z : X)) ∧
        ∃! P : Ideal (X.presheaf.stalk (z : X)), P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, _, ⟨hm, inferInstance⟩, fun P hP => IsLocalRing.eq_maximalIdeal
        (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P hP.1 hP.2)⟩
    exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk (z : X)) hf).out 0 3).mpr h3
  obtain ⟨E, hE⟩ := DivOver.exists_isAt p (z : X)
  obtain ⟨a, rfl⟩ := (hE f).1 (hf z hzx E hE)
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf z).asIdeal.primeCompl a
  refine (mem_primeLocalSubalgebra_iff q _).2 ⟨algebraMap _ _ s.1, ?_, algebraMap _ _ c, ?_⟩
  · have := s.2
    rw [Ideal.mem_primeCompl_iff] at this
    have h' : s.1 ∉ P.asIdeal := by simpa only [hP] using this
    exact h'
  · have e' := congrArg (algebraMap _ X.functionField) e
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
    rw [Algebra.smul_def, mul_comm]
    exact ((algebraMap_germ hx c).trans e'.symm).trans (congrArg _ (algebraMap_germ hx s.1).symm)

end GlobalTheory.Discrepancy
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_at_normal_point_of_divisors : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) → ∀ f : X.functionField, (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → f ∈ E.ring) → RegAt y f := by
  atlas_forward_decl GlobalTheory.Discrepancy.regAt_of_isIntegrallyClosed_stalk
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.LogResConn

theorem mult_le_ord_of_regularAt {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {F : CartierDiv Y} {v : Y} {f : Y.functionField} (h : (-F).RegularAt v f) (hf : f ≠ 0)
    (hv : Order.coheight v = 1) : F.mult v ≤ Scheme.ord f v := by
  obtain ⟨g, hg⟩ := F.exists_isEqn v
  obtain ⟨a, ha⟩ := hg.neg.regularAt_iff.1 h
  have hg0 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact mul_ne_zero hf hg0 ha.symm
  have h2 := ord_algebraMap hv ha0
  rw [ha, Scheme.ord_mul hf hg0] at h2
  have h3 := Scheme.ord_mul (x := v) (Units.ne_zero g) hg0
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, (unitAt_one v).ord_eq_zero] at h3
  rw [hg.mult_eq]
  have : (0 : ℤ) ≤ ((Module.length (Y.presheaf.stalk v) (Y.presheaf.stalk v ⧸ Ideal.span {a})).toNat : ℤ) :=
    Int.natCast_nonneg _
  omega

theorem mem_ring_of_regularAt {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {E : DivOver q} {F : CartierDiv Y} {w : Y}
    {f : Y.functionField} (hE : E.IsAt w) (h : (-F).RegularAt w f) (hF : 0 ≤ F.mult w) :
    f ∈ E.ring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  have h1 := mult_le_ord_of_regularAt h hf hE.coheight_eq_one
  have h2 := hE.ord_eq (Units.mk0 f hf)
  have h3 := (E.ord_nonneg_iff (Units.mk0 f hf)).1 (by rw [h2]; simpa using hF.trans h1)
  simpa using h3

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]

theorem regAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : RegAt y f) : RegAt v (functionFieldMap s f) := by
  obtain ⟨E', hE'⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hv
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_primeDivisor_over_target_birational k X Y p s hbir E'
  have ht := GlobalTheory.T.primeDivisorCentre_through_image k X Y p s E' E hE v (hE'.through specializes_rfl)
  exact (hE' _).1 ((hE f).1 ((ht.of_specializes hsv) f hf))

theorem unitAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : UnitAt y f) : UnitAt v (functionFieldMap s f) := by
  have hf0 := hf.ne_zero
  obtain ⟨h1, h2⟩ := (unitAt_iff hf0).1 hf
  refine (unitAt_iff ((map_ne_zero _).2 hf0)).2 ⟨regAt_pull (p := p) s hbir hv hsv h1, ?_⟩
  rw [← map_inv₀]
  exact regAt_pull (p := p) s hbir hv hsv h2

end GlobalTheory.LogResConn

namespace GlobalTheory.LogResConn

theorem mult_lt_of_connected : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  intro X _ _ p n hp hn η m G N Y _ _ s _ K B F hη hm hres hF hcoh y σ hyint hdisc hσ hsσ hnear
    v hvσ hsv
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hFσ : F.mult σ = 1 := by rw [hF, hσ]; exact Int.ediv_self hm'.ne'
  have hFle : ∀ z, F.mult z ≤ 0 ↔ (pullCart s G - m • K).mult z < m := fun z => by
    rw [hF, ← Int.lt_add_one_iff, zero_add, Int.ediv_lt_iff_lt_mul hm', one_mul]
  have hFnn : ∀ z, 0 ≤ (pullCart s G - m • K).mult z → 0 ≤ F.mult z := fun z hz => by
    rw [hF]; exact Int.ediv_nonneg hz hm'.le
  by_cases hvc : Order.coheight v ≠ 1
  · have : (pullCart s G - m • K).mult v = 0 := by
      by_contra h0
      exact hvc (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    rw [this]; exact hm'
  push_neg at hvc
  haveI := hres.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth (s ≫ p)
  haveI : IsProper (s ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB (s ≫ p)).1 hres.proj).1
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  haveI : IsProper s := IsProper.of_comp s p
  have hbir := hres.bir
  have hσc : Order.coheight σ = 1 :=
    CartierDiv.coheight_eq_one_of_mult_ne_zero (by rw [hσ]; exact_mod_cast hm.ne')
  obtain ⟨h, hσreg, hreg⟩ := GlobalTheory.T.exists_lifted_function_on_logResolution X p n hp hn η m G N Y s K B F hres hcoh y σ
    (fun v w h1 h2 h3 h4 => (hFle v).2 (hnear v w h1 h2 h3 h4)) hsσ hσc
  obtain ⟨h₀, rfl⟩ := hbir.2 h

  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hbir n).1 (h0.trans (map_zero _).symm))

  have hDnn : ∀ (z : X), z ⤳ y → ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), E.IsAt z →
      DivOver.Over s E' E → ∀ w, s w = z → E'.IsAt w → 0 ≤ F.mult w := by
    intro z hz E E' hE hE'E w hwz hw
    subst hwz
    obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
    have hd := hdisc (s w) hz E hE g hg
    have h1 := GlobalTheory.T.discrepancy_formula_divisor ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m hm
      hres.div E' w (fnPull s g) hw (isEqn_pullCart s hg)
    have h2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
      unfold discrep
      rw [GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hbir E' E hE'E n η hη, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hbir E' E hE'E g]
    rw [h2] at h1
    rw [h1] at hd
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) := by
      rw [neg_div, neg_nonpos] at hd
      exact (div_nonneg_iff.1 hd).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hmq))
    exact hFnn w (by exact_mod_cast this)

  have hreg0 : RegAt y h₀ := by
    refine GlobalTheory.T.regular_at_normal_point_of_divisors X p hp y hyint h₀ fun z hz E hE => ?_
    obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p s hbir E
    obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.divisor_point_proper_lift ℂ X Y p s hbir inferInstance E' E hE'E z hE
    have hFw := hDnn z hz E E' hE hE'E w hwz hw
    have hsw : s w ⤳ y := hwz ▸ hz
    rw [hE'E h₀]
    by_cases hwσ : w = σ
    · subst hwσ
      have := mem_ring_of_regularAt hw hσreg hFw
      simpa using add_mem this (one_mem E'.ring)
    · exact mem_ring_of_regularAt hw (hreg w hwσ hw.coheight_eq_one hsw) hFw

  have hunit0 : UnitAt y h₀ := by
    by_cases hh1 : functionFieldMap s h₀ - 1 = 0
    · have : h₀ = 1 := hbir.1 (by rw [map_one]; exact sub_eq_zero.1 hh1)
      rw [this]; exact unitAt_one y
    have hnu : ¬ UnitAt y (h₀ - 1) := fun hu => by
      have hu' := unitAt_pull (p := p) s hbir hσc hsσ hu
      rw [map_sub, map_one] at hu'
      have := mult_le_ord_of_regularAt hσreg hh1 hσc
      rw [hu'.ord_eq_zero, hFσ] at this
      omega
    obtain ⟨a, ha, e⟩ := zeroAt_iff.2 ⟨hreg0.add ⟨-1, by rw [map_neg, map_one]⟩, by
      rwa [sub_eq_add_neg] at hnu⟩
    have h1a : (1 + a) ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := fun h' => by
      have h1 : (1 : X.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        simpa using sub_mem h' ha
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    exact ⟨1 + a, IsLocalRing.notMem_maximalIdeal.1 h1a, by rw [map_add, map_one, e]; ring⟩
  have hu := unitAt_pull (p := p) s hbir hvc hsv hunit0
  have := mult_le_ord_of_regularAt (hreg v hvσ hvc hsv) hu.ne_zero hvc
  rw [hu.ord_eq_zero] at this
  exact (hFle v).1 this

end GlobalTheory.LogResConn
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logResolution_mult_lt_of_connectedness : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  atlas_forward_decl GlobalTheory.LogResConn.mult_lt_of_connected
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.Discrepancy

theorem exists_logRes_subsingleton_cohOn_one : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y) (N : CartierDiv X), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) ∧ (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) := by
  intro hPr X _ _ p n hp hn η m G Z hη hm hZ
  letI := algebraΓOfHom p
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have hpS : IsProjOver (strHom ℂ X) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have hbig : IsBig ℂ H := IsAmpleLB.isBig ℂ X hpS H hH
  obtain ⟨Y, _, s, _, K, B, hlog, hZB, a, Fd, A, hA, hFd⟩ :=
    GlobalTheory.T.exists_log_resolution_big_bundle hPr ℂ X p n hp hn η m G hη Z hZ H hH.isLB hbig
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hlog.smooth
  haveI : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hlog.proj
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor ℂ Y (s ≫ p) n hlog.proj (pullCart s G - m • K) m

  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (hH.eventually_isAmpleLB_tens_lbPow_succ (isLB_toLB (-G)))
  have hj : J ≤ m * (J + 1) - 1 := by
    have : J + 1 ≤ m * (J + 1) := Nat.le_mul_of_pos_left _ hm
    omega
  have hTa := hJ _ hj
  have hsucc : m * (J + 1) - 1 + 1 = m * (J + 1) := by
    have : 1 ≤ m * (J + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm.ne' (Nat.succ_ne_zero J))
    omega
  rw [hsucc] at hTa
  obtain ⟨N, hNc⟩ := toPic_surjective ((J + 2) • cls H hH.isLB)
  have hTn : IsNef ℂ (tens (toLB (-G)) (lbPow H (m * (J + 1)))) := hTa.isNef
  have hcls : cls _ hTn.isLB = (m * 1) • cls (toLB N) (isLB_toLB N) - 1 • toPic G - m • cls H hH.isLB := by
    rw [cls_tens (isLB_toLB (-G)) (isLB_lbPow hH.isLB _), cls_lbPow hH.isLB, ← toPic_apply,
      ← toPic_apply, hNc, map_neg]
    simp only [mul_one, one_smul, smul_smul]
    rw [show m * (J + 2) = m * (J + 1) + m by ring, add_smul]
    abel
  obtain ⟨-, hloc⟩ := GlobalTheory.T.multiplier_vanishing_nef_twist_ample ℂ X p n hp η m G Y s K B F hη hm hlog hF (toLB N) H _
    (isLB_toLB N) hH.isLB 1 hTn one_pos hcls hH.isNef a Fd A hA hFd
  refine ⟨Y, inferInstance, inferInstance, s, inferInstance, K, B, F, N, hlog, hZB, hF,
    fun U hU => ?_⟩
  have hP := pull_isLB (isLB_toLB N) s
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule Y) (isLB_toLB (-F)) hP
    (isLB_toLB (pullCart s N - F)) (by
      rw [← toPic_apply, ← toPic_apply, cls_pull (isLB_toLB N) s hP, ← toPic_apply,
        ← toPic_pullCart, map_sub, map_neg]
      abel)
  exact (cohOn.mapIso Γ(Y, ⊤) (s ⁻¹ᵁ U) 1 e).toEquiv.subsingleton_congr.1 (hloc U hU 1 one_pos)

end GlobalTheory.Discrepancy
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logResolution_localVanishing : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y) (N : CartierDiv X), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) ∧ (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) := by
  atlas_forward_decl GlobalTheory.Discrepancy.exists_logRes_subsingleton_cohOn_one
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem connectedness_at_normal_point :
    GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  intro hP X _ _ p n hp hdim η m G Z hη hm hZ
  obtain ⟨Y, hYi, hYn, s, hs, K, B, F, N, hres, hB, hF, hvan⟩ :=
    GlobalTheory.T.exists_logResolution_localVanishing hP X p n hp hdim η m G Z hη hm hZ
  refine ⟨Y, hYi, hYn, s, hs, K, B, hres, hB, ?_⟩
  intro y σ hy hdisc hσ hσy hloc
  exact GlobalTheory.T.logResolution_mult_lt_of_connectedness X p n hp hdim η m G N Y s K B F hη hm hres hF hvan y σ hy hdisc hσ hσy hloc

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedness_lemma_at_normal_point_logResolution : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  atlas_forward_decl GlobalTheory.connectedness_at_normal_point
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PointSep

open IsLocalRing

theorem span_pair_isPrime_and_height_eq_two : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (a b : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hb : b ∈ IsLocalRing.maximalIdeal R), LinearIndependent (IsLocalRing.ResidueField R) (![(IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩, (IsLocalRing.maximalIdeal R).toCotangent ⟨b, hb⟩] : Fin 2 → IsLocalRing.CotangentSpace R) → (Ideal.span {a, b}).IsPrime ∧ (Ideal.span {a, b}).height = 2 := by
  intro R _ _ a b ha hb h
  classical
  have hdom : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hp := LinearIndependent.pair_iff.mp h
  have hsmul : ∀ (r : R) (x : maximalIdeal R),
      (maximalIdeal R).toCotangent (r • x) = (residue R r) • (maximalIdeal R).toCotangent x := by
    intro r x
    rw [map_smul]; rfl

  have ha2 : a ∉ maximalIdeal R ^ 2 := by
    intro h2
    have h0 : (maximalIdeal R).toCotangent ⟨a, ha⟩ = 0 := by
      rw [Ideal.toCotangent_eq_zero]; exact h2
    have := hp 1 0 (by simp [h0])
    exact one_ne_zero this.1
  have hpa : Prime a := ReciprocityTheory.AnForm.R.prime_of_not_mem_sq ha ha2
  have ha0 : a ≠ 0 := hpa.ne_zero

  have hba : b ∉ Ideal.span {a} := by
    intro hb'
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb'
    have heq : (⟨b, hb⟩ : maximalIdeal R) = r • ⟨a, ha⟩ := by
      ext; simp [hr]
    have := hp (-(residue R r)) 1 (by rw [heq, hsmul]; simp)
    exact one_ne_zero this.2

  have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have hle := h.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  set n := Module.finrank (ResidueField R) (CotangentSpace R) with hn
  have hdim : ringKrullDim R = (((n - 2) + 2 : ℕ) : WithBot ℕ∞) := by
    rw [← hfin, Nat.sub_add_cancel hle]
  have hind : ∀ c : Fin 2 → R, ∑ i, c i * (![a, b] : Fin 2 → R) i ∈ maximalIdeal R ^ 2 →
      ∀ i, c i ∈ maximalIdeal R := by
    intro c hc
    have hc' : (maximalIdeal R).toCotangent (c 0 • ⟨a, ha⟩ + c 1 • ⟨b, hb⟩) = 0 := by
      rw [Ideal.toCotangent_eq_zero]
      simpa [Fin.sum_univ_two] using hc
    rw [map_add, hsmul, hsmul] at hc'
    obtain ⟨h0, h1⟩ := hp _ _ hc'
    intro i
    fin_cases i
    · exact (residue_eq_zero_iff _).mp h0
    · exact (residue_eq_zero_iff _).mp h1
  have hmem : ∀ i, (![a, b] : Fin 2 → R) i ∈ maximalIdeal R := by
    intro i; fin_cases i
    · exact ha
    · exact hb
  obtain ⟨hreg, -⟩ := GlobalTheory.RegularQuotient.quotient_span_range R (n - 2) 2 ![a, b] hdim hmem hind
  have hrange : Set.range (![a, b] : Fin 2 → R) = {a, b} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [hrange] at hreg
  have hqdom : IsDomain (R ⧸ Ideal.span {a, b}) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hP : (Ideal.span {a, b}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hqdom
  refine ⟨hP, le_antisymm ?_ ?_⟩
  · have hmin : Ideal.span {a, b} ∈ (Ideal.span ((({a, b} : Finset R)) : Set R)).minimalPrimes := by
      rw [Finset.coe_insert, Finset.coe_singleton, Ideal.minimalPrimes_eq_subsingleton_self]
      rfl
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_
    exact_mod_cast Finset.card_le_two
  · have hPa : (Ideal.span {a}).IsPrime := (Ideal.span_singleton_prime ha0).mpr hpa
    have h1 : (⊥ : Ideal R) < Ideal.span {a} := by
      rw [bot_lt_iff_ne_bot]; simpa using ha0
    have h2 : Ideal.span {a} < Ideal.span {a, b} := by
      refine lt_of_le_of_ne (Ideal.span_mono (by simp)) ?_
      intro he
      exact hba (he ▸ Ideal.subset_span (by simp))
    have hlt1 := Ideal.height_strict_mono_of_isPrime h1
    have hlt2 := Ideal.height_strict_mono_of_isPrime h2
    have hne : (Ideal.span {a}).height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
    have e1 : (⊥ : Ideal R).height + 1 ≤ (Ideal.span {a}).height := Order.add_one_le_of_lt hlt1
    have e2 : (Ideal.span {a}).height + 1 ≤ (Ideal.span {a, b}).height := Order.add_one_le_of_lt hlt2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal R).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Ideal.span {a}).height + 1 := by gcongr
      _ ≤ _ := e2

end GlobalTheory.PointSep
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_pair_isPrime_height_two_of_cotangent_independent : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (a b : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hb : b ∈ IsLocalRing.maximalIdeal R), LinearIndependent (IsLocalRing.ResidueField R) (![(IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩, (IsLocalRing.maximalIdeal R).toCotangent ⟨b, hb⟩] : Fin 2 → IsLocalRing.CotangentSpace R) → (Ideal.span {a, b}).IsPrime ∧ (Ideal.span {a, b}).height = 2 := by
  atlas_forward_decl GlobalTheory.PointSep.span_pair_isPrime_and_height_eq_two
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncMeet

open IsLocalRing

theorem exists_stalk_equiv_of_fromSpecStalk (X : Scheme.{0}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ∃ (h : X.fromSpecStalk x p ⤳ x)
      (e : X.presheaf.stalk (X.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal),
      ∀ g, e ((X.presheaf.stalkSpecializes h).hom g) = algebraMap _ _ g := by
  obtain ⟨e, he⟩ := GlobalTheory.LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x p.asIdeal
  have hs : X.fromSpecStalk x p ⤳ x := by
    have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  refine ⟨hs, e, ?_⟩
  have hcomp : X.presheaf.stalkSpecializes hs ≫ CommRingCat.ofHom e.toRingHom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)) := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    ext s
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    change e ((X.presheaf.stalkSpecializes hs).hom ((X.presheaf.germ U _ hxU).hom s)) =
      algebraMap _ (Localization.AtPrime p.asIdeal) ((X.presheaf.germ U _ hxU).hom s)
    rw [h3]
    exact he U _ hxU s
  intro g
  exact congrArg (fun f => f.hom g) hcomp

theorem mem_asIdeal_iff (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) (y : X)
    (hy : y ⤳ x) (hp : X.fromSpecStalk x p = y) (g : X.presheaf.stalk x) :
    g ∈ p.asIdeal ↔ (X.presheaf.stalkSpecializes hy).hom g ∈ maximalIdeal (X.presheaf.stalk y) := by
  subst hp
  obtain ⟨h, e, he⟩ := exists_stalk_equiv_of_fromSpecStalk X x p
  have h1 : g ∈ p.asIdeal ↔ algebraMap _ (Localization.AtPrime p.asIdeal) g ∈
      maximalIdeal (Localization.AtPrime p.asIdeal) := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p.asIdeal) p.asIdeal g).symm
  rw [h1, ← he g, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MulEquiv.isUnit_map]

theorem coheight_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = p.asIdeal.height := by
  obtain ⟨h, e, he⟩ := exists_stalk_equiv_of_fromSpecStalk X x p
  have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)
  rw [ringKrullDim_eq_of_ringEquiv e,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  exact_mod_cast h1.symm

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_algebraMap_of_isUnit (x : X) (g : X.presheaf.stalk x) (hg : IsUnit g) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · have hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg.ne_zero
    rw [Scheme.ord_eq_iff hx hne]
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    change Ring.ordFrac _ _ = _
    rw [Ring.ordFrac_of_isUnit hg]
    rfl
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

theorem ord_algebraMap_ne_zero (x : X) (hx : Order.coheight x = 1) (g : X.presheaf.stalk x)
    (hg0 : g ≠ 0) (hg : g ∈ maximalIdeal (X.presheaf.stalk x)) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x ≠ 0 := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg0
  intro h0
  rw [Scheme.ord_eq_iff hx hne] at h0
  change Ring.ordFrac _ _ = _ at h0
  rw [Ring.ordFrac_eq_ord _ hg0] at h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hg0))
  rw [Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hg0) hm.symm] at h0
  have hm0 : m = 0 := by
    have h4 : (m : ℤ) = 0 := Multiplicative.ofAdd.injective (WithZero.coe_injective h0)
    exact_mod_cast h4
  subst hm0
  have h2 : Ring.ord (X.presheaf.stalk x) g = 0 := by rw [← hm]; rfl
  rw [Ring.ord] at h2
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at h2
  exact (mem_maximalIdeal g).1 hg h2

open IsLocalRing in

theorem exists_meet_point : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ v σ w : Y, v ∈ B → σ ∈ B → Order.coheight v = 1 → Order.coheight σ = 1 → v ≠ σ → v ⤳ w → σ ⤳ w → ∃ (w' : Y) (t u : Y.presheaf.stalk w'), w' ⤳ w ∧ v ⤳ w' ∧ σ ⤳ w' ∧ ringKrullDim (Y.presheaf.stalk w') = 2 ∧ Ideal.span {t, u} = IsLocalRing.maximalIdeal (Y.presheaf.stalk w') ∧ Scheme.ord (algebraMap (Y.presheaf.stalk w') Y.functionField t) σ = 1 ∧ Scheme.ord (algebraMap (Y.presheaf.stalk w') Y.functionField u) v = 1 ∧ ∀ v' ∈ B, Order.coheight v' = 1 → v' ⤳ w' → v' = v ∨ v' = σ := by
  classical
  intro Y _ _ q n _ B hB v σ w hvB hσB hv hσ hvσ hvw hσw
  obtain ⟨U, hwU, z, J, wf, uf, hc⟩ := GlobalTheory.T.exists_snc_chart ℂ Y q n B hB w
  obtain ⟨j', hj'J, rfl⟩ := (hc.mem v hvw hv).1 hvB
  obtain ⟨j, hjJ, rfl⟩ := (hc.mem σ hσw hσ).1 hσB
  have hjj : j ≠ j' := fun h => hvσ (by rw [h])
  haveI : IsRegularLocalRing (Y.presheaf.stalk w) := (hB w).1
  have hUmem : ∀ y : Y, y ⤳ w → y ∈ U := fun y hy => hy.mem_open U.isOpen hwU
  have hgerm : ∀ (y : Y) (hy : y ⤳ w) (i : Fin n),
      (Y.presheaf.stalkSpecializes hy).hom (Y.presheaf.germ U w hwU (z i)) =
        Y.presheaf.germ U y (hUmem y hy) (z i) := fun y hy i => by
    rw [← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hwU hy]; rfl
  have hfn : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J →
      algebraMap (Y.presheaf.stalk y) Y.functionField (Y.presheaf.germ U y hy (z i)) =
        (uf i : Y.functionField) := fun y hy i hi => by
    rw [GlobalTheory.Cartier.algebraMap_germ hy, hc.val i hi]
  have hgne : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J → Y.presheaf.germ U y hy (z i) ≠ 0 :=
    fun y hy i hi h0 => (uf i).ne_zero (by rw [← hfn y hy i hi, h0, map_zero])
  have hmy : ∀ i (hi : i ∈ J), Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i) ∈
      maximalIdeal (Y.presheaf.stalk (wf i)) := by
    intro i hi
    by_contra hnm
    have hu : IsUnit (Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i)) := by
      by_contra h'; exact hnm ((mem_maximalIdeal _).2 h')
    have h1 := GlobalTheory.SncMeet.ord_algebraMap_of_isUnit _ _ hu
    rw [hfn _ _ i hi, hc.ord_self i hi] at h1
    exact one_ne_zero h1
  have hm : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ maximalIdeal (Y.presheaf.stalk w) := by
    intro i hi
    by_contra hnm
    have hu : IsUnit (Y.presheaf.germ U w hwU (z i)) := by
      by_contra h'; exact hnm ((mem_maximalIdeal _).2 h')
    have hu' := hu.map (Y.presheaf.stalkSpecializes (hc.spec i hi)).hom
    rw [hgerm] at hu'
    exact (mem_maximalIdeal _).1 (hmy i hi) hu'
  have hli := GlobalTheory.T.linearIndependent_cotangent_of_isTopFormFrame_of_vanishing Y q n U z hc.frame w hwU J (fun i => hm i.1 i.2)

  have hi2 : Function.Injective (![⟨j, hjJ⟩, ⟨j', hj'J⟩] : Fin 2 → J) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact (hjj (by simpa using congrArg Subtype.val hkl)).elim
    · exact (hjj (by simpa using (congrArg Subtype.val hkl).symm)).elim
    · rfl
  have hli2 := hli.comp _ hi2
  obtain ⟨hPp, hPh⟩ := GlobalTheory.T.span_pair_isPrime_height_two_of_cotangent_independent (Y.presheaf.stalk w) (Y.presheaf.germ U w hwU (z j))
    (Y.presheaf.germ U w hwU (z j')) (hm j hjJ) (hm j' hj'J) (by
      convert hli2 using 1
      funext k; fin_cases k <;> rfl)
  let pt : PrimeSpectrum (Y.presheaf.stalk w) :=
    ⟨Ideal.span {Y.presheaf.germ U w hwU (z j), Y.presheaf.germ U w hwU (z j')}, hPp⟩
  obtain ⟨hw', e, he⟩ := GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pt
  have K1 : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal →
      wf i ⤳ Y.fromSpecStalk w pt := by
    intro i hi hiP
    obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem _).2 hiP)
    have hQp : Q.IsPrime := hQmin.1.1
    have hbQ : Y.presheaf.germ U w hwU (z i) ∈ Q := hQmin.1.2 (Ideal.mem_span_singleton_self _)
    have hQh1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQmin
    have hQ0 : Q ≠ ⊥ := fun h => hgne w hwU i hi (by rw [h] at hbQ; exact Ideal.mem_bot.1 hbQ)
    have hQh : Q.height = 1 := by
      refine le_antisymm hQh1 ?_
      rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hQ0
    let pQ : PrimeSpectrum (Y.presheaf.stalk w) := ⟨Q, hQp⟩
    obtain ⟨hQw, -, -⟩ := GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pQ
    have hcoh : Order.coheight (Y.fromSpecStalk w pQ) = 1 := by
      rw [GlobalTheory.SncMeet.coheight_fromSpecStalk]; exact_mod_cast hQh
    have hsp : Y.fromSpecStalk w pQ ⤳ Y.fromSpecStalk w pt :=
      ((PrimeSpectrum.le_iff_specializes pQ pt).1 hQle).map (Y.fromSpecStalk w).continuous
    have hmem : Y.presheaf.germ U _ (hUmem _ hQw) (z i) ∈
        maximalIdeal (Y.presheaf.stalk (Y.fromSpecStalk w pQ)) := by
      rw [← hgerm _ hQw i]; exact (GlobalTheory.SncMeet.mem_asIdeal_iff Y w pQ _ hQw rfl _).1 hbQ
    have hord := GlobalTheory.SncMeet.ord_algebraMap_ne_zero _ hcoh _ (hgne _ _ i hi) hmem
    rw [hfn _ _ i hi] at hord
    have heq : Y.fromSpecStalk w pQ = wf i := by
      by_contra hne; exact hord (hc.ord_other i hi _ hQw hne)
    rw [← heq]; exact hsp
  have hPh' : pt.asIdeal.height = 2 := hPh
  have ht : ∀ g, (Y.presheaf.stalkSpecializes hw').hom g =
      e.symm (algebraMap _ (Localization.AtPrime pt.asIdeal) g) := fun g => by
    rw [← he g, RingEquiv.symm_apply_apply]
  refine ⟨Y.fromSpecStalk w pt, (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)),
    (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j')), hw',
    K1 j' hj'J (Ideal.subset_span (by simp)), K1 j hjJ (Ideal.subset_span (by simp)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv e,
      IsLocalization.AtPrime.ringKrullDim_eq_height pt.asIdeal, hPh']
    rfl
  · have h1 : Ideal.span {(Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)),
        (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j'))} =
        Ideal.map e.symm (Ideal.map (algebraMap _ (Localization.AtPrime pt.asIdeal)) pt.asIdeal) := by
      rw [ht, ht]
      show _ = Ideal.map e.symm (Ideal.map _ (Ideal.span _))
      simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rw [h1, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.symm)
  · rw [hgerm _ hw' j, hfn _ _ j hjJ]; exact hc.ord_self j hjJ
  · rw [hgerm _ hw' j', hfn _ _ j' hj'J]; exact hc.ord_self j' hj'J
  · intro v' hv'B hv'1 hv'w'
    have hv'w := hv'w'.trans hw'
    obtain ⟨i, hi, rfl⟩ := (hc.mem v' hv'w hv'1).1 hv'B
    by_contra hcon
    rw [not_or] at hcon
    have hij' : i ≠ j' := fun h => hcon.1 (by rw [h])
    have hij : i ≠ j := fun h => hcon.2 (by rw [h])
    obtain ⟨pi, hpi⟩ : wf i ∈ Set.range (Y.fromSpecStalk w) := by
      rw [Scheme.range_fromSpecStalk]; exact hv'w
    have hle : pi.asIdeal ≤ pt.asIdeal := by
      have h1 : Y.fromSpecStalk w pi ⤳ Y.fromSpecStalk w pt := hpi ▸ hv'w'
      exact (PrimeSpectrum.le_iff_specializes pi pt).2
        ((IsPreimmersion.isEmbedding (Y.fromSpecStalk w)).specializes_iff.1 h1)
    have hciP : Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal := by
      apply hle
      rw [GlobalTheory.SncMeet.mem_asIdeal_iff Y w pi (wf i) (hc.spec i hi) hpi, hgerm]
      exact hmy i hi
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 hciP
    refine hli.notMem_span_image (s := {⟨j, hjJ⟩, ⟨j', hj'J⟩}) (x := ⟨i, hi⟩) ?_ ?_
    · simp [Subtype.ext_iff, hij, hij']
    · have hsum : (⟨Y.presheaf.germ U w hwU (z i), hm i hi⟩ : maximalIdeal (Y.presheaf.stalk w)) =
          r • ⟨Y.presheaf.germ U w hwU (z j), hm j hjJ⟩ +
            s • ⟨Y.presheaf.germ U w hwU (z j'), hm j' hj'J⟩ := by
        ext; simp [← hrs, smul_eq_mul]
      show (maximalIdeal _).toCotangent ⟨_, _⟩ ∈ _
      rw [hsum, map_add, map_smul, map_smul]
      exact Submodule.add_mem _
        (Submodule.smul_of_tower_mem _ r (Submodule.subset_span ⟨⟨j, hjJ⟩, by simp, rfl⟩))
        (Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨⟨j', hj'J⟩, by simp, rfl⟩))

end GlobalTheory.SncMeet
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.AdjUp

theorem regAt_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    (z : Y) {f : X.functionField} (h : RegAt (s z) f) : RegAt z (functionFieldMap s f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨s.stalkMap z a, (functionFieldMap_algebraMap s z a).symm⟩

theorem scheme_ord_zero {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    Scheme.ord (0 : Y.functionField) z = 0 := by
  unfold Scheme.ord
  split_ifs <;> simp

theorem place_ord_eq {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {q : Y ⟶ Sp k} {E : DivOver q} {z : Y} (h : E.IsAt z) (f : Y.functionField) :
    (placeEquiv q E).ord f = Scheme.ord f z := by
  by_cases hf : f = 0
  · subst hf
    rw [scheme_ord_zero]
    simp [Place.ord]
  · exact h.ord_eq (Units.mk0 f hf)

theorem ring_eq_of_isAt {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}
    {E F : DivOver q} {z : Y} (hE : E.IsAt z) (hF : F.IsAt z) :
    (placeEquiv q E).ring = (placeEquiv q F).ring :=
  SetLike.ext fun f => (hE f).trans (hF f).symm

def stalkEquiv {Y : Scheme.{0}} [IsIntegral Y] (w : Y) : Y.presheaf.stalk w ≃+* locRing w :=
  RingEquiv.ofBijective (algebraMap (Y.presheaf.stalk w) Y.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ Y.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩

theorem stalkEquiv_apply {Y : Scheme.{0}} [IsIntegral Y] (w : Y) (a : Y.presheaf.stalk w) :
    ((stalkEquiv w a : locRing w) : Y.functionField) = algebraMap _ Y.functionField a := rfl

theorem map_maximalIdeal_equiv {R R' : Type*} [CommRing R] [CommRing R'] [IsLocalRing R]
    [IsLocalRing R'] (φ : R ≃+* R') :
    (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal R' := by
  ext a
  rw [Ideal.mem_map_of_equiv, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩ h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb
    exact hb ((isUnit_map_iff φ b).1 h)
  · intro ha
    refine ⟨φ.symm a, ?_, by simp⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    exact ha (by simpa using h.map φ)

end GlobalTheory.FieldPair.AdjUp

open GlobalTheory.FieldPair.AdjUp in

theorem GlobalTheory.FieldPair.mult_lt_of_adjKlt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y) (S : DivOver p) (S' : DivOver (s ≫ p)), TrBasis (Cartier.constFn p) x → 0 < m → IsLogRes p n (dForm (Cartier.constFn p) x) m (CartierDiv.principal g) s K B → DivOver.Over s S' S → S'.IsAt σ → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m := by
  intro X _ _ p n _ _ x m g Y _ _ s _ K B y σ S S' hx hm hres hover hσ hmσ hadj v w hvσ hvw hσw hwy
  by_cases hv0 : (pullCart s (CartierDiv.principal g) - m • K).mult v ≤ 0
  · exact lt_of_le_of_lt hv0 (by exact_mod_cast hm)
  have hv0' : (pullCart s (CartierDiv.principal g) - m • K).mult v ≠ 0 := by omega
  haveI := hres.smooth
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := Discrepancy.CanonIso.isNormalScheme_of_smooth' (s ≫ p)
  have hmσ0 : (pullCart s (CartierDiv.principal g) - m • K).mult σ ≠ 0 := by
    rw [hmσ]; exact_mod_cast hm.ne'
  have hvB : v ∈ B := hres.supp (CartierDiv.mem_supp_of_mult_ne_zero hv0')
  have hσB : σ ∈ B := hres.supp (CartierDiv.mem_supp_of_mult_ne_zero hmσ0)
  have hv1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hv0'
  have hσ1 := hσ.coheight_eq_one
  obtain ⟨w', t, u, hw'w, hvw', hσw', hdim, hspan, htσ, huv, hB⟩ :=
    GlobalTheory.SncMeet.exists_meet_point Y (s ≫ p) n B hres.snc v σ w hvB hσB hv1 hσ1 hvσ hvw hσw
  obtain ⟨Ev, hEv⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hv1
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap s) hres.bir
  have hc : ∀ a, e (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a := fun a =>
    RingHom.congr_fun (EtaleKlt.functionFieldMap_comp_constFn p s) a
  have hadj' := GlobalTheory.FieldPair.adjKlt_ringEquiv (Cartier.constFn p) (Cartier.constFn (s ≫ p)) e hc n x (locRing y)
    (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) (placeEquiv p S) (placeEquiv (s ≫ p) S') hx
    (fun a => (hover a).symm) hadj
  rw [Finsupp.mapDomain_single] at hadj'
  have hη : dForm (Cartier.constFn (s ≫ p)) (e ∘ x) =
      EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) := by
    rw [EtaleKlt.ratPull, formMap_dForm]
    rfl
  have hη0 : EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) ≠ 0 := fun h0 =>
    hadj.form_ne_zero ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hres.bir n).1
      (h0.trans (map_zero _).symm))
  rw [hη] at hadj'
  unfold AdjKlt at hadj'
  have hdisc : ∀ (P : DivOver (s ≫ p)) (z : Y), P.IsAt z →
      (placeEquiv (s ≫ p) P).disc (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x))
        (Finsupp.single (e g) (1 / (m : ℚ))) =
        -((pullCart s (CartierDiv.principal g) - m • K).mult z : ℚ) / m := by
    intro P z hP
    have h1 := disc_placeEquiv P (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x)) m (fnPull s g)
    exact h1.trans (discrep_isAt_eq_neg_mult ℂ Y (s ≫ p) n _ hη0 K _ m hm hres.div P z (fnPull s g) hP
      (isEqn_pullCart s (CartierDiv.isEqn_principal g (s z))))
  have hTQ : (locRing y).map e.toRingHom ≤ locRing w' := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : s w' ⤳ y := (hw'w.map s.continuous).trans hwy
    exact regAt_map s w' (regAt_of_specializes h1 ha)
  have hQ := isLocModel_locRing (p := s ≫ p) w'
  have key := hadj'.2.2 (locRing w') hQ (stalkEquiv w' t) (stalkEquiv w' u) (placeEquiv (s ≫ p) Ev) hTQ
    ?_ ?_ ((isPrimeOf_placeEquiv S' w').2 ⟨σ, hσw', hσ⟩) ((isPrimeOf_placeEquiv Ev w').2 ⟨v, hvw', hEv⟩)
    (by rw [stalkEquiv_apply, place_ord_eq hσ]; exact htσ)
    (by rw [stalkEquiv_apply, place_ord_eq hEv]; exact huv) ?_
  · rw [hdisc Ev v hEv] at key
    have hm' : (0 : ℚ) < m := by exact_mod_cast hm
    rw [lt_div_iff₀ hm'] at key
    have : ((pullCart s (CartierDiv.principal g) - m • K).mult v : ℚ) < m := by linarith
    exact_mod_cast this
  · have h1 : Ideal.span {stalkEquiv w' t, stalkEquiv w' u} = (Ideal.span {t, u}).map (stalkEquiv w') := by
      rw [Ideal.map_span]; simp [Set.image_insert_eq]
    rw [h1, hspan]
    haveI := hQ.isLocalRing
    exact map_maximalIdeal_equiv _
  · exact (ringKrullDim_eq_of_ringEquiv (stalkEquiv w')).symm.trans hdim
  · intro P hP h1 h2
    obtain ⟨P₀, rfl⟩ := (placeEquiv (s ≫ p)).surjective P
    obtain ⟨z, hzw', hz⟩ := (isPrimeOf_placeEquiv P₀ w').1 hP
    rw [hdisc P₀ z hz]
    have hz1 := hz.coheight_eq_one
    have hzσ : z ≠ σ := by rintro rfl; exact h1 (ring_eq_of_isAt hz hσ)
    have hzv : z ≠ v := by rintro rfl; exact h2 (ring_eq_of_isAt hz hEv)
    have hzB : z ∉ B := fun hzB => (hB z hzB hz1 hzw').elim hzv hzσ
    have h0 : (pullCart s (CartierDiv.principal g) - m • K).mult z = 0 := by
      by_contra h0
      exact hzB (hres.supp (CartierDiv.mem_supp_of_mult_ne_zero h0))
    rw [h0]
    simp
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_residue_dominant_cartier : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y) (S : DivOver p) (S' : DivOver (s ≫ p)), TrBasis (Cartier.constFn p) x → 0 < m → IsLogRes p n (dForm (Cartier.constFn p) x) m (CartierDiv.principal g) s K B → DivOver.Over s S' S → S'.IsAt σ → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m := by
  atlas_forward_decl GlobalTheory.FieldPair.mult_lt_of_adjKlt
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.CoeffPlaces

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem supp_neg_le' (D : CartierDiv Z) : (-D).supp ≤ D.supp := fun x hx h =>
  hx (by simpa using h.neg)

theorem supp_nsmul_le' (D : CartierDiv Z) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

variable [IsLocallyNoetherian Z]

theorem mult_zero'' (z : Z) : (0 : CartierDiv Z).mult z = 0 := by
  have h₀ := CartierDiv.mult_add (0 : CartierDiv Z) 0 z
  rw [add_zero] at h₀
  omega

theorem mult_nsmul''' (E : CartierDiv Z) (r : ℕ) (z : Z) : (r • E).mult z = r * E.mult z := by
  induction r with
  | zero => rw [zero_nsmul, mult_zero'']; simp
  | succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem mult_sub'' (D E : CartierDiv Z) (z : Z) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  omega

theorem ord_nonneg_of_regAt' {f : Z.functionField} {z : Z} (hf : RegAt z f) (h0 : f ≠ 0) :
    0 ≤ Scheme.ord f z := by
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, rfl⟩ := hf
    have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
    rw [ord_algebraMap hz ha]
    exact Nat.cast_nonneg _
  · exact (Scheme.ord_eq_zero_of_coheight_neq_one hz _).ge

theorem regAt_functionFieldMap' {X : Scheme.{0}} [IsIntegral X] (q : Z ⟶ X) [IsDominant q] (y : Z)
    {f : X.functionField} (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

end GlobalTheory.Discrepancy.CoeffPlaces

open GlobalTheory.Discrepancy.CoeffPlaces in

theorem GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (g f : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y), η ≠ 0 → 0 < m → IsLogRes p n η m (CartierDiv.principal g) s K B → (∀ y', s y' ∈ (CartierDiv.principal f).supp → y' ∈ B) → RegAt y (f : X.functionField) → Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → (∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m) → ∀ E : DivOver p, E.Through y → -1 < discrep E η m g + E.ord f := by
  intro X _ _ p n hproj _ η m g f Y _ _ s _ K B y σ hη hm hres hfB hfy hσ1 hσm hlt E hE
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p s hres.bir E
  obtain ⟨y', rfl, hE'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p s hres.bir inferInstance E' E hE'E _ hE
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  set F := pullCart s (CartierDiv.principal f) with hFdef
  set G := pullCart s (CartierDiv.principal g) with hGdef
  have hFsupp : F.supp ≤ B := fun v hv => hfB v ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y s _).1 v hv)
  have e : G - m • F - m • K = (G - m • K) + -(m • F) := by abel
  have hsupp : (G - m • F - m • K).supp ≤ B := by
    rw [e]
    exact (CartierDiv.supp_add_le _ _).trans
      (sup_le hres.supp ((supp_neg_le' _).trans ((supp_nsmul_le' _ _).trans hFsupp)))
  have hFm (w : Y) : F.mult w = Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal f (s w))).mult_eq
  have hEqn : (G - m • F).IsEqn y' (fnPull s g / fnPull s f ^ m) :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal g (s y'))).sub
      ((isEqn_pullCart s (CartierDiv.isEqn_principal f (s y'))).nsmul m)
  have hmul (w : Y) : (G - m • F - m • K).mult w = (G - m • K).mult w - m * F.mult w := by
    rw [mult_sub'', mult_sub'', mult_sub'', mult_nsmul''', mult_nsmul''']; ring
  have hlt' : ∀ w, w ⤳ y' → (G - m • F - m • K).mult w < m := by
    intro w hw
    rw [hmul, hFm]
    by_cases hwσ : w = σ
    · subst hwσ
      rw [hσm, hσ1]
      simp only [mul_one, sub_self]
      exact_mod_cast hm
    · have hsw : s w ⤳ s y' := hw.map s.continuous
      have h0 : 0 ≤ Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        ord_nonneg_of_regAt' (regAt_functionFieldMap' s w (regAt_of_specializes hsw hfy))
          (Units.ne_zero _)
      have h1 := hlt w hwσ hsw
      have h2 : (0 : ℤ) ≤ m * Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        mul_nonneg (Int.natCast_nonneg m) h0
      linarith
  have hcrit := (GlobalTheory.T.klt_of_snc_coefficients ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (G - m • F) m B hm
    hres.div hres.snc hsupp y' _ hEqn E' hE').1 hlt'
  have hd : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g / fnPull s f ^ m) =
      discrep E η m g + E.ord f := by
    simp only [discrep]
    rw [GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hres.bir E' E hE'E n η hη, div_eq_mul_inv (fnPull s g), E'.ord_mul, E'.ord_inv,
      E'.ord_pow, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E g,
      GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E f]
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    ring
  rw [← hd]
  exact hcrit
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrepancy_add_ord_gt_neg_one_log_resolution : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (g f : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y), η ≠ 0 → 0 < m → IsLogRes p n η m (CartierDiv.principal g) s K B → (∀ y', s y' ∈ (CartierDiv.principal f).supp → y' ∈ B) → RegAt y (f : X.functionField) → Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → (∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m) → ∀ E : DivOver p, E.Through y → -1 < discrep E η m g + E.ord f := by
  atlas_forward_decl GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory

theorem inversion_of_adjunction_proj : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g f : X.functionFieldˣ) (y : X) (S : DivOver p), TrBasis (Cartier.constFn p) x → 0 < m → IsIntegrallyClosed (X.presheaf.stalk y) → RegAt y (f : X.functionField) → (placeEquiv p S).IsPrimeOf (locRing y) → S.ord f = 1 → discrep S (dForm (Cartier.constFn p) x) m g = -1 → (∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing y) → discrep E (dForm (Cartier.constFn p) x) m g ≤ 0) → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ E : DivOver p, E.Through y → -1 < discrep E (dForm (Cartier.constFn p) x) m g + E.ord f := by
  intro hP X _ _ p n hproj hdim x m g f y S hx hm hnorm hreg hS hSf hdisc hE hadj E hEy
  have hη : (dForm (Cartier.constFn p) x : RatForms p n) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_dForm_of_trBasis _ hx).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨Y, hYi, hYn, s, hsd, K, B, hres, hB, hconn⟩ :=
    GlobalTheory.T.connectedness_lemma_at_normal_point_logResolution hP X p n hproj hdim (dForm (Cartier.constFn p) x) m (CartierDiv.principal g)
      (CartierDiv.principal f).supp hη hm (CartierDiv.supp_ne_top _)
  haveI := hYi; haveI := hYn; haveI := hsd
  obtain ⟨z, hzy, hSz⟩ := (isPrimeOf_placeEquiv S y).1 hS
  have hbir := hres.bir
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  obtain ⟨S', hS'⟩ := DivOver.exists_over ℂ X Y p s hbir S
  obtain ⟨σ, hσz, hS'σ⟩ := DivOver.isAt_lift ℂ X Y p s hbir inferInstance S' S hS' z hSz
  haveI := hres.smooth
  have hη' : EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) ≠ 0 := fun h0 =>
    hη ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hbir n).1
      (h0.trans (map_zero _).symm))
  have hd := discrep_isAt_eq_neg_mult ℂ Y (s ≫ p) n _ hη' K (pullCart s (CartierDiv.principal g)) m
    hm hres.div S' σ (fnPull s g) hS'σ
    (isEqn_pullCart s (hσz ▸ CartierDiv.isEqn_principal g z))
  have hdd : discrep S' (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x)) m (fnPull s g) =
      discrep S (dForm (Cartier.constFn p) x) m g := by
    simp only [discrep]
    rw [BirOrd.formOrd_ratPull_of_over ℂ X Y p s hbir S' S hS' n _ hη,
      DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbir S' S hS' g]
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmult : (pullCart s (CartierDiv.principal g) - m • K).mult σ = m := by
    rw [hdd, hdisc] at hd
    have : ((pullCart s (CartierDiv.principal g) - m • K).mult σ : ℚ) = m := by
      field_simp at hd
      linarith
    exact_mod_cast this
  have hsσ : s σ ⤳ y := hσz ▸ hzy
  have heff : ∀ z', z' ⤳ y → ∀ E' : DivOver p, E'.IsAt z' → ∀ g',
      (CartierDiv.principal g).IsEqn z' g' →
      discrep E' (dForm (Cartier.constFn p) x) m g' ≤ 0 := by
    intro z' hz' E' hE' g' hg'
    have h1 := hE E' ((isPrimeOf_placeEquiv E' y).2 ⟨z', hz', hE'⟩)
    have h2 : E'.ord g' = E'.ord g := by
      rw [hE'.ord_eq, hE'.ord_eq, ← hg'.mult_eq, (CartierDiv.isEqn_principal g z').mult_eq]
    simp only [discrep] at h1 ⊢
    rw [h2]
    exact h1
  have hnb := GlobalTheory.T.log_residue_dominant_cartier X p n hproj hdim x m g Y s K B y σ S S' hx hm hres hS' hS'σ hmult hadj
  have hlt := hconn y σ hnorm heff hmult hsσ hnb
  have hordσ : Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 := by
    rw [← hS'σ.ord_eq, DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbir S' S hS' f, hSf]
  exact GlobalTheory.T.discrepancy_add_ord_gt_neg_one_log_resolution X p n hproj hdim _ m g f Y s K B y σ hη hm hres hB hreg hordσ hmult hlt E hEy

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inversion_of_adjunction_proj_alt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g f : X.functionFieldˣ) (y : X) (S : DivOver p), TrBasis (Cartier.constFn p) x → 0 < m → IsIntegrallyClosed (X.presheaf.stalk y) → RegAt y (f : X.functionField) → (placeEquiv p S).IsPrimeOf (locRing y) → S.ord f = 1 → discrep S (dForm (Cartier.constFn p) x) m g = -1 → (∀ E : DivOver p, (placeEquiv p E).IsPrimeOf (locRing y) → discrep E (dForm (Cartier.constFn p) x) m g ≤ 0) → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ E : DivOver p, E.Through y → -1 < discrep E (dForm (Cartier.constFn p) x) m g + E.ord f := by
  atlas_forward_decl GlobalTheory.inversion_of_adjunction_proj
end
