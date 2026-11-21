import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

noncomputable section

namespace GlobalTheory.FlagZ.Univ

theorem colSpan_le_of_inv_mul {X : Scheme.{0}} {N : ℕ} {x : X} (g h : GL (Fin N) (X.presheaf.stalk x)) (l : ℕ)
    (H : ∀ i j : Fin N, (j : ℕ) < l → l ≤ (i : ℕ) → (g⁻¹ * h).1 i j = 0) :
    colSpan h.1 l ≤ colSpan g.1 l := by
  refine Submodule.span_le.2 ?_
  rintro v ⟨j, hj, rfl⟩
  set b := stalkStd X N x
  set c := (g⁻¹ * h).1 with hc
  have hh : h.1 = g.1 * c := by
    rw [hc, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have e : ∑ i, h.1 i j • b i = ∑ k, c k j • ∑ i, g.1 i k • b i := by
    simp_rw [Finset.smul_sum, smul_smul, hh, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  rw [e]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : (k : ℕ) < l
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · rw [H k j hj (not_lt.1 hk), zero_smul]
    exact Submodule.zero_mem _

theorem stalkStep_eq_colSpan : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : ℕ) (y : Fl ι N)
    (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y)),
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y →
      stalkStep ι N τ l y = colSpan (g τ).1 l := by
  intro ι _ N τ l y g hg
  have key : ∀ g h : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y),
      flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = flagPt Prod.fst Prod.snd h →
        colSpan (h τ).1 l ≤ colSpan (g τ).1 l := by
    intro g h e
    refine colSpan_le_of_inv_mul _ _ l fun i j hj hi => ?_
    have hlN : l < N + 1 := by omega
    exact (flagPt_eq_iff_below ι (ι × Fin (N + 1)) N Prod.fst Prod.snd _ g h).1 e τ i j
      ⟨(τ, ⟨l, hlN⟩), rfl, hj, hi⟩
  refine le_antisymm (iInf_le_of_le g (iInf_le _ hg)) (le_iInf fun h => le_iInf fun hh => ?_)
  exact key h g (hh.trans hg.symm)

end GlobalTheory.FlagZ.Univ
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_stalk_column_span : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : ℕ) (y : Fl ι N) (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y)), flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y → stalkStep ι N τ l y = colSpan (g τ).1 l := by
  first | exact @GlobalTheory.FlagZ.Univ.stalkStep_eq_colSpan | exact GlobalTheory.FlagZ.Univ.stalkStep_eq_colSpan | (intros; apply GlobalTheory.FlagZ.Univ.stalkStep_eq_colSpan <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

theorem flagPt_germ_cellGL_eq_fromSpecStalk (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (y : Fl ι N)
    (hy : y ∈ cellOpen ι N w) :
    flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (fun τ => Matrix.GeneralLinearGroup.map
      (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)) =
      (Fl ι N).fromSpecStalk y := by
  have hU : IsAffineOpen (cellOpen ι N w) :=
    (isAffineOpen_top (Sp (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).image_of_isOpenImmersion _
  have key : spMap (cellRing ι N w) ≫ cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w = hU.fromSpec := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) hU
      (isAffineOpen_top _) (Scheme.Hom.preimage_image_eq _ ⊤).ge
    have e₀ : ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).hom =
        (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appLE (cellOpen ι N w) ⊤
          (Scheme.Hom.preimage_image_eq _ ⊤).ge :=
      Scheme.Hom.appIso_hom' _ _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← e₀] at h
    have e : spMap (cellRing ι N w) = Spec.map ((cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w).appIso ⊤).inv ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of (CellRing (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd))).inv := by
      exact Spec.map_comp _ _
    rw [e]
    erw [Category.assoc, ← h]
    erw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  rw [← spMap_flagPt, ← cell, ← hU.fromSpecStalk_eq_fromSpecStalk hy, IsAffineOpen.fromSpecStalk, ← key]
  rw [spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

end GlobalTheory.FlagZ.Univ
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_flag_point_stalk : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (y : Fl ι N) (hy : y ∈ cellOpen ι N w), flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (fun τ => Matrix.GeneralLinearGroup.map (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)) = (Fl ι N).fromSpecStalk y := by
  first | exact @GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk | exact GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk | (intros; apply GlobalTheory.FlagZ.Univ.flagPt_germ_cellGL_eq_fromSpecStalk <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

theorem GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : ℕ) (y : Fl ι N) (hy : y ∈ cellOpen ι N w), colSpan (Matrix.GeneralLinearGroup.map (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)).1 l = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = (freeModule (Fl ι N) (Fin N)).presheaf.germ (cellOpen ι N w) y hy (cellCol ι N w τ j)} := by
  intro ι _ N w τ l y hy
  unfold colSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Matrix.GeneralLinearGroup.map_apply, cellCol, map_sum, GlobalTheory.QCoh.germ_smul,
    GlobalTheory.Twist.germ_resM, stalkStd, RingHom.comp_apply]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  refine Eq.congr_right (Finset.sum_congr rfl fun i _ => ?_)
  exact congrArg _ (VB.IsFrame.stalkBasis_apply _ _ _ _)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_flag_stalk_span : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : ℕ) (y : Fl ι N) (hy : y ∈ cellOpen ι N w), colSpan (Matrix.GeneralLinearGroup.map (((Fl ι N).presheaf.germ (cellOpen ι N w) y hy).hom.comp (cellRing ι N w)) (cellGL Prod.fst Prod.snd w τ)).1 l = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = (freeModule (Fl ι N) (Fin N)).presheaf.germ (cellOpen ι N w) y hy (cellCol ι N w τ j)} := by
  first | exact @GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL | exact GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL | (intros; apply GlobalTheory.FlagZ.Univ.colSpan_germ_cellGL <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_columns_frame : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι), VB.IsFrame (cellCol ι N w τ) := by
  first | exact @GlobalTheory.FlagZ.Univ.isFrame_cellCol | exact GlobalTheory.FlagZ.Univ.isFrame_cellCol | (intros; apply GlobalTheory.FlagZ.Univ.isFrame_cellCol <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.VB

theorem sum_smul_frame_mem_ofStalks_iff : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (S : ∀ x : X, Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) (l : ℕ), (∀ (y : X) (hy : y ∈ U), S y = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = F.presheaf.germ U y hy (c j)}) → ∀ {V : X.Opens} (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ (VB.Sub.ofStalks S).sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0 := by
  intro X F U N c hc S l hS V h a
  have hg : ∀ (y : X) (hy : y ∈ V), F.presheaf.germ V y hy (∑ j, a j • resM F h (c j)) =
      ∑ j, X.presheaf.germ V y hy (a j) • hc.stalkBasis y (h hy) j := by
    intro y hy
    simp only [map_sum, QCoh.germ_smul, Twist.germ_resM, IsFrame.stalkBasis_apply]
  have hset : ∀ (y : X) (hy : y ∈ U),
      {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = F.presheaf.germ U y hy (c j)} =
        hc.stalkBasis y hy '' {j : Fin N | (j : ℕ) < l} := by
    intro y hy
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image, IsFrame.stalkBasis_apply]
    exact ⟨fun ⟨j, h1, h2⟩ => ⟨j, h1, h2.symm⟩, fun ⟨j, h1, h2⟩ => ⟨j, h1, h2.symm⟩⟩
  change (∀ (y : X) (hy : y ∈ V), F.presheaf.germ V y hy (∑ j, a j • resM F h (c j)) ∈ S y) ↔ _
  constructor
  · intro H j hj
    refine TopCat.Presheaf.section_ext X.sheaf V _ _ fun y hy => ?_
    have H1 := H y hy
    rw [hg y hy, hS y (h hy), hset y (h hy), Module.Basis.mem_span_image] at H1
    have h0 : (hc.stalkBasis y (h hy)).repr
        (∑ j, X.presheaf.germ V y hy (a j) • hc.stalkBasis y (h hy) j) j = 0 := by
      by_contra hne
      have := H1 (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
      exact absurd this (not_lt.2 hj)
    rw [congrFun ((hc.stalkBasis y (h hy)).repr_sum_self _) j] at h0
    exact h0.trans (map_zero (X.presheaf.germ V y hy).hom).symm
  · intro H y hy
    rw [hg y hy, hS y (h hy), hset y (h hy)]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < l
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [H j (not_lt.1 hj), map_zero, zero_smul]
      exact Submodule.zero_mem _

end GlobalTheory.VB
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subbundle_frame_membership : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (S : ∀ x : X, Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) (l : ℕ), (∀ (y : X) (hy : y ∈ U), S y = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = F.presheaf.germ U y hy (c j)}) → ∀ {V : X.Opens} (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ (VB.Sub.ofStalks S).sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0 := by
  atlas_forward_decl GlobalTheory.VB.sum_smul_frame_mem_ofStalks_iff
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.VB

open GlobalTheory.QCoh (appLinear appLinear_apply)
open GlobalTheory.Twist (app_resM)

theorem sum_castLE_eq {M : Type*} [AddCommMonoid M] {N l : ℕ} (hl : l ≤ N) (g : Fin N → M)
    (hg : ∀ j : Fin N, l ≤ (j : ℕ) → g j = 0) :
    ∑ k : Fin l, g (Fin.castLE hl k) = ∑ j, g j :=
  Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _
    (fun j hj => hg j (by
      by_contra h
      exact hj ⟨⟨j, by omega⟩, rfl⟩)) fun _ => rfl

theorem exists_isFrame_sub_of_vanishing {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ}
    (P : VB.Sub F) (c : Fin N → Γ(F, U)) (hc : VB.IsFrame c) (l : ℕ) (hl : l ≤ N)
    (hP : ∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)),
      (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) :
    ∃ e : Fin l → Γ(P.toMod, U), VB.IsFrame e := by
  classical

  have hmem (k : Fin l) : c (Fin.castLE hl k) ∈ P.sec U := by
    have := (hP U le_rfl (Pi.single (Fin.castLE hl k) 1)).2 fun j hj => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      simp at hj
      omega
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using this
  let e : Fin l → Γ(P.toMod, U) := fun k => P.mkSec _ (hmem k)

  have hincl (V : X.Opens) (h : V ≤ U) (b : Fin l → Γ(X, V)) :
      P.incl.app V (Fintype.linearCombination Γ(X, V) (fun k => resM P.toMod h (e k)) b) =
        ∑ k, b k • resM F h (c (Fin.castLE hl k)) := by
    rw [Fintype.linearCombination_apply, ← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, appLinear_apply, app_resM]
    rfl

  let ext (V : X.Opens) (b : Fin l → Γ(X, V)) : Fin N → Γ(X, V) :=
    fun j => if hj : (j : ℕ) < l then b ⟨j, hj⟩ else 0
  have hext0 (V : X.Opens) (b : Fin l → Γ(X, V)) (j : Fin N) (hj : l ≤ (j : ℕ)) : ext V b j = 0 :=
    dif_neg (by omega)
  have hextk (V : X.Opens) (b : Fin l → Γ(X, V)) (k : Fin l) : ext V b (Fin.castLE hl k) = b k :=
    dif_pos k.2
  have hsum (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V))
      (ha : ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) :
      ∑ k : Fin l, a (Fin.castLE hl k) • resM F h (c (Fin.castLE hl k)) =
        ∑ j, a j • resM F h (c j) :=
    sum_castLE_eq hl (fun j => a j • resM F h (c j)) fun j hj => by rw [ha j hj, zero_smul]
  refine ⟨e, fun V h => ⟨fun b b' hbb => ?_, fun s => ?_⟩⟩
  · have h1 := congrArg (P.incl.app V) hbb
    rw [hincl, hincl] at h1
    have h2 : Fintype.linearCombination Γ(X, V) (fun j => resM F h (c j)) (ext V b) =
        Fintype.linearCombination Γ(X, V) (fun j => resM F h (c j)) (ext V b') := by
      rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply,
        ← hsum V h _ (hext0 V b), ← hsum V h _ (hext0 V b')]
      simpa only [hextk] using h1
    funext k
    rw [← hextk V b k, ← hextk V b' k, (hc V h).1 h2]
  · obtain ⟨a, ha⟩ := (hc V h).2 (P.incl.app V s)
    rw [Fintype.linearCombination_apply] at ha
    have hz := (hP V h a).1 (ha ▸ P.incl_app_mem s)
    refine ⟨fun k => a (Fin.castLE hl k), P.incl_app_injective V ?_⟩
    rw [hincl, hsum V h a hz, ha]

end GlobalTheory.VB
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subbundle_frame_exists : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (P : VB.Sub F) (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (l : ℕ), l ≤ N → (∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) → ∃ e : Fin l → Γ(P.toMod, U), VB.IsFrame e := by
  atlas_forward_decl GlobalTheory.VB.exists_isFrame_sub_of_vanishing
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.LB (exists_fun_of_cover)

namespace GlobalTheory.VB.CokerFrame

variable {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]

theorem isFrame_of_injective_of_local {e : ι → Γ(F, U)}
    (inj : ∀ (V : X.Opens) (h : V ≤ U),
      Function.Injective (Fintype.linearCombination Γ(X, V) fun i => resM F h (e i)))
    (loc : ∀ (V : X.Opens) (h : V ≤ U) (s : Γ(F, V)) (x : X), x ∈ V →
      ∃ (W : X.Opens) (h' : W ≤ V), x ∈ W ∧ ∃ a : ι → Γ(X, W),
        Fintype.linearCombination Γ(X, W) (fun i => resM F (h'.trans h) (e i)) a = resM F h' s) :
    VB.IsFrame e := by
  refine fun V h => ⟨inj V h, fun s => ?_⟩
  choose W hW hx a ha using fun x : V => loc V h s x x.2
  have hc : V ≤ iSup W := fun x hxV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
  have key (x y : V) : (fun i => resG X (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) =
      fun i => resG X (inf_le_right : W x ⊓ W y ≤ W y) (a y i) := by
    apply inj _ (inf_le_left.trans ((hW x).trans h))
    rw [← VB.resM_linearCombination e ((hW x).trans h), ← VB.resM_linearCombination e ((hW y).trans h),
      ha, ha, resM_resM, resM_resM]
  choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i)
    fun x y => congrFun (key x y) i
  refine ⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩
  rw [VB.resM_linearCombination, ← ha x]
  exact congrArg _ (funext fun i => hb' i x)

theorem sum_eq_sum_last {M : Type*} [AddCommMonoid M] {N l : ℕ} (hl : l ≤ N) (g : Fin N → M)
    (hg : ∀ j : Fin N, (j : ℕ) < l → g j = 0) :
    ∑ j, g j = ∑ k : Fin (N - l), g ⟨l + k, by omega⟩ := by
  symm
  refine Finset.sum_of_injOn (fun k : Fin (N - l) => (⟨l + k, by omega⟩ : Fin N))
    (fun a _ b _ hab => ?_) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun j _ hj => ?_)
    (fun _ _ => rfl)
  · have := congrArg Fin.val hab
    simp only at this
    exact Fin.ext (by omega)
  · refine hg j (Nat.lt_of_not_le fun hlj => hj ⟨⟨j - l, by omega⟩, by simp, Fin.ext ?_⟩)
    simp only
    omega

end GlobalTheory.VB.CokerFrame

open GlobalTheory.VB.CokerFrame in

theorem GlobalTheory.VB.exists_isFrame_cokernel_of_frame :
    ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (P : VB.Sub F) (c : Fin N → Γ(F, U)),
      VB.IsFrame c → ∀ (l : ℕ), l ≤ N →
      (∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)),
        (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) →
      ∃ e : Fin (N - l) → Γ(cokernel P.incl, U), VB.IsFrame e := by
  intro X F U N P c hc l hl hP
  set π := cokernel.π P.incl

  have hlow (V : X.Opens) (h : V ≤ U) (j : Fin N) (hj : (j : ℕ) < l) :
      π.app V (resM F h (c j)) = 0 := by
    classical
    rw [VB.Sub.cokernel_π_app_eq_zero_iff]
    have := (hP V h (Pi.single j 1)).2 fun j' hj' => by
      rw [Pi.single_apply, if_neg (fun e => by subst e; omega)]
    simpa [Pi.single_apply] using this
  refine ⟨fun k => π.app U (c ⟨l + k, by omega⟩), isFrame_of_injective_of_local ?_ ?_⟩
  · intro V h
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    classical
    let b : Fin N → Γ(X, V) := fun j => if hj : l ≤ (j : ℕ) then a ⟨j - l, by omega⟩ else 0
    have hsum : (∑ j, b j • resM F h (c j)) =
        ∑ k : Fin (N - l), a k • resM F h (c ⟨l + k, by omega⟩) := by
      rw [sum_eq_sum_last hl]
      · refine Finset.sum_congr rfl fun k _ => ?_
        simp only [b, dif_pos (Nat.le_add_right l k)]
        congr 2
        ext
        simp
      · intro j hj
        simp only [b, dif_neg (by omega : ¬ l ≤ (j : ℕ)), zero_smul]
    have hmem : (∑ j, b j • resM F h (c j)) ∈ P.sec V := by
      rw [hsum, ← VB.Sub.cokernel_π_app_eq_zero_iff]
      rw [Fintype.linearCombination_apply] at ha
      rw [map_sum]
      simpa only [Scheme.Modules.Hom.app_smul, app_resM] using ha
    have hb := (hP V h b).1 hmem
    funext k
    have := hb ⟨l + k, by omega⟩ (Nat.le_add_right l k)
    simpa [b] using this
  · intro V h t x hx
    obtain ⟨W, h', hxW, s, hs⟩ := VB.exists_app_eq_of_epi π t hx
    obtain ⟨β, hβ⟩ := (hc W (h'.trans h)).2 s
    refine ⟨W, h', hxW, fun k => β ⟨l + k, by omega⟩, ?_⟩
    rw [← hs, ← hβ, Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum,
      sum_eq_sum_last hl]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Scheme.Modules.Hom.app_smul, app_resM]
    · intro j hj
      rw [Scheme.Modules.Hom.app_smul, hlow W (h'.trans h) j hj, smul_zero]
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_bundle_frame_exists : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (P : VB.Sub F) (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (l : ℕ), l ≤ N → (∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) → ∃ e : Fin (N - l) → Γ(cokernel P.incl, U), VB.IsFrame e := by
  first | exact @GlobalTheory.VB.exists_isFrame_cokernel_of_frame | exact GlobalTheory.VB.exists_isFrame_cokernel_of_frame | (intros; apply GlobalTheory.VB.exists_isFrame_cokernel_of_frame <;> assumption)
end

section
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.FlagZ.Univ

theorem exists_mem_cellOpen (ι : Type) [Fintype ι] (N : ℕ) (y : Fl ι N) :
    ∃ w : ι → Equiv.Perm (Fin N), y ∈ cellOpen ι N w := by
  obtain ⟨w, hw⟩ := GlobalTheory.FlagZ.exists_mem_range_cell ι (ι × Fin (N + 1)) N Prod.fst Prod.snd y
  exact ⟨w, (mem_cellOpen ι N).2 hw⟩

theorem mem_sub_iff_cellCol (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : ℕ) (w : ι → Equiv.Perm (Fin N))
    (V : (Fl ι N).Opens) (h : V ≤ cellOpen ι N w) (a : Fin N → Γ(Fl ι N, V)) :
    (∑ j, a j • resM _ h (cellCol ι N w τ j)) ∈ (sub ι N τ l).sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0 :=
  GlobalTheory.T.subbundle_frame_membership _ (GlobalTheory.T.cell_columns_frame ι N w τ) _ _
    (fun y hy => (GlobalTheory.T.flag_stalk_column_span ι N τ l y _ (GlobalTheory.T.cell_flag_point_stalk ι N w y hy)).trans (GlobalTheory.T.cell_flag_stalk_span ι N w τ l y hy)) h a

theorem isVB_F_and_isSubbundle_incl : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (i : Fin (N + 1)),
    VB.IsVB (F ι N τ i) i ∧ VB.IsSubbundle (incl ι N τ i) := by
  intro ι _ N τ i
  refine ⟨fun y => ?_, ⟨?_, N - i, ?_⟩⟩
  · obtain ⟨w, hw⟩ := exists_mem_cellOpen ι N y
    obtain ⟨e, he⟩ := GlobalTheory.T.subbundle_frame_exists (sub ι N τ i) _ (GlobalTheory.T.cell_columns_frame ι N w τ) i i.is_le
      (mem_sub_iff_cellCol ι N τ i w)
    exact ⟨_, e, hw, he⟩
  · exact @mono_comp _ _ _ _ _ _ (VB.Sub.mono_incl _) _ inferInstance
  · refine (show VB.IsVB (cokernel (sub ι N τ i).incl) (N - i) from fun y => ?_).of_iso
      (cokernelCompIsIso _ _).symm
    obtain ⟨w, hw⟩ := exists_mem_cellOpen ι N y
    obtain ⟨e, he⟩ := GlobalTheory.T.quotient_bundle_frame_exists (sub ι N τ i) _ (GlobalTheory.T.cell_columns_frame ι N w τ) i i.is_le
      (mem_sub_iff_cellCol ι N τ i w)
    exact ⟨_, e, hw, he⟩

end GlobalTheory.FlagZ.Univ
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_subbundle_rank : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (i : Fin (N + 1)), VB.IsVB (F ι N τ i) i ∧ VB.IsSubbundle (incl ι N τ i) := by
  atlas_forward_decl GlobalTheory.FlagZ.Univ.isVB_F_and_isSubbundle_incl
end
