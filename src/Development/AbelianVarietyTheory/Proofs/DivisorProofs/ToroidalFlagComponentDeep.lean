import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChoiceFreeSectionConstructionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerate
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadyDataMulStableMulBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false
noncomputable section
open GlobalTheory.Vanishing.H0 GlobalTheory.CompHS

namespace GlobalTheory.HSApp

theorem modif_generic_map {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) [IrreducibleSpace M.X] (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ) :
    genericPoint M.X ∈ M.opn ∧ M.σ (genericPoint M.X) = η := by
  have := M.iso
  have hne : (M.opn : Set M.X).Nonempty := M.dense.nonempty
  have hm : genericPoint M.X ∈ M.opn :=
    ((genericPoint_spec M.X).mem_open_set_iff M.opn.isOpen).2 (by simpa using hne)
  refine ⟨hm, ?_⟩
  obtain ⟨x, hx⟩ := (M.σ ∣_ U).surjective ⟨η, hη⟩
  have hx' : M.σ x.1 = η := (morphismRestrict_base_coe M.σ U x).symm.trans (congrArg Subtype.val hx)
  have hcl : η ∈ closure {M.σ (genericPoint M.X)} := by
    rw [← hx', ← Set.image_singleton]
    exact image_closure_subset_closure_image M.σ.continuous
      ⟨x.1, by rw [(genericPoint_spec M.X).def]; trivial, rfl⟩
  have hgen : IsGenericPoint (M.σ (genericPoint M.X)) Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hcl) isClosed_closure
  exact hgen.eq hg

theorem modif_residueFieldMap_surjective {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) (z : M.X) (hz : z ∈ M.opn) : Function.Surjective (M.σ.residueFieldMap z).hom := by
  have := M.iso
  have : IsIso (M.σ.stalkMap z) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap M.σ U ⟨z, hz⟩)).1
      (((isIso_iff_isIso_stalkMap (M.σ ∣_ U)).1 M.iso).2 ⟨z, hz⟩)
  have hst : Function.Surjective (M.σ.stalkMap z).hom := (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨a, rfl⟩ := M.X.residue_surjective z y
  obtain ⟨b, rfl⟩ := hst a
  exact ⟨Y.residue _ b, congr($(Scheme.residue_residueFieldMap M.σ z).hom b)⟩

theorem modif_residueFieldMap_germ {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    (hnb : NoBase hB W U) (z : M.X) (hz : z ∈ M.opn) (i : B.ι) (hi : M.σ z ∈ B.U i) :
    ∃ c : M.X.residueField z, c ≠ 0 ∧ ∀ w : W,
      (M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (germ i (M.σ z) (memTop _) hi w.1)) =
        c * (M.sys Δ φ f abelian₂).toLinSys.val (Adelic.resPt z) (toSec (Δ.lift w)) := by
  set S := (M.sys Δ φ f abelian₂).toLinSys
  have hp : Adelic.ptOf (Adelic.resPt z) = z := Adelic.ptOf_resPt z
  have hj : z ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z))) :=
    (congrArg (fun y => y ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z)))) hp).mp
      (S.mem_chartAt (Adelic.ptOf (Adelic.resPt z)))
  set j := S.chartAt (Adelic.ptOf (Adelic.resPt z))
  have hi0 : M.σ z ∈ B.U (j.1 PUnit.unit) := mem_pull.1 hj.1
  have hu : IsUnit (ger z hj.2 (Δ.t.f j.2)) :=
    (isUnit_ger_iff _ hj.2).2 ((Δ.mem_nonzeroLocus z).2 (M.notMem_support hnb z (M.off_eq.ge hz)))
  refine ⟨(M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (tr B (M.σ z) i (j.1 PUnit.unit)).val) *
    (M.X.residue z).hom (ger z hj.2 (Δ.t.f j.2)), mul_ne_zero ?_ ?_, fun w => ?_⟩
  · exact (map_ne_zero _).2 (((tr B (M.σ z) i (j.1 PUnit.unit)).isUnit.map (Y.residue (M.σ z)).hom).ne_zero)
  · exact (hu.map (M.X.residue z).hom).ne_zero
  have hv : S.val (Adelic.resPt z) (toSec (Δ.lift w)) = (M.X.residue z).hom (germ j z (memTop z) hj (Δ.lift w)) := by
    rw [Adelic.LinSys.val, Adelic.projSys.valR_resPt z _ hj, ← ger_toSec]
    rfl
  rw [hv, germ_change i (j.1 PUnit.unit) (M.σ z) (memTop _) hi hi0, map_mul, map_mul, mul_assoc]
  congr 1
  rw [← map_mul (M.X.residue z).hom, Δ.germ_lift w j z hj]
  refine Eq.trans ?_ (congrArg (M.X.residue z).hom
    (GlobalTheory.Vanishing.H0.germ_pull (p := p) M.σ le_top j.1 z (memTop z) hj.1 w.1)).symm
  exact congr($(Scheme.residue_residueFieldMap M.σ z).hom _)

theorem sys_birational_of_ratField {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    [IsIntegral M.X] (hnb : NoBase hB W U) (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ)
    (hr : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) η hη = ⊤) :
    (M.sys Δ φ f abelian₂).toLinSys.Birational := by
  classical
  obtain ⟨hmem, hσ⟩ := modif_generic_map M η hη hg
  subst hσ
  set S := (M.sys Δ φ f abelian₂).toLinSys with hS
  set z := genericPoint M.X with hz
  have hsurj := modif_residueFieldMap_surjective M z hmem
  have hbpf : S.BasePointFree := Δ.iSup_nonzeroLocus (f.b.map φ).span_eq
  obtain ⟨j0, hj0⟩ := Function.ne_iff.1 (hbpf.coords_ne_zero (Adelic.resPt z))
  have key : ∀ w : W, S.val (Adelic.resPt z) (toSec (Δ.lift w)) / S.coords (Adelic.resPt z) j0 ∈
      S.ratioField (Adelic.resPt z) := fun w => by
    set u := f.b.equivFun (φ.symm w)
    have e : toSec (Δ.lift w) = S.comb u := by
      refine (bijective_ofSec_top (p := M.str)).1 ?_
      rw [ofSec_toSec]
      refine Eq.trans ?_ (M.ofSec_comb Δ φ f abelian₂ u).symm
      simp [u]
    rw [e, S.val_comb, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨j, j0, rfl⟩))
  have hgen : ∀ r ∈ {r | ∃ (i : B.ι) (hi : M.σ z ∈ B.U i) (s s' : H0 p B U),
      s ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      s' ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      r = (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s) / (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s')},
      (M.σ.residueFieldMap z).hom r ∈ S.ratioField (Adelic.resPt z) := by
    rintro r ⟨i, hi, _, _, ⟨w, rfl⟩, ⟨w', rfl⟩, rfl⟩
    obtain ⟨c, hc, hcw⟩ := modif_residueFieldMap_germ M Δ φ f abelian₂ hnb z hmem i hi
    rw [germ_restr, germ_restr, map_div₀, hcw, hcw, mul_div_mul_left _ _ hc,
      ← div_div_div_cancel_right₀ hj0]
    exact div_mem (key w) (key w')
  have hle : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) (M.σ z) hη ≤
      (S.ratioField (Adelic.resPt z)).comap (M.σ.residueFieldMap z).hom :=
    Subfield.closure_le.2 hgen
  refine ⟨z, genericPoint_spec M.X, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle (hr.symm ▸ Subfield.mem_top y)

theorem geo_second_birational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₂ → (h.geo f₁ f₂ th k).second.Birational := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hR
  obtain ⟨η, hη, hgen, hrat⟩ := hR
  have : IsIntegral R.X := (h.geo f₁ f₂ th k).isIntegral
  refine sys_birational_of_ratField R.toModif R.Δ₂ h.ext₂.equiv f₂ k.abelian₂ h.free₂ η hη hgen ?_
  convert hrat using 2
  ext s
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨h.ext₂.equiv.symm w, by rw [← h.ext₂.restr_equiv, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨h.ext₂.equiv g, h.ext₂.restr_equiv g⟩

end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.BirationalBig

theorem isNef_and_isBig : Quoted → ∀ (F : Type) [Field F] [NumberField F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → IsNef F S.L ∧ IsBig F S.L := by
  intro Q F _ _ S hV hb hB
  have hstr : strHom F S.Y = S.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom F S.Y) := hstr ▸ hV.proj
  have hnef : IsNef F S.L := IsGenerated.isNef_of_isProjOver ⟨S.N, S.b, hb⟩ hV.proj
  exact ⟨hnef, (Q.nef.2.2.isBig_iff hproj (GlobalTheory.ImageDegree.topologicalKrullDim_eq S hV) hnef).2
    (GlobalTheory.ImageDegree.degree_image_eq_topSelf Q F S hV hb hB).1⟩

end GlobalTheory.BirationalBig
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.HSApp.geoHyp_of_parts : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ Λ₀ : ℝ, WtBig P → RatGen TF.X Z Y.U P.u₁ → RatGen TF.X Z Y.U P.u₂ → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → 1 ≤ k.abelian₂ → (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ k.abelian₂) → 1 ≤ Λ₀ → (h.data f₁ f₂ th k).ShortFamily 0 Λ₀ → (h.data f₁ f₂ th k).ShortFamily (dimFlag (T.Q.Dw j)) k.LamD → (h.data f₁ f₂ th k).ShortFamily P.T k.LamT → GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ := by
  intro hPr hGD hQ hNad hPrin hSi hFa hLie D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k Λ₀ hW hR₁ hR₂ hB hL hLe h1 hS0 hSD hST
  have hNN := hQ.nef
  have hF := hG.geo
  have hA : IsNef Y.d.c₂.F (h.geo f₁ f₂ th k).LA ∧ IsBig Y.d.c₂.F (h.geo f₁ f₂ th k).LA := by
    apply GlobalTheory.T.choice_free_section_construction <;> assumption
  obtain ⟨hnef, hbig⟩ := hA
  have hbir := GlobalTheory.HSApp.birational_of_ratGen TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₁
  have hbir₂ := GlobalTheory.HSApp.geo_second_birational TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₂
  obtain ⟨hms, hmb⟩ := GlobalTheory.HSApp.ready_data_mulStable_mulBound hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have hnb₂ : IsNef Y.d.c₂.F (h.data f₁ f₂ th k).L₂ ∧ IsBig Y.d.c₂.F (h.data f₁ f₂ th k).L₂ :=
    GlobalTheory.BirationalBig.isNef_and_isBig hQ _ (h.geo f₁ f₂ th k).second.toLinSys
    (h.geo f₁ f₂ th k).alg₂.variety (h.geo f₁ f₂ th k).alg₂.bpf hbir₂
  have hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  obtain ⟨hD, hT, -, -, hLam, -, hLD, hLT, -⟩ := Ready.data_numbers h f₁ f₂ th k
  refine ⟨hTC, ?_, ?_, ?_, ?_, ?_, hms, hmb, ?_, ?_, h1, hS0, ?_, ?_⟩
  · exact hbir
  · exact hnef
  · exact hbig
  · exact hnb₂.1
  · exact hnb₂.2
  · intro q σ
    rw [hLam]
    exact hLe q σ
  · rw [hLam]; exact hL
  · rw [hD, hLD]; exact hSD
  · rw [hT, hLT]; exact hST
end
