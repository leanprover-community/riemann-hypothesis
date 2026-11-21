import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSuccessiveQuotientLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyRelativeDimDrop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortExactOfComposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagModelOfIsIsometry

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_relative_dim_drop : ∀ (k : Type) [CommRing k] (Y Y₁ : Scheme.{0}) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k) (ρ : Y ⟶ Y₁) (D : ℕ),
    ρ ≫ q₁ = p → IsArithVar p D → IsIntegral Y₁ → IsProjOver q₁ → Surjective ρ →
    topologicalKrullDim Y = topologicalKrullDim Y₁ + 1 → ∃ d₁ : ℕ, D = d₁ + 1 ∧ IsArithVar q₁ d₁ := by
  first | exact @GlobalTheory.isArithVar_of_surjective_dim_succ | exact GlobalTheory.isArithVar_of_surjective_dim_succ | (intros; apply GlobalTheory.isArithVar_of_surjective_dim_succ <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SubqPair

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.VMetric
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem chart_eq {F : X.Modules} {r : ℕ} {U : X.Opens} {e e' : Fin r → Γ(F, U)} (he : IsFrame e)
    (he' : IsFrame e') (h : e = e') : (⟨U, e, he⟩ : Chart F r) = ⟨U, e', he'⟩ := by
  subst h
  rfl

theorem isometric_det_of_eq {F : X.Modules} {r : ℕ} {h₁ h₂ : VMetric p F r} (H₁ : h₁.IsCInf)
    (H₂ : h₂.IsCInf) (e : h₁ = h₂) : (det H₁).Isometric (det H₂) := by
  subst e
  exact CurveDens.det_isometric_of_isIsometry k X p _ _ r _ _ H₁ H₂ (Iso.refl _)
    fun _ _ _ _ _ _ => rfl

theorem pull_restrict {E F : X.Modules} {r s : ℕ} (h : VMetric p E r) {j : F ⟶ E}
    (hj : IsSubbundle j) (hF : IsVB F s) (π : Y ⟶ X) (w : π ≫ p = q)
    (hj' : IsSubbundle ((Scheme.Modules.pullback π).map j)) :
    (h.restrict hj hF).pull π w = (h.pull π w).restrict hj' (hF.pullback π) := by
  have := hF.isQuasicoherent
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun z => ?_)
  have hc := hF.mem_pick (PtsOver.map π w _ z)
  refine ⟨(hF.pick (PtsOver.map π w _ z)).pull hF π, hc, ?_⟩
  refine (((h.met σ).restrict hj hF).pull_G π w _ hc).trans ?_
  ext a b
  have e (a) := QCoh.pullback_map_app_pullbackSections π j
    (le_refl (π ⁻¹ᵁ (hF.pick (PtsOver.map π w _ z)).U)) ((hF.pick (PtsOver.map π w _ z)).e a)
  exact (((h.met σ).form_pull π w _ _ le_rfl hc).symm).trans
    (congrArg₂ (fun s t => ((h.met σ).pull π w).form s t z) (e a).symm (e b).symm)

theorem pull_quot {S : ShortComplex X.Modules} {r s : ℕ} (h : VMetric p S.X₂ (r + s))
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (π : Y ⟶ X) (w : π ≫ p = q)
    (w' : (Scheme.Modules.pullback π).map S.f ≫ (Scheme.Modules.pullback π).map S.g = 0)
    (hS' : (ShortComplex.mk _ _ w').ShortExact) :
    (h.quot hS h₁ h₃).pull π w =
      VMetric.quot (S := .mk _ _ w') (h.pull π w) hS' (h₁.pullback π) (h₃.pullback π) := by
  have := h₁.isQuasicoherent
  have := h.isVB.isQuasicoherent
  have := h₃.isQuasicoherent
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun z => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ (PtsOver.map π w _ z)
  have eg : (fun j => ((Scheme.Modules.pullback π).map S.g).app (π ⁻¹ᵁ a.U)
      (pullbackSections π _ le_rfl (a.t j))) =
      fun j => pullbackSections π _ le_rfl (S.g.app a.U (a.t j)) :=
    funext fun j => QCoh.pullback_map_app_pullbackSections π S.g _ _
  let a' : AdaptedChart (.mk _ _ w') r s :=
    { U := π ⁻¹ᵁ a.U
      e := fun j => pullbackSections π _ le_rfl (a.e j)
      t := fun j => pullbackSections π _ le_rfl (a.t j)
      he := a.he.pullback π
      ht := eg ▸ a.ht.pullback π }
  have ha' : z ∈ ptsIn q σ a'.U := ha
  have hq : a'.quot = a.quot.pull h₃ π := chart_eq _ _ eg
  have hf (j) : a'.frame j = pullbackSections π _ le_rfl (a.frame j) := by
    rcases j with j | j
    · exact QCoh.pullback_map_app_pullbackSections π S.f _ _
    · rfl
  refine ⟨a'.quot, ha', Eq.trans ?_ (Met.quot_G (S := .mk _ _ w') ((h.met σ).pull π w) hS'
    (h₁.pullback π) (h₃.pullback π) a' ha').symm⟩
  rw [hq]
  refine (((h.met σ).quot hS h₁ h₃).pull_G π w a.quot ha).trans ?_
  rw [(h.met σ).quot_G hS h₁ h₃ a ha]
  congr 1
  ext i j
  exact ((h.met σ).form_pull π w _ _ le_rfl ha').symm.trans
    (congrArg₂ (fun s t => ((h.met σ).pull π w).form s t z) (hf i).symm (hf j).symm)

theorem isIsometry_quot_zero {S : ShortComplex X.Modules} (h : VMetric p S.X₂ (0 + 1))
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ 0) (h₃ : IsVB S.X₃ 1) [IsIso S.g] :
    VMetric.IsIsometry (r := 1) h (h.quot hS h₁ h₃) (asIso S.g) := by
  rw [VMetric.isIsometry_iff]
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun y => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  have ht : IsFrame a.t := by
    convert a.ht.map_iso (inv S.g) using 2 with j
    exact (congr(($(IsIso.hom_inv_id S.g)).app a.U (a.t j))).symm
  let c : Chart S.X₂ 1 := ⟨a.U, a.t, ht⟩
  refine ⟨a.quot, ha, ((h.met σ).quot_G hS h₁ h₃ a ha).trans ?_⟩
  refine Eq.trans ?_ (Met.map_G (r := 1) (h.met σ) (asIso S.g) c ha).symm
  ext i j
  rw [← Met.form_frame (r := 1) (h.met σ) c ha]
  simp [quotGram, Matrix.mul_apply, Matrix.toBlocks₂₂, Met.gram, AdaptedChart.frame, c]

theorem isometric_pair {E A B V : X.Modules} {r n : ℕ} {h : VMetric p E r} (H : h.IsCInf)
    (fl : Vert.Flag E r) (hn₀ : n < r) (hn : n + 1 < r) {u : A ⟶ B} {t : B ⟶ V} {w : u ≫ t = 0}
    (hS : (ShortComplex.mk u t w).ShortExact) (hA : IsVB A n) (hB : IsVB B (n + (1 + 1)))
    (hV : IsVB V (1 + 1)) {j : B ⟶ E} (hj : IsSubbundle j)
    (eB : B ≅ fl.F (Fin.succ ⟨n + 1, hn⟩)) (heB : eB.hom ≫ fl.ι _ = j)
    (eA : A ≅ fl.F (Fin.castSucc ⟨n, hn₀⟩)) (heA : eA.hom ≫ fl.ι _ = u ≫ j)
    (fl₁ : Vert.Flag V 2) (x : fl.F (Fin.succ ⟨n, hn₀⟩) ⟶ B) (g : fl.F (Fin.succ ⟨n, hn₀⟩) ⟶ fl₁.F 1)
    (hx : x ≫ j = fl.ι _) (hg : g ≫ fl₁.ι 1 = x ≫ t) [Epi g] {h₁ : VMetric p V 2} (H₁ : h₁.IsCInf)
    (e₁ : h₁ = VMetric.quot (S := .mk u t w) (r := n) (s := 1 + 1) (h.restrict hj hB) hS hA hV) :
    (grLB fl₁ 0 H₁).Isometric (grLB fl ⟨n, hn₀⟩ H) ∧
      (grLB fl₁ 1 H₁).Isometric (grLB fl ⟨n + 1, hn⟩ H) := by
  subst e₁
  let i₀ : Fin r := ⟨n, hn₀⟩
  let i₁ : Fin r := ⟨n + 1, hn⟩
  change eB.hom ≫ fl.ι i₁.succ = j at heB
  change eA.hom ≫ fl.ι i₀.castSucc = u ≫ j at heA
  change x ≫ j = fl.ι i₀.succ at hx
  have := hj.mono
  have res {F F' : X.Modules} {s : ℕ} {a : F ⟶ E} {b : F' ⟶ E} (ha : IsSubbundle a)
      (hb : IsSubbundle b) (hF : IsVB F s) (hF' : IsVB F' s) (e : F ≅ F') (he : e.hom ≫ b = a) :
      (h.restrict ha hF).IsIsometry (h.restrict hb hF') e := fun σ U s t y hy => by
    refine ((h.met σ).form_restrict hb hF' _ _ hy).trans
      (Eq.trans ?_ ((h.met σ).form_restrict ha hF s t hy).symm)
    rw [← he]
    rfl
  let f : A ⟶ fl.F i₀.succ := eA.hom ≫ fl.step i₀
  let q₁ : B ⟶ fl.gr i₁ := eB.hom ≫ fl.π i₁
  have hxB : x ≫ eB.hom = fl.step i₁ := by
    rw [← cancel_mono (fl.ι i₁.succ), Category.assoc, heB, hx]
    exact (fl.step_ι i₁).symm
  have w₀ : f ≫ fl.π i₀ = 0 := by
    simp only [f, Category.assoc]
    rw [show fl.step i₀ ≫ fl.π i₀ = 0 from cokernel.condition _, comp_zero]
  have w₁ : x ≫ q₁ = 0 := by
    rw [← Category.assoc, hxB]
    exact cokernel.condition _
  have hS₀ : (ShortComplex.mk f _ w₀).ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl i₀) eA.symm (Iso.refl _)
      (Iso.refl _) (by simp [f]) (by simp)) (stepSeq_shortExact fl i₀)
  have hS₁ : (ShortComplex.mk x q₁ w₁).ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl i₁) (Iso.refl _) eB.symm
      (Iso.refl _) ((Category.id_comp _).trans ((Iso.eq_comp_inv _).2 hxB)) (by simp [q₁]))
      (stepSeq_shortExact fl i₁)
  have hu : f ≫ x = u := by
    rw [← cancel_mono j, Category.assoc, hx, Category.assoc, fl.step_ι, heA]
  have hxs : IsSubbundle x := isSubbundle_of_shortExact hS₁ (fl.isVB_gr i₁)
  obtain ⟨l, m, w₃, hS₃, el, em⟩ := ThirdIso.abelian f x u (fl.π i₀) q₁ t w₀ w₁ w hS₀ hS₁ hS hu
  have hl : IsSubbundle l := isSubbundle_of_shortExact hS₃ (fl.isVB_gr i₁)
  have key (σ : k →+* ℂ) := MetStage.metStages k X p σ _ _ _ _ _ _ f x u (fl.π i₀) q₁ t w₀ w₁ w
    hS₀ hS₁ hS l m w₃ hS₃ n hA (fl.isVB i₀.succ) (fl.isVB_gr i₀) (fl.isVB_gr i₁) hV hxs
    ((h.restrict hj hB).met σ) hu el em hl

  have hfg : fl.step i₀ ≫ g = 0 := by
    rw [← cancel_mono (fl₁.ι 1), ← cancel_epi eA.hom, zero_comp, comp_zero, Category.assoc, hg,
      ← Category.assoc, ← Category.assoc]
    exact (congrArg (· ≫ t) hu).trans w
  let e : fl.gr i₀ ⟶ fl₁.F 1 := cokernel.desc _ g hfg
  have he : fl.π i₀ ≫ e = g := cokernel.π_desc _ _ _
  have hel : e ≫ fl₁.ι 1 = l := by
    rw [← cancel_epi (fl.π i₀), ← Category.assoc, he, hg, el]
  have : Mono l := hl.mono
  have : Mono e := mono_of_mono_fac hel
  have : Epi e := epi_of_epi_fac he
  have : IsIso e := isIso_of_mono_of_epi e
  have HB : (h.restrict hj hB).IsCInf := H.restrict hj hB
  constructor
  · have : IsIso (stepSeq fl₁ 0).g := (stepSeq_shortExact fl₁ 0).isIso_g_iff.2
      (isVB_zero_iff.1 (fl₁.isVB 0))
    have a₁ := CurveDens.det_isometric_of_isIsometry k X p _ _ 1 _ _
      (H₁.restrict (fl₁.isSubbundle 1) (fl₁.isVB 1)) (H₁.grMet fl₁ 0) _
      (isIsometry_quot_zero (S := stepSeq fl₁ 0) (stepMet _ fl₁ 0) (stepSeq_shortExact fl₁ 0)
        (fl₁.isVB 0) (fl₁.isVB_gr 0))
    have a₂ := CurveDens.det_isometric_of_isIsometry k X p _ _ 1 _ _
      (H₁.restrict hl (fl.isVB_gr i₀)) (H₁.restrict (fl₁.isSubbundle 1) (fl₁.isVB 1)) (asIso e)
      fun σ U s t y hy => by
        refine (Met.form_restrict _ (fl₁.isSubbundle 1) (fl₁.isVB 1) _ _ hy).trans
          (Eq.trans ?_ (Met.form_restrict _ hl (fl.isVB_gr i₀) s t hy).symm)
        rw [← hel]
        rfl
    have a₃ := isometric_det_of_eq (H₁.restrict hl (fl.isVB_gr i₀))
      (IsCInf.quot (S := .mk f _ w₀) hS₀ hA (fl.isVB_gr i₀) (HB.restrict hxs (fl.isVB i₀.succ)))
      (VMetric.ext (funext fun σ => (key σ).1))
    have a₄ := (isometric_detQuot_and_bcInt_eq_of_iso k X p (.mk f _ w₀) (stepSeq fl i₀) n 1 _
      (h.stepMet fl i₀) (HB.restrict hxs (fl.isVB i₀.succ)) (H.restrict _ _) hS₀
      (stepSeq_shortExact fl i₀) hA (fl.isVB_gr i₀) (fl.isVB i₀.castSucc) (fl.isVB_gr i₀) eA
      (Iso.refl _) (Category.comp_id _).symm fun σ U s t y hy => by
        refine ((h.met σ).form_restrict (fl.isSubbundle i₀.succ) (fl.isVB i₀.succ) _ _ hy).trans
          (Eq.trans ?_ ((Met.form_restrict _ hxs (fl.isVB i₀.succ) s t hy).trans
            ((h.met σ).form_restrict hj hB _ _ hy)).symm)
        rw [← hx]
        rfl).1
    exact a₁.symm.trans (a₂.symm.trans (a₃.trans a₄))
  · have : IsIso (fl₁.ι 2) := fl₁.isIso_last
    have a₁ := (isometric_detQuot_and_bcInt_eq_of_iso k X p (.mk l m w₃) (stepSeq fl₁ 1) 1 1 _
      (stepMet _ fl₁ 1) H₁ (H₁.restrict _ _) hS₃ (stepSeq_shortExact fl₁ 1) (fl.isVB_gr i₀)
      (fl.isVB_gr i₁) (fl₁.isVB 1) (fl₁.isVB_gr 1) (asIso e) (asIso (fl₁.ι 2)).symm
      ((Iso.eq_comp_inv (asIso (fl₁.ι 2))).2 ((Category.assoc _ _ _).trans
        ((congrArg (e ≫ ·) (fl₁.step_ι 1)).trans hel))) fun σ U s t y hy => by
        refine (Met.form_restrict _ (fl₁.isSubbundle 2) (fl₁.isVB 2) _ _ hy).trans ?_
        have e (v : Γ(V, U)) : (fl₁.ι 2).app U ((inv (fl₁.ι 2)).app U v) = v :=
          congr(($(IsIso.inv_hom_id (fl₁.ι 2))).app U v)
        exact congrArg₂ (fun s t => Met.form _ s t y) (e s) (e t)).1
    have a₂ := isometric_det_of_eq (IsCInf.quot (S := .mk l m w₃) hS₃ (fl.isVB_gr i₀)
      (fl.isVB_gr i₁) H₁) (IsCInf.quot (S := .mk x q₁ w₁) (r := n + 1) (s := 1) hS₁
        (fl.isVB i₀.succ) (fl.isVB_gr i₁) HB) (VMetric.ext (funext fun σ => (key σ).2))
    have a₃ := (isometric_detQuot_and_bcInt_eq_of_iso k X p (.mk x q₁ w₁) (stepSeq fl i₁) (n + 1) 1
      _ (h.stepMet fl i₁) HB (H.restrict _ _) hS₁ (stepSeq_shortExact fl i₁) (fl.isVB i₀.succ)
      (fl.isVB_gr i₁) (fl.isVB i₁.castSucc) (fl.isVB_gr i₁) (Iso.refl _) eB
      ((Category.id_comp _).trans hxB.symm) (res hj _ hB _ eB heB)).1
    exact a₁.symm.trans (a₂.trans a₃)

end GlobalTheory.SubqPair

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

theorem GlobalTheory.SubqPair.exists_isometric_pair : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (i i' : Fin n), (i' : ℕ) = i + 1 → ∀ (S P E₁ : Y₁.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback σ).obj E)
    (t : P ⟶ E₁) (wst : s ≫ t = 0) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2),
    (ShortComplex.mk s t wst).ShortExact → GlobalTheory.VB.IsSubbundle s → GlobalTheory.VB.IsSubbundle j → GlobalTheory.VB.IsVB S i →
    GlobalTheory.VB.IsVB P ((i : ℕ) + 2) → GlobalTheory.VB.IsVB E₁ 2 →
    (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ fl.F i'.succ, e.hom ≫ fl.ι i'.succ =
      (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ fl.F i.castSucc, e.hom ≫ fl.ι i.castSucc =
      (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ (x : fl.F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : fl.F i.succ ⟶ fl₁.F 1),
      x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E = fl.ι i.succ ∧
      g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) →
    ∃ (h₁ : VMetric q₁ E₁ 2) (H₁ : h₁.IsCInf),
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i (H.pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i' (H.pull π w)) := by
  intro k _ B Y Y₁ q p q₁ π σ ρ w wσ wρ wq E n h H fl i i' hi S P E₁ s j t wst fl₁ hS hs hj hSv hP hE₁
    ⟨eP, heP⟩ ⟨eS, heS⟩ ⟨x, g, hx, hg, _⟩
  obtain ⟨i, hi₀⟩ := i
  obtain ⟨i', hi₁⟩ := i'
  obtain rfl : i' = i + 1 := hi
  subst wσ
  have H₁ := VMetric.IsCInf.quot (S := .mk s t wst) (r := i) (s := 1 + 1) hS hSv hE₁
    ((H.pull σ wq).restrict hj hP)
  refine ⟨_, H₁, ?_⟩
  have := hS.epi_g
  have := hSv.isQuasicoherent
  have := hP.isQuasicoherent
  have w' : (Scheme.Modules.pullback ρ).map s ≫ (Scheme.Modules.pullback ρ).map t = 0 := by
    rw [← Functor.map_comp, wst, Functor.map_zero]
  have hS' : (ShortComplex.mk _ _ w').ShortExact :=
    ShortComplex.ShortExact.mk' (QCoh.exact_map_pullback ρ hS.exact).1
      (SubPull.isSubbundle_pullback _ _ ρ _ _ s i hSv hs).mono (QCoh.exact_map_pullback ρ hS.exact).2
  have hj₁ := SubPull.isSubbundle_pullback _ _ ρ _ _ j _ hP hj
  let φ := (Scheme.Modules.pullbackComp ρ σ).app E
  have hj₂ : VB.IsSubbundle ((Scheme.Modules.pullback ρ).map j ≫ φ.hom) := by
    obtain ⟨_, a, ha⟩ := hj₁
    exact ⟨inferInstance, a, ha.of_iso (Limits.cokernelCompIsIso _ _).symm⟩
  refine GlobalTheory.SubqPair.isometric_pair (H.pull _ w) fl hi₀ hi₁ hS' (hSv.pullback ρ) (hP.pullback ρ)
    (hE₁.pullback ρ) hj₂ eP heP eS (heS.trans ?_) fl₁ x g hx hg (H₁.pull ρ wρ) ?_
  · rw [Functor.map_comp, Category.assoc]
    rfl
  · refine (GlobalTheory.SubqPair.pull_quot (S := .mk s t wst) (r := i) (s := 1 + 1) _ hS hSv hE₁ ρ wρ w' hS').trans ?_
    congr 1
    refine (GlobalTheory.SubqPair.pull_restrict _ hj hP ρ wρ hj₁).trans ?_
    refine VMetric.ext (funext fun τ => Met.ext_form fun U a b y hy => ?_)
    refine (Met.form_restrict _ hj₁ (hP.pullback ρ) a b hy).trans
      (Eq.trans ?_ (Met.form_restrict _ hj₂ (hP.pullback ρ) a b hy).symm)
    exact ((VMetric.isIsometry_pull_id_comp k B q E n h).2 Y₁ Y q₁ p σ ρ wq wρ w τ U _ _ y hy).symm

end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_flag_successive_quotient_exact : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (i i' : Fin n), (i' : ℕ) = i + 1 → ∀ (S P E₁ : Y₁.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback σ).obj E)
    (t : P ⟶ E₁) (wst : s ≫ t = 0) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2),
    (ShortComplex.mk s t wst).ShortExact → GlobalTheory.VB.IsSubbundle s → GlobalTheory.VB.IsSubbundle j → GlobalTheory.VB.IsVB S i →
    GlobalTheory.VB.IsVB P ((i : ℕ) + 2) → GlobalTheory.VB.IsVB E₁ 2 →
    (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ fl.F i'.succ, e.hom ≫ fl.ι i'.succ =
      (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ fl.F i.castSucc, e.hom ≫ fl.ι i.castSucc =
      (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ (x : fl.F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : fl.F i.succ ⟶ fl₁.F 1),
      x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E = fl.ι i.succ ∧
      g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) →
    ∃ (h₁ : VMetric q₁ E₁ 2) (H₁ : h₁.IsCInf),
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i (H.pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i' (H.pull π w)) := by
  atlas_forward_decl GlobalTheory.SubqPair.exists_isometric_pair
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open Limits

namespace GlobalTheory.StepLine

theorem isVB_cokernel_of_succ {X : Scheme.{0}} {A₀ A₁ : X.Modules} {u : A₀ ⟶ A₁} {a : ℕ}
    (hu : IsSubbundle u) (h₀ : IsVB A₀ a) (h₁ : IsVB A₁ (a + 1)) : IsVB (cokernel u) 1 := fun x => by
  have : Nonempty X := ⟨x⟩
  have := hu.mono
  obtain ⟨s, hs⟩ := hu.isVB_cokernel
  obtain ⟨h, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X (.mk u (cokernel.π _)
    (cokernel.condition _)) a s { exact := ShortComplex.exact_cokernel _ } h₀ hs
  obtain rfl : s = 1 := by have := h.rank_unique h₁; omega
  exact hs x

abbrev seq {X : Scheme.{0}} {A₀ A₁ : X.Modules} (u : A₀ ⟶ A₁) : ShortComplex X.Modules :=
  .mk u (cokernel.π u) (cokernel.condition u)

theorem seq_shortExact {X : Scheme.{0}} {A₀ A₁ : X.Modules} {u : A₀ ⟶ A₁} (hu : IsSubbundle u) :
    (seq u).ShortExact :=
  have := hu.mono
  { exact := ShortComplex.exact_cokernel _ }

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Line

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  (ρ : Y ⟶ Y₁) (wρ : ρ ≫ q₁ = p) {G : Y₁.Modules} {E : Y.Modules}
  (ψ : (Scheme.Modules.pullback ρ).obj G ≅ E) {n : ℕ} (fl : Vert.Flag E n) (l : Fin n)
  {A₀ A₁ : Y₁.Modules} (u : A₀ ⟶ A₁) (v : A₁ ⟶ G)
  (e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc)
  (e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ)

theorem map_comp_e₁ (he₁ : e₁.hom ≫ fl.ι l.succ = (Scheme.Modules.pullback ρ).map v ≫ ψ.hom)
    (he₀ : e₀.hom ≫ fl.ι l.castSucc = (Scheme.Modules.pullback ρ).map (u ≫ v) ≫ ψ.hom) :
    (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l := by
  rw [← cancel_mono (fl.ι l.succ), Category.assoc, Category.assoc, he₁, fl.step_ι, he₀,
    Functor.map_comp, Category.assoc]

variable {ρ ψ fl l u v e₀ e₁} in

def grIso (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l) :
    (Scheme.Modules.pullback ρ).obj (cokernel u) ≅ fl.gr l :=
  PreservesCokernel.iso (Scheme.Modules.pullback ρ) u ≪≫ cokernel.mapIso _ _ e₀ e₁ sq

variable {ρ ψ fl l u v e₀ e₁} in
theorem map_π_grIso (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l) :
    (Scheme.Modules.pullback ρ).map (cokernel.π u) ≫ (grIso sq).hom = e₁.hom ≫ fl.π l := by
  have e := Limits.π_comp_cokernelComparison u (Scheme.Modules.pullback ρ)
  rw [← Limits.PreservesCokernel.iso_inv] at e
  have e' := congrArg (· ≫ (Limits.PreservesCokernel.iso (Scheme.Modules.pullback ρ) u).hom) e
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at e'
  change _ ≫ (PreservesCokernel.iso (Scheme.Modules.pullback ρ) u).hom ≫
    (cokernel.mapIso _ _ e₀ e₁ sq).hom = e₁.hom ≫ cokernel.π (fl.step l)
  rw [← Category.assoc, ← e']
  simp [cokernel.mapIso]

end Line

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Chart

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  {ρ : Y ⟶ Y₁} {G : Y₁.Modules} {E : Y.Modules} {n : ℕ} {fl : Vert.Flag E n} {l : Fin n}
  {A₀ A₁ : Y₁.Modules} {u : A₀ ⟶ A₁}
  {e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc}
  {e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ}

def pullChart (hA₀ : IsVB A₀ l) (hQ : IsVB (cokernel u) 1)
    (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l)
    (a : AdaptedChart (seq u) l 1) : AdaptedChart (VMetric.stepSeq fl l) l 1 :=
  have := hA₀.isQuasicoherent
  have := hQ.isQuasicoherent
  { U := ρ ⁻¹ᵁ a.U
    e := fun j => e₀.hom.app _ (pullbackSections ρ _ le_rfl (a.e j))
    t := fun j => e₁.hom.app _ (pullbackSections ρ _ le_rfl (a.t j))
    he := (a.he.pullback ρ).map_iso e₀.hom
    ht := by
      have h := (a.ht.pullback ρ).map_iso (grIso sq).hom
      convert h using 2 with j
      rw [← QCoh.pullback_map_app_pullbackSections]
      exact (congr(($(map_π_grIso sq)).app _ _)).symm }

end Chart

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Gram

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  {ρ : Y ⟶ Y₁} {G : Y₁.Modules} {E : Y.Modules} {n : ℕ} {fl : Vert.Flag E n} {l : Fin n}
  {A₀ A₁ : Y₁.Modules} {u : A₀ ⟶ A₁}
  {e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc}
  {e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ}
  (hA₀ : IsVB A₀ l) (hA₁ : IsVB A₁ (l + 1)) (hQ : IsVB (cokernel u) 1)
  (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l)
  (a : AdaptedChart (seq u) l 1)

theorem pullChart_frame (j : Fin l ⊕ Fin 1) :
    (pullChart hA₀ hQ sq a).frame j =
      have := hA₁.isQuasicoherent
      e₁.hom.app _ (pullbackSections ρ _ le_rfl (a.frame j)) := by
  have := hA₁.isQuasicoherent
  have := hA₀.isQuasicoherent
  rcases j with j | j
  · change (fl.step l).app _ (e₀.hom.app _ _) = e₁.hom.app _ (pullbackSections ρ _ le_rfl (u.app a.U (a.e j)))
    rw [← QCoh.pullback_map_app_pullbackSections]
    exact (congr(($(sq)).app _ _)).symm
  · rfl

theorem pullChart_quot :
    (pullChart hA₀ hQ sq a).quot = (a.quot.pull hQ ρ).map (grIso sq) := by
  have := hQ.isQuasicoherent
  have e : (pullChart hA₀ hQ sq a).quot.e = ((a.quot.pull hQ ρ).map (grIso sq)).e := by
    funext j
    refine Eq.trans ?_ (congrArg ((grIso sq).hom.app _)
      (QCoh.pullback_map_app_pullbackSections ρ (cokernel.π u) le_rfl (a.t j)))
    exact (congr(($(map_π_grIso sq)).app _ _)).symm
  have key : ∀ {F : Y.Modules} {U : Y.Opens} {e e' : Fin 1 → Γ(F, U)} (he : IsFrame e)
      (he' : IsFrame e'), e = e' → (⟨U, e, he⟩ : Chart F 1) = ⟨U, e', he'⟩ := by
    rintro F U e e' he he' rfl
    rfl
  exact key _ _ e

end Gram

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Met

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  {ρ : Y ⟶ Y₁} {G : Y₁.Modules} {E : Y.Modules} {n : ℕ} {fl : Vert.Flag E n} {l : Fin n}
  {A₀ A₁ : Y₁.Modules} {u : A₀ ⟶ A₁} {v : A₁ ⟶ G}
  {e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc}
  {e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ}
  (hA₀ : IsVB A₀ l) (hA₁ : IsVB A₁ (l + 1)) (hQ : IsVB (cokernel u) 1)
  (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l)
  (a : AdaptedChart (seq u) l 1)
  {ψ : (Scheme.Modules.pullback ρ).obj G ≅ E} (g : VMetric q₁ G n) (h' : VMetric p E n)
  (wρ : ρ ≫ q₁ = p)

theorem gram_pullChart (hψ : (g.pull ρ wρ).IsIsometry h' ψ) (hv : IsSubbundle v)
    (he₁ : e₁.hom ≫ fl.ι l.succ = (Scheme.Modules.pullback ρ).map v ≫ ψ.hom) {τ : k →+* ℂ}
    {z : CxPts p τ} (hz : z ∈ ptsIn p τ (ρ ⁻¹ᵁ a.U)) :
    ((h'.stepMet fl l).met τ).gram (pullChart hA₀ hQ sq a).frame z =
      ((g.restrict hv hA₁).met τ).gram a.frame (PtsOver.map ρ wρ _ z) := by
  have := g.isVB.isQuasicoherent
  have := hA₁.isQuasicoherent
  have hz' : PtsOver.map ρ wρ _ z ∈ ptsIn q₁ τ a.U := hz
  ext j m
  change ((h'.met τ).restrict (fl.isSubbundle l.succ) (fl.isVB l.succ)).form _ _ z =
    ((g.met τ).restrict hv hA₁).form _ _ _
  refine (Met.form_restrict _ _ _ _ _ hz).trans (Eq.trans ?_ (Met.form_restrict _ _ _ _ _ hz').symm)
  have e (j) : (fl.ι l.succ).app (ρ ⁻¹ᵁ a.U) ((pullChart hA₀ hQ sq a).frame j) =
      ψ.hom.app _ (pullbackSections ρ G le_rfl (v.app a.U (a.frame j))) := by
    rw [pullChart_frame hA₀ hA₁ hQ sq a j, ← QCoh.pullback_map_app_pullbackSections]
    exact congr(($(he₁)).app _ _)
  rw [e j, e m, hψ τ _ _ _ z hz]
  exact (g.met τ).form_pull ρ wρ _ _ le_rfl hz

end Met

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Eq

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  {ρ : Y ⟶ Y₁} {G : Y₁.Modules} {E : Y.Modules} {n : ℕ} {fl : Vert.Flag E n} {l : Fin n}
  {A₀ A₁ : Y₁.Modules} {u : A₀ ⟶ A₁} {v : A₁ ⟶ G}
  {e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc}
  {e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ}
  (hA₀ : IsVB A₀ l) (hA₁ : IsVB A₁ (l + 1)) (hQ : IsVB (cokernel u) 1)
  (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l)
  {ψ : (Scheme.Modules.pullback ρ).obj G ≅ E} (g : VMetric q₁ G n) (h' : VMetric p E n)
  (wρ : ρ ≫ q₁ = p)

theorem grMet_eq (hψ : (g.pull ρ wρ).IsIsometry h' ψ) (hu : IsSubbundle u) (hv : IsSubbundle v)
    (he₁ : e₁.hom ≫ fl.ι l.succ = (Scheme.Modules.pullback ρ).map v ≫ ψ.hom) :
    h'.grMet fl l = ((((g.restrict hv hA₁).quot (seq_shortExact hu) hA₀ hQ).pull ρ wρ).map
      (grIso sq)) := by
  refine VMetric.ext (funext fun τ => Met.ext_of_exists fun z => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted (seq_shortExact hu) hA₀ hQ (PtsOver.map ρ wρ _ z)
  have ha' : z ∈ ptsIn p τ (ρ ⁻¹ᵁ a.U) := ha
  refine ⟨(pullChart hA₀ hQ sq a).quot, ha', ?_⟩
  refine (((h'.stepMet fl l).met τ).quot_G (VMetric.stepSeq_shortExact fl l) (fl.isVB l.castSucc)
    (fl.isVB_gr l) (pullChart hA₀ hQ sq a) ha').trans ?_
  rw [gram_pullChart hA₀ hA₁ hQ sq a g h' wρ hψ hv he₁ ha', pullChart_quot hA₀ hQ sq a]
  set M := ((g.restrict hv hA₁).quot (seq_shortExact hu) hA₀ hQ).met τ with hM
  change _ = ((M.pull ρ wρ).map (grIso sq)).G ((a.quot.pull M.isVB ρ).map (grIso sq)) z
  have h₁ := (M.pull ρ wρ).map_G (grIso sq) (a.quot.pull M.isVB ρ) ha'
  have h₂ := M.pull_G ρ wρ a.quot ha
  have h₃ := ((g.restrict hv hA₁).met τ).quot_G (seq_shortExact hu) hA₀ hQ a ha
  rw [h₁, h₂]
  exact h₃.symm

end Eq

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

variable {k : Type} [CommRing k]

theorem isIsometry_pull_congr {X Y : Scheme.{0}} {q : Y ⟶ Sp k} {t : X ⟶ Sp k} {E : Y.Modules}
    {r : ℕ} (h : VMetric q E r) {f f' : X ⟶ Y} (e : f = f') (hf : f ≫ q = t) (hf' : f' ≫ q = t) :
    (h.pull f hf).IsIsometry (h.pull f' hf') ((Scheme.Modules.pullbackCongr e).app E) := by
  subst e
  intro σ V s s' y hy
  rfl

theorem det_congr {X : Scheme.{0}} {p : X ⟶ Sp k} {F : X.Modules} {r : ℕ} {h₁ h₂ : VMetric p F r}
    (H₁ : h₁.IsCInf) (H₂ : h₂.IsCInf) (e : h₁ = h₂) : VMetric.det H₁ = VMetric.det H₂ := by
  subst e
  rfl

end GlobalTheory.StepLine

theorem GlobalTheory.StepLine.isometric_grLB_of_steps_pull : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (l : Fin n) (A₀ A₁ : Y₁.Modules) (u : A₀ ⟶ A₁) (v : A₁ ⟶ (Scheme.Modules.pullback σ).obj E),
    GlobalTheory.VB.IsSubbundle u → GlobalTheory.VB.IsSubbundle v → GlobalTheory.VB.IsVB A₀ l → GlobalTheory.VB.IsVB A₁ (l + 1) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ, e.hom ≫ fl.ι l.succ =
      (Scheme.Modules.pullback ρ).map v ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc, e.hom ≫ fl.ι l.castSucc =
      (Scheme.Modules.pullback ρ).map (u ≫ v) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    ∃ M : HermLB q₁, (M.pull ρ wρ).Isometric (VMetric.grLB fl l (H.pull π w)) := by
  intro k _ B Y Y₁ q p q₁ π σ ρ w wσ wρ wq E n h H fl l A₀ A₁ u v hu hv hA₀ hA₁ ⟨e₁, he₁⟩ ⟨e₀, he₀⟩
  let ψ := (Scheme.Modules.pullbackComp ρ σ).app E ≪≫ (Scheme.Modules.pullbackCongr wσ).app E
  have he₁' : e₁.hom ≫ fl.ι l.succ = (Scheme.Modules.pullback ρ).map v ≫ ψ.hom := he₁
  have he₀' : e₀.hom ≫ fl.ι l.castSucc = (Scheme.Modules.pullback ρ).map (u ≫ v) ≫ ψ.hom := he₀
  have e : (ρ ≫ σ) ≫ q = p := by rw [Category.assoc, wq, wρ]
  have hψ : ((h.pull σ wq).pull ρ wρ).IsIsometry (h.pull π w) ψ :=
    IsometryPullback.isIsometry_trans ((VMetric.isIsometry_pull_id_comp k B q E n h).2 Y₁ Y q₁ p σ ρ wq wρ e)
      (StepLine.isIsometry_pull_congr h wσ e w)
  have sq := StepLine.map_comp_e₁ ρ ψ fl l u v e₀ e₁ he₁' he₀'
  have hQ := StepLine.isVB_cokernel_of_succ hu hA₀ hA₁
  have HQ := (((H.pull σ wq).restrict hv hA₁).quot (StepLine.seq_shortExact hu) hA₀ hQ)
  refine ⟨VMetric.det HQ, ?_⟩
  have eq := StepLine.grMet_eq hA₀ hA₁ hQ sq (h.pull σ wq) (h.pull π w) wρ hψ hu hv he₁'
  refine (VMetric.isometric_det_pull HQ ρ wρ).symm.trans
    ((VMetric.isometric_det_map (HQ.pull ρ wρ) (StepLine.grIso sq)).trans ?_)
  rw [VMetric.grLB, StepLine.det_congr _ ((H.pull π w).grMet fl l) eq.symm]
  exact HermLB.Isometric.refl _
end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_flag_quotient_connecting_map : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (l : Fin n) (A₀ A₁ : Y₁.Modules) (u : A₀ ⟶ A₁) (v : A₁ ⟶ (Scheme.Modules.pullback σ).obj E),
    GlobalTheory.VB.IsSubbundle u → GlobalTheory.VB.IsSubbundle v → GlobalTheory.VB.IsVB A₀ l → GlobalTheory.VB.IsVB A₁ (l + 1) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ, e.hom ≫ fl.ι l.succ =
      (Scheme.Modules.pullback ρ).map v ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc, e.hom ≫ fl.ι l.castSucc =
      (Scheme.Modules.pullback ρ).map (u ≫ v) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    ∃ M : HermLB q₁, (M.pull ρ wρ).Isometric (VMetric.grLB fl l (H.pull π w)) := by
  atlas_forward_decl GlobalTheory.StepLine.isometric_grLB_of_steps_pull
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.SwapBundle

theorem swapFl_bundle : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ),
    IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∃ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp k) (d₁ : ℕ) (ρ : Y ⟶ Y₁) (wρ : ρ ≫ q₁ = p) (E₁ : Y₁.Modules) (h₁ : VMetric q₁ E₁ 2)
      (H₁ : h₁.IsCInf) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (M : (Σ a, Fin (r a)) → HermLB q₁),
      D = d₁ + 1 ∧ IsArithVar q₁ d₁ ∧ IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i ((H a).pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i' ((H a).pull π w)) ∧
      ∀ z : Σ a, Fin (r a), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        ((M z).pull ρ wρ).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) := by
  intro k _ B Y _ _ q p d D hq hp π w ι _ E r h H fl hfl a i i' hi
  obtain ⟨Y₁, σ, ρ, wσ, S, P, E₁, s, j, t, wst, fl₁, A₀, A₁, u, v, hY₁, hproj, hsurj, hdim, hfb, hS, hs, hj,
    hSv, hPv, hEv, hPj, hSj, hx, hz⟩ := GlobalTheory.T.flag_bundle_successive_quotient_line k B Y q p d D hq hp π w ι E r (fun a => (h a).isVB) fl hfl a i i' hi
  have wρ : ρ ≫ (σ ≫ q) = p := by rw [← Category.assoc, wσ, w]
  obtain ⟨d₁, hD, had⟩ := GlobalTheory.T.arith_variety_relative_dim_drop k Y Y₁ p (σ ≫ q) ρ D wρ hp hY₁ hproj hsurj hdim
  obtain ⟨h₁, H₁, i1, i2⟩ := GlobalTheory.T.metric_flag_successive_quotient_exact k B Y Y₁ q p (σ ≫ q) π σ ρ w wσ wρ rfl (E a) (r a) (h a) (H a) (fl a) i i' hi
    S P E₁ s j t wst fl₁ hS hs hj hSv hPv hEv hPj hSj hx
  have key : ∀ z : Σ a, Fin (r a), z ≠ ⟨a, i⟩ ∧ z ≠ ⟨a, i'⟩ → ∃ M : HermLB (σ ≫ q),
      (M.pull ρ wρ).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) := fun z hz' => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz z hz'.1 hz'.2
    exact GlobalTheory.T.metric_flag_quotient_connecting_map k B Y Y₁ q p (σ ≫ q) π σ ρ w wσ wρ rfl (E z.1) (r z.1) (h z.1) (H z.1) (fl z.1) z.2 (A₀ z) (A₁ z)
      (u z) (v z) h1 h2 h3 h4 h5 h6
  refine ⟨Y₁, σ ≫ q, d₁, ρ, wρ, E₁, h₁, H₁, fl₁,
    fun z => if hz' : z ≠ ⟨a, i⟩ ∧ z ≠ ⟨a, i'⟩ then (key z hz').choose else HermLB.triv _,
    hD, had, hfb, i1, i2, fun z h1 h2 => ?_⟩
  simp only [dif_pos (show z ≠ ⟨a, i⟩ ∧ z ≠ ⟨a, i'⟩ from ⟨h1, h2⟩)]
  exact (key z ⟨h1, h2⟩).choose_spec

end GlobalTheory.SwapBundle
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_metric_grading : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ),
    IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∃ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp k) (d₁ : ℕ) (ρ : Y ⟶ Y₁) (wρ : ρ ≫ q₁ = p) (E₁ : Y₁.Modules) (h₁ : VMetric q₁ E₁ 2)
      (H₁ : h₁.IsCInf) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (M : (Σ a, Fin (r a)) → HermLB q₁),
      D = d₁ + 1 ∧ IsArithVar q₁ d₁ ∧ IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i ((H a).pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB (fl a) i' ((H a).pull π w)) ∧
      ∀ z : Σ a, Fin (r a), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        ((M z).pull ρ wρ).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) := by
  first | exact @GlobalTheory.SwapBundle.swapFl_bundle | exact GlobalTheory.SwapBundle.swapFl_bundle | (intros; apply GlobalTheory.SwapBundle.swapFl_bundle <;> assumption)
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.CovTest.SwapFlProof

theorem comb_isometric_pullback {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {κ : Type} [Fintype κ]
    (L : κ → HermLB q) (M : κ → HermLB p) (ρ : Y ⟶ X) (wρ : ρ ≫ p = q) (n : κ → ℤ) (S : κ → Prop)
    (hn : ∀ z, S z → n z = 0) (hM : ∀ z, ¬ S z → ((M z).pull ρ wρ).Isometric (L z)) :
    (comb L n).Isometric ((comb M n).pull ρ wρ) := by
  refine HermLB.Isometric.trans ?_ (isometric_comb_pull M n ρ wρ)
  refine HermLB.icls_eq_iff.1 ?_
  rw [icls_comb, icls_comb]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : S z
  · rw [hn z hz, zero_smul, zero_smul]
  · rw [HermLB.icls_eq_iff.2 (hM z hz).symm]

theorem lin_update_two_coords {κ : Type} [Fintype κ] [DecidableEq κ] (x y : κ) (hxy : x ≠ y) (n n' : κ → ℤ)
    (hx0 : n' x = 0) (hy0 : n' y = 0) (hne : ∀ z, z ≠ x → z ≠ y → n' z = n z) (c₀ c₁ : ℤ) :
    (lin fun z => ∑ j : Fin 3, (![(c₀ : ℝ), c₁, 1] j) *
      ((![Pi.single x 1, Pi.single y 1, n'] : Fin 3 → κ → ℤ) j z : ℝ)) =
      lin fun z => ((Function.update (Function.update n x c₀) y c₁ z : ℤ) : ℝ) := by
  congr 1
  funext z
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Pi.single_apply, Function.update_apply]
  by_cases h1 : z = x
  · subst h1; simp [hx0, hxy]
  · by_cases h2 : z = y
    · subst h2; simp [hy0, h1]
    · simp [h1, h2, hne z h1 h2]

theorem swapFl_of_swap2 : ArCalc → ∀ G, Homog G → Swap2 G → SwapFl G := by
  intro _ G _ hS k _ B Y _ _ q p d D hq hp π w ι _ E r h H fl hfl Φ Ψ hΦ hΨ a i i' hi n
  obtain ⟨Y₁, q₁, d₁, ρ, wρ, E₁, h₁, H₁, fl₁, M, rfl, hY₁, hfl₁, hS0, hS1, hM⟩ :=
    GlobalTheory.T.flag_bundle_hermitian_metric_grading k B Y q p d D hq hp π w ι E r h H fl hfl a i i' hi
  haveI := hY₁.isIntegral
  set x : Σ a, Fin (r a) := ⟨a, i⟩ with hx
  set y : Σ a, Fin (r a) := ⟨a, i'⟩ with hy
  have hxy : x ≠ y := by
    intro e
    rw [hx, hy, Sigma.mk.inj_iff] at e
    have := congrArg Fin.val (eq_of_heq e.2)
    omega
  set L : (Σ a, Fin (r a)) → HermLB p := fun z => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w) with hL
  set n' : (Σ a, Fin (r a)) → ℤ := fun z => if z = x ∨ z = y then 0 else n z with hn'
  set Mf : Fin 3 → HermLB p := ![VMetric.grLB fl₁ 0 (H₁.pull ρ wρ), VMetric.grLB fl₁ 1 (H₁.pull ρ wρ),
    (comb M n').pull ρ wρ] with hMf
  set Am : Fin 3 → (Σ a, Fin (r a)) → ℤ := ![Pi.single x 1, Pi.single y 1, n'] with hAm
  have hiso : ∀ j, (comb L (Am j)).Isometric (Mf j) := by
    intro j
    fin_cases j
    · exact (isometric_comb_single L x).trans hS0.symm
    · exact (isometric_comb_single L y).trans hS1.symm
    · exact comb_isometric_pullback L M ρ wρ n' (fun z => z = x ∨ z = y) (fun z hz => if_pos hz)
        (fun z hz => hM z (fun e => hz (Or.inl e)) (fun e => hz (Or.inr e)))
  set f : Fin 3 → MvPolynomial (Σ a, Fin (r a)) ℝ := fun j => lin fun z => (Am j z : ℝ) with hf
  have hΦ' := ((Published.arIso_holds k Y p (d₁ + 1) hp).2 _ L Φ hΦ).2.2 (Fin 3) Mf Am hiso
  have hΨ' : IsGeoFun Mf (d₁ + 1) (Ψ ∘ₗ (aeval f : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] _).toLinearMap) := by
    refine ⟨fun m => ?_, fun P e he hP => ?_⟩
    · rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin]
      have h2 := hΨ.1 (fun z => ∑ j, m j * Am j z)
      simp only [Int.cast_sum, Int.cast_mul] at h2
      rw [h2]
      exact ((isometric_comb_comb L Am m).trans (isometric_comb_congr hiso m)).gdeg_eq _
    · rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      exact hΨ.2 _ e he (by simpa using hP.aeval _ fun j => isHomogeneous_lin _)
  have key := hS k Y₁ Y q₁ p d₁ hY₁ hp ρ wρ E₁ h₁ H₁ fl₁ hfl₁ (comb M n') _ _ hΦ' hΨ' (n x) (n y)
  have hsw : aeval f (G (d₁ + 1) (n x) (n y)) = swapPol G (d₁ + 1) x y n := by
    unfold swapPol
    congr 2
    funext j
    fin_cases j
    · exact lin_single x
    · exact lin_single y
    · simp only [hf, hAm, hn', Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      congr 1
      funext z
      by_cases hz : z = x ∨ z = y <;> simp [hz]
  have hx0 : n' x = 0 := if_pos (Or.inl rfl)
  have hy0 : n' y = 0 := if_pos (Or.inr rfl)
  have hne : ∀ z, z ≠ x → z ≠ y → n' z = n z := fun z h1 h2 => if_neg (by tauto)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin] at key
  rw [← hsw, ← key, hAm, lin_update_two_coords x y hxy n n' hx0 hy0 hne (n x) (n y), lin_update_two_coords x y hxy n n' hx0 hy0 hne (n y) (n x)]
  congr 4 <;> funext z
  · rw [Function.update_eq_self, Function.update_eq_self]
  · by_cases h1 : z = x
    · subst h1; simp [Function.update_apply, hxy, Equiv.swap_apply_left]
    · by_cases h2 : z = y
      · subst h2; simp [Function.update_apply, Equiv.swap_apply_right]
      · simp [Function.update_apply, h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

end GlobalTheory.CovTest.SwapFlProof
end
