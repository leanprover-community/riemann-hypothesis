import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
import Development.WeilBound.ThetaLifts.DoubleEigenvalues.DblEigenW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExistsStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnimodularHermitianFrameCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorNormalisesSchroedingerOperator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeVacuumFixedAndUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalChartInertPlaceUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalHeisenbergEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalHeisenbergOperatorsLawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelOppositeLagrangianUnitaryOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesVacuumInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilHomFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceWeilNormalisesHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceIntegralUnitaryPointsFixVacuum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq

section
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem inert_ctx {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {v : Pl F} (he : IsEmpty (E →ₐ[F] Fv F v)) :
    (∃ w, Formalism.UG.IsInertAt F E v w) ∧ v ∉ X.T :=
  ⟨inert_of_local F E σ B hT.base v he, fun hv => he.false (B.τ ⟨v, hT.chars.sub hv⟩)⟩

theorem unrAt_div {χ χ' : Chr F E} {u : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ u) (h' : UnrAt χ' u) :
    UnrAt (χ / χ') u := fun x hx => by
  have e : χ / χ' * χ' = χ := div_mul_cancel χ χ'
  have e2 : locChar (χ / χ' * χ') u x = locChar (χ / χ') u x * locChar χ' u x := by simp [locChar]
  rw [e, h x hx, h' x hx, mul_one] at e2
  exact e2.symm

theorem fix_of {B : Base F E} (hB : B.IsGood σ) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') {M : Model σ X W} (hM : M.IsGood B.ψ) {χX χW : Chr F E} {om : Rep σ X W}
    (hw : M.IsWeil B.ψ χX χW om) {v : Pl F} (hX' : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt χX u)
    (hW' : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt χW u)
    {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}
    (hL : IsLocRep M B.ψ om v ω ρ) :
    (∀ g ∈ KAt σ X v, ω (g, 1) (M.vac v) = M.vac v) ∧ (∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v) := by
  have hSB := (hM.vac v).1
  refine ⟨fun g hg => ?_, fun k hk => ?_⟩
  · have hA := PositivityTheory.ThKU.Vac.vacFixX hB hX hW hM hw hW' (k := g) hg
    exact ((hL.acts g hg.1 1 (GlobalTheory.InertSph.one_mem_KAt σ W v).1 _ hSB _).1 hA).symm
  · have hA := PositivityTheory.ThKU.Vac.vacFixW hB hX hW hM hw hX' (k := k) hk
    exact ((hL.acts 1 (GlobalTheory.InertSph.one_mem_KAt σ X v).1 k hk.1 _ hSB _).1 hA).symm

end PositivityTheory.Sph

end
end

section
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.KFinLoc

theorem locDataV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hin : Formalism.UG.IsInertAt F E v w)
    (hvT : v ∉ X.T) : LocData G.M om v := by
  obtain ⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, ψL, ι, hunr, hodd, hδ, hpi, hpn, hinj, him, hmul, hσ, hint, hψ⟩ :=
    GlobalTheory.T.inert_place_local_field_data_exists F E σ B hT.base v w hin
  obtain ⟨JS, JT, Xm, iV, iW, hiS, hiT, hhS, hhT, hψ2, himX, hlat1, hlat2, hact, hUV, hUW, hKV, hKW⟩ :=
    GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates F E σ B a a' G hT.base hT.geo v w hin L ϖ σL q δ ψL ι hunr hodd hδ hinj him hmul hσ hint hψ
  obtain ⟨ρ, hρ0, hρmul, hρA, hρspan⟩ := GlobalTheory.T.exists_local_schroedinger_family_at_place F v B.ψ hT.base.std (hT.base.inert v w hin).2.2 G.M.co
    (Matrix (Fin (a + a')) (Fin a) L) Xm
    (fun x y => ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) himX hψ2
  let j := iV.prodMap iW
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_localWeilOperators_supportedAtPlace F E σ B a a' G X om om' hT v _ j (fun g => ⟨hUV g.1, hUW g.2⟩)
  have hnorm := GlobalTheory.T.localWeilOperator_normalises_schroedingerOperator F E σ B a a' G X om om' hT v _ Xm (fun y => (himX _).2 ⟨y, rfl⟩) ρ hρA _ j ω hω
    (fun g x => ((g.2 : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
      (((g.1 : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) (fun g x => hact g.1 g.2 x)
  obtain ⟨hvac, huniq⟩ := GlobalTheory.T.inertPlace_latticeVacuum_fixed_and_unique F E σ B a a' G X om om' hT v w hin hvT _ Xm
    (fun u => ∀ i j, u i j ∈ Formalism.UG.intL L) hlat1 hlat2 ρ hρA
  have hfix := GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hin hvT
  have hvSB := (hT.geo.hM.vac v).1
  have hv0 := (hT.geo.hM.vac v).2.1
  let s : SB (Fin a × Fin (a + a') → Fv F v) := ⟨G.M.vac v, hvSB⟩
  have hs0 : s ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hspan := hρspan s hs0
  have hωs : ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
    intro g h hg hh
    exact Subtype.ext ((hω (g, h) s (G.M.vac v)).1 (hfix _ (hKV g hg) _ (hKW h hh))).symm
  refine ⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, JS, JT, ψL, ρ, ω, iV, iW, s, ?_, hs0, fun u hu => hvac s rfl u hu, hspan, rfl,
    hUV, hUW, hKV, hKW, fun g h m φ₁ _ => (hω (g, h) m φ₁).trans eq_comm⟩
  exact
    { unr := hunr
      odd := hodd
      intS := hiS
      intT := hiT
      hermS := hhS
      hermT := hhT
      delta := hδ
      psi_int := hpi
      psi_ne := hpn
      rho_zero := hρ0
      rho_mul := hρmul
      span := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, s, fun u hu => hvac s rfl u hu, rfl⟩
      norm := fun g h x => hnorm (g, h) x
      fix := by
        intro g h hg hh s' hs'
        obtain ⟨c, hc⟩ := huniq s' hs'
        have e : s' = c • s := Subtype.ext hc
        rw [e, map_smul, hωs g h hg hh] }

end PositivityTheory.Sph

end
end

section
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.KFinLoc

theorem locDataV' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hTr : IsTriple B G X om om') {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hv : v ∉ X.T) : LocData G.M' om' v := by
  obtain ⟨ϖ, σL, q, δ, JS, JT, ψL, κ, ιS, ιT, hC⟩ := GlobalTheory.T.exists_localChart_inertPlace_unitaryPair F E σ B a a' G X om om' hTr v w hw hv
  have hC' := hC
  obtain ⟨unr, hodd, intS, intT, hS, hT, hδ, p1, p2, -, -, -, -, -, hιS, hιT, hKS, hKT⟩ := hC'
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_inertPlace_local_heisenbergEndomorphism F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_localWeilHom_finitePlace F E σ B a a' G X om om' hTr v w hw hv σL JS JT ιS ιT hιS hιT
  obtain ⟨r0, rmul⟩ := GlobalTheory.T.inertPlace_localHeisenbergOperators_law F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨s, hs, hs0, hsv⟩ := GlobalTheory.T.inertPlace_vacuum_isLocalVacuum_chart F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  have hline := GlobalTheory.T.exists_smul_vac_eq_of_localVacuum_linearModel F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s
  have hspan := GlobalTheory.T.span_heisenbergTranslates_vacuum_inertPlace F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s hs
  have hnorm := GlobalTheory.T.inertPlace_weil_normalises_heisenberg F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ ω hω
  have hfix := GlobalTheory.T.inertPlace_integralUnitaryPoints_fix_vacuum F E σ B a a' G X om om' hTr v w hw hv ϖ σL q δ JS JT ψL κ ιS ιT hC ω hω s hs
  refine ⟨w.adicCompletion E, inferInstance, inferInstance, inferInstance, inferInstance, ϖ, σL, q, δ, JS, JT, ψL, ρ, ω,
    ιS, ιT, s, ⟨unr, hodd, intS, intT, hS, hT, hδ, p1, p2, r0, rmul, ?_, hnorm, ?_⟩, hs0, hsv, hspan, hs,
    hιS, hιT, hKS, hKT, fun g h m φ₁ hφ₁ => hω g h m φ₁ hφ₁⟩
  · rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono (by rintro _ ⟨x, rfl⟩; exact ⟨x, s, hsv, rfl⟩)
  · intro g h hg hh t ht
    obtain ⟨c, rfl⟩ := hline t hs ht
    rw [map_smul, hfix g h hg hh]

end PositivityTheory.Sph

end
end

section
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem gen_of {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
    {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}
    (hL : IsLocRep M ψ om v ω ρ) (hD : LocData M om v) :
    (∀ φ ∈ SB _, (∀ g ∈ KAt σ X v, ω (g, 1) φ = φ) →
      φ ∈ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)}) ∧
    (∀ φ ∈ SB _, (∀ k ∈ KAt σ W v, ω (1, k) φ = φ) →
      φ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)}) := by
  obtain ⟨L, _, _, _, _, ϖ, σL, q, δ, JS, JT, ψL, ρL, ωL, ιS, ιT, s, hP, hs0, hsv, hspan, hsvac,
    hιS, hιT, hKS, hKT, hLoc⟩ := hD
  obtain ⟨h1, h2⟩ := GlobalTheory.Hk3.howeUnram_holds _ _ _ _ _ _ _ _ _ _ _ _ _ hP s hs0 hsv hspan
  have key : ∀ g h m, (↑(ωL (g, h) m) : Fn F n d v) = ω (ιS g, ιT h) ↑m := by
    intro g h m
    have hφ₁ := hL.pres _ (hιS g) _ (hιT h) _ m.2
    exact (hLoc g h m _ hφ₁).1 ((hL.acts _ (hιS g) _ (hιT h) _ m.2 _).2 rfl)
  have hS1 : ιS 1 = 1 := map_one ιS
  have hT1 : ιT 1 = 1 := map_one ιT
  constructor
  · intro φ hφ hfix
    have hw := h1 ⟨φ, hφ⟩ fun g hg => by
      apply Subtype.ext
      rw [key, hT1]
      exact hfix _ (by rw [kAt_eq]; exact hKS g hg)
    have hmap := Submodule.mem_map_of_mem (f := Submodule.subtype _) hw
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq]
    exact ⟨ιT h, hιT h, by rw [Submodule.subtype_apply, key, hS1, hsvac]⟩
  · intro φ hφ hfix
    have hw := h2 ⟨φ, hφ⟩ fun h hh => by
      apply Subtype.ext
      rw [key, hS1]
      exact hfix _ (by rw [kAt_eq]; exact hKT h hh)
    have hmap := Submodule.mem_map_of_mem (f := Submodule.subtype _) hw
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq]
    exact ⟨ιS g, hιS g, by rw [Submodule.subtype_apply, key, hT1, hsvac]⟩

end PositivityTheory.Sph

end
end

section
noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem howeInert : HoweInert := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he
  obtain ⟨⟨w, hin⟩, hvT⟩ := inert_ctx hT he
  have ha : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.α u :=
    fun u hu => hT.chars.unrα u fun h => hvT (hu ▸ h)
  have hb : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.β u :=
    fun u hu => hT.chars.unrβ u fun h => hvT (hu ▸ h)
  refine ⟨fun ω ρ hL => ?_, fun ω ρ hL => ?_⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hb
      (fun u hu => unrAt_div (hb u hu) (ha u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' ha
      (fun u hu => unrAt_div (ha u hu) (hb u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV' hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩

end PositivityTheory.Sph

end
end
