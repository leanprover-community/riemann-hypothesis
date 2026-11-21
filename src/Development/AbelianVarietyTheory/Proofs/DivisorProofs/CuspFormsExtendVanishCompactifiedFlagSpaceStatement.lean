import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEquationHolomorphicLimit
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoPowMulExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorInvLePowHolomorphicOrbitPeriodBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameChartVectorsCompactFlagSpaceAffi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPoint

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem eq_zero_of_ger_dense {Y : Scheme.{0}} [IsReduced Y] {O V : Y.Opens} (hd : Dense (O : Set Y))
    (a : Γ(Y, V)) (h : ∀ z (hz : z ∈ V), z ∈ O → ger z hz a = 0) : a = 0 := by
  refine eq_zero_of_basicOpen_eq_bot a ?_
  by_contra hne
  obtain ⟨y, hy', hy⟩ := hd.inter_open_nonempty _ (Y.basicOpen a).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))
  have hm := Y.basicOpen_le _ hy'
  have hu : IsUnit (ger y hm a) := (Y.mem_basicOpen _ y hm).1 hy'
  rw [h y hm hy] at hu
  exact not_isUnit_zero hu

theorem exists_ext_of_dense_local : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} [IsReduced Y] (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (O : Y.Opens), Dense (O : Set Y) → ∀ (m : H0 p B O), (∀ y : Y, y ∉ O → ∃ (W : Y.Opens) (i : B.ι) (hi : W ≤ B.U i) (b : Γ(Y, W)), y ∈ W ∧ (∀ y' (h : y' ∈ W) (h' : y' ∈ O), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∉ O → ger y' h b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y')) → ∃ s : H0 p B ⊤, H0.restr le_top s = m ∧ ∀ y : Y, y ∉ O → ∀ (i : B.ι) (hi : y ∈ B.U i), H0.germ i y (memTop y) hi s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  intro k _ Y _ p B hB O hd m hloc
  choose W i hi b hyW hagree hmax using hloc
  let τ := B.ι ⊕ {y : Y // y ∉ O}
  let V : τ → Y.Opens := fun t => Sum.elim (fun j => O ⊓ B.U j) (fun y => W y.1 y.2) t
  let c : τ → B.ι := fun t => Sum.elim (fun j => j) (fun y => i y.1 y.2) t
  have hc : ∀ t, V t ≤ B.U (c t) := fun t => by
    rcases t with j | ⟨y, hy⟩
    · exact inf_le_right
    · exact hi y hy
  let u : ∀ t, Γ(Y, V t) := fun t => match t with
    | Sum.inl j => m.loc j
    | Sum.inr y => b y.1 y.2
  have key : ∀ t z (h : z ∈ V t) (hz : z ∈ O), ger z h (u t) = H0.germ (c t) z hz (hc t h) m := by
    intro t z h hz
    rcases t with j | ⟨y, hy⟩
    · rfl
    · exact hagree y hy z h hz
  have cover : ∀ y ∈ (⊤ : Y.Opens), ∃ t, y ∈ V t := fun y _ => by
    by_cases hy : y ∈ O
    · obtain ⟨j, hj⟩ := exists_chart hB y
      exact ⟨Sum.inl j, hy, hj⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, hyW y hy⟩
  have rule : ∀ y t t' (h : y ∈ V t) (h' : y ∈ V t'),
      ger y h (u t) = tr B y (c t) (c t') * ger y h' (u t') := by
    intro y t t' h h'
    have l₁ : V t ⊓ V t' ≤ V t := inf_le_left
    have l₂ : V t ⊓ V t' ≤ V t' := inf_le_right
    have l₃ : V t ⊓ V t' ≤ B.U (c t) ⊓ B.U (c t') := inf_le_inf (hc t) (hc t')
    have hz : ∀ z (hz : z ∈ V t ⊓ V t'), ger z hz (resG Y l₁ (u t) -
        resG Y l₃ (B.g (c t) (c t')).val * resG Y l₂ (u t')) =
        ger z (l₁ hz) (u t) - (tr B z (c t) (c t')).val * ger z (l₂ hz) (u t') := by
      intro z hz
      rw [map_sub, map_mul, ger_resG, ger_resG, ger_resG, val_tr B z (l₃ hz)]
    have e := eq_zero_of_ger_dense hd _ fun z hzV hzO => by
      rw [hz z hzV, key t z (l₁ hzV) hzO, key t' z (l₂ hzV) hzO, sub_eq_zero]
      exact H0.germ_change _ _ z hzO _ _ m
    have e' := congrArg (ger y (memInf h h')) e
    rw [hz y (memInf h h'), map_zero, sub_eq_zero] at e'
    exact e'
  obtain ⟨f, hf⟩ := H0.exists_of_germs (p := p) (O := ⊤) hB V c (fun _ => le_top) hc cover u rule
  refine ⟨f, ?_, ?_⟩
  · refine H0.ext_germ fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart hB y
    refine ⟨j, hj, ?_⟩
    rw [H0.germ_restr]
    exact (hf (Sum.inl j) y ⟨hy, hj⟩).trans rfl
  · intro y hy j hj
    rw [H0.germ_change j (i y hy) y _ hj (hi y hy (hyW y hy))]
    have e := hf (Sum.inr ⟨y, hy⟩) y (hyW y hy)
    refine (congrArg (fun x => (tr B y j (i y hy)).val * x) e).symm ▸ ?_
    exact Ideal.mul_mem_left _ _ (hmax y hy y (hyW y hy) hy)

end GlobalTheory.CompHS
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_extension_of_dense_local : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} [IsReduced Y] (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (O : Y.Opens), Dense (O : Set Y) → ∀ (m : H0 p B O), (∀ y : Y, y ∉ O → ∃ (W : Y.Opens) (i : B.ι) (hi : W ≤ B.U i) (b : Γ(Y, W)), y ∈ W ∧ (∀ y' (h : y' ∈ W) (h' : y' ∈ O), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∉ O → ger y' h b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y')) → ∃ s : H0 p B ⊤, H0.restr le_top s = m ∧ ∀ y : Y, y ∉ O → ∀ (i : B.ι) (hi : y ∈ B.U i), H0.germ i y (memTop y) hi s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  atlas_forward_decl GlobalTheory.CompHS.exists_ext_of_dense_local
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

namespace GlobalTheory.CompHS.ChartBd

theorem mem_iff_not_mem_basicOpen {X : Scheme.{0}} (C : Closeds X) (U : X.affineOpens) (g : Γ(X, U.1))
    (hD : (Scheme.IdealSheafData.vanishingIdeal C).ideal U = Ideal.span {g}) (x : X) (hx : x ∈ U.1) :
    x ∈ C ↔ x ∉ X.basicOpen g := by
  obtain ⟨s, rfl⟩ : x ∈ Set.range U.2.fromSpec := by rw [U.2.range_fromSpec]; exact hx
  have hcl : IsClosed (U.2.fromSpec ⁻¹' (C : Set X)) := C.isClosed.preimage U.2.fromSpec.continuous
  have hz : PrimeSpectrum.zeroLocus ((Scheme.IdealSheafData.vanishingIdeal C).ideal U : Set Γ(X, U.1)) =
      U.2.fromSpec ⁻¹' (C : Set X) := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hcl.closure_eq
  have h1 : U.2.fromSpec s ∈ X.basicOpen g ↔ s ∈ PrimeSpectrum.basicOpen g := by
    rw [← U.2.fromSpec_preimage_basicOpen]; rfl
  have h2 : U.2.fromSpec s ∈ C ↔ s ∈ U.2.fromSpec ⁻¹' (C : Set X) := Iff.rfl
  have h3 : s ∈ PrimeSpectrum.basicOpen g ↔ g ∉ (s : PrimeSpectrum Γ(X, U.1)).asIdeal :=
    PrimeSpectrum.mem_basicOpen g s
  have h4 : s ∈ U.2.fromSpec ⁻¹' (C : Set X) ↔ g ∈ (s : PrimeSpectrum Γ(X, U.1)).asIdeal := by
    rw [← hz, hD, PrimeSpectrum.zeroLocus_span]
    exact (PrimeSpectrum.mem_zeroLocus (s : PrimeSpectrum Γ(X, U.1)) {g}).trans Set.singleton_subset_iff
  exact h2.trans (h4.trans (not_not.symm.trans (h1.trans h3).not.symm))

end GlobalTheory.CompHS.ChartBd

namespace GlobalTheory.CompHS.ChartBd

theorem exists_chart_bd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw), IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, ∃ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (p : Γ(Y₀ TF.X Z, W)), y ∈ W ∧ W ≤ (L₀ TF.X Z la).U i ∧ IsDomain Γ(Y₀ TF.X Z, W) ∧ RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)).hom ∧ p ≠ 0 ∧ ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
  intro E _ _ _ H Dw l Xo c TF Z la hV y

  let q : Y₀ TF.X Z ⟶ TF.Y.X := inc₀ TF.X Z ≫ TF.X.π
  obtain ⟨-, U', hxU', n, f, J, -, hD⟩ := TF.snc (q y)
  let g : Γ(TF.Y.X, U'.1) := ∏ i ∈ J, f i
  have hZ : ∀ x ∈ U'.1, x ∈ (LogKS.interior TF.Y).compl ↔ x ∉ TF.Y.X.basicOpen g :=
    mem_iff_not_mem_basicOpen _ U' g hD

  have hs : Smooth (str₀ TF.X Z) := by
    haveI := hV.1
    exact SmoothOfRelativeDimension.smooth (GlobalTheory.FlagTan.dimFlag Dw) (str₀ TF.X Z)
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ _ hs
  have := GlobalTheory.IsNormalScheme.of_pred hn
  obtain ⟨W₁, hyW₁, hW₁⟩ := GlobalTheory.ModelChart.exists_open_isDomain (Y₀ TF.X Z) y
  obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ TF.X Z la) y
  let O : (Y₀ TF.X Z).Opens := W₁ ⊓ (L₀ TF.X Z la).U i ⊓ q ⁻¹ᵁ U'.1
  have hyO : y ∈ O := ⟨⟨hyW₁, hi⟩, hxU'⟩
  obtain ⟨W, hW, hyW, hWO⟩ := exists_isAffineOpen_mem_and_subset (U := O) (x := y) hyO
  have hWO' : W ≤ O := hWO
  have hWq : W ≤ q ⁻¹ᵁ U'.1 := hWO'.trans inf_le_right
  let p : Γ(Y₀ TF.X Z, W) := (Y₀ TF.X Z).presheaf.map (homOfLE hWq).op (q.app U'.1 g)
  have hbo : (Y₀ TF.X Z).basicOpen p = W ⊓ q ⁻¹ᵁ TF.Y.X.basicOpen g := by
    rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
  have key : ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
    intro y' hy'
    have e1 : y' ∈ bd₀ TF.X Z ↔ q y' ∈ (LogKS.interior TF.Y).compl := Iff.rfl
    have e2 : y' ∈ (Y₀ TF.X Z).basicOpen p ↔ q y' ∈ TF.Y.X.basicOpen g := by
      rw [hbo]; exact ⟨fun h => h.2, fun h => ⟨hy', h⟩⟩
    rw [e1, e2]
    exact hZ _ (hWq hy')
  refine ⟨W, hW, i, p, hyW, hWO'.trans (inf_le_left.trans inf_le_right), hW₁ W hyW (hWO'.trans (inf_le_left.trans inf_le_left)), ?_, ?_, key⟩
  · have hφ : Spec.map (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)) =
        (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z := Spec.map_preimage _
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp (by rw [hφ]; infer_instance)
  · intro hp0
    obtain ⟨y', hy'W, hy'U⟩ := (dense_U₀ TF.X Z).inter_open_nonempty W W.isOpen ⟨y, hyW⟩
    have h := (key y' hy'W).not.mp (not_not.mpr hy'U)
    rw [hp0, Scheme.basicOpen_zero] at h
    exact h (by simp)

end GlobalTheory.CompHS.ChartBd
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_affine_chart_boundary_zero_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw), IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, ∃ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (p : Γ(Y₀ TF.X Z, W)), y ∈ W ∧ W ≤ (L₀ TF.X Z la).U i ∧ IsDomain Γ(Y₀ TF.X Z, W) ∧ RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)).hom ∧ p ≠ 0 ∧ ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
  atlas_forward_decl GlobalTheory.CompHS.ChartBd.exists_chart_bd
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
open GlobalTheory.ShFam.BdArc GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.CompHS

theorem evalPt_spMap_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R]
    (ψ : Γ(X, U) →+* R) (h : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) ⁻¹ᵁ U) :
    GlobalTheory.TangentOrigin.evalPt (spMap ψ ≫ (show Sp Γ(X, U) ⟶ X from hU.fromSpec)) U h = ψ := by
  have := GlobalTheory.TangentOrigin.eq_spec_fromSpec hU _ h
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem exists_extension_of_arcZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ) (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)), ArcZero X Z la σ m → ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι) (p : Γ(Y₀ X Z, W)) (hi : W ≤ (L₀ X Z la).U i), IsDomain Γ(Y₀ X Z, W) → RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom → p ≠ 0 → (∀ y' ∈ W, (y' ∈ bd₀ X Z ↔ y' ∉ (Y₀ X Z).basicOpen p)) → ∃ b : Γ(Y₀ X Z, W), (∀ y' (h : y' ∈ W) (h' : y' ∈ U₀ X Z), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∈ bd₀ X Z → ger y' h b ∈ IsLocalRing.maximalIdeal ((Y₀ X Z).presheaf.stalk y') := by
  intro E _ _ _ H Dw l Xo c Y X Z la σ m hm W hW i p hi hdom hsm hp hbd
  have hPW : (Y₀ X Z).basicOpen p ≤ W := (Y₀ X Z).basicOpen_le p
  have hPU : (Y₀ X Z).basicOpen p ≤ U₀ X Z := fun y hy => by
    by_contra h
    exact (hbd y (hPW hy)).1 h hy
  have hPL : (Y₀ X Z).basicOpen p ≤ U₀ X Z ⊓ (L₀ X Z la).U i := le_inf hPU (hPW.trans hi)
  have := hW.isLocalization_basicOpen p
  obtain ⟨⟨a, _, M, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers p) (resG _ hPL (m.loc i))
  have e' : resG _ hPL (m.loc i) * resG _ hPW (p ^ M) = resG _ hPW a := e
  have hφ : Spec.map (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)) =
      (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z := Spec.map_preimage _
  letI : Algebra c.F Γ(Y₀ X Z, W) :=
    (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom.toAlgebra
  obtain ⟨b, hab, hb⟩ := exists_eq_mul_pow_of_tendsto_zero c.F Γ(Y₀ X Z, W) hsm σ p a M hp
    fun ψ r hψ hσ h0 h1 => by
      have hlim := hm W hW i hi ψ r hψ
        (fun u hu => by
          rw [← hσ u hu]
          exact (congrArg (spMap (ψ u) ≫ ·) hφ.symm).trans (Spec.map_comp _ _).symm)
        (fun s => (hbd _ (spMap_fromSpec_mem hW _ s)).2 fun h =>
          (spMap_fromSpec_mem_basicOpen hW _ p s).1 h h0)
        (fun u hu hu0 s _ => hPU ((spMap_fromSpec_mem_basicOpen hW _ p s).2 (h1 u hu hu0)))
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hψ.1
      filter_upwards [hlim ε hε, mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hub hu0
      have hWx : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ W :=
        fun s _ => spMap_fromSpec_mem hW _ s
      have hPx : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (Y₀ X Z).basicOpen p :=
        fun s _ => (spMap_fromSpec_mem_basicOpen hW _ p s).2 (h1 u hub hu0)
      have hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z :=
        fun s hs => hPU (hPx hs)
      have hiu : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ X Z la).U i :=
        fun s hs => hi (hWx hs)
      have hev := evalPt_spMap_fromSpec hW (ψ u) hWx
      have hpu : ψ u (p ^ M) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (h1 u hub hu0)
      have hmul : H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) i hO hiu m * ψ u (p ^ M) =
          ψ u a := by
        have e₁ := congrArg (GlobalTheory.TangentOrigin.evalPt _ _ hPx) e'
        rw [map_mul, GlobalTheory.TangentOrigin.evalPt_res _ hPL (GlobalTheory.TopForm.le_preimage_inf hO hiu) hPx,
          GlobalTheory.TangentOrigin.evalPt_res _ hPW hWx hPx, GlobalTheory.TangentOrigin.evalPt_res _ hPW hWx hPx, hev] at e₁
        exact e₁
      rw [dist_zero_right, ← hmul, mul_div_cancel_right₀ _ hpu]
      exact hu hO hiu
  refine ⟨b, fun y' h h' => ?_, fun y' h hy => ?_⟩
  · have hyP : y' ∈ (Y₀ X Z).basicOpen p := by
      by_contra hn
      exact (hbd y' h).2 hn h'
    have hunit : IsUnit (ger y' h p) := ((Y₀ X Z).mem_basicOpen p y' h).1 hyP
    have hunit' : IsUnit (ger y' h (p ^ M)) := by
      rw [map_pow]
      exact hunit.pow M
    have e₁ := congrArg (ger y' hyP) e'
    rw [map_mul, ger_resG, ger_resG, ger_resG, hab, map_mul] at e₁
    exact (hunit'.mul_right_cancel e₁).symm
  · have hyP : y' ∉ (Y₀ X Z).basicOpen p := (hbd y' h).1 hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨n, hn⟩ := hb
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hn
    refine hyP (((Y₀ X Z).mem_basicOpen p y' h).2 ?_)
    have h₂ := hu.pow n
    rw [← map_pow, ← hd, map_mul] at h₂
    exact isUnit_of_mul_isUnit_right h₂

end GlobalTheory.CompHS
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_of_arc_vanishing_smooth_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ) (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)), ArcZero X Z la σ m → ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι) (p : Γ(Y₀ X Z, W)) (hi : W ≤ (L₀ X Z la).U i), IsDomain Γ(Y₀ X Z, W) → RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom → p ≠ 0 → (∀ y' ∈ W, (y' ∈ bd₀ X Z ↔ y' ∉ (Y₀ X Z).basicOpen p)) → ∃ b : Γ(Y₀ X Z, W), (∀ y' (h : y' ∈ W) (h' : y' ∈ U₀ X Z), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∈ bd₀ X Z → ger y' h b ∈ IsLocalRing.maximalIdeal ((Y₀ X Z).presheaf.stalk y') := by
  first | exact @GlobalTheory.CompHS.exists_extension_of_arcZero | exact GlobalTheory.CompHS.exists_extension_of_arcZero | (intros; apply GlobalTheory.CompHS.exists_extension_of_arcZero <;> assumption)
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
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenFrame_chartVectors_compactFlagSpace_affine : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(Y₀ TF.X Z, W)), (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ → ∀ (k : TF.X.F.J) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (x' : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.Y.X) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x'), ∃ fr : GlobalTheory.ShFam.EigFrame TF.Y φ x', ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt k _ hz hx τ j)).left := by
  first | exact @GlobalTheory.CompHS.exists_eigFrame_vecAt₀ | exact GlobalTheory.CompHS.exists_eigFrame_vecAt₀ | (intros; apply GlobalTheory.CompHS.exists_eigFrame_vecAt₀ <;> assumption)
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
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_weightSection_flagSpace_eq_rule_at_framedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  first | exact @GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | exact GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | (intros; apply GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

namespace GlobalTheory.CompHS.ArcBridge

theorem arc_bridge : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι), W ≤ (L₀ TF.X Z la).U i → ∀ (ψ : ℂ → (Γ(Y₀ TF.X Z, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap σ) → (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ bd₀ TF.X Z) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) → ∃ (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (fr : EigFrame TF.Y φ (x ≫ genι TF.Y)) (y : ℂ → FrPt Xo c (CAt σ)), IsBdArc TF.Y σ φ x ψ r ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) ∧ ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (u : ℂ), u ∈ Metric.ball (0 : ℂ) r → u ≠ 0 → ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 (y u)) := by
  intro E _ _ _ H Dw l Xo c TF Z la σ hσ W hW i hWi ψ r hψ hs hin hout
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)
  let φ : c.F →+* Γ(Y₀ TF.X Z, W) := φ'.hom
  have hφ : (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ := hφ'.symm
  have hxc : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z ≫ TF.X.π) ≫ TF.Y.s = spMap φ ≫ spMap (RingHom.id c.F) := by
    have hid : spMap (RingHom.id c.F) = 𝟙 _ := by unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [hid, Category.comp_id, ← hφ]
    simp only [Category.assoc]
  let x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y := pullback.lift _ _ hxc
  have hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y := by
    rw [Category.assoc]; exact (pullback.lift_fst _ _ _).symm
  have hxs : x ≫ genStr TF.Y = spMap φ := pullback.lift_snd _ _ _
  have hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit) := fun s _ => by
    have h1 : (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) s ∈ W := hW.range_fromSpec.le ⟨s, rfl⟩
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.1 (hWi h1)
  obtain ⟨fr, hfr⟩ := GlobalTheory.T.exists_eigenFrame_chartVectors_compactFlagSpace_affine TF Z W hW φ hφ (i PUnit.unit) hz _ hx
  have hφu : ∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp φ = σ := fun u hu => by
    have h1 := hs u hu
    rw [hφ, spMap_comp'] at h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have key : ∀ (u : ℂ) (s : Sp ℂ), (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ U₀ TF.X Z ↔ (spMap (ψ u) ≫ x) s ∉ genBd TF.Y := by
    intro u s
    haveI := GlobalTheory.LogKS.isIso_fst TF.Y
    have e : (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ U₀ TF.X Z ↔ genι TF.Y ((spMap (ψ u) ≫ x) s) ∈ Set.range TF.Y.j := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hx]
      exact Iff.rfl
    rw [e, mem_genBd, not_not]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (genι TF.Y).isOpenEmbedding.injective (by rw [← ha]; rfl)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; rfl⟩
  have hb : IsBdArc TF.Y σ φ x ψ r := ⟨⟨hψ, hxs, hφu⟩, fun s => by
      have := hin s
      by_contra h
      exact this ((key 0 s).2 h), fun u hu h s => (key u s).1 (hout u hu h (Set.mem_univ s))⟩
  have hy' : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) r ∧ u ≠ 0 → ∃ y : FrPt Xo c (CAt σ), Matches fr (ψ u) y :=
    fun u hu => GlobalTheory.ShFam.BdArc.exists_matches E H Dw l Xo c c.F (RingHom.id c.F) TF.Y σ _ φ x fr (ψ u) hxs
      (hφu u hu.1) (hb.2.2 u hu.1 hu.2)
  have hr : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r ∧ ((r / 2 : ℝ) : ℂ) ≠ 0 := by
    have := hψ.1
    refine ⟨?_, by exact_mod_cast (half_pos this).ne'⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos this).le]
    exact half_lt_self this
  haveI : Nonempty (FrPt Xo c (CAt σ)) := ⟨(hy' _ hr).choose⟩
  choose! yy hyy using hy'
  refine ⟨φ, x, fr, yy, hb, fun u hu h => hyy u ⟨hu, h⟩, fun g u hu h hO hi => ?_⟩
  exact GlobalTheory.T.value_weightSection_flagSpace_eq_rule_at_framedPoint TF Z la σ W hW i φ x hx hz fr hfr (ψ u) (yy u) (hφu u hu) (hyy u ⟨hu, h⟩) g hO hi

end GlobalTheory.CompHS.ArcBridge
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenFrame_along_arc_flagSpaceChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι), W ≤ (L₀ TF.X Z la).U i → ∀ (ψ : ℂ → (Γ(Y₀ TF.X Z, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap σ) → (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ bd₀ TF.X Z) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) → ∃ (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (fr : EigFrame TF.Y φ (x ≫ genι TF.Y)) (y : ℂ → FrPt Xo c (CAt σ)), IsBdArc TF.Y σ φ x ψ r ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) ∧ ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (u : ℂ), u ∈ Metric.ball (0 : ℂ) r → u ≠ 0 → ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 (y u)) := by
  atlas_forward_decl GlobalTheory.CompHS.ArcBridge.arc_bridge
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

section ArcQuot

variable {Y : Scheme.{0}} {W : Y.Opens}

theorem arcPt_mem_basicOpen (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) (q : Γ(Y, W)) (s : Sp ℂ) :
    (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ Y.basicOpen q ↔ φ q ≠ 0 := by
  change (spMap φ) s ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen q ↔ _
  rw [hW.fromSpec_preimage_basicOpen q]
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change q ∉ (Ideal.comap φ s.asIdeal) ↔ _
  rw [hs]
  simp [Ideal.mem_comap]

theorem evalPt_arcPt (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ)
    (h : ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W) :
    GlobalTheory.TangentOrigin.evalPt (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) W h = φ := by
  have := GlobalTheory.TangentOrigin.eq_spec_fromSpec hW _ h
  dsimp only [spMap] at this
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem arcPt_top_le (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) :
    ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  change ⊤ ≤ spMap φ ⁻¹ᵁ (hW.fromSpec ⁻¹ᵁ W)
  rw [hW.fromSpec_preimage_self]
  exact le_rfl

theorem exists_punctured_ne_zero {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    {u₀ : ℂ} (hu₀ : u₀ ∈ Metric.ball (0 : ℂ) r) (h₀ : f u₀ ≠ 0) (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → f u ≠ 0 := by
  have ha := hf.analyticOnNhd Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  rcases (ha 0 h0).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exact absurd (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) r).isPreconnected h0 hz hu₀) h₀
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hz
    obtain ⟨ε, hε, hz⟩ := hz
    refine ⟨min ε r, lt_min hε hr, min_le_right _ _, fun u hu hu0 => hz u ?_ hu0⟩
    exact Metric.ball_subset_ball (min_le_left _ _) hu

end ArcQuot

end GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

theorem exists_quot_along_arc : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (m : H0 p B O) (W : Y.Opens) (hW : IsAffineOpen W) (i : B.ι), W ≤ B.U i → ∀ (ψ : ℂ → (Γ(Y, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) → ∃ (ρ : ℝ) (a b : Γ(Y, W)), 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u b ≠ 0 ∧ ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ B.U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) i hO hi m * ψ u b = ψ u a := by
  intro k _ Y p B O m W hW i hWi ψ r hψ hout
  obtain ⟨hr, hhol⟩ := hψ
  have hu₀ : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  have hu₀0 : ((r / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (half_pos hr).ne'
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hyO : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ O :=
    hout _ hu₀ hu₀0 (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hyW : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ W :=
    arcPt_top_le hW (ψ (r / 2 : ℝ)) (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨q, hqle, hqy⟩ := hW.exists_basicOpen_le (V := O ⊓ B.U i) ⟨_, hyO, hWi hyW⟩ hyW
  have hq0 : ψ (r / 2 : ℝ) q ≠ 0 := (arcPt_mem_basicOpen hW _ q s).1 hqy
  haveI := hW.isLocalization_basicOpen q
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj q (resG Y hqle (m.loc i))
  obtain ⟨ρ, hρ, hρr, hne⟩ := exists_punctured_ne_zero (hhol q) hu₀ hq0 hr
  refine ⟨ρ, a, q ^ n, hρ, hρr, fun u hu hu0 => ?_⟩
  have hqu : ψ u q ≠ 0 := hne u hu hu0
  refine ⟨by rw [map_pow]; exact pow_ne_zero _ hqu, fun hO hi => ?_⟩
  have hD : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ Y.basicOpen q :=
    fun s _ => (arcPt_mem_basicOpen hW (ψ u) q s).2 hqu
  have hWx := arcPt_top_le hW (ψ u)
  have e := congrArg (GlobalTheory.TangentOrigin.evalPt _ _ hD) hna
  have hres (z : Γ(Y, W)) : GlobalTheory.TangentOrigin.evalPt _ _ hD (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen q) z) = ψ u z := by
    exact (GlobalTheory.TangentOrigin.evalPt_res _ (Y.basicOpen_le q) hWx hD z).trans
      (DFunLike.congr_fun (evalPt_arcPt hW (ψ u) hWx) z)
  rw [map_mul, map_pow, hres, hres] at e
  rw [H0.val_apply, ← GlobalTheory.TangentOrigin.evalPt_res _ hqle _ hD, map_pow, e]

end GlobalTheory.Vanishing
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_quotient_along_arc : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (m : H0 p B O) (W : Y.Opens) (hW : IsAffineOpen W) (i : B.ι), W ≤ B.U i → ∀ (ψ : ℂ → (Γ(Y, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) → ∃ (ρ : ℝ) (a b : Γ(Y, W)), 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u b ≠ 0 ∧ ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ B.U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) i hO hi m * ψ u b = ψ u a := by
  atlas_forward_decl GlobalTheory.Vanishing.exists_quot_along_arc
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
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

noncomputable section

namespace GlobalTheory.KoecherArc

theorem tendsto_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N} (hσ : GoodEmb c σ) (hU : IsUnf U) (la : ∀ k, Wt (U.X k).Ψ N)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (la k) γ = 1) {e : Ix Dw → ℤ} (he : e none = 0) {g : Rul Xo c}
    (hg : g ∈ AllWt.secZ Xo c e) (hS : ∀ k, rdU U g k ∈ (U.X k).SS (la k)) {A : Type} [CommRing A] {φ : c.F →+* A}
    {x : Sp A ⟶ gen Z} (fr : EigFrame Z φ (x ≫ genι Z)) {ψ : ℂ → (A →+* ℂ)} {r : ℝ} {y : ℂ → FrPt Xo c (CAt σ)}
    (hb : IsBdArc Z σ φ x ψ r) (hm : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) (p q : A)
    (hpq : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u q ≠ 0 ∧ toC (evR Xo c g (y u)) * ψ u q = ψ u p) :
    Tendsto (fun u => toC (evR Xo c g (y u))) (𝓝[≠] 0) (𝓝 0) := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨k, T, M₀, γ₀, xx, hT, hO₀, hL⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc E H Dw l Xo c O β Z σ N U A φ x fr ψ r y hσ hU hb.1 hm
  obtain ⟨M, γ, hO, hγ⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two E N _ T M₀ γ₀ xx hO₀
  have hne : γ ≠ 1 := by
    rintro rfl
    obtain ⟨x₀, hx₀, x', h1, h2⟩ := GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain E N _ T M xx hO
    exact GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T xx hσ hU hb hm hL x₀ hx₀ x' h1 h2
  obtain ⟨ξ, c', hξ, hc', ht⟩ := GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short E N _ T M γ xx hO hγ hne
  obtain ⟨m, v, Lp, Lm, hlim⟩ :=
    GlobalTheory.T.exists_arcLift_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  have hper := GlobalTheory.T.eigenframe_specialization_uniform_bound E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound E N _ T M γ xx (la k) m v Lp Lm hO hlim hper
  have hp := tendsto_cusp (hS k) hO.2.2.2.1 hξ hc' ht hn
  have hsec := (hS k).1.1
  obtain ⟨hM, hΓ, hdiff, hdom, hperd⟩ := hO
  have hγd : ∀ w : ℂ, T < w.im → lact γ (xx w) ∈ (U.X k).dom := fun w hw =>
    GlobalTheory.MajInv.lact_mem_dom _ ((U.X k).Γ_stab γ hΓ) (hdom w hw)
  refine GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus (fun w => rdU U g k (xx w)) (fun _ => 0) _ (fun u => ψ u p) (fun u => ψ u q) T r M 1 1 hM
    one_pos (one_pow 1) hb.1.1.1 (hsec.1.comp hdiff hdom) (differentiableOn_const 0) (fun w hw => ?_) hp
    (hb.1.1.2 p) (hb.1.1.2 q) hpq
  obtain ⟨b, hb1, hb2, hb3⟩ := hperd w hw
  obtain ⟨h, hl⟩ := hL w hw
  refine ⟨?_, rfl, ?_⟩
  · simp only [hb3]
    rw [hsec.2.1 _ (hγd w hw) b hb1, hsec.2.2 γ hΓ _ (hdom w hw), hχ k γ hΓ]
    simp [ReciprocityTheory.ChartRestriction.G.FD.bchar, hb2]
  · rw [Complex.exp_zero, norm_one, mul_one]
    have rd : rdU U g k (xx w) = toC (evR Xo c g (U.un k ⟨xx w, h⟩)) := dif_pos h
    show ‖toC (evR Xo c g (y (eTwoPi w)))‖ = ‖rdU U g k (xx w)‖
    rw [rd, GlobalTheory.ShFam.KeyRel.evR_sameLie he hg hl]

theorem isBdArc_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z} {ψ : ℂ → (A →+* ℂ)} {r ρ : ℝ}
    (h : IsBdArc Z σ φ x ψ r) (hρ : 0 < ρ) (hρr : ρ ≤ r) : IsBdArc Z σ φ x ψ ρ :=
  ⟨⟨⟨hρ, fun a => (h.1.1.2 a).mono (Metric.ball_subset_ball hρr)⟩, h.1.2.1,
    fun u hu => h.1.2.2 u (Metric.ball_subset_ball hρr hu)⟩, h.2.1, fun u hu => h.2.2 u (Metric.ball_subset_ball hρr hu)⟩

end GlobalTheory.KoecherArc
end
end

section
noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)

theorem ext_of_arcZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ),
    IsVariety₀ TF.X Z → ∀ m : H0 (str₀ TF.X Z) (L₀ TF.X Z la) (U₀ TF.X Z), ArcZero TF.X Z la σ m →
      ∃ s ∈ vanBd TF.X Z la, H0.restr le_top s = m := by
  intro E _ _ _ H Dw l Xo c TF Z la σ hv m hm
  obtain ⟨s, hs, hz⟩ := GlobalTheory.T.exists_section_extension_of_dense_local (str₀ TF.X Z) (L₀ TF.X Z la) (isLB_L₀ TF.X Z la) (U₀ TF.X Z) (dense_U₀ TF.X Z) m
    fun y _ => by
      obtain ⟨W, hW, i, p, hyW, hi, hd, hsm, hp, hb⟩ := GlobalTheory.T.exists_smooth_affine_chart_boundary_zero_set E H Dw l Xo c TF Z la hv y
      obtain ⟨b, h1, h2⟩ := GlobalTheory.T.exists_extension_of_arc_vanishing_smooth_chart E H Dw l Xo c TF.Y TF.X Z la σ m hm W hW i p hi hd hsm hp hb
      exact ⟨W, i, hi, b, hyW, h1, fun y' h h' => h2 y' h h'⟩
  exact ⟨s, fun y hy i hi => hz y hy i hi, hs⟩

end GlobalTheory.CompHS

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal GlobalTheory.KoecherArc

theorem arcZero_cusp : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), ∀ σ : Y.d.c₂.F →+* ℂ, GoodEmb Y.d.c₂ σ → ∀ f : Cusp Z Y.U la, ArcZero TF.X Z la σ (cuspSec TF.X Z Y.U la f) := by
  intro D T j Y e o hY Z TF la σ hσ f
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hU := hY.unf σ hσ
  obtain ⟨hfW, -⟩ := Submodule.mem_inf.1 f.2
  obtain ⟨-, hhol⟩ := AllWt.mem_cuspW.1 hfW
  have hS := GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ (hhol σ hσ)
  have hχ := AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) (AllWt.wtOf _ la 0) (AllWt.even_wtOf la 0)
  have he : AllWt.exOf (T.Q.Dw j) la 0 none = 0 := by
    show (AllWt.wtOf (T.Q.Dw j) la 0).2 = 0
    rw [AllWt.wtOf_snd, mul_zero]
  intro W hW i hWi ψ r hψ hs hin hout ε hε
  obtain ⟨φ, x, fr, y, hb, hm, hval⟩ := GlobalTheory.T.exists_eigenFrame_along_arc_flagSpaceChart TF Z la σ hσ W hW i hWi ψ r hψ hs hin hout
  obtain ⟨ρ, p, q, hρ, hρr, hpq⟩ := GlobalTheory.T.exists_holomorphic_quotient_along_arc (cuspSec TF.X Z Y.U la f) W hW i hWi ψ r hψ hout
  have hi : ∀ u, ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ
      (L₀ TF.X Z la).U i := fun u s _ => hWi (hW.range_fromSpec.le ⟨_, rfl⟩)
  let g : AllWt.secZ Y.d.Xo₂ Y.d.c₂ (AllWt.exOf (T.Q.Dw j) la 0) := ⟨f.1, cusp_le_secZ Z Y.U la f.2⟩
  have hv : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u q ≠ 0 ∧ toC (evR _ _ g.1 (y u)) * ψ u q = ψ u p :=
    fun u hu h => by
      have hur : u ∈ Metric.ball (0 : ℂ) r := Metric.ball_subset_ball hρr hu
      refine ⟨(hpq u hu h).1, ?_⟩
      rw [← hval g u hur h (hout u hur h) (hi u)]
      exact (hpq u hu h).2 _ _
  have ht := tendsto_val TF.Y hσ hU _ hχ he g.2 hS fr (isBdArc_mono hb hρ hρr)
    (fun u hu h => hm u (Metric.ball_subset_ball hρr hu) h) p q hv
  have h2 : Tendsto (fun u => ‖toC (evR _ _ g.1 (y u))‖) (𝓝[≠] 0) (𝓝 0) := by simpa using ht.norm
  filter_upwards [h2.eventually (gt_mem_nhds hε), self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hρ)] with u h1 h3 h4 hO hi'
  rw [show cuspSec TF.X Z Y.U la f = sec₀ TF.X Z _ g from rfl,
    hval g u (Metric.ball_subset_ball hρr h4) h3 hO hi']
  exact h1

end GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

theorem GlobalTheory.CompHS.cusp_extends_comp : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), Extends TF.X Z Y.U la := by
  intro D T j Y e o hG hE Z TF la
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  intro f
  exact ext_of_arcZero _ _ _ _ _ _ TF Z la _ (GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hG.geo) _
    (arcZero_cusp D T j Y e o hG Z TF la _ hσ f)
end
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_extend_vanish_compactifiedFlagSpace : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j)), Extends TF.X Z Y.U la := by
  first | exact @GlobalTheory.CompHS.cusp_extends_comp | exact GlobalTheory.CompHS.cusp_extends_comp | (intros; apply GlobalTheory.CompHS.cusp_extends_comp <;> assumption)
end
