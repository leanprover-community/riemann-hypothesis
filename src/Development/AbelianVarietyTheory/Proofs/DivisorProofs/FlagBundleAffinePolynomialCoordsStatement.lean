import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackFrameSpanningFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackUnipotentFrameIsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagSpannedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCarriesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChartOfFlagBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsSameFrameIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialPointFactorsThroughChart

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_frame_spanning_flag : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens) (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, W)), (∀ a, Spans (fl a) W (pullCol π (eU a) hW (uniR fun s => n ⟨a, s⟩))) ∧ ∀ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(Y, V)), (∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n' ⟨a, s⟩))) → ∃ hVW : V ≤ W, ∀ s, Y.presheaf.map (homOfLE hVW).op (n s) = n' s := by
  first | exact @GlobalTheory.FlagCell.exists_cellLocus | exact GlobalTheory.FlagCell.exists_cellLocus | (intros; apply GlobalTheory.FlagCell.exists_cellLocus <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_unipotent_frame_isFrame : ∀ (X B : Scheme.{0}) (g : X ⟶ B) (E : B.Modules) (m : ℕ), IsVB E m → ∀ (U : B.Opens) (e : Fin m → Γ(E, U)), IsFrame e → ∀ (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (n : Low m → Γ(X, V)), IsFrame (pullCol g e hV (uniR n)) := by
  first | exact @GlobalTheory.UniColFrame.isFrame_pullCol_uniR | exact GlobalTheory.UniColFrame.isFrame_pullCol_uniR | (intros; apply GlobalTheory.UniColFrame.isFrame_pullCol_uniR <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_spanned_frame : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (v : Fin m → Γ(F, ⊤)), IsFrame v → ∃ fl : Vert.Flag F m, Spans fl ⊤ v := by
  first | exact @GlobalTheory.FlagCell.exists_flag_spans_of_frame | exact GlobalTheory.FlagCell.exists_flag_spans_of_frame | (intros; apply GlobalTheory.FlagCell.exists_flag_spans_of_frame <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_carries_base_change : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens) (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∀ (T : Scheme.{0}) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)), Carries π E r fl g' g w fl' → ∀ (V' : T.Opens) (hV' : V' ≤ g ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(T, V')), (∀ a, Spans (fl' a) V' (pullCol g (eU a) hV' (uniR fun s => n' ⟨a, s⟩))) → ∀ t ∈ V', ∃ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, V)), g' t ∈ V ∧ ∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩)) := by
  first | exact @GlobalTheory.FlagCell.CellOpen.spans_uniR_near_image | exact GlobalTheory.FlagCell.CellOpen.spans_uniR_near_image | (intros; apply GlobalTheory.FlagCell.CellOpen.spans_uniR_near_image <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_chart_of_flag_bundle : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (U : B.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (N : Type) (n : N → Γ(Y, W)), W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n)) ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U))) ≫ hU.fromSpec = W.ι ≫ π ∧ ∀ (h : ⊤ ≤ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))) ⁻¹ᵁ ⊤) (h' : ⊤ ≤ W.ι ⁻¹ᵁ W) (s : N), ((W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))).appLE ⊤ ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N Γ(B, U)))).inv.hom (MvPolynomial.X s)) = (W.ι.appLE W ⊤ h').hom (n s) := by
  first | exact @GlobalTheory.cellToSpec | exact GlobalTheory.cellToSpec | (intros; apply GlobalTheory.cellToSpec <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flags_same_frame_iso : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl₁ fl₂ : Vert.Flag F m) (v : Fin m → Γ(F, ⊤)), Spans fl₁ ⊤ v → Spans fl₂ ⊤ v → ∀ i, ∃ e : fl₁.F i ≅ fl₂.F i, e.hom ≫ fl₂.ι i = fl₁.ι i := by
  first | exact @GlobalTheory.FlagCell.steps_iso_of_spans_top | exact GlobalTheory.FlagCell.steps_iso_of_spans_top | (intros; apply GlobalTheory.FlagCell.steps_iso_of_spans_top <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_point_factors_through_chart : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (U : B.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (N : Type) (n : N → Γ(Y, W)) (ψ : Spec (CommRingCat.of (MvPolynomial N Γ(B, U))) ⟶ Y), ψ ≫ π = Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U))) ≫ hU.fromSpec → ∀ (hψ : ⊤ ≤ ψ ⁻¹ᵁ W), (∀ s, (ψ.appLE W ⊤ hψ).hom (n s) = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N Γ(B, U)))).inv.hom (MvPolynomial.X s)) → W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n)) ≫ ψ = W.ι → IsAffineOpen W ∧ Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) := by
  first | exact @GlobalTheory.FlagCell.isAffineOpen_and_bijective_of_section | exact GlobalTheory.FlagCell.isAffineOpen_and_bijective_of_section | (intros; apply GlobalTheory.FlagCell.isAffineOpen_and_bijective_of_section <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CellScheme

theorem cell_affine : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens), IsAffineOpen U → ∀ (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), IsAffineOpen W ∧ ∃ n : (Σ a, Low (r a)) → Γ(Y, W), Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) ∧ ∀ a, GlobalTheory.FlagCell.Spans (fl a) W (GlobalTheory.FlagCell.pullCol π (eU a) hW (GlobalTheory.FlagCell.uniR fun s => n ⟨a, s⟩)) := by
  intro B Y π ι _ r E fl hfl hE U hU eU heU
  obtain ⟨W, hW, n, hSp, hMax⟩ := GlobalTheory.T.exists_pullback_frame_spanning_flag B Y π ι r E fl hE U eU heU
  let A := CommRingCat.of (MvPolynomial (Σ a, Low (r a)) Γ(B, U))
  let g : Spec A ⟶ B := Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial (Σ a, Low (r a)) Γ(B, U))) ≫ hU.fromSpec
  have hgU : (⊤ : (Spec A).Opens) ≤ g ⁻¹ᵁ U := by
    simp [g, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  let n' : (Σ a, Low (r a)) → Γ(Spec A, ⊤) := fun s => (Scheme.ΓSpecIso A).inv.hom (MvPolynomial.X s)
  have hfr : ∀ a, IsFrame (pullCol g (eU a) hgU (uniR fun s => n' ⟨a, s⟩)) := fun a =>
    GlobalTheory.T.pullback_unipotent_frame_isFrame _ _ g (E a) (r a) (hE a) U (eU a) (heU a) ⊤ hgU _
  choose fl' hfl' using fun a => GlobalTheory.T.exists_flag_spanned_frame (Spec A) _ (r a) _ (hfr a)
  obtain ⟨ψ, ⟨w, hC⟩, -⟩ := hfl (Spec A) g fl'
  have hψ : (⊤ : (Spec A).Opens) ≤ ψ ⁻¹ᵁ W := by
    intro t _
    obtain ⟨V, hV, n₀, ht, hV'⟩ := GlobalTheory.T.flag_bundle_carries_base_change B Y π ι r E fl hE U eU heU (Spec A) ψ g w fl' hC ⊤ hgU n' hfl' t trivial
    obtain ⟨hVW, -⟩ := hMax V hV n₀ hV'
    exact hVW ht
  have hn : ∀ s, (ψ.appLE W ⊤ hψ).hom (n s) = (Scheme.ΓSpecIso A).inv.hom (MvPolynomial.X s) := by
    rintro ⟨a, s⟩
    have h1 := GlobalTheory.T.carried_flag_triangular_frame B Y (Spec A) π ι r E fl ψ g w fl' hC U a (eU a) W hW (uniR fun s => n ⟨a, s⟩) ⊤ hψ hgU (hSp a)
    rw [map_uniR] at h1
    exact congrFun (GlobalTheory.T.pullback_unipotent_frame_unique (Spec A) B g (E a) (r a) (hE a) U (eU a) (heU a) (fl' a) ⊤ hgU _ _ h1 (hfl' a)) s
  let φ : W.toScheme ⟶ Spec A := W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))
  obtain ⟨hφg, hφn⟩ := GlobalTheory.T.exists_polynomial_chart_of_flag_bundle B Y π U hU W hW _ n
  have hφg' : φ ≫ g = W.ι ≫ π := by simpa only [φ, g, Category.assoc] using hφg
  have hWU : (⊤ : W.toScheme.Opens) ≤ (W.ι ≫ π) ⁻¹ᵁ U := by
    intro x _
    exact hW x.2
  have h₁ : (⊤ : W.toScheme.Opens) ≤ φ ⁻¹ᵁ ⊤ := le_top.trans (by simp)
  have h₂ : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  have hφC : Carries g E r fl' φ (W.ι ≫ π) hφg' (carried π E r fl W.ι (W.ι ≫ π) rfl) := by
    intro a i
    have k₁ := GlobalTheory.T.carried_flag_triangular_frame _ _ _ g ι r E fl' φ (W.ι ≫ π) hφg' _ (carries_carried g E r fl' φ (W.ι ≫ π) hφg') U a (eU a) ⊤ hgU (uniR fun s => n' ⟨a, s⟩) ⊤ h₁ hWU (hfl' a)
    have k₂ := GlobalTheory.T.carried_flag_triangular_frame _ _ _ π ι r E fl W.ι (W.ι ≫ π) rfl _ (carries_carried π E r fl W.ι (W.ι ≫ π) rfl) U a (eU a) W hW (uniR fun s => n ⟨a, s⟩) ⊤ h₂ hWU (hSp a)
    rw [map_uniR] at k₁ k₂
    have e : (fun s => (φ.appLE ⊤ ⊤ h₁).hom (n' ⟨a, s⟩)) = fun s => (W.ι.appLE W ⊤ h₂).hom (n ⟨a, s⟩) :=
      funext fun s => hφn h₁ h₂ _
    rw [e] at k₁
    obtain ⟨e, he⟩ := GlobalTheory.T.flags_same_frame_iso _ _ _ _ _ _ k₁ k₂ i
    exact ⟨e, by simpa [carried, Vert.Flag.ofIso, Vert.Flag.pull] using he⟩
  have huniq : W.ι = φ ≫ ψ := (hfl W.toScheme (W.ι ≫ π) (carried π E r fl W.ι (W.ι ≫ π) rfl)).unique
    ⟨rfl, carries_carried π E r fl W.ι (W.ι ≫ π) rfl⟩
    ⟨by rw [Category.assoc, w, hφg'], carries_comp π E r fl ψ g w fl' φ (W.ι ≫ π) hφg' _ _ hC hφC⟩
  obtain ⟨hAff, hBij⟩ := GlobalTheory.T.polynomial_point_factors_through_chart B Y π U hU W hW _ n ψ w hψ hn (by simpa only [φ, Category.assoc] using huniq.symm)
  exact ⟨W, hW, hAff, n, hBij, hSp⟩

end GlobalTheory.CellScheme

end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_affine_polynomial_coords : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens), IsAffineOpen U → ∀ (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), IsAffineOpen W ∧ ∃ n : (Σ a, Low (r a)) → Γ(Y, W), Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) ∧ ∀ a, GlobalTheory.FlagCell.Spans (fl a) W (GlobalTheory.FlagCell.pullCol π (eU a) hW (GlobalTheory.FlagCell.uniR fun s => n ⟨a, s⟩)) := by
  first | exact @GlobalTheory.CellScheme.cell_affine | exact GlobalTheory.CellScheme.cell_affine | (intros; apply GlobalTheory.CellScheme.cell_affine <;> assumption)
end
