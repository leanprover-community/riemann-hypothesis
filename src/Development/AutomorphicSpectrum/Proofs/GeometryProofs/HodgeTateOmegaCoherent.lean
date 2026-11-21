import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtEnd

theorem pullPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {A B : Over X} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) :
    ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.comp_mul, ih]

theorem homPow {X : Scheme.{0}} {G : Over X} [GrpObj G] {Z : Over X} (a : G ⟶ G) [IsMonHom a] (x : Z ⟶ G) (n : ℕ) :
    (x ^ n) ≫ a = (x ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero, CategoryTheory.MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.MonObj.mul_comp, ih]

theorem epiSp {Ω K : Type} [Field Ω] [Field K] (a : Ω →+* K) : Epi (spMap a) := by
  letI := a.toAlgebra
  haveI : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom a)) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : AlgebraicGeometry.Surjective (Spec.map (CommRingCat.ofHom a)) := by
    rw [AlgebraicGeometry.surjective_iff]
    intro y
    exact ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective _

theorem powDescend {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω K : Type} [Field Ω] [Field K]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {N : ℕ} (a : Ω →+* K)
    {g₀ : Over.mk ξ ⟶ G} {g : Over.mk (spMap a ≫ ξ) ⟶ G} (e : g.left = spMap a ≫ g₀.left) (hg : g ^ N = 1) :
    g₀ ^ N = 1 := by
  let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a)
  haveI : Epi ψ := Over.epi_of_epi_left ψ (hk := epiSp a)
  have hψ : ψ ≫ g₀ = g := Over.OverMorphism.ext (by simp [ψ, e])
  apply (cancel_epi ψ).mp
  rw [pullPow, hψ, hg, CategoryTheory.MonObj.comp_one]

theorem secVal_app {B : Type} [CommRing B] {Z Z' : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (φ : Z ⟶ Z')
    (W : Z'.Opens) (f : Γ(Z', W)) (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ W)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ W) :
    secVal x (φ ⁻¹ᵁ W) h ((φ.app W).hom f) = secVal (x ≫ φ) W h' f := by
  simp only [secVal, Scheme.Hom.comp_appLE]
  rfl

end GlobalTheory.CompanionTheory.Ar.HtEnd

open GlobalTheory.CompanionTheory.Ar.HtEnd in

theorem GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  intro X _ Ω _ _ ξ _ _ G _ _ L n _ hFT ep hW E _ _ M a _ A hA y y' hy hy' hyy' q w hH
  obtain ⟨hw, W, f, hη, P1, P2⟩ := hH
  have hExt : ∀ {e' : E} {v}, M.Extends q e' v → M.Extends q (A e') (v ≫ a) := by
    intro e' v hv
    refine ⟨?_, ?_⟩
    · have h1 := hv.1
      unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, CategoryTheory.MonObj.one_comp]
    · rw [hA e', Over.comp_left, hv.2]
      erw [Category.assoc]
  have hlat : ∀ e' ∈ M.lat q, A e' ∈ M.lat q := by
    intro e' he'
    have hle : M.lat q ≤ (M.lat q).comap (A.restrictScalars (regAt ξ q)) := by
      refine Submodule.span_le.mpr ?_
      rintro e'' ⟨v, hv⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      exact Submodule.subset_span ⟨v ≫ a, hExt hv⟩
    exact hle he'
  have hw' : ∀ e' ∈ M.lat q, w e' ∈ regAt ξ q := hw
  refine ⟨?_, a.left ⁻¹ᵁ W, (a.left.app W).hom f, ?_, ?_, ?_⟩
  · show ∀ e' ∈ M.lat q, (w ∘ₗ A) e' ∈ regAt ξ q
    intro e' he'
    exact hw' (A e') (hlat e' he')
  · have h1 : (η[G] ≫ a).left = (η[G]).left := by rw [IsMonHom.one_hom]
    show a.left ((η[G]).left q.1) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h1]
    exact hη
  · intro k _ _ i xk g c h hx hg hWe
    have h2 : ⊤ ≤ (g.left ≫ a.left) ⁻¹ᵁ W := h
    rw [secVal_app g.left a.left W f h h2]
    obtain ⟨g₀, hg₀⟩ := hFT k i g hg
    have hg₀n : g₀ ^ n = 1 := powDescend i hg₀ hg
    have hga : (g ≫ a) ^ n = 1 := by rw [← homPow, hg, CategoryTheory.MonObj.one_comp]
    have hg₀a : (g₀ ≫ a) ^ n = 1 := by rw [← homPow, hg₀n, CategoryTheory.MonObj.one_comp]
    have hc : (c : k) = i (ep y' g₀) := (hW.weil y' g₀ hy' hg₀n k i xk g c hx hg₀).mp hWe
    rw [hyy' g₀ hg₀n] at hc
    let xk0 : Over.mk (spMap i ≫ ξ) ⟶ G := Over.homMk (spMap i ≫ y.left)
    have hg' : (g ≫ a).left = spMap i ≫ (g₀ ≫ a).left := by
      rw [Over.comp_left, Over.comp_left, hg₀, Category.assoc]
    have hWa := (hW.weil y (g₀ ≫ a) hy hg₀a k i xk0 (g ≫ a) c rfl hg').mpr hc
    exact P1 k i xk0 (g ≫ a) c h2 rfl hga hWa
  · intro e' v hv h
    have h2 : ⊤ ≤ (v.left ≫ a.left) ⁻¹ᵁ W := h
    obtain ⟨r, hr, hE⟩ := P2 (A e') (v ≫ a) (hExt hv) h2
    refine ⟨r, hr, ?_⟩
    rw [LinearMap.comp_apply, secVal_app v.left a.left W f h h2]
    exact hE
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_weil_endomorphism : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ (y y' : Over.mk ξ ⟶ G), y ^ n = 1 → y' ^ n = 1 → (∀ g, g ^ n = 1 → e y' g = e y (g ≫ a)) → ∀ (q : Cpt ξ) (w : Module.Dual Ω E), M.IsHTAt L n y q w → M.IsHTAt L n y' q (w ∘ₗ A) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HTCoh

theorem htOm_coherent : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), (M.htOm L n).IsCohOn Set.univ ∧ ∀ q : Cpt ξ, (∀ u ∈ M.omLat q, n • u ∈ M.htOm L n q) ∧ M.htOm L n q ≤ M.omLat q ∧ ∀ (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ w ∈ M.htOm L n q, w ∘ₗ A ∈ M.htOm L n q := by
  intro X _ Ω _ _ ξ hgen hnorm G _ hsemi L n hn hfull e hW E _ _ M
  have gen : ∀ (q : Cpt ξ) (x : Over.mk ξ ⟶ G) (w : Module.Dual Ω E),
      x ^ n = 1 → M.IsHTAt L n x q w → w ∈ M.htOm L n q := by
    intro q x w hx hw
    simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
    exact Submodule.subset_span ⟨x, hx, hw⟩
  have mult : ∀ (q : Cpt ξ) (u : Module.Dual Ω E), u ∈ M.omLat q → n • u ∈ M.htOm L n q := by
    intro q u hu
    obtain ⟨⟨U, hqU, w, hw⟩, hdiff⟩ :=
      GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q
    have h1 : (1 : Over.mk ξ ⟶ G) ^ n = 1 := one_pow n
    have h0 : M.IsHTAt L n 1 q (w 1) := hw 1 h1 q hqU
    have h2 : M.IsHTAt L n 1 q (w 1 + n • u) := (hdiff 1 (w 1) _ h1 h0).2 ⟨u, hu, rfl⟩
    have hsub := Submodule.sub_mem _ (gen q 1 _ h1 h2) (gen q 1 _ h1 h0)
    rwa [add_sub_cancel_left] at hsub
  refine ⟨?_, fun q => ⟨fun u hu => mult q u hu, ?_, ?_⟩⟩
  · intro p _
    haveI := hsemi
    haveI : IsCommMonObj G := IsSemiAbelian.comm
    have hsm : AlgebraicGeometry.Smooth G.hom := IsSemiAbelian.smooth
    obtain ⟨-, hVB⟩ := GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ G E M hgen hsm
    obtain ⟨U2, hpU2, bv, -, hfr⟩ := hVB p (Set.mem_univ p)
    obtain ⟨⟨U1, hpU1, w, hw⟩, -⟩ :=
      GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M p
    haveI : Finite {x : Over.mk ξ ⟶ G // x ^ n = 1} := hW.finite
    obtain ⟨k, ⟨eqv⟩⟩ := Finite.exists_equiv_fin {x : Over.mk ξ ⟶ G // x ^ n = 1}
    let b1 : Fin k → Module.Dual Ω E := fun i => w (eqv.symm i).1
    let b2 : Fin (Module.finrank Ω E) → Module.Dual Ω E := fun j => n • bv j
    refine ⟨U1 ⊓ U2, TopologicalSpace.Opens.mem_inf.2 ⟨hpU1, hpU2⟩, k + Module.finrank Ω E, Fin.append b1 b2, ?_⟩
    intro q _ hqU
    have hq1 := (TopologicalSpace.Opens.mem_inf.1 hqU).1
    have hq2 := (TopologicalSpace.Opens.mem_inf.1 hqU).2
    obtain ⟨-, hframe⟩ := hfr q (Set.mem_univ q) hq2
    obtain ⟨-, hdiff⟩ := GlobalTheory.T.hodge_tate_weil_local X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q
    apply le_antisymm
    · simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
      refine Submodule.span_le.mpr ?_
      rintro w' ⟨y, hy, hyw'⟩
      have hwy : M.IsHTAt L n y q (w y) := hw y hy q hq1
      obtain ⟨u, hu, rfl⟩ := (hdiff y (w y) w' hy hwy).1 hyw'
      refine Submodule.add_mem _ ?_ ?_
      · apply Submodule.subset_span
        refine ⟨Fin.castAdd _ (eqv ⟨y, hy⟩), ?_⟩
        simp [b1, Fin.append_left]
      · rw [hframe] at hu
        clear hyw'
        induction hu using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨j, rfl⟩ := hv
          apply Submodule.subset_span
          exact ⟨Fin.natAdd k j, by simp [b2, Fin.append_right]⟩
        | zero => rw [smul_zero]; exact Submodule.zero_mem _
        | add v1 v2 _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
        | smul r v _ h => rw [smul_comm]; exact Submodule.smul_mem _ r h
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left]
        exact gen q _ _ (eqv.symm i).2 (hw _ (eqv.symm i).2 q hq1)
      | right j =>
        rw [Fin.append_right]
        exact mult q _ (by rw [hframe]; exact Submodule.subset_span ⟨j, rfl⟩)
  · simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, -, hw⟩
    exact hw.1
  · intro a _ A hA w hw
    simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm] at hw ⊢
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, hxw⟩ := hw
      obtain ⟨y', hy', hrel⟩ := hW.perfect (fun g => e x (g ≫ a)) (by
        intro g g' hg hg'
        show e x ((g * g') ≫ a) = e x (g ≫ a) * e x (g' ≫ a)
        rw [MonObj.mul_comp]
        exact hW.mul_right x _ _ hx (by rw [← MonObj.pow_comp, hg, MonObj.one_comp])
          (by rw [← MonObj.pow_comp, hg', MonObj.one_comp]))
      exact Submodule.subset_span ⟨y', hy', GlobalTheory.T.hodge_tate_weil_endomorphism X Ω ξ hgen hnorm G hsemi L n hn hfull e hW
        E M a A hA x y' hx hy' (fun g hg => (hrel g hg).symm) q w hxw⟩
    | zero => rw [LinearMap.zero_comp]; exact Submodule.zero_mem _
    | add w1 w2 _ _ h1 h2 => rw [LinearMap.add_comp]; exact Submodule.add_mem _ h1 h2
    | smul r w _ h =>
      have hc : (r • w) ∘ₗ A = r • (w ∘ₗ A) := LinearMap.ext fun _ => rfl
      rw [hc]; exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.Ar.HTCoh
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_omega_coherent : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), (M.htOm L n).IsCohOn Set.univ ∧ ∀ q : Cpt ξ, (∀ u ∈ M.omLat q, n • u ∈ M.htOm L n q) ∧ M.htOm L n q ≤ M.omLat q ∧ ∀ (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ w ∈ M.htOm L n q, w ∘ₗ A ∈ M.htOm L n q := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.HTCoh.htOm_coherent
end
