import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraph

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.ZH

theorem exists_cp_zhOut : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE, ∃ P : GlobalTheory.UU.CP Z.G, P.L = Z.L := by
  intro o Ω _ _ _ _ S ρS M U₀ EE hO Z
  obtain ⟨s, hs, hr⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric Z.L Z.sym

  have hrange : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hO.ne (Set.mem_univ w)
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hrange
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _

  have w' : pullback.fst Z.G.hom M.pt ≫ Z.G.hom = (((Over.pullback M.pt).obj Z.G).hom ≫ x) ≫ U₀.ι := by
    rw [Category.assoc, hx]; exact pullback.condition
  let φ' := Z.cart.1.lift (pullback.fst Z.G.hom M.pt) (((Over.pullback M.pt).obj Z.G).hom ≫ x) w'
  have n : IsGrpPullback ((Over.pullback M.pt).obj Z.G) Z.G (x ≫ U₀.ι) (φ' ≫ Z.φ) :=
    (isGrpPullback_pullback Z.G M.pt).congr hx.symm (Z.cart.1.lift_fst _ _ _).symm
  have h1 := IsGrpPullback.cancel Z.cart n (Z.cart.1.lift_snd _ _ _)
  have h2 := (IsGrpPullback.comp h1 (isGrpPullback_pullback ρS.P.A Z.u₀)).congr (Z.u₀_gen x hx) rfl
  have hA : IsAbelianScheme ((Over.pullback M.pt).obj Z.G) :=
    GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback ρS.P.isAb h2
  have h3 := GlobalTheory.ValueForm.surjective_cube_baseChange GlobalTheory.globalFns_holds M.pt hA (Iso.refl _)

  have := Z.semi.smooth
  have : Flat (G3 Z.G).hom := by
    show Flat (pullback.fst Z.G.hom (pullback.fst Z.G.hom Z.G.hom ≫ Z.G.hom) ≫ Z.G.hom)
    infer_instance
  have := M.sep
  have : QuasiCompact M.pt := by infer_instance
  have : IsSchemeTheoreticallyDominant M.pt := IsSchemeTheoreticallyDominant.of_isDominant M.pt
  have : IsSchemeTheoreticallyDominant (pullback.fst (G3 Z.G).hom M.pt) :=
    .of_isPullback (IsPullback.of_hasPullback (G3 Z.G).hom M.pt).flip
  have hi : ∀ U, Function.Injective ((pullback.fst (G3 Z.G).hom M.pt).app U).hom :=
    fun U => (pullback.fst (G3 Z.G).hom M.pt).app_injective U
  exact ⟨⟨Z.L, Z.cub, s, hs, hr, GlobalTheory.ValueForm.sym_cub_of_baseChange M.pt hi h3 Z.cub s hs hr⟩, rfl⟩

end GlobalTheory.ZH
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubicalStructure_semiAbelianExtension : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE, ∃ P : GlobalTheory.UU.CP Z.G, P.L = Z.L := by
  atlas_forward_decl GlobalTheory.ZH.exists_cp_zhOut
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.MumGen

theorem genFibre_pullback : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (e : Ω →+* FractionRing R₁) (M' : Modif R₁) (h : M'.S ⟶ M.Z), M'.gp ≫ h = spMap e ≫ M.pt → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ α : A₁.A.left ⟶ ((Over.pullback h).obj Z.G).left, IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α ∧ LBIso A₁.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) := by
  intro R₁ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z e M' h hh A₁ φ hcart hlb
  have hr : Set.range M.pt ⊆ (U₀ : Set M.Z) := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt (by rw [Scheme.Opens.range_ι]; exact hr)
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hy₀ : (spMap e ≫ x) ≫ Z.u₀ = spMap (e.comp S.R.val.toRingHom) := by
    rw [Category.assoc, Z.u₀_gen x hx, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  have w₁ : φ ≫ ρS.P.A.hom = (A₁.A.hom ≫ (spMap e ≫ x)) ≫ Z.u₀ := by
    rw [hcart.1.w, Category.assoc, hy₀]
  let lam : A₁.A.left ⟶ pullback ρS.P.A.hom Z.u₀ := pullback.lift φ (A₁.A.hom ≫ (spMap e ≫ x)) w₁
  have hlam : IsGrpPullback A₁.A ((Over.pullback Z.u₀).obj ρS.P.A) (spMap e ≫ x) lam :=
    IsGrpPullback.cancel (isGrpPullback_pullback ρS.P.A Z.u₀)
      (hcart.congr hy₀.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcomp : IsGrpPullback A₁.A Z.G ((spMap e ≫ x) ≫ U₀.ι) (lam ≫ Z.φ) := IsGrpPullback.comp hlam Z.cart
  have hyy : (spMap e ≫ x) ≫ U₀.ι = M'.gp ≫ h := by rw [Category.assoc, hx, hh]
  have w₂ : (lam ≫ Z.φ) ≫ Z.G.hom = (A₁.A.hom ≫ M'.gp) ≫ h := by
    rw [hcomp.1.w, hyy, Category.assoc]
  let α : A₁.A.left ⟶ pullback Z.G.hom h := pullback.lift (lam ≫ Z.φ) (A₁.A.hom ≫ M'.gp) w₂
  have hα : IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α :=
    IsGrpPullback.cancel (isGrpPullback_pullback Z.G h)
      (hcomp.congr hyy (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  refine ⟨α, hα, ?_⟩
  have hP := ρS.P.isLB
  have hZ := Z.L.isLB
  have i₁ : LBIso (ρS.P.L.pull φ) ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP lam (pullback.lift_fst _ _ _).symm
  have i₂ : LBIso ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam) ((Z.L.L.pull Z.φ).pull lam) :=
    GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm ⟨Z.w, Z.w_gen⟩) lam
  have i₃ : LBIso ((Z.L.L.pull Z.φ).pull lam) (Z.L.L.pull (lam ≫ Z.φ)) :=
    LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hZ lam rfl)
  have i₄ : LBIso (Z.L.L.pull (lam ≫ Z.φ)) ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hZ α (pullback.lift_fst _ _ _).symm
  have j₁ := LBIso.trans A₁.isLB (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) hlb i₁
  have j₂ := LBIso.trans A₁.isLB (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hZ _) _) j₁ i₂
  have j₃ := LBIso.trans A₁.isLB (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) j₂ i₃
  exact LBIso.trans A₁.isLB (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) j₃ i₄

end GlobalTheory.MumGen
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_pulled_semiAbelian_eq_abelianVariety : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (e : Ω →+* FractionRing R₁) (M' : Modif R₁) (h : M'.S ⟶ M.Z), M'.gp ≫ h = spMap e ≫ M.pt → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ α : A₁.A.left ⟶ ((Over.pullback h).obj Z.G).left, IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α ∧ LBIso A₁.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) := by
  atlas_forward_decl GlobalTheory.MumGen.genFibre_pullback
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum

theorem eq_gp_of_lies_over_bot {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} [IsReduced S] (π : S ⟶ Sp R)
    (gp : Sp (FractionRing R) ⟶ S) (hgp : gp ≫ π = jK R) (hd : IsDominant gp)
    {B : CommRingCat} (e₀ : Spec B ⟶ S) [he₀ : IsOpenImmersion e₀] (P : Spec B)
    (hP : π (e₀ P) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)) (k : Sp (FractionRing R)) : e₀ P = gp k := by
  have hsub : Set.range gp ⊆ Set.range e₀ := by
    obtain ⟨a, ha⟩ := hd.denseRange.exists_mem_open e₀.isOpenEmbedding.isOpen_range ⟨e₀ P, P, rfl⟩
    rintro _ ⟨x, rfl⟩
    rwa [Subsingleton.elim x a]
  set g' := IsOpenImmersion.lift e₀ gp hsub with hg'
  have hfac : g' ≫ e₀ = gp := IsOpenImmersion.lift_fac _ _ _
  set g := Spec.preimage g' with hg
  set ρ := Spec.preimage (e₀ ≫ π) with hρ
  have hgg : Spec.map g = g' := Spec.map_preimage _
  have hρρ : Spec.map ρ = e₀ ≫ π := Spec.map_preimage _
  have hcomp : ρ ≫ g = CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgg, hρρ, ← Category.assoc, hfac, hgp]
  have hcomp' : ∀ r, g.hom (ρ.hom r) = algebraMap R (FractionRing R) r := fun r => by
    have := congrArg (fun f => f.hom r) hcomp
    simpa using this
  have hden : DenseRange g' := by
    rw [denseRange_iff_closure_range, e₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      ← Set.range_comp]
    have : (e₀ ∘ g') = gp := by funext x; rw [← hfac]; rfl
    rw [this, hd.denseRange.closure_range, Set.preimage_univ]
  have hred : _root_.IsReduced B := by
    have : IsReduced (Spec B) := isReduced_of_isOpenImmersion e₀
    exact (affine_isReduced_iff B).1 this
  have hinj : Function.Injective g.hom := by
    have h1 : DenseRange (PrimeSpectrum.comap g.hom) := by rw [← hgg] at hden; exact hden
    have h2 := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.hom).1 h1
    rw [nilradical_eq_zero] at h2
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h2)
  have hPρ : Ideal.comap ρ.hom P.asIdeal = ⊥ := by
    have h2 : (Spec.map ρ) P = π (e₀ P) := by rw [hρρ]; rfl
    rw [hP] at h2
    exact congrArg PrimeSpectrum.asIdeal h2
  have hPb : P.asIdeal = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := R) (g.hom x)
    have hs0 : algebraMap R (FractionRing R) s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have h0 : ρ.hom s * x - ρ.hom a = 0 := by
      apply hinj
      rw [map_sub, map_mul, hcomp', hcomp', ← hxs, map_zero, mul_div_cancel₀ _ hs0, sub_self]
    have ha : a ∈ Ideal.comap ρ.hom P.asIdeal := by
      rw [Ideal.mem_comap, ← sub_eq_zero.1 h0]
      exact P.asIdeal.mul_mem_left _ hx
    rw [hPρ, Ideal.mem_bot] at ha
    have hx0 : g.hom x = 0 := by rw [← hxs, ha, map_zero, zero_div]
    rw [Ideal.mem_bot]
    exact hinj (by rw [hx0, map_zero])
  rw [← hfac]
  show e₀ P = e₀ (g' k)
  congr 1
  rw [← hgg]
  apply PrimeSpectrum.ext
  show P.asIdeal = Ideal.comap g.hom k.asIdeal
  have hk : k.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ k.isPrime
  rw [hPb, hk, Ideal.comap_bot_of_injective _ hinj]

theorem modif_pt_over_gen : ∀ (R : Type) [CommRing R] [IsDomain R] (M' : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (ξ : Sp W ⟶ M'.S), Function.Injective φ → ξ ≫ M'.π = spMap φ → ∃ (w : Sp W) (k : Sp (FractionRing R)), ξ w = M'.gp k := by
  intro R _ _ M' W _ _ φ ξ hφ hξ
  have : IsReduced M'.S := by have := M'.integral; infer_instance
  let w : Sp W := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W)
  let k : Sp (FractionRing R) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  refine ⟨w, k, ?_⟩
  let j := M'.S.affineCover.idx (ξ w)
  have hoi : IsOpenImmersion (M'.S.affineCover.f j) := M'.S.affineCover.map_prop j
  obtain ⟨P, hP⟩ := M'.S.affineCover.covers (ξ w)
  rw [← hP]
  refine eq_gp_of_lies_over_bot (he₀ := hoi) M'.π M'.gp M'.gp_π M'.dominant (M'.S.affineCover.f j) P ?_ k
  refine (congrArg M'.π hP).trans ?_
  have h1 : M'.π (ξ w) = (spMap φ) w := by rw [← hξ]; rfl
  rw [h1]
  apply PrimeSpectrum.ext
  show Ideal.comap φ ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ hφ

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericPoint_of_lies_over_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (M' : Modif R) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W) (ξ : Sp W ⟶ M'.S), Function.Injective φ → ξ ≫ M'.π = spMap φ → ∃ (w : Sp W) (k : Sp (FractionRing R)), ξ w = M'.gp k := by
  atlas_forward_decl GlobalTheory.Mum.modif_pt_over_gen
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.Mum.CoverPull

theorem pt_mem_abLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (w : Sp Ω), M.pt w ∈ abLocus Z.G := by
  intro o Ω _ _ _ _ S ρS M U₀ EE hO Z w
  haveI : IsProper ρS.P.A.hom := ρS.P.isAb.proper
  haveI : IsProper ((Over.pullback Z.u₀).obj ρS.P.A).hom := by
    show IsProper (pullback.snd ρS.P.A.hom Z.u₀)
    infer_instance
  refine GlobalTheory.range_subset_abLocus_of_isProper (G' := (Over.pullback Z.u₀).obj ρS.P.A) (f := U₀.ι) (φ := Z.φ) Z.semi Z.cart.1 ?_
  have hm : M.pt w ∈ U₀ := M.top_le_preimage_pt hO.ne (x := w) trivial
  exact ⟨⟨_, hm⟩, rfl⟩

theorem exists_unif_pullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (T : Scheme.{0}) (h : T ⟶ M.Z) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ξ : Sp W ⟶ T, ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty → ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (β : G'.left ⟶ ((Over.pullback h).obj Z.G).left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'), IsGrpPullback G' ((Over.pullback h).obj Z.G) ξ β ∧ LBIso U'.LG.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull β) := by
  intro o Ω _ _ _ S ρS M U₀ EE Z T h W _ _ _ hW ξ hab
  obtain ⟨hdvr, hc, hch⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  haveI := hch
  obtain ⟨D, A, U, hl, -⟩ := Z.unif W inferInstance inferInstance hc (ξ ≫ h) hab
  have hpt : (pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ) ≫ h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ ≫ h := Category.assoc _ _ _
  let β : pullback Z.G.hom (ξ ≫ h) ⟶ pullback Z.G.hom h :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ) (pullback.condition.trans hpt.symm)
  have hβf : β ≫ pullback.fst Z.G.hom h = pullback.fst Z.G.hom (ξ ≫ h) := pullback.lift_fst _ _ _
  have hβs : β ≫ pullback.snd Z.G.hom h = pullback.snd Z.G.hom (ξ ≫ h) ≫ ξ := pullback.lift_snd _ _ _
  refine ⟨(Over.pullback (ξ ≫ h)).obj Z.G, inferInstance, inferInstance, β, D, A, U, ?_, ?_⟩
  · refine (isGrpPullback_pullback Z.G h).cancel ?_ hβs
    exact (isGrpPullback_pullback Z.G (ξ ≫ h)).congr rfl hβf.symm
  · exact LBIso.trans U.LG.isLB (pull_isLB Z.L.isLB _) (pull_isLB (pull_isLB Z.L.isLB _) _) hl
      (GlobalTheory.GenSpread.lbIso_pull_pull Z.L.isLB β hβf.symm)

end GlobalTheory.Mum.CoverPull

namespace GlobalTheory.Mum

theorem exists_uCover_of_zhOut : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → GlobalTheory.ZH.ZHOut ρS M U₀ EE → ∀ (b : o →+* R₁) (e : Ω →+* FractionRing R₁), (∀ x : o, e (algebraMap o Ω x) = algebraMap R₁ (FractionRing R₁) (b x)) → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ C : UCover R₁, C.A = A₁ := by
  intro R₁ _ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z b e hb A₁ φ hcart hlb
  have hs : IsProper M.s := GlobalTheory.SpreadAb.isProper_of_isProjOver hO.proj
  have hy : (spMap e ≫ M.pt) ≫ M.s = jK R₁ ≫ spMap b := by
    rw [Category.assoc, M.pt_s, jK, spMap, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hb x
  obtain ⟨M', h, hgp, -⟩ := GlobalTheory.T.exists_modification_closure_of_graph R₁ o b M.Z M.s hs _ hy
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_cubicalStructure_semiAbelianExtension o Ω S ρS M U₀ EE hO Z
  have hw : pullback.fst Z.G.hom h ≫ Z.G.hom = ((Over.pullback h).obj Z.G).hom ≫ h := pullback.condition
  have mul : ∀ (T : Over M'.S) (x y : T ⟶ (Over.pullback h).obj Z.G), toBase hw (x * y) = toBase hw x * toBase hw y := by
    intro T x y
    exact Over.OverMorphism.ext ((isGrpPullback_pullback Z.G h).2 T x y (toBase hw x) (toBase hw y) rfl rfl).symm
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, -⟩ := GlobalTheory.UU.exists_isCPMap P₀ mul _ (pull_isLB P₀.L.isLB _) _
    (GlobalTheory.UU.pullIso_isGen P₀.L.isLB _)
  obtain ⟨α, hα, hαl⟩ := GlobalTheory.T.genericFibre_pulled_semiAbelian_eq_abelianVariety R₁ o Ω S ρS M U₀ EE hO Z e M' h hgp A₁ φ hcart hlb
  refine ⟨{ toModif := M'
            G := (Over.pullback h).obj Z.G
            semi := IsSemiAbelian.pullback _ _ Z.semi
            P := ⟨⟨_, rig, pull_isLB P₀.L.isLB _, hr⟩, c, s, h₁, h₂, h₃⟩
            A := A₁
            α := α
            α_cart := hα
            α_lb := by
              show LBIso A₁.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull α)
              rw [hP₀]; exact hαl
            trait := ?_ }, rfl⟩
  intro W _ _ _ hW φW ξ hφ hξ
  obtain ⟨w, k, hk⟩ := GlobalTheory.T.exists_genericPoint_of_lies_over_generic R₁ M' W φW ξ hφ hξ
  have hab : ((ξ ≫ h) ⁻¹' abLocus Z.G).Nonempty := by
    refine ⟨w, ?_⟩
    have e1 : (ξ ≫ h) w = M.pt ((spMap e) k) := by
      rw [Scheme.Hom.comp_apply, hk, ← Scheme.Hom.comp_apply, hgp, Scheme.Hom.comp_apply]
    show (ξ ≫ h) w ∈ abLocus Z.G
    rw [e1]
    exact CoverPull.pt_mem_abLocus o Ω S ρS M U₀ EE hO Z _
  obtain ⟨G', iG, cG, β, D', A', U', hβ, hl⟩ := CoverPull.exists_unif_pullback o Ω S ρS M U₀ EE Z M'.S h W hW ξ hab
  have hid : spMap (RingHom.id W) ≫ ξ = ξ := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine ⟨W, _, inferInstance, inferInstance, RingHom.id W, G', iG, cG, β, D', A', U', hW, Function.injective_id,
    RingHom.Finite.id W, hid.symm ▸ hβ, ?_⟩
  show LBIso U'.LG.L ((P₀.L.L.pull (pullback.fst Z.G.hom h)).pull β)
  rw [hP₀]; exact hl

end GlobalTheory.Mum
end
