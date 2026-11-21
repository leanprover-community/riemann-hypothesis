import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnFibre

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_lift_with_principal_lineBundle : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (i : Y₀.left ⟶ Y.left) (l : (Y₀ ⊗ Y₀).left ⟶ (Y ⊗ Y).left) (Q : LB (Y ⊗ Y).left), IsAbelianScheme Y ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ IsSquare i l ∧ Q.IsLB ∧ GlobalTheory.AbDual.IsAdditive Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ LBIso (Q.pull l) (abelian₂ Y₀ L₀) := by
  first | exact @GlobalTheory.AltLift.exists_lift_lam | exact GlobalTheory.AltLift.exists_lift_lam | (intros; apply GlobalTheory.AltLift.exists_lift_lam <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 400000 in

theorem GlobalTheory.Mum.exists_lift_of_lam_lift_sq : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left) (l : (Y₀ ⊗ Y₀).left ⟶ (Y ⊗ Y).left), IsAbelianScheme Y₀ → IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → IsSquare i l → ∀ (L₀ : LB Y₀.left) (Q : LB (Y ⊗ Y).left), L₀.IsLB → Q.IsLB → GlobalTheory.AbDual.IsAdditive Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → LBIso (Q.pull l) (abelian₂ Y₀ L₀) → ∃ L : LB Y.left, L.IsLB ∧ LBIso L₀ (L.pull i) := by
  intro R R₀ _ _ _ _ _ π hπ hI Y₀ _ Y _ i l hY₀ hY hgp hsq L₀ Q hL₀ hQ _ _ hΛ
  haveI : IsCommMonObj Y₀ := hY₀.comm
  obtain ⟨L, hL, hiso⟩ := GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle R R₀ π hπ (by rw [hI]; rfl) Y Y₀ i l hY hgp hsq Q L₀
    hQ hL₀ (LBIso.symm hΛ)
  exact ⟨L, hL, LBIso.symm hiso⟩
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_lift_of_mumfordBundle_lift_sqZero : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left) (l : (Y₀ ⊗ Y₀).left ⟶ (Y ⊗ Y).left), IsAbelianScheme Y₀ → IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → IsSquare i l → ∀ (L₀ : LB Y₀.left) (Q : LB (Y ⊗ Y).left), L₀.IsLB → Q.IsLB → GlobalTheory.AbDual.IsAdditive Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → LBIso (Q.pull l) (abelian₂ Y₀ L₀) → ∃ L : LB Y.left, L.IsLB ∧ LBIso L₀ (L.pull i) := by
  atlas_forward_decl GlobalTheory.Mum.exists_lift_of_lam_lift_sq
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.KTrivSqZero

theorem exists_specializes_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀}
    (hπ : Function.Surjective π) (hJ : RingHom.ker π ≤ Ideal.jacobson ⊥) (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum R₀, p ⤳ PrimeSpectrum.comap π q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : RingHom.ker π ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem le_jacobson_of_sq_eq_bot {R : Type} [CommRing R] {J : Ideal R} (h : J ^ 2 = ⊥) : J ≤ Ideal.jacobson ⊥ := by
  intro x hx
  have hx2 : x ∈ (⊥ : Ideal R).radical := ⟨2, by
    have : x ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hx 2
    rw [h] at this
    exact this⟩
  exact Ideal.radical_le_jacobson hx2

theorem kTriv_lift : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  intro R R₀ _ _ _ π hπ hsq Y₀ _ Y _ i hY hi L₀ L hL₀ hL hA e hK
  have hJ := le_jacobson_of_sq_eq_bot hsq
  have key : ∀ p : Sp R, ∃ U : (Sp R).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj Y) (L.pull (pullback.fst Y.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes_of_surjective hπ hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hL hL₀ hY hA hi e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL' := fun p => pull_isLB hL (pullback.fst Y.hom (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U Y _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback Y (U p).ι) _ _ hL hL' (fun p => GlobalTheory.lbIso_refl (hL' p)) hY
    (fun p => GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hY (isGrpPullback_pullback Y (U p).ι)) hK

end GlobalTheory.KTrivSqZero
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelPolarisation_trivial_lifts_sqZero : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  atlas_forward_decl GlobalTheory.KTrivSqZero.kTriv_lift
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SqStep.exists_lift : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (L : LB Y.left) (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ LBIso L₀ (L.pull i) := by
  intro R R₀ _ _ _ _ _ π hπ hsq Y₀ _ hY₀ L₀ hL₀ hamp hK
  obtain ⟨Y, _, i, l, Q, hY, hpb, hsqr, hQ, a₁, a₂, hQi⟩ :=
    GlobalTheory.T.exists_abelianScheme_lift_with_principal_lineBundle R R₀ π hπ hsq Y₀ hY₀ L₀ hL₀ hamp hK
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.exists_lineBundle_lift_of_mumfordBundle_lift_sqZero R R₀ π hπ hsq Y₀ Y i l hY₀ hY hpb hsqr L₀ Q hL₀ hQ a₁ a₂ hQi
  haveI : Smooth Y.hom := hY.smooth
  have hamp' : RelAmple Y L :=
    GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ hsq Y Y₀ i hpb.1 inferInstance L L₀ hL hL₀ hLi hamp
  exact ⟨Y, inferInstance, L, i, hY, hL, hamp',
    GlobalTheory.T.kernelPolarisation_trivial_lifts_sqZero R R₀ π hπ hsq Y₀ Y i hY hpb L₀ L hL₀ hL hamp' hLi hK, hpb, hLi⟩
end
