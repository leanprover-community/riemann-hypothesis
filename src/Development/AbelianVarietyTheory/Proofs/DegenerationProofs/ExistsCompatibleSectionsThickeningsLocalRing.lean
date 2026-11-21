import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionsBasisBaseChangeH1Vanishing

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecLiftClosed

variable {X Z : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem gs_comb {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z) (W : X.Opens) (hz : r z ∈ W)
    (c : Fin n → R) (u : Fin n → Γ(X, W)) :
    gs r z W (∑ i, AbLaw.cst p W (c i) * u i) =
      ∑ i, gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) * gs r z W (u i) := by
  rw [gs_eq r z _ hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => (gs_eq r z _ hz _).symm.trans ((gs_mul r z _ hz _ _).trans ?_)
  exact congrArg (· * _) ((gs_res r z le_top hz _).trans (gs_pull r p z ⊤ trivial _))

theorem gs_const_comp (q : Z ⟶ Spec (CommRingCat.of R')) (h : R →+* R') (z : Z) (a : R) :
    gs (q ≫ Spec.map (CommRingCat.ofHom h)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (h a)) := by
  refine (gs_pull q (Spec.map (CommRingCat.ofHom h)) z ⊤ trivial _).symm.trans ?_
  exact congrArg (gs q z ⊤) (congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom h))).symm

def combSec {n : ℕ} (p : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (c : Fin n → R) (τ : Fin n → LB.Sec M) :
    LB.Sec M where
  f := fun k => ∑ i, AbLaw.cst p (M.U k) (c i) * (τ i).f k
  compat := fun i j => fn_ext fun y hy => by
    refine (gs_res _ y _ hy _).trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit _ y _ hy _) (gs_res _ y _ hy _))).symm)
    refine (gs_comb p (𝟙 X) y (M.U i) hy.1 _ _).trans (Eq.trans ?_ (congrArg (_ * ·)
      (gs_comb p (𝟙 X) y (M.U j) hy.2 _ _)).symm)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [GlobalTheory.SecPullIso.gs_sec_trans (τ a) (𝟙 X) y hy.1 hy.2, mul_left_comm]

theorem exists_lift : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∀ (A' : Type) [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)), M'.IsLB → w.IsGen → ∀ s' : LB.Sec M', ∃ s : LB.Sec M, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  intro A _ _ _ X f hf hp M hM K _ g₀ hg₀ X₀ π f₀ hπ M₀ w₀ hM₀ hw₀ hH A' _ g hg X' β f' hβ M' w hM' hw s'
  obtain ⟨n, τ, hτ⟩ := GlobalTheory.T.exists_sections_basis_baseChange_h1Vanishing A X f hf hp M hM K g₀ hg₀ X₀ π f₀ hπ M₀ w₀ hM₀ hw₀ hH
  choose τ' hτ' using fun i => (GlobalTheory.SecPullIso.section_pull X X' β M M' w hM hM' hw (τ i)).1.exists
  obtain ⟨c, hc, -⟩ := hτ A' g X' β f' hβ M' w τ' hM' hw hτ' s'
  choose d hd using fun i => hg (c i)
  refine ⟨combSec f d τ, fun z k k' hk hk' => ?_⟩
  refine (gs_comb f β z (M.U k) hk _ _).trans ?_
  rw [hc k', gs_comb f' (𝟙 X') z (M'.U k') hk', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hβ.w, gs_const_comp, hd, hτ' i z k k' hk hk', Category.id_comp, mul_left_comm]

end GlobalTheory.SecLiftClosed
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_lift_closed_baseChange_of_h1Vanishes : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∀ (A' : Type) [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)), M'.IsLB → w.IsGen → ∀ s' : LB.Sec M', ∃ s : LB.Sec M, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  atlas_forward_decl GlobalTheory.SecLiftClosed.exists_lift
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLifts

theorem exists_compatible_sections_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Flat (Y e).hom) → (∀ e, IsProjBy (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (K : Type) [Field K] (g₀ : R ⧸ I ^ (0 + 1) →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ (Y 0).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)) → ∀ (N₀ : LB X₀) (w₀ : LB.Iso N₀ ((N 0).pull π)), N₀.IsLB → w₀.IsGen → FirstCohomologyVanishes N₀ → ∀ s₀ : LB.Sec (N 0), ∃ s : ∀ e, LB.Sec (N e), s 0 = s₀ ∧ ∀ e, (∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' → gs (β e) z _ ((s (e + 1)).f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s e).f k')) := by
  intro R _ _ _ I hI Y β hβ hfl hpr N v hN K _ g₀ hg₀ X₀ π f₀ hπ N₀ w₀ hN₀ hw₀ h1 s₀
  have step : ∀ e (s' : LB.Sec (N e)), ∃ s : LB.Sec (N (e + 1)),
      ∀ z (k : (N (e + 1)).ι) (k' : (N e).ι), (β e) z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        gs (β e) z _ (s.f k) = (Geo.Tor.gw (v e) (𝟙 _) z k k').val * gs (𝟙 _) z _ (s'.f k') := by
    intro e s'
    obtain ⟨j, hj, w, hw⟩ := exists_closedFibre R I Y β hβ N v hN e
    have g := (isGen_iff _).1 hw
    have g' := (isGen_iff _).1 hw₀
    obtain ⟨w'', T⟩ := exists_comp (hN 0).1 w w₀ g g' (hN (e + 1)).1 hN₀
    have hne : I ^ (e + 1 + 1) ≠ ⊤ := fun h =>
      hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero _)))
    have : Nontrivial (R ⧸ I ^ (e + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
    have : IsLocalRing (R ⧸ I ^ (e + 1 + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have h := hπ.paste_horiz hj
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
    exact GlobalTheory.T.exists_section_lift_closed_baseChange_of_h1Vanishes (R ⧸ I ^ (e + 1 + 1)) _ (Y (e + 1)).hom (hfl (e + 1)) (hpr (e + 1)) (N (e + 1))
      (hN (e + 1)).1 K _ (hg₀.comp (Ideal.Quotient.factor_surjective _)) X₀ (π ≫ j) f₀ h N₀ w'' hN₀
      ((isGen_iff _).2 (T.pgen_comp (hN 0).1 g g')) h1 _ _ (Ideal.Quotient.factor_surjective _) _ (β e)
      (Y e).hom (hβ e) (N e) (v e) (hN e).1 (hN e).2 s'
  choose L hL using step
  exact ⟨fun e => Nat.rec (motive := fun e => LB.Sec (N e)) s₀ L e, rfl, fun e => hL e _⟩

end GlobalTheory.SecLifts
end
