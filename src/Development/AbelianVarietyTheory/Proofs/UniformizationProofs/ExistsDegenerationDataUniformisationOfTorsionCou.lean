import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenCubicUnitEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyAlgebraisationAbelianQuotientTower
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfFlatOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqTopOfClosedFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfIsWtZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinatesCompatOfTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtCoordOfTorusQuotient
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivTorusQuotientTowerAlgebraisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataFunctionalEquationDegreeOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifAssembly

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_mumfordTorusQuotientTower : (AllSet fun s => Nonempty (Tower s)) := by
  first | exact @GlobalTheory.UU.TowerEx.nonempty_tower | exact GlobalTheory.UU.TowerEx.nonempty_tower | (intros; apply GlobalTheory.UU.TowerEx.nonempty_tower <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_algebraisation_abelian_quotient_tower : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ t : Tower s, Nonempty t.Alg := by
  first | exact @GlobalTheory.AlgTower.nonempty_alg | exact GlobalTheory.AlgTower.nonempty_alg | (intros; apply GlobalTheory.AlgTower.nonempty_alg <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtTower

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] {s : HidaSetting V A G}

theorem exists_levels (t : Tower s) (χ : s.X) : ∃ (N : ∀ e, LB (t.l e).Q.B.left)
    (u : ∀ e, LB.Gen ((N e).pull (t.l e).Q.q.left)),
    ∀ e, (N e).IsLB ∧ (t.l e).Q.GenWt (N e) (u e) χ ∧ Triv (abelian₂ (t.l e).Q.B (N e)) := by
  have H : ∀ e, ∃ (N : LB (t.l e).Q.B.left) (u : LB.Gen (N.pull (t.l e).Q.q.left)),
      N.IsLB ∧ (t.l e).Q.GenWt N u χ ∧ Triv (abelian₂ (t.l e).Q.B N) := by
    intro e
    haveI := isLocalRing_quotient_pow V e
    obtain ⟨N, u, hN, hu, g, hg⟩ := GlobalTheory.exists_weight_bundle _ _ _ (t.l e).Q χ
    exact ⟨N, u, hN, hu, g, hg⟩
  choose N u h using H
  exact ⟨N, u, h⟩

theorem lbIso_succ (t : Tower s) {χ : s.X} (e : ℕ) {N : LB (t.l e).Q.B.left} {N' : LB (t.l (e + 1)).Q.B.left}
    {u : LB.Gen (N.pull (t.l e).Q.q.left)} {u' : LB.Gen (N'.pull (t.l (e + 1)).Q.q.left)} (hN : N.IsLB)
    (hN' : N'.IsLB) (hu : (t.l e).Q.GenWt N u χ) (hu' : (t.l (e + 1)).Q.GenWt N' u' χ) :
    LBIso N (N'.pull (t.β e)) := by
  obtain ⟨v, hv⟩ := exists_genWt_pull (t.l (e + 1)).Q (t.l e).Q
    (isGrpPullback_thickMap (IsLocalRing.maximalIdeal V) G e) (t.tor e) (t.β_q e) hu'
  exact lbIso_of_genWt _ _ _ (t.l e).Q N (N'.pull (t.β e)) u v χ hN (pull_isLB hN' _) hu hv

theorem isPullback_of_isCPPullback {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B']
    [GrpObj B] [IsCommMonObj B] {M' : CP B'} {M : CP B} {f : S' ⟶ S} {β : B'.left ⟶ B.left}
    (h : IsCPPullback M' M f β) : IsPullback β B'.hom B.hom f := by
  obtain ⟨hg, -⟩ := h
  exact hg.1

theorem exists_alg_of_lbIso {V : Type} [CommRing V] [IsDomain V] [i : IsLocalRing V] (hV : CDVR V)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e))
    (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left) (hp : IsProjBy B.hom) (hf : Flat B.hom)
    (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e))
    (hc : ∀ e, β e ≫ b (e + 1) = b e) (N : ∀ e, LB (Y e).left) (hN : ∀ e, (N e).IsLB)
    (h : ∀ e, LBIso (N e) ((N (e + 1)).pull (β e))) :
    ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  haveI : IsDiscreteValuationRing V := hV.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hV.2.1
  choose w hw using h
  exact GlobalTheory.LBAlg.exists_lineBundle_of_thickenings V Y β hβ B b hp hf hb hc N w fun e => ⟨hN e, hw e⟩

theorem isPullback_β (t : Tower s) (e : ℕ) : IsPullback (t.β e) (t.l e).Q.B.hom (t.l (e + 1)).Q.B.hom
    (thickTrans V (IsLocalRing.maximalIdeal V) e) := isPullback_of_isCPPullback (t.β_pb e)

theorem isPullback_b {t : Tower s} (a : t.Alg) (e : ℕ) : IsPullback (a.b e) (t.l e).Q.B.hom a.B.hom
    (thick V (IsLocalRing.maximalIdeal V) e) := isPullback_of_isCPPullback (a.b_pb e)

theorem flat_alg {t : Tower s} (a : t.Alg) : Flat a.B.hom := by
  haveI := a.isAb.smooth
  infer_instance

theorem exists_alg {t : Tower s} (a : t.Alg) (N : ∀ e, LB (t.l e).Q.B.left) (hN : ∀ e, (N e).IsLB)
    (h : ∀ e, LBIso (N e) ((N (e + 1)).pull (t.β e))) :
    ∃ O : LB a.B.left, O.IsLB ∧ ∀ e, LBIso (N e) (O.pull (a.b e)) := by
  have hp : IsProjBy a.B.hom := isProjBy_of_relAmple a.B a.M.L.3 a.ample
  exact exists_alg_of_lbIso s.cdvr (fun e => (t.l e).Q.B) t.β (isPullback_β t) a.B a.b hp (flat_alg a)
    (isPullback_b a) a.b_β N hN h

theorem triv_lam_alg (hG : GlobalFnsSt) {t : Tower s} (a : t.Alg) {N : ∀ e, LB (t.l e).Q.B.left}
    (hN : ∀ e, (N e).IsLB) {O : LB a.B.left} (hO : O.IsLB) (hi : ∀ e, LBIso (N e) (O.pull (a.b e)))
    (h : ∀ e, Triv (abelian₂ (t.l e).Q.B (N e))) : Triv (abelian₂ a.B O) := by
  haveI : IsDiscreteValuationRing V := s.cdvr.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := s.cdvr.2.1
  have hp : IsProjBy a.B.hom := isProjBy_of_relAmple a.B a.M.L.3 a.ample
  refine triv_lam_of_levels hG a.isAb hp hO fun e => ?_
  obtain ⟨hb, -⟩ := a.b_pb e
  exact triv_lam_pull hb hO (hN e) (hi e) (h e) (fstG (IsLocalRing.maximalIdeal V) e (a.B ⊗ a.B))

theorem exists_weight_bundle_alg : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ : s.X), ∃ O : LB a.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ a.B O), u.IsGen) ∧ ∀ e, ∃ u : LB.Gen (O.pull ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ := by
  intro hL V _ _ _ A G _ _ s t a χ
  obtain ⟨N, u, h⟩ := exists_levels t χ
  have hiso : ∀ e, LBIso (N e) ((N (e + 1)).pull (t.β e)) := fun e =>
    lbIso_succ t e (h e).1 (h (e + 1)).1 (h e).2.1 (h (e + 1)).2.1
  obtain ⟨O, hO, hi⟩ := exists_alg a N (fun e => (h e).1) hiso
  have hT := triv_lam_alg hL.globalFns a (fun e => (h e).1) hO hi (fun e => (h e).2.2)
  refine ⟨O, hO, hT, fun e => ?_⟩
  obtain ⟨v, hv⟩ := exists_genWt_of_lbIso (t.l e).Q (h e).1 (pull_isLB hO _) (hi e) (h e).2.1
  exact exists_gen_comp (t.l e).Q (a.b e) hv

end GlobalTheory.WtTower
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightBundle_torusQuotientTower_algebraisation : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ : s.X), ∃ O : LB a.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ a.B O), u.IsGen) ∧ ∀ e, ∃ u : LB.Gen (O.pull ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ := by
  atlas_forward_decl GlobalTheory.WtTower.exists_weight_bundle_alg
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WtPoint

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {Y : Scheme.{0}} {f : G.left ⟶ Y}

theorem gm_gen_pull {Z W : Scheme.{0}} {F : Z ⟶ Y} {M : LB Y} {t : LB.Gen (M.pull F)} (ht : t.IsGen) (r : W ⟶ Z) (y : W)
    {j j' : M.ι} (hj : F (r y) ∈ M.U j) (hj' : F (r y) ∈ M.U j') :
    gm r y ((M.pull F).U fun _ => j) (t.s fun _ => j) =
      gm (r ≫ F) y (M.U j ⊓ M.U j') (M.g j j') * gm r y ((M.pull F).U fun _ => j') (t.s fun _ => j') := by
  have hm : r y ∈ (M.pull F).U (fun _ => j) ⊓ (M.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  have e := congrArg (gm r y _) (ht (fun _ => j) (fun _ => j'))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g M F r y _ _ hm.1 hm.2] at e
  exact e

theorem gm_iso {W : Scheme.{0}} {O N : LB Y} {w : LB.Iso O N} (hw : w.IsGen) (r : W ⟶ Y) (y : W)
    {j j' : N.ι} {k k' : O.ι} (h : r y ∈ N.U j ⊓ O.U k) (h' : r y ∈ N.U j' ⊓ O.U k') :
    gm r y (N.U j ⊓ O.U k) (w.s (j, k)) =
      gm r y (N.U j ⊓ N.U j') (N.g j j') * (gm r y (O.U k ⊓ O.U k') (O.g k k'))⁻¹ *
        gm r y (N.U j' ⊓ O.U k') (w.s (j', k')) := by
  have hm : r y ∈ N.U j ⊓ O.U k ⊓ (N.U j' ⊓ O.U k') := ⟨h, h'⟩
  exact (gm_res r y _ hm _).symm.trans ((congrArg (gm r y _) (hw (j, k) (j', k'))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div O N r y (j, k) (j', k') hm) (gm_res r y _ hm _))))

theorem exists_gen_of_iso
    (hf : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ f = g.left ≫ f)
    {O N : LB Y} (hO : O.IsLB) (hN : N.IsLB) (h : LBIso O N) {χ : X} (u : LB.Gen (O.pull f)) (hu : u.IsGen)
    (hχ : ∀ k, IsWt i _ (u.s k).val χ) :
    ∃ v : LB.Gen (N.pull f), v.IsGen ∧ ∀ j, IsWt i _ (v.s j).val χ := by
  obtain ⟨w, hw⟩ := h
  have tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (j j' : N.ι) (k k' : O.ι), f (r z) ∈ N.U j ⊓ O.U k →
      f (r z) ∈ N.U j' ⊓ O.U k' →
      gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) =
        gm (r ≫ f) z (N.U j ⊓ N.U j') (N.g j j') *
          (gm (r ≫ f) z (N.U j' ⊓ O.U k') (w.s (j', k')) * gm r z ((O.pull f).U fun _ => k') (u.s fun _ => k')) := by
    intro Z r z j j' k k' h h'
    rw [gm_iso hw (r ≫ f) z h h', gm_gen_pull hu r z h.2 h'.2, _root_.mul_assoc, _root_.mul_assoc,
      mul_left_comm (gm (r ≫ f) z (N.U j' ⊓ O.U k') (w.s (j', k'))), inv_mul_cancel_left]
  have glue : ∀ j : N.ι, ∃ s : Γ(G.left, (N.pull f).U fun _ => j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (k : O.ι),
      f (r z) ∈ N.U j ⊓ O.U k → gm r z _ s =
        gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) := by
    intro j
    have l₀ : ∀ k, f ⁻¹ᵁ (N.U j ⊓ O.U k) ≤ (N.pull f).U fun _ => j := fun k x hx => mem_pull.2 hx.1
    have l₁ : ∀ k, f ⁻¹ᵁ (N.U j ⊓ O.U k) ≤ (O.pull f).U fun _ => k := fun k x hx => mem_pull.2 hx.2
    obtain ⟨a, ha⟩ : ∃ a : ∀ k, Γ(G.left, f ⁻¹ᵁ (N.U j ⊓ O.U k))ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (k : O.ι),
        f (r z) ∈ N.U j ⊓ O.U k → gm r z _ (a k) =
          gm (r ≫ f) z (N.U j ⊓ O.U k) (w.s (j, k)) * gm r z ((O.pull f).U fun _ => k) (u.s fun _ => k) :=
      ⟨fun k => pullU f (N.U j ⊓ O.U k) (w.s (j, k)) * res (l₁ k) (u.s fun _ => k), fun Z r z k hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull r f z _ hz _) (gm_res r z (l₁ k) hz _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ _ l₀ (fun x hx => by
        obtain ⟨k, hk⟩ := exists_chart hO (f x)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_pull.1 hx, hk⟩) a (fun k k' x hx => by
        rw [ha _ (𝟙 _) x k hx.1, ha _ (𝟙 _) x k' hx.2, tr _ (𝟙 _) x j j k k' hx.1 hx.2,
          gm_self hN (𝟙 _ ≫ f) x hx.1.1, _root_.one_mul])
    exact ⟨s, fun Z r z k hz => (gm_res r z (l₀ k) hz s).symm.trans
      ((congrArg (gm r z (f ⁻¹ᵁ (N.U j ⊓ O.U k))) (hs k)).trans (ha Z r z k hz))⟩
  choose s hs using glue
  refine ⟨⟨fun J => s (J PUnit.unit)⟩, fun J J' => unit_ext fun y hy => ?_, fun J => isWt_of_gm _ _ ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hO (f y)
    have h₁ := mem_pull.1 hy.1
    have h₂ := mem_pull.1 hy.2
    exact ((gm_res _ y _ hy _).trans ((hs _ _ (𝟙 _) y k ⟨h₁, hk⟩).trans
      (tr _ (𝟙 _) y _ _ k k ⟨h₁, hk⟩ ⟨h₂, hk⟩))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (gm_pull_g N f (𝟙 _) y J J' hy.1 hy.2) ((gm_res _ y _ hy _).trans (hs _ _ (𝟙 _) y k ⟨h₂, hk⟩)))).symm
  · intro Z t g z hz
    obtain ⟨k, hk⟩ := exists_chart hO (f (g.left z))
    have h₂ : f (g.left z) ∈ N.U (J PUnit.unit) ⊓ O.U k := ⟨mem_pull.1 hz, hk⟩
    have h₁ : f (((t ≫ i) * g).left z) ∈ N.U (J PUnit.unit) ⊓ O.U k :=
      (congrArg (fun m : Z.left ⟶ Y => m z ∈ N.U (J PUnit.unit) ⊓ O.U k) (hf Z t g)).mpr h₂
    refine (hs _ _ _ z k h₁).trans (Eq.trans ?_ (congrArg (_ * ·) (hs _ _ _ z k h₂)).symm)
    rw [hf, WtBundle.gm_of_isWt (hχ fun _ => k) t g z (mem_pull.2 h₁.2) (mem_pull.2 h₂.2), gm_charUnit,
      mul_left_comm]

theorem exists_gen_neg {B : Scheme.{0}} {L : LB B} {K : Type} [Fintype K] {φ : K → (Y ⟶ B)} {ε ε' : K → ℤ}
    (hε : ∀ k, ε' k = - ε k) {χ : X} (u : LB.Gen ((LB.LinComb L φ ε).pull f)) (hu : u.IsGen)
    (hχ : ∀ k, IsWt i _ (u.s k).val (-χ)) :
    ∃ v : LB.Gen ((LB.LinComb L φ ε').pull f), v.IsGen ∧ ∀ j, IsWt i _ (v.s j).val χ := by
  refine ⟨⟨fun J => (u.s J)⁻¹⟩, fun J J' => ?_, fun J => ?_⟩
  · refine unit_ext fun y hy => ?_
    have h₁ : f y ∈ LB.wchart L φ (J PUnit.unit) := mem_pull.1 hy.1
    have h₂ : f y ∈ LB.wchart L φ (J' PUnit.unit) := mem_pull.1 hy.2
    have e : gm (𝟙 _ ≫ f) y _ ((LB.LinComb L φ ε').g (J PUnit.unit) (J' PUnit.unit)) =
        (gm (𝟙 _ ≫ f) y _ ((LB.LinComb L φ ε).g (J PUnit.unit) (J' PUnit.unit)))⁻¹ := by
      refine (gm_linComb L φ ε' (𝟙 _ ≫ f) y _ _ h₁ h₂).trans (Eq.trans ?_
        (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 _ ≫ f) y _ _ h₁ h₂)).symm)
      simp only [hε, zpow_neg, Finset.prod_inv_distrib]
    exact ((gm_res _ y _ hy _).trans ((map_inv _ _).trans ((congrArg (·⁻¹) (gm_gen_pull hu (𝟙 _) y h₁ h₂)).trans
      (mul_inv _ _)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_pull_g (LB.LinComb L φ ε') f (𝟙 _) y J J' hy.1 hy.2).trans e)
        ((gm_res _ y _ hy _).trans (map_inv _ _)))).symm
  · have := (hχ J).inv
    rwa [neg_neg] at this

theorem sym_of_cp [IsCommMonObj G] (P : CP G) : Out.Sym G P.L.L := fun _ => by
  obtain ⟨t, ht, -⟩ := exists_gen P.L.isLB (K' := Fin 2)
    (φ' := ![(G.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ ⊤).ι]) (ε' := ![1, -1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.pullGen _ _ _ P.sym (G.hom ⁻¹ᵁ ⊤).ι)
    (LB.isGen_pullGen _ _ _ _ P.sym_gen _)
  exact ⟨⊤, trivial, t, ht⟩

end GlobalTheory.WtPoint

namespace GlobalTheory

theorem exists_point_repWt : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ χ : s.X, ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  intro hL V _ _ _ A G _ _ s t a hK χ
  have : IsDiscreteValuationRing V := s.cdvr.1
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim V a.B a.isAb
  obtain ⟨O, hO, hΛ, hu⟩ := GlobalTheory.T.exists_weightBundle_torusQuotientTower_algebraisation hL V A G s t a (-χ)
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.PrimitiveOverValuationRing.exists_section_translate hL V
    { A := a.B, isAb := a.isAb, g := g, smoothDim := hg, L := a.M.L.L, isLB := a.M.L.isLB,
      rigid := ⟨a.M.L.rig, a.M.L.rigGen⟩, sym := WtPoint.sym_of_cp a.M, ample := a.ample, ktriv := hK } O hO hΛ
  refine ⟨c, fun e => ?_⟩
  obtain ⟨u, hu, hw⟩ := hu e
  obtain ⟨v, hv, hw'⟩ := WtPoint.exists_gen_of_iso (fun Z τ x => by
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, WtBundle.act_comp])
    hO (LB.isLB_linComb a.M.L.isLB _ _) hc u hu hw
  exact WtPoint.exists_gen_neg (fun k => by fin_cases k <;> rfl) v hv hw'

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_point_representing_weight_mumfordQuotient : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ χ : s.X, ∃ c : 𝟙_ _ ⟶ a.B, ∀ e, a.RepWt c χ e := by
  first | exact @GlobalTheory.exists_point_repWt | exact GlobalTheory.exists_point_repWt | (intros; apply GlobalTheory.exists_point_repWt <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.mumfordTower_repWt_unique : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ (χ : s.X) (c c' : 𝟙_ _ ⟶ a.B), (∀ e, a.RepWt c χ e) → (∀ e, a.RepWt c' χ e) → c = c' := by
  first | exact @GlobalTheory.UU.repWt_unique | exact GlobalTheory.UU.repWt_unique | (intros; apply GlobalTheory.UU.repWt_unique <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.mumfordTower_repWt_mul_add : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ χ' : s.X) (c c' : 𝟙_ _ ⟶ a.B) (e : ℕ), a.RepWt c χ e → a.RepWt c' χ' e → a.RepWt (c * c') (χ + χ') e := by
  first | exact @GlobalTheory.UU.repWt_add | exact GlobalTheory.UU.repWt_add | (intros; apply GlobalTheory.UU.repWt_add <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem exists_weightPoints : Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∃ c : s.X → (𝟙_ _ ⟶ a.B), (∀ χ χ', c (χ + χ') = c χ * c χ') ∧ ∀ χ e, a.RepWt (c χ) χ e := by
  intro hL V _ _ _ A G _ _ s
  have h1 := GlobalTheory.T.exists_point_representing_weight_mumfordQuotient hL V A G s
  have h2 := GlobalTheory.T.mumfordTower_repWt_unique hL V A G s
  have h3 := GlobalTheory.T.mumfordTower_repWt_mul_add V A G s
  intro t a hK
  choose c hc using h1 t a hK
  refine ⟨c, fun χ χ' => ?_, hc⟩
  exact h2 t a hK (χ + χ') _ _ (hc _) fun e => h3 t a χ χ' _ _ e (hc χ e) (hc χ' e)

end GlobalTheory.UU
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PreUnif

theorem exists_ratio {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB) (hL' : L'.IsLB)
    (w₁ w₂ : LB.Iso L' (L.pull F)) (h₁ : PGen w₁) (h₂ : PGen w₂) :
    ∃ u : Γ(X', ⊤)ˣ, ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), F (r y) ∈ L.U j → r y ∈ L'.U k →
      gw w₁ r y j k = gm r y ⊤ u * gw w₂ r y j k := by
  let W : L.ι × L'.ι → X'.Opens := fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2
  let v : ∀ p, Γ(X', W p)ˣ := fun p => w₁.s (fun _ => p.1, p.2) * (w₂.s (fun _ => p.1, p.2))⁻¹
  have hv : ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) p, gm r y (W p) (v p) =
      gw w₁ r y p.1 p.2 * (gw w₂ r y p.1 p.2)⁻¹ := fun Y r y p =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩) v (fun p q x hx => by
      have a := h₁ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 X') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      rw [hv, hv, a, b, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨u, fun Y r y j k hj hk => ?_⟩
  have hy : r y ∈ W (j, k) := ⟨mem_pull.2 hj, hk⟩
  rw [← gm_res r y (le_top : W (j, k) ≤ ⊤) hy u, hu, hv, inv_mul_cancel_right]

section
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']

theorem gw_unique (hG : GlobalFnsSt) [ConnectedSpace S'] [ConnectedSpace G'.left] {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] (Q : TQ G' X) {P' : CP G'} {P : CP G} {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    {hw : F ≫ G.hom = G'.hom ≫ f} {w₁ w₂ : LB.Iso P'.L.L (P.L.L.pull F)} (h₁ : IsCPMap P' P f F hw w₁)
    (h₂ : IsCPMap P' P f F hw w₂) (Y : Scheme.{0}) (r : Y ⟶ G'.left) (y : Y) (j : P.L.L.ι) (k : P'.L.L.ι)
    (hj : F (r y) ∈ P.L.L.U j) (hk : r y ∈ P'.L.L.U k) : gw w₁ r y j k = gw w₂ r y j k := by
  obtain ⟨u, hu⟩ := exists_ratio P.L.isLB P'.L.isLB w₁ w₂ ((isGen_iff _).1 h₁.gen) ((isGen_iff _).1 h₂.gen)
  have e : u = 1 := by
    refine GlobalTheory.even_cubic_unit_eq_one hG S' X G' Q u fun T U hU => ?_
    let V : (T ⟶ G') → Γ(T.left, ⊤)ˣ := fun x => Units.map x.left.appTop.hom.toMonoidHom u
    have hV : ∀ x, U x = (V x).val := hU
    have key : ∀ z : T.left, gm (𝟙 T.left) z ⊤ (V 1) = 1 ∧
        (∀ x, gm (𝟙 T.left) z ⊤ (V x⁻¹) = gm (𝟙 T.left) z ⊤ (V x)) ∧
        ∀ x y v, gm (𝟙 T.left) z ⊤ (V (x * y * v) * V x * V y * V v) =
          gm (𝟙 T.left) z ⊤ (V (x * y) * V (x * v) * V (y * v)) := fun z => by
      obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
      obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
      obtain ⟨B, hB⟩ : ∃ B : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
        ∀ x, B x = gw w₂ x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
      obtain ⟨A, hA⟩ : ∃ A : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
        ∀ x, A x = gm (𝟙 T.left) z ⊤ (V x) := ⟨_, fun _ => rfl⟩
      obtain ⟨a₁, a₂, a₃⟩ := h₁.vals T z J' J hJ' hJ (fun x => A x * B x) fun x => by
        rw [hA, hB, hu _ x.left z _ _ (hJ (x.left ≫ F)) (hJ' x.left), gm_top x.left z u]
      obtain ⟨b₁, b₂, b₃⟩ := h₂.vals T z J' J hJ' hJ B hB
      have c₁ : A 1 = 1 := mul_eq_right.1 (mul_right_cancel (a₁.symm.trans b₁))
      simp only [map_mul, ← hA]
      refine ⟨c₁, fun x => ?_, fun x y v => ?_⟩
      · have a := congrArg Additive.ofMul (a₂ x)
        have b := congrArg Additive.ofMul (b₂ x)
        apply Additive.ofMul.injective
        simp only [ofMul_mul] at a b ⊢
        linear_combination (norm := abel) b - a
      · have a := congrArg Additive.ofMul (a₃ x y v)
        have b := congrArg Additive.ofMul (b₃ x y v)
        apply Additive.ofMul.injective
        simp only [c₁, _root_.one_mul, ofMul_mul] at a b ⊢
        linear_combination (norm := abel) b - a
    simp only [hV, ← Units.val_mul, Units.val_inj]
    refine ⟨?_, fun x => unit_ext fun z _ => (key z).2.1 x, fun x y v => unit_ext fun z _ => (key z).2.2 x y v⟩
    exact congrArg Units.val (unit_ext fun z _ => (key z).1.trans (map_one _).symm : V 1 = 1)
  rw [hu Y r y j k hj hk, e, map_one, _root_.one_mul]

theorem comp_of_eq {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S}
    {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} (hw'' : F'' ≫ G.hom = G''.hom ≫ f'') (ef : f' ≫ f = f'') (eF : F' ≫ F = F'')
    {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    (h : IsCPMap P' P f F hw w) (h' : IsCPMap P'' P' f' F' hw' w') :
    ∃ w'', IsCPMap P'' P f'' F'' hw'' w'' ∧ ∀ (Y : Scheme.{0}) (r : Y ⟶ G''.left) (y : Y) (j : P.L.L.ι) (i : P'.L.L.ι)
      (k : P''.L.L.ι), F'' (r y) ∈ P.L.L.U j → F' (r y) ∈ P'.L.L.U i → r y ∈ P''.L.L.U k →
      gw w'' r y j k = gw w (r ≫ F') y j i * gw w' r y i k := by
  subst ef eF
  obtain ⟨w'', T, H⟩ := h.exists_comp h' hw''
  exact ⟨w'', H, T⟩

theorem cancel_of_eq {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S}
    {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    (hw' : F' ≫ G'.hom = G''.hom ≫ f') {hw'' : F'' ≫ G.hom = G''.hom ≫ f''} (ef : f' ≫ f = f'') (eF : F' ≫ F = F'')
    (mul : ∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y)
    {w : LB.Iso P'.L.L (P.L.L.pull F)} {w'' : LB.Iso P''.L.L (P.L.L.pull F'')}
    (h : IsCPMap P' P f F hw w) (h'' : IsCPMap P'' P f'' F'' hw'' w'') :
    ∃ w', IsCPMap P'' P' f' F' hw' w' ∧ ∀ (Y : Scheme.{0}) (r : Y ⟶ G''.left) (y : Y) (j : P.L.L.ι) (i : P'.L.L.ι)
      (k : P''.L.L.ι), F'' (r y) ∈ P.L.L.U j → F' (r y) ∈ P'.L.L.U i → r y ∈ P''.L.L.U k →
      gw w'' r y j k = gw w (r ≫ F') y j i * gw w' r y i k := by
  subst ef eF
  exact (isCPMap_comp_cancel S S' S'' f f' G G' G'' P P' P'' F hw w F' hw' hw'' h).2 mul w'' h''

theorem mul_of_comp {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S}
    {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left} (hF : IsGrpPullback G' G f F)
    (hw' : F' ≫ G'.hom = G''.hom ≫ f') {hw'' : F'' ≫ G.hom = G''.hom ≫ f''} (ef : f' ≫ f = f'') (eF : F' ≫ F = F'')
    (mul : ∀ (T : Over S'') (x y : T ⟶ G''), toBase hw'' (x * y) = toBase hw'' x * toBase hw'' y)
    (T : Over S'') (x y : T ⟶ G'') : toBase hw' (x * y) = toBase hw' x * toBase hw' y := by
  subst ef eF
  let ρ : Over.mk ((Over.mk (T.hom ≫ f')).hom ≫ f) ⟶ Over.mk (T.hom ≫ f' ≫ f) := Over.homMk (𝟙 T.left) (by simp)
  have e : ∀ a : T ⟶ G'', (ρ ≫ toBase hw'' a).left = (toBase hw' a).left ≫ F := fun a =>
    (Category.id_comp _).trans (Category.assoc _ _ _).symm
  refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  rw [← hF.2 _ _ _ _ _ (e x) (e y), ← MonObj.comp_mul, ← mul, e]

theorem gw_pullIso {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {j : L.ι}
    (hj : F (r z) ∈ L.U j) : gw (pullIso L F) r z j (fun _ => j) = 1 :=
  gm_self (pull_isLB hL F) r z (mem_pull.2 hj : _ ∈ (L.pull F).U fun _ => j)

end

theorem cubV_map {S S' : Scheme.{0}} {f : S' ⟶ S} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B}
    (c : CubicalStr B L) {H T : Over S'} (p : (Over.map f).obj H ⟶ B) (hw : p.left ≫ B.hom = H.hom ≫ f) (z : T.left) (J)
    (x y u : T ⟶ H) :
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := (Over.map f).obj T) z J ((Over.map f).map x ≫ p)
      ((Over.map f).map y ≫ p) ((Over.map f).map u ≫ p)) =
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := Over.mk (T.hom ≫ f)) z J (toBase (A := B) (A' := H) (f := f) (g := p.left) hw x)
      (toBase (A := B) (A' := H) (f := f) (g := p.left) hw y) (toBase (A := B) (A' := H) (f := f) (g := p.left) hw u)) := rfl

section
variable {S S' S'' : Scheme.{0}} {G B : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G]
  [GrpObj B] [IsCommMonObj B] [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']

def IsPullMap (P : CP G) (M : CP B) (f : S' ⟶ S) (F : G'.left ⟶ G.left) (hF : F ≫ G.hom = G'.hom ≫ f)
    (p : G'.left ⟶ B.left) (hp : p ≫ B.hom = G'.hom ≫ f) (w : LB.Iso (P.L.L.pull F) (M.L.L.pull p)) : Prop :=
  ∃ (rig : LB.Gen ((P.L.L.pull F).pull (eSec G'))) (hr : rig.IsGen)
    (c : CubicalStr G' ⟨P.L.L.pull F, rig, pull_isLB P.L.isLB F, hr⟩) (s : _) (h₁ : _) (h₂ : _) (h₃ : _),
    IsCPMap ⟨⟨P.L.L.pull F, rig, pull_isLB P.L.isLB F, hr⟩, c, s, h₁, h₂, h₃⟩ P f F hF (pullIso P.L.L F) ∧
    IsCPMap ⟨⟨P.L.L.pull F, rig, pull_isLB P.L.isLB F, hr⟩, c, s, h₁, h₂, h₃⟩ M f p hp w

variable {P : CP G} {M : CP B} {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hF : F ≫ G.hom = G'.hom ≫ f}
  {p : G'.left ⟶ B.left} {hp : p ≫ B.hom = G'.hom ≫ f}

theorem exists_isPullMap {P' : CP G'} {a v} (ha : IsCPMap P' P f F hF a) (hv : IsCPMap P' M f p hp v) :
    ∃ w, IsPullMap P M f F hF p hp w := by
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, hN⟩ := exists_isCPMap P ha.mul _ (pull_isLB P.L.isLB F) _
    (pullIso_isGen P.L.isLB F)
  obtain ⟨b, hb, -⟩ := cancel_of_eq (f' := 𝟙 _) (F' := 𝟙 _) (by simp) (Category.id_comp _) (Category.id_comp _)
    (toBase_mul_of_isMonHom (𝟙 G') _) ha hN
  obtain ⟨w, h, -⟩ := comp_of_eq hp (Category.id_comp _) (Category.id_comp _) hv hb
  exact ⟨w, rig, hr, c, s, h₁, h₂, h₃, hN, h⟩

variable {w : LB.Iso (P.L.L.pull F) (M.L.L.pull p)}

theorem IsPullMap.gen (h : IsPullMap P M f F hF p hp w) : w.IsGen := by
  obtain ⟨_, _, _, _, _, _, _, -, h⟩ := h
  exact h.gen

theorem IsPullMap.vals (h : IsPullMap P M f F hF p hp w) (T : Over S') (z : T.left)
    (JG : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ B.left) → M.L.L.ι) (hJG : Good P.L.L z JG) (hJ : Good M.L.L z J)
    (W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ)
    (hW : ∀ x, W x = gw w x.left z (J (x.left ≫ p)) (fun _ => JG (x.left ≫ F))) :
    (val (L := M.L.L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) M.L.rig (T.hom ≫ f) z J =
        W 1 * val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig (T.hom ≫ f) z JG) ∧
      (∀ x : T ⟶ G', val M.sym (x.left ≫ p) z J * W x = W x⁻¹ * val P.sym (x.left ≫ F) z JG) ∧
      ∀ x y u : T ⟶ G',
        @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := Over.mk (T.hom ≫ f)) z J (toBase hp x) (toBase hp y)
          (toBase hp u)) * W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u *
          @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := Over.mk (T.hom ≫ f)) z JG (toBase hF x) (toBase hF y)
            (toBase hF u)) := by
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, hN, hw⟩ := h
  let J' : (T.left ⟶ G'.left) → (P.L.L.pull F).ι := fun r _ => JG (r ≫ F)
  have hJ' : Good (P.L.L.pull F) z J' := fun r => mem_pull.2 (hJG (r ≫ F))
  obtain ⟨a₁, a₂, a₃⟩ := hw.vals T z J' J hJ' hJ W hW
  obtain ⟨b₁, b₂, b₃⟩ := hN.vals T z J' JG hJ' hJG (fun _ => 1) fun x =>
    (gw_pullIso P.L.isLB _ x.left z (hJG (x.left ≫ F))).symm
  simp only [_root_.mul_one, _root_.one_mul] at b₁ b₂ b₃
  exact ⟨a₁.trans (congrArg (W 1 * ·) b₁.symm), fun x => (a₂ x).trans (congrArg (W x⁻¹ * ·) (b₂ x).symm),
    fun x y u => (a₃ x y u).trans (congrArg (W (x * y * u) * W x * W y * W u * ·) (b₃ x y u).symm)⟩

theorem IsPullMap.compat (hG : GlobalFnsSt) [ConnectedSpace S''] [ConnectedSpace G''.left] {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] (Q : TQ G'' X) {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} {F' : G''.left ⟶ G'.left}
    {F'' : G''.left ⟶ G.left} {p'' : G''.left ⟶ B.left} {hF'' : F'' ≫ G.hom = G''.hom ≫ f''}
    {hp'' : p'' ≫ B.hom = G''.hom ≫ f''} {w'' : LB.Iso (P.L.L.pull F'') (M.L.L.pull p'')}
    (h : IsPullMap P M f F hF p hp w) (h'' : IsPullMap P M f'' F'' hF'' p'' hp'' w'') (hpb : IsGrpPullback G' G f F)
    (hm : F' ≫ G'.hom = G''.hom ≫ f') (ef : f' ≫ f = f'') (eF : F' ≫ F = F'') (ep : F' ≫ p = p'')
    (Z : Scheme.{0}) (x : Z ⟶ G''.left) (z : Z) (j : M.L.L.ι) (k : P.L.L.ι) (hj : p'' (x z) ∈ M.L.L.U j)
    (hk : F'' (x z) ∈ P.L.L.U k) : gw w (x ≫ F') z j (fun _ => k) = gw w'' x z j (fun _ => k) := by
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, hN, hw⟩ := h
  obtain ⟨rig'', hr'', c'', s'', h₁'', h₂'', h₃'', hN'', hw''⟩ := h''
  have hk' : F (F' (x z)) ∈ P.L.L.U k := (congrArg (fun g => g (x z) ∈ P.L.L.U k) eF).mpr hk
  obtain ⟨v, hv, tv⟩ := cancel_of_eq hm ef eF (mul_of_comp hpb hm ef eF hN''.mul) hN hN''
  obtain ⟨w', hw', tw⟩ := comp_of_eq hp'' ef ep hw hv
  have e₁ := tv Z x z k (fun _ => k) (fun _ => k) hk (mem_pull.2 hk') (mem_pull.2 hk)
  rw [gw_pullIso P.L.isLB _ x z hk, gw_pullIso P.L.isLB _ (x ≫ F') z hk', _root_.one_mul] at e₁
  have e₂ := tw Z x z j (fun _ => k) (fun _ => k) hj (mem_pull.2 hk') (mem_pull.2 hk)
  rw [← e₁, _root_.mul_one] at e₂
  exact e₂.symm.trans (gw_unique hG Q hw' hw'' Z x z j _ hj (mem_pull.2 hk))

end

section
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) {G B : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] [GrpObj B] [IsCommMonObj B]

def Vals (P : CP G) (M : CP B) (e : ℕ) (p : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ B)
    (w : LB.Iso (P.L.L.pull (fstG I e G).left) (M.L.L.pull p.left)) : Prop :=
  ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left)
    (JG : (T.left ⟶ G.left) → P.L.L.ι) (J : (T.left ⟶ B.left) → M.L.L.ι), Good P.L.L z JG → Good M.L.L z J →
    ∀ W : (T ⟶ thickObj R I e G) → (T.left.presheaf.stalk z)ˣ,
      (∀ x, W x = gw w x.left z (J (x.left ≫ p.left)) (fun _ => JG (x.left ≫ (fstG I e G).left))) →
      (val (L := M.L.L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) M.L.rig (T.hom ≫ thick R I e) z J =
        W 1 * val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig (T.hom ≫ thick R I e) z JG) ∧
      (∀ x : T ⟶ thickObj R I e G, val M.sym (x.left ≫ p.left) z J * W x =
        W x⁻¹ * val P.sym (x.left ≫ (fstG I e G).left) z JG) ∧
      ∀ x y u : T ⟶ thickObj R I e G,
        @id (T.left.presheaf.stalk z)ˣ (cubV M.c (T := (Over.map (thick R I e)).obj T) z J
            ((Over.map (thick R I e)).map x ≫ p) ((Over.map (thick R I e)).map y ≫ p)
            ((Over.map (thick R I e)).map u ≫ p)) * W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u *
          @id (T.left.presheaf.stalk z)ˣ (cubV P.c (T := (Over.map (thick R I e)).obj T) z JG
            ((Over.map (thick R I e)).map x ≫ fstG I e G) ((Over.map (thick R I e)).map y ≫ fstG I e G)
            ((Over.map (thick R I e)).map u ≫ fstG I e G))

theorem exists_w (hG : GlobalFnsSt) [IsLocalRing R] (hI : I ≠ ⊤) (hS : IsSemiAbelian G) (P : CP G) (M : CP B)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] (Q : ∀ e, TQ (thickObj R I e G) X)
    (p : ∀ e, (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ B)
    (hp : ∀ e, thickMap R I e G ≫ (p (e + 1)).left = (p e).left)
    (H : ∀ e, ∃ P' : CP (thickObj R I e G), IsLevelCP I e P' P ∧
      ∃ v, IsCPMap P' M (thick R I e) (p e).left (Over.w (p e)) v) :
    ∃ w : ∀ e, LB.Iso (P.L.L.pull (fstG I e G).left) (M.L.L.pull (p e).left), (∀ e, (w e).IsGen) ∧
      (∀ e, Vals I P M e (p e) (w e)) ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (j : M.L.L.ι) (k : P.L.L.ι),
        (p e).left (x z) ∈ M.L.L.U j → (fstG I e G).left (x z) ∈ P.L.L.U k →
        gw (w (e + 1)) (x ≫ thickMap R I e G) z j (fun _ => k) = gw (w e) x z j (fun _ => k) := by
  have hw : ∀ e, ∃ w, IsPullMap (G' := thickObj R I e G) P M (thick R I e) (fstG I e G).left pullback.condition
      (p e).left (Over.w (p e)) w := fun e => by
    obtain ⟨P', ⟨a, ha⟩, v, hv⟩ := H e
    exact exists_isPullMap ha hv
  choose w hw using hw
  refine ⟨w, fun e => (hw e).gen, fun e T z JG J hJG hJ W hW => ?_, fun e => ?_⟩
  · obtain ⟨a₁, a₂, a₃⟩ := (hw e).vals T z JG J hJG hJ W hW
    refine ⟨a₁, a₂, fun x y u => ?_⟩
    rw [cubV_map M.c (p e) (Over.w (p e)), cubV_map P.c (fstG I e G) pullback.condition]
    exact a₃ x y u
  · have hJ : I ^ (e + 1) ≠ ⊤ := fun h => hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
    have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
    have : IsLocalRing (R ⧸ I ^ (e + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have : ConnectedSpace (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := SplitTorus.connectedSpace_of_isLocalRing _
    have := hS.smooth
    have := hS.geomConnected
    have : Smooth (thickObj R I e G).hom := inferInstanceAs (Smooth (pullback.snd _ _))
    have : GeometricallyConnected (thickObj R I e G).hom := inferInstanceAs (GeometricallyConnected (pullback.snd _ _))
    have : ConnectedSpace (thickObj R I e G).left := (GroupConn.connectedSpace_group _ _).1
    have eF : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    have hm : thickMap R I e G ≫ (thickObj R I (e + 1) G).hom = (thickObj R I e G).hom ≫ thickTrans R I e :=
      pullback.lift_snd _ _ _
    exact (hw (e + 1)).compat hG (Q e) (hw e) (isGrpPullback_pullback G _) hm (thickTrans_comp R I e) eF (hp e)

end

theorem exists_preU : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegPre V) (U : PreU (IsLocalRing.maximalIdeal V) D A G), U.P = s.P ∧ U.gen = s.gen := by
  intro hc L V _ _ _ A G _ _ s
  obtain ⟨t⟩ := GlobalTheory.T.nonempty_mumfordTorusQuotientTower V A G s
  obtain ⟨a⟩ := GlobalTheory.T.nonempty_algebraisation_abelian_quotient_tower hc L V A G s t
  have hK := GlobalTheory.T.kTriv_torusQuotientTower_algebraisation hc L V A G s t a
  obtain ⟨c, hadd, hrep⟩ := exists_weightPoints L V A G s t a hK
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim V a.B a.isAb
  have hsym : Sym a.B a.M.L.L := fun _ => ⟨⊤, trivial, by
    obtain ⟨u, hu, -⟩ := exists_gen a.M.L.isLB (φ' := ![(a.B.hom ⁻¹ᵁ ⊤).ι ≫ (ι[a.B]).left, (a.B.hom ⁻¹ᵁ ⊤).ι])
      (ε' := ![1, -1]) (fun V _ h => by simp [Fin.prod_univ_two])
      (LB.pullGen a.M.L.L _ _ a.M.sym (a.B.hom ⁻¹ᵁ ⊤).ι) (DVR.pullGen_isGen _ _ _ _ a.M.sym_gen _)
    exact ⟨u, hu⟩⟩
  let Pol : PolAV (Spec (CommRingCat.of V)) :=
    { A := a.B, isAb := a.isAb, g := g, smoothDim := hg, L := a.M.L.L, isLB := a.M.L.isLB,
      rigid := ⟨a.M.L.rig, a.M.L.rigGen⟩, sym := hsym, ample := a.ample, ktriv := hK }
  choose ψ hψ using fun χ : s.X => DVR.exists_gen_of_local (V := FractionRing V) a.M.L.L a.M.L.isLB (K := PUnit)
    (fun _ => ptK (c χ)) (fun _ => -1)
  let D : DegPre V :=
    { P := Pol, rig := a.M.L.rig, rig_gen := a.M.L.rigGen, cub := a.M.c, sym := a.M.sym, sym_gen := a.M.sym_gen,
      sym_rig := a.M.sym_rig, X := s.X, c := c, c_add := hadd, psi := ψ, psi_gen := hψ }
  choose gt hi hq using fun e => exists_gtCoord_of_torusQuotient L.globalFns V (IsLocalRing.maximalIdeal V) D e G
    (t.l e).Q (a.b e) (a.b_pb e).1 fun χ => hrep χ e
  have gq : ∀ e, thickMap V _ e G ≫ (gt (e + 1)).pG.left = (gt e).pG.left := fun e => by
    rw [hq, hq, ← a.b_β e, ← Category.assoc, ← Category.assoc, t.β_q]
  obtain ⟨w, w₁, w₂, w₃⟩ := exists_w (B := a.B) (IsLocalRing.maximalIdeal V) L.globalFns
    (IsLocalRing.maximalIdeal.isMaximal V).ne_top s.semi s.P a.M (fun e => (t.l e).Q) (fun e => (gt e).pG) gq fun e => by
      obtain ⟨_, v, hv⟩ := a.b_pb e
      obtain ⟨w, h, -⟩ := comp_of_eq (Over.w (gt e).pG) (Category.id_comp _) (hq e).symm hv (t.l e).D.map
      exact ⟨_, (t.l e).lev, w, h⟩
  exact ⟨D,
    { semi := s.semi, gen := s.gen, gen_hom := s.gen_hom, P := s.P, wA := s.wA, wA_gen := s.wA_gen, gt := gt,
      gt_q := gq
      gt_t := fun e => GlobalTheory.T.torusCoordinates_compat_of_torus_compat L.globalFns V _ D e G (gt e) (gt (e + 1)) (gq e) (by rw [hi, hi]; exact t.tor e)
      w := w, w_gen := w₁, w_vals := w₂, w_compat := w₃ }, rfl, rfl⟩

end GlobalTheory.PreUnif
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisation_data_before_choice : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegPre V) (U : PreU (IsLocalRing.maximalIdeal V) D A G), U.P = s.P ∧ U.gen = s.gen := by
  first | exact @GlobalTheory.PreUnif.exists_preU | exact GlobalTheory.PreUnif.exists_preU | (intros; apply GlobalTheory.PreUnif.exists_preU <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_degData_unif : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → Laws2 → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c :=
  fun h0 h1 h2 => GlobalTheory.UU.unif_assembly h1 h2 (GlobalTheory.T.exists_uniformisation_data_before_choice h0 h1) (GlobalTheory.T.exists_degenerationData_functionalEquation_degree_one h1 h2)

end GlobalTheory.UU
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_uniformisation_of_torsionCount : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → Laws2 → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c := by
  atlas_forward_decl GlobalTheory.UU.exists_degData_unif
end
