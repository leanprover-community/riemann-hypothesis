import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongrFunHeq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsSameGeometricHalf
import Formalism.LocalToGlobal.NumberFieldFamilies.OwnStruct

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.R3.Rw.JmtUp

theorem agree {D : D7} {T : Type} {W : Type} [AddCommGroup W] [Module ℂ W] (U U' : D.what₂.Tup → Prop) {n : Fin D.R.m → T → ℕ}
    (tup tup' : T → D.what₂.Tup) (e1 : HEq tup' tup)
    (eM : ∀ (i : Fin D.R.m) t, (Fin (n i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (eM' : ∀ (i : Fin D.R.m) t, (Fin (n i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup' t) ((i : ℕ) + 1)) (e2 : HEq eM' eM)
    (i : Fin D.R.m) (val : ∀ t, (Fin (n i t) → D.what₂.LL) → W)
    (g : ∀ μ, U μ → D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] W) (g' : ∀ μ, U' μ → D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] W)
    (hs : ∀ t, Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t (Pi.single k 1))) = ⊤)
    (hg : ∀ t h y, g (tup t) h (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t y)) = val t y)
    (hg' : ∀ t h y, g' (tup' t) h (D.what₂.jMt (tup' t) ((i : ℕ) + 1) (eM' i t y)) = val t y)
    (μ : D.what₂.Tup) (τ : T) (hτ : tup τ = μ) (h : U μ) (h' : U' μ) (x : D.what₂.Mt μ ((i : ℕ) + 1)) : HEq (g' μ h' x) (g μ h x) := by
  cases e1
  cases e2
  subst hτ
  refine heq_of_eq (LinearMap.congr_fun (LinearMap.ext_on_range (hs τ) fun k => ?_) x)
  rw [hg, hg']

section Side

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

abbrev Val (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (i : Fin D.R.m) : Type :=
  GA D ((toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).V i) → (toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).TauV i

noncomputable def gOf (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (i : Fin D.R.m) (μ : D.what₂.Tup) (h : Used0 D μ) :
    D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] Val Y i := (Submodule.subtype _).comp (Y.IL.jMt μ h i).toLinearMap

theorem side (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0) (i : Fin D.R.m) (U : D.what₂.Tup → Prop) (tup : T → D.what₂.Tup) (e1 : HEq Y.tup tup)
    (eM : ∀ (i : Fin D.R.m) t, (Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (e2 : HEq Y.eMt eM) (g : ∀ μ, U μ → D.what₂.Mt μ ((i : ℕ) + 1) →ₗ[ℂ] Val Y i)
    (hs : ∀ t, Submodule.span ℂ (Set.range fun k => D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t (Pi.single k 1))) = ⊤)
    (hg : ∀ t h y, g (tup t) h (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eM i t y)) =
      R.extV i t (R.jV i t (GlobalTheory.Mem.R3.liftForm A3.A F.P0 F.ψ0 i t y)))
    (μ : D.what₂.Tup) (τ : T) (hτ : tup τ = μ) (h : U μ) (h' : Used0 D μ) (x : D.what₂.Mt μ ((i : ℕ) + 1)) :
    HEq (gOf Y i μ h' x) (g μ h x) :=
  agree U (Used0 D) tup Y.tup e1 eM Y.eMt e2 i _ g (gOf Y i) hs hg (fun t h y => Y.mtRead i t h y) μ τ hτ h h' x

end Side

theorem jMt_rowsSame : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1 := by
  intro K B f T w Z Wt S' N h p0 t p0' t' hs μ hμ hμ' i x
  have H := side t'.r.Y ((by with_unfolding_all exact (i :)))
  have a1 := hs.tup
  have a2 := hs.eMt
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  exact (by with_unfolding_all exact ((H ((by with_unfolding_all exact ((Formalism.IndefR.RecTie.Used0 (w.D Z)) :))) ((by with_unfolding_all exact (t.r.Y.tup :))) ((by with_unfolding_all exact (a1 :))) ((by with_unfolding_all exact (t.r.Y.eMt :))) ((by with_unfolding_all exact (a2 :))) ((by with_unfolding_all exact ((gOf t.r.Y i) :)))
    ((by with_unfolding_all exact ((fun τ => (t.r.Y.formsL i τ).span) :))) ((by with_unfolding_all exact ((t.r.Y.mtRead i) :))) ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact ((t.r.Y.tupT μ) :))) ((by with_unfolding_all exact ((t.r.Y.tupTie μ hμ) :))) ((by with_unfolding_all exact (hμ :)))
    ((by with_unfolding_all exact (hμ' :))) ((by with_unfolding_all exact (x :)))) :))

end GlobalTheory.Mem.R3.Rw.JmtUp
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowReadings_sameRows_identify_definiteForms : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1 := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.JmtUp.jMt_rowsSame
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000

theorem tupTied_ext {D : D7} {cf : CharFrame D} {C : NChoice D} {p q : TupTied D cf C} (h1 : p.xi = q.xi) (h2 : p.psi = q.psi) :
    p = q := by
  cases p; cases q; cases h1; cases h2; rfl

section
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {nch : NChoice (w.D Z)}
  {xd : ThData (w.D Z)}

theorem nchT_up (n : NchT w Z Wt nch) : Nonempty (NchT w (upL Z S' N h) Wt (nchUp S' N h nch)) :=
  ⟨{ tp := by kcopy n.tp, xi := kc% n.xi, psi := kc% n.psi, tie := by kcopy n.tie, Q := n.Q, chrPsi := by kcopy n.chrPsi }⟩

theorem kept_up (nch : NChoice (w.D Z)) : Kept nch (nchUp S' N h nch) := by
  refine ⟨?_, ?_, ?_, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩ <;> constructor <;> first | rfl | exact HEq.rfl

theorem goodO_up (g : GoodO (w.D Z) nch xd) : GoodO (w.D (upL Z S' N h)) (nchUp S' N h nch) (xdUp S' N h xd) := by
  obtain ⟨⟨E, N0, S⟩, h1, h2, h3⟩ := g.tw
  cases h1
  exact ⟨⟨⟨twEOf (xdUp S' N h xd), N0, S⟩, rfl, kc% h2, kc% h3⟩, g.sep⟩
end

theorem layer_up : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z)), ∃ (nch' : NChoice (w.D (upL Z S' N h))) (xd' : ThData (w.D (upL Z S' N h))), Kept nch nch' ∧ (S' = Z.S → HEq nch' (nchTr (D := w.D Z) N h nch) ∧ HEq xd' (xdTr (D := w.D Z) N h xd)) ∧ (NchT w Z Wt nch → Nonempty (NchT w (upL Z S' N h) Wt nch')) ∧ (GoodO (w.D Z) nch xd → GoodO (w.D (upL Z S' N h)) nch' xd') ∧ ∀ (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (n : NchT w Z Wt nch) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0') (n' : NchT w (upL Z S' N h) Wt nch'), RowsSame t t' → HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) → NX hL (NEb hL) K B f T w Z Wt p0 t nch n xd → Nonempty (NX hL (NEb hL) K B f T w (upL Z S' N h) Wt p0' t' nch' n' xd') := by
  intro hL K B f T w Z Wt S' N h nch xd
  refine ⟨nchUp S' N h nch, xdUp S' N h xd, kept_up S' N h nch, ?_, nchT_up S' N h, goodO_up S' N h, ?_⟩
  · rintro rfl
    exact ⟨HEq.rfl, HEq.rfl⟩
  · rintro p0 t n p0' t' ⟨tp', xi', psi', tie', Q', chr'⟩ hs hg ⟨c, e, ⟨bk⟩⟩
    have e1 : tp' = (by with_unfolding_all exact (((mvOf w Z S' N h).tp n.tp) :)) := tupTied_ext (xi'.trans ((by with_unfolding_all exact (n.xi.symm :)))) (psi'.trans ((by with_unfolding_all exact (n.psi.symm :))))
    subst e1
    obtain ⟨a', hA⟩ := (mvOf w Z S' N h).exists_at c.a
    refine Exists.elim (exists_row hL K B f T w Z Wt S' N h nch xd p0 t p0' t' hs hg
      (GlobalTheory.T.rowReadings_sameRows_identify_definiteForms K B f T w Z Wt S' N h p0 t p0' t' hs) (GlobalTheory.T.rows_same_geometric_half K B f T w Z Wt S' N h nch p0 t p0' t' hs hg)
      (tp' := (by with_unfolding_all exact (((mvOf w Z S' N h).tp n.tp) :))) c.a ((by with_unfolding_all exact (a' :))) ((by with_unfolding_all exact (hA :))) c.row e) fun r' hr => hr.elim fun e' => ?_
    have hq : a'.Pq = (by with_unfolding_all exact (c.a.Pq :)) := eq_of_heq ((by with_unfolding_all exact (hA.2.1 :)))
    have hsel : Set.range a'.Pq = (by with_unfolding_all exact ((Set.range w.I.sel) :)) := (congrArg Set.range hq).trans ((by with_unfolding_all exact (c.sel :)))
    exact ⟨⟨⟨(by with_unfolding_all exact (a' :)), (by with_unfolding_all exact (r' :)), (by with_unfolding_all exact (hsel :))⟩, (by with_unfolding_all exact (e' :)), ⟨(by with_unfolding_all exact (((mvOf w Z S' N h).bkLaw bk) :))⟩⟩⟩

end GlobalTheory.LayerMove
end
end
