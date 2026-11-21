import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtMapP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.FirstChernClassUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PeriodMapZEqCast
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsCrystallineChernClassLimit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.CupAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.OmCup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.FirstChernCompatGlue
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.FirstChernClassUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.EtaleMapFirstChern

section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {G : Model l K → Prop}
  {D : Dat R} {C : PerC R} {I : Iso l K C.K₀} {β : BMap G D} {β₁ : BPhi β}

variable (hF : R.Facts) (hC : C.Facts) (Fm : FMap G C I D β₁.pull) (hL : D.Laws G) (E : EMap G D)
  {X : XEnd I} {Y : XMid D X}

include hL in
theorem plus_cup (HX : XLaws Y E β β₁ Fm) {M : Model l K} (hM : G M) (a : D.Ch M) {i j : ℕ} (x : M.T i) (y : M.T j)
    (z : M.T (i + j)) (hz : M.CupT x y z) {m m' : ℕ} (b : Module.Basis (Fin m) C.K₀ (I.D M i))
    (b' : Module.Basis (Fin m') C.K₀ (I.D M j)) (f : Module.Dual C.K₀ (I.D M (i + j))) :
    delta hF hC Fm a (i + j) (E.e a (i + j) z) f = ∑ s, ∑ s', delta hF hC Fm a i (E.e a i x) (b.coord s) *
      delta hF hC Fm a j (E.e a j y) (b'.coord s') * C.k (f (X.cupD M i j (b s) (b' s'))) := by
  obtain ⟨zh, hzh⟩ := HX.cup_ex a hM (dX β a hM i (E.e a i x)) (dX β a hM j (E.e a j y))
  have h1 := HX.β_cup a hM _ _ _ hzh
  rw [dX_spec, dX_spec] at h1
  have h2 := hL.cup_smul a (R.t ^ dN β a hM i) (R.t ^ dN β a hM j) _ _ _ (E.cup a hM x y z hz)
  have h3 := hL.cup_uniq a _ _ _ _ h1 h2
  have h4 := HX.ψ_cup a hM _ _ _ hzh b b' f
  rw [delta_key hF hC Fm hM h3 f] at h4
  simp only [delta_key' hF hC Fm hM] at h4
  have hu : IsUnit (iP C Fm.k (R.t ^ dN β a hM i * R.t ^ dN β a hM j)) := by
    rw [map_mul]; exact (iP_unit hF hC _ _).mul (iP_unit hF hC _ _)
  apply hu.mul_left_cancel
  rw [h4, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [map_mul]
  ring

include hL in
theorem plus_one (HX : XLaws Y E β β₁ Fm) {M : Model l K} (hM : G M) (a : D.Ch M) (v : M.T 0) (y : I.D M 0)
    (hv : X.oneT M v) (hy : X.oneD M y) (f : Module.Dual C.K₀ (I.D M 0)) :
    delta hF hC Fm a 0 (E.e a 0 v) f = C.k (f y) := by
  obtain ⟨x, hx⟩ := HX.one_ex a hM
  have h1 := hL.one_uniq a _ _ (HX.β_one a hM x hx) (HX.e_one a hM v hv)
  have h2 := delta_key hF hC Fm hM (c := 1) (by rw [h1, one_smul]) f
  rw [map_one, one_mul] at h2
  rw [← h2, HX.ψ_one a hM x y hx hy f]

theorem pairing_first_chern_value (HX : XLaws Y E β β₁ Fm) {M : Model l K} (hM : G M) (a : D.Ch M) (L : X.Ln M) (v : M.T 2)
    (y : I.D M 2) (hv : X.c1T L v) (hy : X.c1D L y) (f : Module.Dual C.K₀ (I.D M 2)) :
    (l : C.C) ^ Fm.k * C.c R.t * delta hF hC Fm a 2 (E.e a 2 v) f = C.k (f y) := by
  obtain ⟨x, hx⟩ := HX.first_chern_class_exists a hM L
  have h1 := HX.first_chern_class_unique a hM L _ _ (HX.beta_firstChern a hM L x hx) (HX.etale_firstChern a hM L v hv)
  have h2 := delta_key hF hC Fm hM h1 f
  rw [HX.psi_firstChern a hM L x y hx hy f, iP_apply] at h2
  have e : R.φ^[Fm.k] R.t = (l : R.A) ^ Fm.k * R.t := by
    simpa using phiA_iterate_tA_of_prime hF Fm.k 1
  rw [h2, e, map_mul, map_pow, map_natCast]

theorem phiPlus : ProductClassComparison := by
  intro l _ K R G C I D X Y hF hC hE hL E β β₁ κ Fm HX
  obtain ⟨P, -, hP⟩ := pre' l K R G D hF hE hL E β κ
  refine ⟨crys hF hC Fm hL E hE (fun M n hM => cC_inj hF hC Fm hL E hE κ inj P hP M n hM), ?_⟩
  refine ⟨fun M hM i j x y z hz m m' b b' f => ?_, fun M hM v y hv hy f => ?_,
    fun M hM L v y hv hy f => ?_⟩
  · show cC hF hC Fm hL E M (i + j) (M.toV _ z) f = ∑ s, ∑ s', cC hF hC Fm hL E M i (M.toV _ x) (b.coord s) *
      cC hF hC Fm hL E M j (M.toV _ y) (b'.coord s') * C.k (f (X.cupD M i j (b s) (b' s')))
    simp only [cC_toV hF hC Fm hL E hM (a0 hL M hM)]
    exact plus_cup hF hC Fm hL E HX hM _ x y z hz b b' f
  · show cC hF hC Fm hL E M 0 (M.toV 0 v) f = C.k (f y)
    rw [cC_toV hF hC Fm hL E hM (a0 hL M hM)]
    exact plus_one hF hC Fm hL E HX hM _ v y hv hy f
  · show (l : C.C) ^ Fm.k * C.c R.t * cC hF hC Fm hL E M 2 (M.toV 2 v) f = C.k (f y)
    rw [cC_toV hF hC Fm hL E hM (a0 hL M hM)]
    exact pairing_first_chern_value hF hC Fm E HX hM _ L v y hv hy f

end CrystallineSemistableComparison
end
end

section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

namespace PlusCup

def lev (r : Res l K) (M : Model l K) (i j m : ℕ) :
    (Wc.HS l (B.schFn M.p) r.ρ i).M m →ₗ[WittVector l r.k] (Wc.HS l (B.schFn M.p) r.ρ j).M m →ₗ[WittVector l r.k]
      (Wc.HS l (B.schFn M.p) r.ρ (i + j)).M m :=
  (P.cup_bilin (CH.mulP (Wc.OA l (B.schFn M.p) r.ρ m)) (rfl : i + j = i + j)).choose

theorem lev_eq (r : Res l K) (M : Model l K) (i j m : ℕ) (x : (Wc.HS l (B.schFn M.p) r.ρ i).M m)
    (y : (Wc.HS l (B.schFn M.p) r.ρ j).M m) :
    lev r M i j m x y = (CH.mulP (Wc.OA l (B.schFn M.p) r.ρ m)).cup rfl x y :=
  (P.cup_bilin (CH.mulP (Wc.OA l (B.schFn M.p) r.ρ m)) (rfl : i + j = i + j)).choose_spec x y

theorem lev_comm (r : Res l K) (M : Model l K) (i j m : ℕ) (x : (Wc.HS l (B.schFn M.p) r.ρ i).M (m + 1))
    (y : (Wc.HS l (B.schFn M.p) r.ρ j).M (m + 1)) :
    (Wc.HS l (B.schFn M.p) r.ρ (i + j)).r m (lev r M i j (m + 1) x y) =
      lev r M i j m ((Wc.HS l (B.schFn M.p) r.ρ i).r m x) ((Wc.HS l (B.schFn M.p) r.ρ j).r m y) := by
  rw [lev_eq, lev_eq]
  exact CupAbs.om_cup (Wc.redM l (B.schFn M.p) r.ρ m) (RingHom.id _) (Wc.red_mk l r.k m) rfl x y

def limCup (r : Res l K) (M : Model l K) (i j : ℕ) :
    Pb.Lim r M i →ₗ[WittVector l r.k] Pb.Lim r M j →ₗ[WittVector l r.k] Pb.Lim r M (i + j) :=
  CupAbs.limBil (lev r M i j) (lev_comm r M i j)

end PlusCup

open PlusCup in

theorem cupEx : CupEx := by
  intro l _ K r
  refine ⟨fun M i j => CupAbs.bc (Wc.K₀ l r.k) (limCup r M i j), fun M i j x y =>
    ⟨limCup r M i j x y, fun m => ?_, ?_⟩⟩
  · exact (CupAbs.limBil_apply _ _ x y m).trans (lev_eq r M i j m _ _)
  · exact CupAbs.bc_tmul _ _ _ _

theorem limOne_ex (r : Res l K) (M : Model l K) : ∃ x, Pb.LimOne r M x :=
  ⟨⟨fun m => CH.oneH (Wc.OA l (B.schFn M.p) r.ρ m),
    fun m => CupAbs.om_one (Wc.redM l (B.schFn M.p) r.ρ m) (RingHom.id _) (Wc.red_mk l r.k m)⟩, fun _ => rfl⟩

end CrystallineSemistableComparison
end
end

section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueP'

theorem lim_one_ex {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R}
    (act : ∀ j g, Sys.Hom (S j) (S j) (σ g)) (one : ∀ n, (S 0).M n)
    (cup : ∀ n i j, (S i).M n → (S j).M n → (S (i + j)).M n) (ho : ∀ n, (S 0).r n (one (n + 1)) = one n) :
    ∃ x, (limAlg S act one cup).one x :=
  ⟨(⟨one, ho⟩ : (S 0).lim), fun _ => rfl⟩

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem one_ex (hC : B.CompatH l) (M : Model l K) : ∃ x, (M.HA true).one x :=
  lim_one_ex (M.HS true) _ _ _ (fun n => hC.one (B.schFn M.p) (okToOC l K) true n.le_succ)

theorem b_one (hC : B.Compat l) (M : Model l K) (x : (M.HA true).N 0) (hx : (M.HA true).one x) :
    M.MA.one ((GlueB'.βS hC (B.schFn M.p) (okToOC l K) true 0).lim x) :=
  GlueBL.lim_one (fun j => GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j) (fun n => hC.one (B.schFn M.p) (okToOC l K) true n) x hx

theorem b_cup (hC : B.Compat l) (M : Model l K) {i j : ℕ} (x : (M.HA true).N i) (y : (M.HA true).N j)
    (z : (M.HA true).N (i + j)) (hz : (M.HA true).cup x y z) :
    M.MA.cup ((GlueB'.βS hC (B.schFn M.p) (okToOC l K) true i).lim x) ((GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j).lim y)
      ((GlueB'.βS hC (B.schFn M.p) (okToOC l K) true (i + j)).lim z) :=
  GlueBL.lim_cup (fun j => GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j)
    (fun n i j x y => hC.cup (B.schFn M.p) (okToOC l K) true n rfl x y) x y z hz

theorem cup_ex (hC : B.CompatH l) (M : Model l K) {i j : ℕ} (x : (M.HA true).N i) (y : (M.HA true).N j) :
    ∃ z, (M.HA true).cup x y z :=
  GlueLim.cup_ex (M.HS true) _ _ (fun n _ _ x y => (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) true n)).cup rfl x y)
    (GlueL'.red_cup hC M true) x y

variable (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

variable (r : Res l K) (ζ : E.Roots l) (μ : r.Cup)

theorem xlaws (hR : E.RIn l) (hU : E.FirstChernUniqueEtale) (hCH : B.CompatH l) (hMain : B.Main l) (hC : B.Compat l) (h1 : B.FirstChernCompatible l)
    (e : E.EtFam l K) (he : e.Good) (hone : ∀ (M : Model l K) n, e M n 0 (GlobalTheory.EtC.one (l ^ n) _) = CH.oneH _)
    (hc1 : ∀ (M : Model l K) D v, HT.IsEtaleFirstChernUntwisted ζ D v → E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D (e.tMul M v))
    (F : FMap Model.Sm r.perC r.iso (dat Amp) (datPull Amp)) (hF : FPlus (r.xmid ζ μ Amp) F) :
    XLaws (r.xmid ζ μ Amp) (GlueE.emap Amp e he) (GlueB'.bmap Amp hMain hC h1) (GlueB'.bphi Amp hMain hC h1) F where
  e_one := fun {M} _ _ v hv n => (congrArg (e M n 0) (hv n)).trans (hone M n)
  etale_firstChern := fun {M} _ _ L v hv => hc1 M L.1 v hv
  first_chern_class_unique := fun {M} _ _ L x y hx hy => Subtype.ext (hU l hR (OK l K) M.X M.p (okToOC l K) L.1 L.2.1 _ _ hx hy)
  one_ex := fun {M} _ _ => one_ex hCH M
  cup_ex := fun {M} _ _ _ _ x y => cup_ex hCH M x y
  first_chern_class_exists := fun {M} a hM L => (hF.first_chern_class_exists a hM L).1
  β_one := fun {M} _ _ x hx => b_one hC M x hx
  β_cup := fun {M} _ _ _ _ x y z hz => b_cup hC M x y z hz
  beta_firstChern := fun {M} _ _ L x hx => h1 M.p (okToOC l K) true L.1 _ hx
  ψ_one := fun {M} a hM x y hx hy f => hF.one a hM x y hx hy f
  ψ_cup := fun {M} a hM _ _ x y z hz _ _ b b' f => hF.cup a hM x y z hz b b' f
  psi_firstChern := fun {M} a hM L x y hx hy f => hF.c1 a hM L x y hx hy f

end GlueP'

open GlueP' in

theorem glueP : GlueP := fun hCf hI h hE hP l _ K _ r ζ =>
  Exists.elim (cupEx l K r) fun μ hμ =>
  Exists.elim (h.p l K) fun Amp hA =>
  Exists.elim (hE l K ζ) fun e he =>
  Exists.elim (hP l K r ζ μ Amp hμ) fun F hF =>
  Exists.elim (phiPlus l K (per l K) Model.Sm r.perC r.iso (dat Amp) (r.xend ζ μ) (r.xmid ζ μ Amp) (facts l K)
      (hCf l K r).1 (hI l K) (glueL l K Amp (h.compatH l) (h.rin l) h.uniq hA.1 hA.2.1) (GlueE.emap Amp e he.1)
      (GlueB'.bmap Amp (h.main l) (h.compat l) (h.c1 l)) (GlueB'.bphi Amp (h.main l) (h.compat l) (h.c1 l))
      hA.2.2.1.some F (xlaws Amp r ζ μ (h.rin l) h.uniq (h.compatH l) (h.main l) (h.compat l) (h.c1 l) e he.1 he.2.1
        he.2.2.1 F hF)) fun c hc =>
  ⟨μ, F.k, c, hμ, fun M hM => ⟨he.2.2.2.2 M, Exists.elim (limOne_ex r M) fun x hx => ⟨_, x, hx, rfl⟩,
    fun L => ⟨he.2.2.2.1 M L.1, Exists.elim (hA.2.1 M hM) fun D hD => (hF.first_chern_class_exists ⟨D, hD⟩ hM L).2⟩⟩, hc⟩

end CrystallineSemistableComparison
end
end
