import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PinOfNTrue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPlacesOverOfIsConjPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.LabAllOf

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem labAll_of_labTrue_labConj : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), LabTrue D T → LabConj D T →
    GlobalTheory.PendOf.LabAll D T := by
  intro D T hT hC
  have key : ∀ (k : Fin 2) (w : PlE D.host), ∃ γ : G D.host.E D.nd.Om,
      (∀ v, w = D.naut.plGw k v → γ = D.ntypes.tg k v) ∧
      ∀ v, IsConjPl D.host (D.naut.plGw k v) w → ∃ c : D.nd.Om ≃+* D.nd.Om,
        (∀ x : D.host.E, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x)) ∧
        (∀ x, x ∈ D.nd.plOm.1 (D.naut.plGw k v) ↔ c x ∈ D.nd.plOm.1 w) ∧ (∀ x, γ (c x) = c (D.ntypes.tg k v x)) ∧
        ∀ a : D.naut.LP w, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
          D.naut.items₂ k w a = GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) γ (T.e w a) := by
    intro k w
    by_cases h : ∃ v, IsConjPl D.host (D.naut.plGw k v) w
    · obtain ⟨v, hv⟩ := h
      obtain ⟨c, γ, h1, h2, h3, h4⟩ := hC k v w hv
      refine ⟨γ, fun v' e => absurd (e ▸ hv) (D.naut.plGw_nconj k v v'), fun v' hv' => ?_⟩
      obtain rfl : v = v' := D.naut.plGw_inj k (GlobalTheory.HeightCounting.LabConjModel.eq_of_isConjPl hv hv')
      exact ⟨c, h1, h2, h3, h4⟩
    · refine ⟨Function.extend (D.naut.plGw k) (D.ntypes.tg k) (fun _ => 1) w, fun v e => ?_,
        fun v hv => absurd ⟨v, hv⟩ h⟩
      rw [e]; exact (D.naut.plGw_inj k).extend_apply _ _ v
  choose γ h1 h2 using key
  refine ⟨γ, fun k v => h1 k _ v rfl, fun k v w' hw' => ?_, fun k w hw a => ?_⟩
  · obtain ⟨c, hc1, hc2, hc3, -⟩ := h2 k w' v hw'
    exact ⟨c, hc1, hc2, hc3⟩
  · obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [h1 k _ v rfl]; exact hT k v a
    · obtain ⟨c, -, -, -, h4⟩ := h2 k w v hv
      exact h4 a

end GlobalTheory.LabAllOf

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneLabels_all_places_of_fixed_and_conj : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), LabTrue D T → LabConj D T → GlobalTheory.PendOf.LabAll D T := by
  atlas_forward_decl GlobalTheory.LabAllOf.labAll_of_labTrue_labConj
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.GreenSide

open Polynomial

theorem eSerC_eq_of_gen (hG : GlobalTheory.Published.GreenCuspidal) (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g)
    (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (z : ℕ → Formalism.CyclotomicNorms.Fbar g) (hz : IsGenSys z) (he : z = L.gen) (htL : t = L.teich)
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht z hz))
    (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht z hz) τ (O.lab d τ))
    (r : ℕ) (f : (ZMod g)[X]) (hr : 1 ≤ r) : GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  subst he
  exact GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG g L t ht hz htL O hO r f hr

theorem exists_greenLab : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7) (cf : CharFrame D) (Γ : GrpSide D), TypesTrue D.ntypes cf.P cf.W → (∀ k, Γ.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩)) → ∃ Γ' : GrpSide D, GlobalTheory.PendOf.GreenLab Γ' ∧ ∀ k, Γ'.ζ k = Γ.ζ k := by
  intro hG D cf Γ hT hζ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have key : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k))
          (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)),
        Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
        (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod (D.host.g k)))), 1 ≤ d → CategoryTheory.Simple τ →
          Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod (D.host.g k)) τ →
          Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k)) τ
            (O.lab d τ)) ∧
        ∀ f, D.ntypes.eSer k f = eSerO O D.R.r f := by
    intro k
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨O, h1, h2, hO⟩ := GlobalTheory.CuspTwist.exists_labelMap_twist_cuspLabel (ZMod (D.host.g k)) _
      (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (Γ.ζ k) (Γ.ζ_gen k))
    exact ⟨O, h1, h2, hO, fun f => (hT.ser k f).trans
      (eSerC_eq_of_gen hG _ _ _ _ _ _ (hζ k) (hT.teich k) O hO D.R.r f hr)⟩
  refine ⟨{ Γ with
    O := fun k => (key k).choose
    eSer_def := fun k f => (key k).choose_spec.2.2.2 f
    O_equiv := fun k => (key k).choose_spec.1
    O_tw := fun k => (key k).choose_spec.2.1 }, ?_, fun _ => rfl⟩
  intro k d
  exact (key k).choose_spec.2.2.1 d

end GlobalTheory.GreenSide

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_green_cuspidal_labelling_same_generators : GlobalTheory.Published.GreenCuspidal → ∀ (D : D7) (cf : CharFrame D) (Γ : GrpSide D), TypesTrue D.ntypes cf.P cf.W → (∀ k, Γ.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩)) → ∃ Γ' : GrpSide D, GlobalTheory.PendOf.GreenLab Γ' ∧ ∀ k, Γ'.ζ k = Γ.ζ k := by
  atlas_forward_decl GlobalTheory.GreenSide.exists_greenLab
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.PinLayer

set_option maxHeartbeats 4000000 in

theorem pinAt_of_side {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) (hG : GlobalTheory.Published.GreenCuspidal) (hT : TypesTrue D.ntypes cf.P cf.W) (hval : ValLL0 D cf)
    (rep' : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hrep : HEq a.nt.rep rep')
    (hinj : ∀ σ σ', (rep' σ).Iso (rep' σ') → σ = σ') (hE : Elem D) (hcheb : GlobalTheory.RowTie.ChebSplit D.nd)
    (labc : LabConj a.nt.D a.nt.A.wdT)
    (zeta : ∀ k, a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩ (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)) :
    ∃ P : GlobalTheory.NPin.Pin hL D, PinAt a P := by
  rcases a with ⟨nt, all, chr_eq, host, frameN, chrN, chrGal, Pq', Pq_over, pq, jE_eq, mt_eq, Pq_eq, low', split, ratIn, ratIn_hL, ratIn_eig, ratIn_θ, depth⟩
  obtain ⟨⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hLm, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, heq⟩, pack⟩ := nt
  dsimp only at pack heq hrep labc zeta mt_eq ⊢
  subst heq
  cases pack
  cases hrep
  obtain ⟨Hk, hHk⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hE.star hE.int hE.split hcheb big L Sp Au
  obtain ⟨ty⟩ := GlobalTheory.HeightCounting.typesOpen_withLoc D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hE.star hE.int hE.split hcheb big L Sp Au ss
  obtain ⟨tw⟩ := GlobalTheory.T.side_multiplicity_character D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hE.star hE.int hE.split hcheb big L Sp Au
  obtain ⟨Γ, hΓ, -⟩ := GlobalTheory.T.exists_green_cuspidal_labelling_same_generators hG (withLoc L) (cfL L cf0) { A.grp with } hT zeta
  refine ⟨{ cf := cfL L cf0, C := chL L C0, tp := tpL L tp0, chr := tw.chrN, val := hval, Q_eq := ?Q, T := { A.wdT with }, lab := A.lab, cg := { cg with }, M := mtL L M, H := Hk, au := ?au, rep := rep, rep_inj := hinj, row := ?row, locW_eq := fun i i' σ w => (Au.locW i σ w).trans (Au.locW i' σ w).symm, jE := jE, ty := { ty with grp := Γ }, wd := { A.wd with }, wdOf := Au.wdOf }, ⟨rfl, rfl, HEq.rfl, HEq.rfl, eq_of_heq mt_eq, ?lab, hΓ, ?chiT⟩⟩
  case Q =>
    intro i
    have hm : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i hm).trans (Sp.Qc_eq _ _)
  case au =>
    intro j h1 h2 π s σ h
    rw [hHk]
    exact au j h1 h2 π s σ h
  case row =>
    intro i
    refine ⟨fun σ s τ h => ?_, fun σ v w hvw Dv hα => ?_⟩
    · exact (congrArg (A.wdT.e s.w) (Au.locW i σ s.w)).trans (row.1 σ s τ h)
    · obtain ⟨α, h1, h2⟩ := row.2 σ v w hvw Dv hα
      exact ⟨α, h1, (Au.satW i σ w).trans h2⟩
  case lab =>
    exact GlobalTheory.T.weilDeligneLabels_all_places_of_fixed_and_conj _ _ A.lab labc
  case chiT =>
    exact A.chiT

set_option maxHeartbeats 4000000 in

theorem pin_atMem : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL,
    AtMem hL fun _ _ _ _ w Z _ _ t nch n c => ∃ P : GlobalTheory.NPin.Pin hL (w.D Z), PinAt c.a P := by
  intro hP hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c hE _ _ => ?_
  obtain ⟨e⟩ := hE
  have e' : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  have hT : TypesTrue (w.D Z).ntypes (TC.cf w.I w.l Z).P (TC.cf w.I w.l Z).W := by
    show TypesTrue _ w.I.C.P w.I.C.W
    rw [w.C_eq]
    exact t.grp
  have hEl : Elem (w.D Z) := by
    refine ⟨fun y => ?_, fun j g => ((w.D Z).hc ((w.D Z).eTau.symm g)).e_int j, fun v hv => ?_⟩
    · exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
        (starRingEnd (w.D Z).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩
    · have hc : ∀ p ∈ (w.D Z).host.levelPrimes, p.Prime ∧ p % ((w.D Z).host.QS * (w.D Z).host.q * (w.D Z).host.d) = 1 :=
        (w.st Z).B.level_cond
      rcases hv with hv | hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.1 v hv
      · exact GlobalTheory.HeightCounting.Up.isSplitPl_of_mem_levelPrimes _ hc (w.D Z).host.pde_level.2 v hv
  exact pinAt_of_side c.a hP.greenC hT (GlobalTheory.HeightCounting.Up.valLL0_colW w Z)
    (fun σ => Formalism.IndefR.principalLevelFrame.rowRepR t.r.z.R.θ (t.r.Y.eFT σ)) c.row.rep_eq
    (fun σ σ' h => t.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) hEl
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _) e'.labc e'.zeta

end GlobalTheory.PinLayer
end
