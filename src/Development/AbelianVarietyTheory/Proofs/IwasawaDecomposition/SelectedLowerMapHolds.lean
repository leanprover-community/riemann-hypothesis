import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapSharpAmbientTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToLevelOfDvdTrueDGam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTwGen
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonalStatement

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.R3.GamDvd

attribute [local instance] starE

section Stab

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)

def stabRat (d : DecoSet X.E n ST SG) : MulAction.stabilizer (FormG Λ) d →* autO d.1.N where
  toFun g := ⟨(g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n), g.1.1.2,
    congrArg (fun e : DecoSet X.E n ST SG => e.1.N) ((MulAction.mem_stabilizer_iff).1 g.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem stabRat_injective (d : DecoSet X.E n ST SG) : Function.Injective (stabRat Λ d) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hγ : (g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) = 1 := congrArg Subtype.val hg
  have hbe := congrArg (fun e : DecoSet X.E n ST SG => e.1.be) ((MulAction.mem_stabilizer_iff).1 g.2)
  have hM : ∀ w : SG, ((g.1.2 : GLG X.E n SG) w : Matrix (Fin n) (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) = 1 := by
    intro w
    refine Matrix.ext_of_mulVec_single fun i => ?_
    obtain ⟨x, -, hx⟩ := d.2.be_surj w (Pi.single i 1)
    have e := congrFun (congrFun hbe w) x
    change ((g.1.2 : GLG X.E n SG) w : Matrix (Fin n) (Fin n) _).mulVec
      (d.1.be w ((g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n).symm x)) = d.1.be w x at e
    rw [hγ] at e
    change ((g.1.2 : GLG X.E n SG) w : Matrix (Fin n) (Fin n) _).mulVec (d.1.be w x) = d.1.be w x at e
    rw [hx] at e
    rw [e, Matrix.one_mulVec]
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hγ
  · exact Subtype.ext (funext fun w => Units.ext (hM w))

theorem card_stab_dvd (d : DecoSet X.E n ST SG) :
    Nat.card (MulAction.stabilizer (FormG Λ) d) ∣ Nat.card (autO d.1.N) :=
  Subgroup.card_dvd_of_injective (stabRat Λ d) (stabRat_injective Λ d)

end Stab

section Fam

variable {B : Base} {px : PreX B.toPre} (I : TC B px) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL))
  (tr : TrI B px)

theorem gamDvd_DGam :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ DGam B.fields.E B.R) ∧
    ∀ (j : Fin B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ DGam B.fields.E B.R := by
  refine ⟨fun t c => ?_, fun j t c => ?_⟩
  · rw [Fintype.card_eq_nat_card]
    exact (card_stab_dvd _ (Quotient.out c)).trans
      (dvd_DGam (posStar_of_ok hX) B.R (pred_mem_gamRanks B.R) (Quotient.out c).2.lat (Quotient.out c).2.uni)
  · rw [Fintype.card_eq_nat_card]
    exact (card_stab_dvd _ (Quotient.out c)).trans
      (dvd_DGam (posStar_of_ok hX) B.R (nV_mem_gamRanks B.R) (Quotient.out c).2.lat (Quotient.out c).2.uni)

theorem gamDvd (l : I.Laws) (Z : Later B (I.cols l)) :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ ((I.rec7 l Z).mem (I.rec7 l Z).u₀).C.DGam) ∧
    ∀ (j : Fin B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ ((I.rec7 l Z).mem (I.rec7 l Z).u₀).C.DGam :=
  gamDvd_DGam I hX U Xg tr


end Fam

end GlobalTheory.Mem.R3.GamDvd
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.SelRowPin

theorem amb_of_eq {D : D7} {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ} {A : FamIn D.what₂.LL Gp Pl0 T m}
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    {X : RowSide D EE} {Fm Fm' : AmbForm D X} {P : Subgroup Gp} {ψ : P →* D.what₂.LLˣ} {tup tup' : T → D.what₂.Tup}
    {jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)}
    {jA' : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup' t)}
    (hF : Fm = Fm') (h : tup = tup') (hj : HEq jA jA') :
    (∃ J, AmbTie D A X Fm' P ψ tup' jA' J) → ∃ J, AmbTie D A X Fm P ψ tup jA J := by
  subst hF; subst h; cases hj; exact id

set_option maxHeartbeats 4000000 in

theorem selected_lower_map_third_stage : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.sat.P → HEq sS q.sat.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → Formalism.L2.Rows.RowSideDetermined R.T (divisionPairOfAdelicFormsFaceColumnsData x) := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ R hR sP sS _ _ a x hax
  obtain rfl := eq_of_heq hax
  obtain ⟨he, hTw⟩ := hR.s.tw
  have hC : TC.StdC q.w.I q.w.l q.Z R.T.cols := hR.s.cols ▸ q.x.col.std
  apply GlobalTheory.Mem.R3.lower_map_sharp_ambient_tie _ _ _ _ _ _ _ _ q.O.ex a.x R.T
  · exact fun u => GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie q.w.I q.w.ok q.w.pins q.w.l q.Z u _ _ _ (hC u)
  · exact fun u μ hμ _ h1 => GlobalTheory.Mem.Col2.LowerTie.lowerMap_tieTw q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ _ _ _ _ _ _ q.O.ex R.T he hC hTw u μ hμ h1
  · cases a with
    | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
    cases x with
    | mk G Pl0 I0 T' A3 core R' F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
    cases pack
    exact amb_of_eq rfl (eq_of_heq htup) hjA q.x.obj.amb.1
  · cases a with
    | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
    cases x with
    | mk G Pl0 I0 T' A3 core R' F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
    cases pack
    exact GlobalTheory.Mem.R3.GamDvd.gamDvd q.w.I q.x.what₂.hX _ _ _ q.w.l q.Z

end GlobalTheory.Mem.R3.SelRowPin
end
