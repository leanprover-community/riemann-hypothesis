import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
import Formalism.SharpRestriction.InertJacobiLevels.ExtraKer
import Formalism.SharpRestriction.InertJacobiLevels.ExtraNch
import Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta
import Formalism.SharpRestriction.InertJacobiLevels.ResCharConj
import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat
import Formalism.SharpRestriction.InertJacobiLevels.ExtraEnt
import Formalism.LocalRingCardinality.DataMink

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain



theorem locLe_of_subsingleton {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    [Subsingleton V] (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (A B : Submodule (𝓞 K) V) : DV.LocLe w k A B :=
  fun x _ => ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [Subsingleton.elim ((1 : 𝓞 K) • x) 0]; exact Submodule.zero_mem _⟩




def lieOfSubsingleton (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [Subsingleton V] [Subsingleton W] : V ≃ₗᵢ[ℂ] W :=
  ⟨LinearEquiv.ofSubsingleton V W, fun x => by
    rw [Subsingleton.elim x 0, map_zero, norm_zero, norm_zero]⟩

set_option synthInstance.maxHeartbeats 200000 in

def rowSideZero (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    [Subsingleton EE] : RowSide D EE where
  Amb := fun _ => Z0
  Mult := fun _ _ => Z0
  multZero := fun _ => lieOfSubsingleton _ _
  multTop := fun _ => LinearIsometryEquiv.refl ℂ Z0
  io := fun _ _ => 0
  Mtilde := fun _ => zeroOLat _
  cen := fun _ => (Representation.trivial ℂ _ _).asAlgebraHom.comp (Subalgebra.val _)
  eOp := fun _ => 0
  eOp_idem := fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  eOp_sa := fun _ _ _ => by simp
  eOp_tie := fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  RR := zeroHLat D.what₂.LL
  RR_frames := (zeroHLat_good D.what₂.LL).1
  jEE := 0
  jEE_basis := ⟨by
    have : IsEmpty (zeroHLat D.what₂.LL).ι := inferInstanceAs (IsEmpty (Fin 0))
    exact linearIndependent_empty_type, Subsingleton.elim _ _⟩
  jEE_norm := fun x => (normAt_empty (ι := Fin 0) _ _ _ _).trans (by simp)

theorem rowSideZero_RRDef (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] [Subsingleton EE] : (rowSideZero D EE).RRDef := by
  intro x
  have hx : x = 0 := Subsingleton.elim (α := Fin 0 → D.what₂.LL) x 0
  rw [hx]
  exact ⟨fun _ w => ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [smul_zero]; exact Submodule.zero_mem _⟩, fun _ => Submodule.zero_mem _⟩

def trivialSide (D : D7) [Subsingleton D.what₂.EE0] : BaseLevelRowSide D := ⟨rowSideZero D D.what₂.EE0⟩

theorem trivialSide_rrDef_of_subsingleton (D : D7) [Subsingleton D.what₂.EE0] : (trivialSide D).s.RRDef := rowSideZero_RRDef D _

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped TensorProduct

theorem idxDefs_zero (D : D7) (X : DivX D) [∀ j, Subsingleton (X.MjH j).V] [∀ μ j, Subsingleton (D.what₂.MtL μ j)]
    (hI : ∀ μ j w, D.what₂.Ij μ j w = 0) (hj : ∀ μ j w, D.what₂.jw μ j w = 0) : IdxDefs D X where
  Ij_def := fun μ j w _ _ => by rw [hI, Idx.IjIdx_of_subsingleton]
  jw_def := fun μ j w _ _ => by rw [hj, Idx.jwIdx_of_subsingleton]

theorem lamDef_zero (D : D7) [∀ j, Subsingleton (D.what₂.Mj j)] : DV.LamDef D :=
  fun _ _ _ _ _ h => absurd (Subsingleton.elim _ _) h

theorem kapOf_zero {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {n : ℕ} (ty : Fin n → D.what₂.FT) (hn : n = 0) : S.kapOf ty = 1 := by
  subst hn
  unfold RowSide.kapOf
  split_ifs <;> simp

theorem kapSharp_zero (D : D7) (h : D.what₂.Drows = 0) : kapSharp D = 1 := kapOf_zero _ _ h

theorem kapRBase_zero {D : D7} (X : DivX D) (h : D.what₂.Drows = 0) (hk : X.kapR D.what₂.embLL = 1) : DV.KapRBase X :=
  hk.trans (kapSharp_zero D h).symm

theorem nuUnserved_zero {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) [∀ u, Subsingleton (D.div.Nu u).V] :
    NuUnserved X K := fun _ _ _ _ => ⟨locLe_of_subsingleton _ _ _ _, locLe_of_subsingleton _ _ _ _⟩

theorem dGamDef_of (D : D7) (h : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam) : DGamDef D :=
  fun u μ => ⟨fun u' μ' i hi c => by
    rw [h u μ, ← h u' μ']
    exact (D.chTw u' μ').dvd_DGam i hi c, h u μ⟩

theorem tensor_subsingleton (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
    [Subsingleton M] : Subsingleton (A ⊗[R] M) :=
  ⟨fun x y => by
    have h : ∀ z : A ⊗[R] M, z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul a m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    rw [h x, h y]⟩

set_option synthInstance.maxHeartbeats 400000 in

def nmjZero (D : D7) (X : DivX D) (c : NChoice D) [∀ j, Subsingleton (X.MjH j).V]
    [∀ i j b, Subsingleton (D.nexp.Fm i j b)] : NMj D X c where
  eMj := fun _ _ => 0
  eMj_smul := fun _ _ _ _ _ _ => by simp
  eMj_li := fun _ j _ _ _ => by
    have := hlat_index_isEmpty (X.MjH j)
    exact linearIndependent_empty_type
  eMj_lat := fun w j _ _ _ => by
    have := tensor_subsingleton (D.ntw.O (c.twI w)) (c.Oe w) (D.nexp.Fm (c.twI w) j (c.sd w))
    refine ⟨?_, le_of_eq (Subsingleton.elim _ _), fun x _ => ⟨1, one_ne_zero, ?_⟩⟩
    · rw [Subsingleton.elim (Submodule.span _ _) ⊥]
      exact Submodule.fg_bot
    · rw [Subsingleton.elim ((1 : c.Oe w) • x) 0]
      exact Submodule.zero_mem _
  eMj_th := fun w j _ _ _ _ _ _ _ => by
    have := tensor_subsingleton (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) (D.nexp.Fm (c.twI w) j (c.sd w))
    exact Subsingleton.elim _ _

def ambZero (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) [∀ μ, Subsingleton (S.Amb μ)] : AmbForm D S where
  MtH := fun _ => Examples₂.zeroHLat D.what₂.LL
  jAmb := fun _ => 0
  MtH_good := fun _ _ => Examples₂.zeroHLat_good D.what₂.LL
  jAmb_basis := fun _ _ => ⟨by
    have : IsEmpty (Examples₂.zeroHLat D.what₂.LL).ι := inferInstanceAs (IsEmpty (Fin 0))
    exact linearIndependent_empty_type, Subsingleton.elim _ _⟩
  jAmb_lat := fun _ _ _ => ⟨fun _ => ⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ => Submodule.mem_top⟩
  jAmb_gen := fun _ _ v _ => ⟨0, Subsingleton.elim _ _⟩
  jAmb_norm := fun _ _ x => (Examples₂.normAt_empty (ι := Fin 0) _ _ _ _).trans (by simp)

instance trivialSide_ambient_subsingleton (D : D7) [Subsingleton D.what₂.EE0] (μ : D.what₂.Tup) : Subsingleton ((trivialSide D).s.Amb μ) :=
  inferInstanceAs (Subsingleton Examples₂.Z0)

end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

structure Shape (D : D7) : Prop where
  mult : ∀ μ j, Subsingleton (D.what₂.Mult μ j)
  amb : ∀ μ, Subsingleton (D.what₂.Amb μ)
  mtL : ∀ μ j, Subsingleton (D.what₂.MtL μ j)
  mj : ∀ j, Subsingleton (D.what₂.Mj j)
  ee0 : Subsingleton D.what₂.EE0
  rr : Subsingleton D.div.RR.V
  nu : ∀ u, Subsingleton (D.div.Nu u).V
  lat : ∀ u j, Subsingleton ((D.fm u).lat j).V
  yTw : ∀ u μ i, IsEmpty ((D.chTw u μ).Y i)
  clsTw : ∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))
  mtV : ∀ i j b k Q ψ, Subsingleton (D.nexp.MtV i j b k Q ψ)
  fmN : ∀ i j b, Subsingleton (D.nexp.Fm i j b)
  ll0 : ∀ x : D.what₂.LL, x ∈ D.LL0
  Ij0 : ∀ μ j w, D.what₂.Ij μ j w = 0
  jw0 : ∀ μ j w, D.what₂.jw μ j w = 0
  drows : D.what₂.Drows = 0
  dgam : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamMink D
  loc : IsEmpty D.nd.Loc
  gatM : ∀ u w h, (D.gat u w h).M = ⊥
  gatComp : ∀ u w h, Nonempty ((D.gat u w h).comp ≃ (D.chTw u (D.what₂.muAt w)).cls 0)
  gatTr : ∀ u w h (c : (D.gat u w h).comp) (L L' : (D.gat u w h).P.Tup), (D.gat u w h).P.IsLatTup L →
    (D.gat u w h).P.IsLatTup L' → ∃ γ : ((D.gat u w h).lev c).Γ, L' = ((D.gat u w h).lev c).smul γ L

structure LevErr (D : D7) where
  lev : LevelData D
  errX : ErrX D
  piG_lev : PiGLevel D lev errX
  piT_lev : PiTLevel D lev errX
  seen : SeenDef D errX
  tauOf : TauOfDef D errX

def GaugeExists {R : Ranks} (H : Host R) (sp : @Spaces R H.F H.E _ _ _ _ H.cmStar _) : Prop :=
  letI := H.cmStar
  ∃ G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam H.F H.E sp.cm.sig, G.IsGauge

structure ExtraIn (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (X : DivX D) (cX : ExtraC) where
  shape : Shape D

  mjH : ∀ j, Subsingleton (X.MjH j).V
  kapR : X.kapR D.what₂.embLL = 1

  compS : ∀ u w h j, IsEmpty ((Gl.Lv u w h).compS j)
  vram : ∀ u w h, Gl.Vram u w h = ⊥
  latTied : G.LatTied hT Gi Gl

  ep_def : G.EpDef Gi cX.Ce
  ep_tie : EpTie Gi
  kapI_def : G.KapIDef Gi K
  fills_all : FillsAll hT Gl
  fdef : L.FDef

  kap_def : DV.KapDef D
  duStar_def : ∀ u, ((D.mem u).A.duStar : ℝ) = StandardLattice.duStarU D u
  Dstar_def : D.what₂.Dstar = StandardLattice.DstarD D
  cover : NTw.TwCover D.ntw

  le : LevErr D
  served : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    ServedEmb D u w h
  gauge : GaugeExists D.host D.sp

  large : cX.err.Large
  edef : L.EDef le.errX K cX.err

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D}
  {K : G.Consts} {X : DivX D} {cX : ExtraC}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def extraOf (I : ExtraIn D L hT Gi Gl K X cX) : Extra D L hT Gi Gl K X cX :=
  haveI := I.shape.mult
  haveI := I.shape.mtL
  haveI := I.shape.mj
  haveI := I.shape.ee0
  haveI := I.shape.nu
  haveI := I.shape.lat
  haveI := I.shape.yTw
  haveI := I.shape.mtV
  haveI := I.shape.fmN
  haveI := I.mjH
  haveI := I.shape.clsTw
  haveI := I.shape.loc
  { lev := I.le.lev
    th := thetaZero D
    th_io := thetaZero_io D
    cmp := latCmpZero D I.shape.gatM I.served
    lat := latDefsZero D I.shape.gatM I.served Gi Gl K I.vram
    tw := twFormsZero D
    ker := fun u w h =>
      haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
      haveI := I.shape.clsTw u (D.what₂.muAt w)
      haveI := I.compS u w h
      kerZeroE D hT I.shape.gatM I.served (twFormsZero D) (plEmb D) u w h (Gl.Ch u w h) (I.latTied u w h).2.1 (I.latTied u w h).1
        (I.shape.gatComp u w h).some (I.shape.gatTr u w h) (exists_latTup _)
    ep_def := I.ep_def
    ep_tie := I.ep_tie
    kapI_def := I.kapI_def
    fills_all := I.fills_all
    nu_unserved := nuUnserved_zero Gi K
    idx := idxDefs_zero D X I.shape.Ij0 I.shape.jw0
    kap_def := I.kap_def
    lam_def := lamDef_zero D
    kapR_def := kapRBase_zero X I.shape.drows I.kapR
    errX := I.le.errX
    err := ⟨I.large, I.le.piG_lev, I.le.piT_lev, I.le.seen, I.le.tauOf, dGamDef_of D I.shape.dgam, I.edef⟩
    nch := nchZero D (nchEmbOf D I.shape.ll0 I.cover)
    nch_tie := nchTie_zero D I.shape.ll0 I.cover
    xd := thDataZero D
    p0 := trivialSide D
    rationalRoots_def := trivialSide_rrDef_of_subsingleton D
    amb := haveI : ∀ μ, Subsingleton ((RowSide.sharp D).Amb μ) := I.shape.amb; ambZero D _
    amb0 := ambZero D _
    fdef := I.fdef
    duStar_def := I.duStar_def
    Dstar_def := I.Dstar_def
    gauge := I.gauge.choose
    gauge_def := I.gauge.choose_spec }

end Formalism.MainNotions.Inhab

end
end
