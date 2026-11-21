import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriplesGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalLocTripleWithLocalization
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistOfPlaceInWeightSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllTriplesLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPlaceDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqRationalDataOfEigenStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemImpAltAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeAlgebraHasStableSublayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGaloisPsiLevelAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqRationalDataOfEigen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigOfRatAd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPlaceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SatakeIdentityOfIsTriple

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.InW1TwistAtMember
theorem twist_mem_weightOne_subspace_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  intro _ _ hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  intro a
  rw [n.tie.twOf_eq a]
  exact GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.D Z) nch n.tie B.coeffGaloisSubfield_isGalois _ ((w.D Z).nd.w_tw a)
end GlobalTheory.HeightCounting.InW1TwistAtMember
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_index_place_tw_of : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  first | exact @_root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt | exact _root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt | (intros; apply _root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay.EigCopy
set_option maxHeartbeats 4000000 in
theorem parIn_built_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (_root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  exact ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩
end GlobalTheory.RowTriple.Lay.EigCopy
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay.EigCopy
set_option maxHeartbeats 4000000 in
theorem eigenvalues_at_member_tripleLayer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => ∀ (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ), HEq S (ratL c.a.nt.L c.a.nt.S) → HEq hL' c.a.nt.hL → HEq eig c.a.nt.eig → HEq θ c.a.nt.θ → ∃ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (w.D Z) (TC.cf w.I w.l Z) Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig := by
  intro hN hS hL
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.T.exists_superset_low_heckeRd_of_subset_S0 hN hS hL) (_root_.GlobalTheory.T.exists_theta_heq_lvlPsi_at_members hN hS hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c hE H S hL' eig θ hS' hhL heig hθ
  obtain ⟨H2, H3⟩ := H
  obtain ⟨e⟩ := hE
  have e' : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  obtain ⟨Sb, eg, hSb, heq, hAd⟩ := e'.eig
  obtain ⟨Sb', hsub, hS0, hlow, hrd⟩ := H2 Sb hSb
  obtain ⟨θ0, hθ0, hψ⟩ := H3
  obtain ⟨Rw0, hRw0, ⟨hpar⟩⟩ := _root_.GlobalTheory.RowTriple.Lay.EigCopy.parIn_built_alt c.a.nt _ c.row.rep_eq
  have hT := _root_.GlobalTheory.TwInputs.Eig.eigTrue_of_read hL t.r.Y t.r.z.pins.char.base.lev hpar.T Rw0 hpar.row hAd hsub hlow
  have hO := GlobalTheory.TwInputs.Eig.eigOcc t.r.Y t.r.z.pins.char.base.lev t.r.intersectionNumber_baseChange.prim.unif t.r.z.pins.char.base.models.HW
    t.r.z.good.2 hψ hAd hsub hlow hrd
  rw [t.r.z.lev.C] at hT
  obtain rfl : S = _ := eq_of_heq (hS'.trans c.row.S_eq)
  obtain rfl : hL' = c.row.hecke.hL := eq_of_heq (hhL.trans c.row.hL_eq)
  obtain rfl : eig = eg := eq_of_heq (heig.trans heq)
  obtain rfl : θ = θ0 := eq_of_heq (hθ.trans hθ0.symm)
  refine ⟨Sb', hS0, fun Rw hRw => ⟨eigTrue_congr ?_ hT, hO⟩⟩
  exact eq_of_heq (hRw0.trans hRw.symm)
end GlobalTheory.RowTriple.Lay.EigCopy
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleSystem_tripleLayer_eigenvalues_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => ∀ (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ), HEq S (ratL c.a.nt.L c.a.nt.S) → HEq hL' c.a.nt.hL → HEq eig c.a.nt.eig → HEq θ c.a.nt.θ → ∃ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (w.D Z) (TC.cf w.I w.l Z) Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig := by
  first | exact @_root_.GlobalTheory.RowTriple.Lay.EigCopy.eigenvalues_at_member_tripleLayer_alt | exact _root_.GlobalTheory.RowTriple.Lay.EigCopy.eigenvalues_at_member_tripleLayer_alt | (intros; apply _root_.GlobalTheory.RowTriple.Lay.EigCopy.eigenvalues_at_member_tripleLayer_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem readTw_withLoc_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (a : (withLoc b.L).nd.Loc) :
    ReadTw (withLoc b.L) a := by
  have hpq : (withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a) = (withLoc b.L).nd.l a := (withLoc b.L).ntw.twOf_l a
  refine ⟨(castQ hpq).symm.toRingHom.comp (((withLoc b.L).naut.iotaQ a).comp
      (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a))),
    (castQ hpq).trans ((withLoc b.L).naut.iotaQC a), ?_, ?_, ?_⟩
  · intro z
    obtain ⟨z', hz⟩ := exists_heq hpq z
    show (castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    erw [b.Sp.twO_alg a z z' hz, (withLoc b.L).naut.iotaQ_alg a z']
    exact castQ_alg hpq z z' hz
  · intro x
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ _)))) = _
    have hemb : ∀ x : ↥b.D.LL0, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a)
        ((if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x) =
        (withLoc b.L).nd.embK a (x : b.D.what₂.LL) :=
      fracMap_eq ((withLoc b.L).ntw.twist₂ a) _ (if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a))
        (((withLoc b.L).nd.embK a).comp (algebraMap ↥b.D.LL0 b.D.what₂.LL)) (fun x y hy => (withLoc b.L).ntw.twO_emb a x y hy)
    rw [RingEquiv.apply_symm_apply, hemb x]
    exact (withLoc b.L).naut.iota_LL a _
  · intro y
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap _ _ y))))) = _
    rw [RingEquiv.apply_symm_apply, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    rfl
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sideB_built_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D')
    (ψ : D'.nd.Loc → NC.HC D'.host.E) (hψ : ∀ a, NC.ReadC D'.nd.plOm.1 (D'.ntw.psiL a) (NC.iotaC D' a) (ψ a) 0)
    (cf : CharFrame D') (hcf : HEq cf (cfL b.L b.cf))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D'.host.E)) → PlE D'.host) (hPq : HEq Pq b.Pq)
    (S : RatDat D'.ntw) (hS : HEq S (ratL b.L b.S))
    (hL' : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL (S.WL j)) (hhL : HEq hL' b.hL)
    (eig : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0) (heig : HEq eig b.eig)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ) (hθ : HEq θ b.θ) :
    ∃ Rw : RowSide D', HEq Rw.locR b.A.row.locR ∧ Nonempty (SideB D' cf Rw b.low Pq S hL' eig θ) ∧
      (∀ a σ v, IsSplitPl D'.host v → D'.naut.locW a σ v = Rw.locR σ v) := by
  obtain ⟨D, cf0, jE, A, cg, au, rep, row, low, Pq0, S0, hL0, eig0, θ0, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  obtain rfl := eq_of_heq hcf
  obtain rfl := eq_of_heq hPq
  obtain rfl := eq_of_heq hS
  obtain rfl : hL0 = hL' := (eq_of_heq hhL).symm
  obtain rfl : eig0 = eig := (eq_of_heq heig).symm
  obtain rfl : θ0 = θ := (eq_of_heq hθ).symm
  obtain ⟨Rw, hRw, Bs', -⟩ := GlobalTheory.T.twist_second_step_kept_with_localisations D cf0 A.row low Pq S0 hL0 eig0 θ0 Bs L ψ hψ
  refine ⟨Rw, hRw, ⟨Bs'⟩, fun a σ v _ => ?_⟩
  have e : Rw.locR = A.row.locR := eq_of_heq hRw
  rw [e]
  exact Au.locW a σ v
set_option maxHeartbeats 4000000 in
theorem isKsForm_of_built_heq (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D') (S : RatDat D'.ntw)
    (hS : HEq (ratL b.L b.S) S) (h : ∀ j, 1 ≤ j → j ≤ b.D.R.m → (b.S.A j).IsKsForm) :
    ∀ j, 1 ≤ j → j ≤ D'.R.m → (S.A j).IsKsForm := by
  obtain ⟨D, cf0, jE, A, cg, au, rep, row, low, Pq0, S0, hL0, eig0, θ0, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  obtain rfl := eq_of_heq hS
  exact h
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
end GlobalTheory.RowTriple.Lay
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
end GlobalTheory.RowTriple.Lay
namespace GlobalTheory.RowTriple.Lay
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tripleLayer_inputs_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ (cf : CharFrame (w.D Z)) (Rw : RowSide (w.D Z)) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.D Z).host.E)) → PlE (w.D Z).host) (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ) (_ : SideB (w.D Z) cf Rw low Pq S hL' eig θ) (Sb : Finset (PlE (w.D Z).host)), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (S.A j).IsKsForm) ∧ GlobalTheory.TwInputs.EigTrue (w.D Z) cf Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig ∧ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw ∧ (w.D Z).nexp.sig_all ∧ (∀ a σ v, IsSplitPl (w.D Z).host v → (w.D Z).naut.locW a σ v = Rw.locR σ v) ∧ ∀ a, GlobalTheory.RowTriple.ReadTw (w.D Z) a := by
  intro hP hS hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_galSide_cf_eq_cgTrue_at_members hP hS hL)
    (_root_.GlobalTheory.T.good_cusp_param_at_member_of_heq_locR hP hL)) (_root_.GlobalTheory.T.compatibleSystem_tripleLayer_eigenvalues_alt hP hS hL))
    fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨⟨G, -, -, -⟩, hpar⟩, heigH⟩ := h
  have hcf : HEq (TC.cf w.I w.l Z) (cfL c.a.nt.L c.a.nt.cf) := heq_cf_of_pack c.a.nt.pack
  obtain ⟨eig, heig⟩ := exists_heq_of_eq (F := fun D : D7 => ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) c.a.nt.eq.symm
    c.a.nt.eig
  obtain ⟨θ, hθ⟩ := exists_heq_of_eq (F := fun D : D7 => ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    c.a.nt.eq.symm c.a.nt.θ
  obtain ⟨Rw, hRw, ⟨Bs⟩, hloc⟩ := _root_.GlobalTheory.RowTriple.Lay.sideB_built_alt hL (w.D Z) c.a.nt.toNBuilt c.a.all.chiD.psi c.a.all.chi.psi (TC.cf w.I w.l Z) hcf
    c.a.Pq c.a.Pq_eq.symm _ c.row.S_eq.symm c.row.hecke.hL c.row.hL_eq.symm
    eig heig θ hθ
  obtain ⟨Sb, hSb, hET⟩ := heigH _ c.row.hecke.hL eig θ c.row.S_eq.symm c.row.hL_eq.symm heig hθ
  obtain ⟨hT, hO⟩ := hET Rw hRw
  have hR : ∀ a, ReadTw (withLoc c.a.nt.L) a := _root_.GlobalTheory.RowTriple.Lay.readTw_withLoc_alt hL _ c.a.nt.toNBuilt
  rw [← c.a.nt.eq] at hR
  exact ⟨TC.cf w.I w.l Z, Rw, c.a.nt.low, c.a.Pq, _, c.row.hecke.hL, eig, θ, Bs, Sb, hSb,
    _root_.GlobalTheory.RowTriple.Lay.isKsForm_of_built_heq hL (w.D Z) c.a.nt.toNBuilt _ c.row.S_eq c.a.ratIn.ks, hT, hO, hpar Rw hRw,
    _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion.sig_all G.triple, hloc, hR⟩
end GlobalTheory.RowTriple.Lay
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleSystem_tripleLayer_inputs_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ (cf : CharFrame (w.D Z)) (Rw : RowSide (w.D Z)) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.D Z).host.E)) → PlE (w.D Z).host) (S : RatDat (w.D Z).ntw) (hL' : ∀ j, ℕ → PlE (w.D Z).host → Module.End (w.D Z).what₂.LL (S.WL j)) (eig : ℕ → (w.D Z).what₂.FT → ℕ → PlE (w.D Z).host → ↥(w.D Z).LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ) (_ : SideB (w.D Z) cf Rw low Pq S hL' eig θ) (Sb : Finset (PlE (w.D Z).host)), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (S.A j).IsKsForm) ∧ GlobalTheory.TwInputs.EigTrue (w.D Z) cf Rw Sb eig ∧ GlobalTheory.TwInputs.EigOcc (w.D Z) S θ hL' Sb eig ∧ GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw ∧ (w.D Z).nexp.sig_all ∧ (∀ a σ v, IsSplitPl (w.D Z).host v → (w.D Z).naut.locW a σ v = Rw.locR σ v) ∧ ∀ a, GlobalTheory.RowTriple.ReadTw (w.D Z) a := by
  first | exact @_root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt | exact _root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt | (intros; apply _root_.GlobalTheory.RowTriple.Lay.tripleLayer_inputs_at_member_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end GlobalTheory.RowTriple
namespace GlobalTheory.RowTriple
open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal
theorem forall_triple_condition_of_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.AllTriples (w.D Z) := by
  intro hP hS hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.T.compatibleSystem_tripleLayer_inputs_alt hP hS hL) fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨cf, Rw, low, Pq, S, hL', eig, θ, Bs, Sb, hSb, hKs, hT, hOcc, hcp, hall, hloc, hR⟩ := h
  exact GlobalTheory.TwistedSelmerCompare.allTriples_of_tripAll _
    (tripAll_of_sideB _ cf Rw low Pq S hL' eig θ Bs Sb hSb hKs hT hOcc hcp hall hloc hR)
end GlobalTheory.RowTriple
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allTriples_at_members_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.AllTriples (w.D Z) := by
  first | exact @_root_.GlobalTheory.RowTriple.forall_triple_condition_of_member_alt | exact _root_.GlobalTheory.RowTriple.forall_triple_condition_of_member_alt | (intros; apply _root_.GlobalTheory.RowTriple.forall_triple_condition_of_member_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.HeightCounting.Up.TripFin
theorem finiteTriples_satisfy_condition_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.PtCore.TriplesGood (w.D Z) := by
  intro hP hS hL
  have h := _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_galSide_cf_eq_cgTrue_at_members hP hS hL) (_root_.GlobalTheory.T.nonzero_index_place_tw_of hP hS hL)) (_root_.GlobalTheory.T.allTriples_at_members_of_third_layer hP hS hL)
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp h ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨⟨G, -, -, -⟩, hW⟩, hA⟩ a σ Sg h1 h2
  obtain ⟨s, hs⟩ := hA a σ Sg h1 h2
  exact ⟨s, hs, (_root_.GlobalTheory.Triple.adm8_allGood_sig_of_isTriple _ G.triple).2.1 _ (hW a) s⟩
end GlobalTheory.HeightCounting.Up.TripFin
end
end
end
