import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadInjectiveStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRationalityAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRationalityAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPrimeMemExceptionalSetStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InGeoGeoHalfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatIoAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlace

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.read_injective : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.readInj_alt | exact _root_.GlobalTheory.BigOn.Exp.readInj_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.readInj_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
theorem kerOfAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p hR hM w hw j => ?_⟩⟩⟩
  intro ρ hρ hpin
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have hpl := placesAt (j := j) hw hρ hpin
  have hl : (Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w) = Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w) := by
    rw [(Fm.ex x hx i).nch.twI_l, Formalism.L2.G.ServJoint.plc_plEq]
  have hpD : ∀ P, P ∈ (Fm.D x i).ntw.pD ((Fm.ex x hx i).nch.twI w) ↔
      ((ownAt (Fm.D x i) ((Fm.D x i).plEq w) : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal := fun P => by
    rw [← Finset.mem_coe, (Fm.D x i).ntw.pD_eq, ownAt, ← hl]
    rfl
  have hQ : (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.Q = plW p w := by
    ext P
    rw [hpl.1 P, hpD P]
    unfold plW GlobalTheory.OnTies.placesOver
    classical
    rw [Finset.mem_filter]
    rfl
  have hwt : (Fm.D x i).plEq w ∈ (R2 p).twPl := hw
  obtain ⟨ω, φ, hK⟩ := GlobalTheory.OnCmp.exists_baseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on
  obtain ⟨χ, ξR, hD⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on ω φ hK
  have hχ : χ = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi :=
    GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ hD.chr (hl ▸ hpin.delta _ j _)
  subst hχ
  have hω := hρ.weil_base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  rw [Base.IsWeil, mul_one, Base.mu, hpin.psi, hpin.mu0, hpin.eta] at hω
  refine ⟨hBo, hQ, ξR, φ, { hD with weil := hω }⟩
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kerOfAt' : _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.SerBase.kerOfAt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
theorem traceOfAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt' := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hR hM w hw j => ?_
  intro ρ hρ hpin hlev h P
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have key := GlobalTheory.T.thetaTraceLevelCompatible_proof _ _ _ _ _ _ (R2 p) (F2 p) hC j _ (hρ.base _ j _) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)))
    ?_ ?_ ?_ _ (hρ.weil_base _ j _) h P
  · exact key.symm
  · intro g Q hQ hQ' a c
    have e := hpin.grp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ((p.R.eG.trans p.cG) g) Q hQ hQ' a c
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at e
    exact e
  · intro g
    exact mem_level_iff hM.2.2 hlev _ j _ g
  · intro u hu
    refine (level_chi hM.2.2 hρ hlev _ j _ u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_rationality_at_place' : _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt' := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.SerBase.traceOfAt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratHyp0_of_bad_prime_mem_S0 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p →
  ∀ t : (Fm.D x i).ntw.Tw, (Fm.D x i).ntw.NonzeroIndexPlace t →
  (∀ P : Pl (Fm.D x i).host.E, (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 *
    (Fm.D x i).host.pde * (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 t) →
  ∀ j : Fin (Fm.D x i).R.m, RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt | exact _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt in
theorem kerRatAt_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt := by
  intro hP hA hR hS
  refine (_root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt.and _root_.GlobalTheory.BigOn.Exp.twAdm_alt).imp fun Fm x hx i p hp hM w hw j hLT => ?_
  obtain ⟨l1, l2⟩ := hLT
  have h0 := _root_.GlobalTheory.T.ratHyp0_of_bad_prime_mem_S0 Fm x hx i p hp hM _ l2.2.2 l1 j
  obtain ⟨c', w', hw', hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.T.inGeo_half_of_ratHyp0 hP Fm x hx i p hp hM _ j h0)
  obtain ⟨S', YS', -⟩ := GlobalTheory.T.seriesRationality_back_from_movedReadings p.R p.cG p.Sx p.nexp w' hw'
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w').toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w' hw' h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w').toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w').phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w') (F2 p) B'.κ B'.v₀ B'.O ((Fm.ex x hx i).nch.twI w) j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  intro χ ξR ω φ hK h hh y hy u hu
  have hK' : KerDat (fullHeckeRealDatMovedReadings p.R w').toRealDat j ((fullHeckeRealDatMovedReadings p.R w').C.delAt (Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w))) χ ξR
      (placesOver (fullHeckeRealDatMovedReadings p.R w').toRealDat ((fullHeckeRealDatMovedReadings p.R w').mu ((Fm.D x i).plEq w)) (ownAt (Fm.D x i) ((Fm.D x i).plEq w)))
      ω φ := ⟨hK.chr, hK.fin, hK.triv, hK.tame, hK.pl, hK.off, hK.ram, hK.res, hK.weil, hK.vec⟩
  have hy' : InCoefLat (fullHeckeRealDatMovedReadings p.R w').toRealDat j h y := hy
  obtain ⟨x', hx'⟩ := kerRat_framed (T := setCE p.T c') hP hA hR hS YS' hRat (fun k => p.phsOne k) ((Fm.D x i).plEq w) hK' hh
    hy' u (by rw [hv]; exact hu)
  exact ⟨(p.R.FW j).ρ (w' j (sg0 _ p.P.A3.A)) x', hx'⟩
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_rationality_of_reciprocity_hypotheses_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.SerBase.kerRatAt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
section GenericCmp
variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}
variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))
end GenericCmp
end GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 4000000 in
theorem readCmpAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt := by
  unfold _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hr hm w _ j => ?_
  intro ρ hρ e he1 he2 ν hν rd hcan u hu f y a hfa
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add, map_add]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  have htop : ∀ y, y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)) := fun y => by
    obtain ⟨n, b, hmem, -, -, -, hLs⟩ := hK
    have h2 : (p.nexp.fi j).e.symm y ∈ Submodule.span (Fm.D x i).what₂.LL (Set.range b) := hLs ▸ Submodule.mem_top
    have h3 := Submodule.mem_map_of_mem (f := (p.nexp.fi j).e.toLinearMap) h2
    rw [Submodule.map_span] at h3
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h3
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨b k, hmem k, rfl⟩
  have hv : (fun τ => (u τ : ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)).sm τ)) = p.v₀ j (sg0 (Fm.D x i) p.P.A3.A) := funext hu
  have h1 : R ((1 : FractionRing ((Fm.ex x hx i).nch.Oe w)) ⊗ₜ f) = a • R (rd y) := by
    rw [hRdef, readExt_tmul, map_one, one_smul, hfa, ← hRdef, hrd y (htop y), hv]
  by_cases hf : f = 0
  · exact Or.inl hf
  · refine Or.inr (readExt_eq_smul_of_read _ e hL hF _ _ a h1 ?_)
    rw [readExt_tmul, map_one, one_smul]
    exact fun h0 => hf (hF.injective (h0.trans (map_zero _).symm))
end GlobalTheory.BigOn.Exp.SerBase
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readCmpAt_of_serBase : _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.SerBase.readCmpAt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
end Point
theorem baseGe_of_serBase_facts_flatKer_centLat (hI : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt) (hG : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators) (h1 : _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt) (h2 : _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt') (h3 : _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt) (h4 : _root_.GlobalTheory.BigOn.Exp.SerBase.LatticeInclusionAt)
    (h5 : _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt) (hF : FlatKer) (hC : CentLat) (hTr : TraceRat) (hO : OwnUnit) : _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ := by
  unfold _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ _root_.GlobalTheory.BigOn.Exp.CanonicalFits _root_.GlobalTheory.BigOn.Exp.ReadInjAlt _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt' _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt _root_.GlobalTheory.BigOn.Exp.SerBase.LatticeInclusionAt _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine ((((((Formalism.MainNotions.Closed.and hI hG).and h1).and h2).and h3).and h4).and h5).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := H
  obtain ⟨x0, hx0⟩ := (((((a1.and a2).and a3).and a4).and a5).and a6).and a7
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν rd hfit hcan => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hx0 x hx hle i p hp
  exact baseLat_le_realBase p w j hfit (b1 hm w hw j ρ hρ ν hfit.norm.1) (b2 hm w hw j ρ hρ hfit.pin) fun h hh Q hQ g hg =>
    tmul_mem_realBase p w j (_root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hm.1) (b3 hm w hw j) (b4 hm w hw j) (b5 hm w hw j)
      (b6 hm w hw j) (b7 hm w hw j) hF hC hTr hO hfit hcan hh hQ hg
end GlobalTheory.BigOn.Exp.SerBase
namespace GlobalTheory.BigOn.Exp
theorem baseGe_of_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ := fun hP hA hR hS =>
  _root_.GlobalTheory.BigOn.Exp.SerBase.baseGe_of_serBase_facts_flatKer_centLat _root_.GlobalTheory.T.read_injective _root_.GlobalTheory.T.latSmallGen' _root_.GlobalTheory.T.kerOfAt' _root_.GlobalTheory.T.trace_rationality_at_place' (_root_.GlobalTheory.T.kernel_rationality_of_reciprocity_hypotheses_alt hP hA hR hS) _root_.GlobalTheory.T.latIoAt' _root_.GlobalTheory.T.readCmpAt_of_serBase
    GlobalTheory.T.flatDatum_series_unit_times_kernel_series GlobalTheory.T.central_element_moves_coefficient_lattice_by_prime_pow GlobalTheory.T.kernelTrace_algebraic_at_lowestTypes GlobalTheory.T.ownPrime_isUnit_at_place
end GlobalTheory.BigOn.Exp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseGe_of_cuspRapidDecay_artin_rayClassField_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.baseGe_of_alt
end
end
