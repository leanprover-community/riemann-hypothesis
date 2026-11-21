import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftGroupFormsEqExtendedRationalFormsCompanion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSphericalEigensystemFirstLiftBaseLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfMemISup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPsiOfStdFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasEigEigOfType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointInjectiveOnPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTypePartLeEigensystemPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullAlgebraPartLeSplitHeckePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystemStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartLeEigensystemPartPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricParameterOfReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParameterOfDiscreteSeriesReciprocityStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sphericalEigensystem_firstLift_baseLevel : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ π : D.what₂.FT, ∃ c, HasEig R F Y π c := by
  first | exact @GlobalTheory.Mem.R3.EigEx.exists_hasEig | exact GlobalTheory.Mem.R3.EigEx.exists_hasEig | (intros; apply GlobalTheory.Mem.R3.EigEx.exists_hasEig <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem isSF_ssetF_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hW : R.WeakCharacterisation F) (hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2) :
    GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat A3.A.μ0) := by
  intro v
  have hQ := (GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).1
  have hS : R.Sb = R.Pg := hW.allPl
  unfold SsetF
  rw [hQ, hS]
  simp only [Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  exact ⟨fun h => by rw [← h]; rfl, fun h => HeightOneSpectrum.ext h⟩

set_option maxHeartbeats 1000000 in

theorem prt_le_hPart_of_carries : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → (Y.Ish.prt : D.what₂.FT → Submodule ℂ (AmbT (R.MY 0))) π ≤ (hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polE (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hE hc
  obtain ⟨hC, hSF, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have hS := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hR R.toRealDat
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hSF' : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    rw [hμ]; exact isSF_ssetF_base R F hP.char hC
  have hinj := GlobalTheory.AdjPart.adjoint_injective_on_part R
    ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hR D) hH.ok hP.char hH.aux.ex hS hinj p c hc
  have hpart := (GlobalTheory.T.full_algebra_part_le_split_hecke_part R.toRealDat F.lv2 (s := 1) hH.ok.ok2 hC _ hSF' c (RealDat.polE (A := A3.A) p.1.1)).1
    fun P hP => (hlab P hP).1
  rw [Y.prtE π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.rowTypePart_le_eigensystemPart R.toRealDat F.lv2 (s := 1) hC hS _ hSF' Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ _ c hE true U hU
  exact hpart x hx

end GlobalTheory.Mem.R3
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in

theorem prtW_le_hPart : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c p, HasEig R F Y π c → R.Carries p c → ∀ i : Fin D.R.m, (Y.IL.prtW : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (AmbT (R.MW i (sg0 D A3.A)))) i π ≤ (hPart (R.MW i (sg0 D A3.A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A3.A.ok A3.A.μ0) R.pl A3.A.q (RealDat.polW (A := A3.A) p.1.1)).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap := by
  intro _ _ _ hcusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH _ π c p hc hcar i
  obtain ⟨hC, -, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hH.aux.ex
  have ht : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  have hQ : R.Q A3.A.μ0 = ∅ := (GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hC.lev).1
  have hSb : R.Sb = R.Pg := hP.char.allPl
  have hSF : GlobalTheory.Hk3.IsSF R.toRealDat (SsetF R.toRealDat (Y.tupT D.what₂.mu0)) := by
    classical
    intro v
    unfold SsetF
    rw [ht, hQ, hSb, Finset.union_empty, Finset.mem_image]
    refine exists_congr fun PP => and_congr_right fun _ => ?_
    rw [← underPl_asIdeal]
    exact ⟨fun h => by rw [h], fun h => HeightOneSpectrum.ext h⟩
  have hlab := GlobalTheory.T.heckePolynomials_of_carried_eigensystem R F (GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hcusp D) hH.ok hP.char hH.aux.ex
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hcusp R.toRealDat)
    (GlobalTheory.AdjPart.adjoint_injective_on_part R ⟨hH.prim.posScal.1, fun i t p => hH.prim.posScal.2 i t p _⟩ hH.prim.thmB)
    p c hcar
  rw [Y.prtWE i π]
  refine Submodule.map_mono fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.typePart_le_eigensystemPart_principalLevel R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2
    _ ⟨0, Y.hm⟩ c hc i U hU
  exact (GlobalTheory.T.full_algebra_part_le_split_hecke_part R.toRealDat F.lv2 hH.ok.ok2 hC _ hSF c _).2 i (fun P hP => (hlab P hP).2) x hx

end GlobalTheory.Mem.R3
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

theorem partsRec_of_eig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → (∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) → Xd.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e))) → ∃ (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PartsRec R.toRealDat F.lv2 Y.tupT Y.hm Y.PY Y.PW Y.eFT E labPi piOf Y.Ish.prt Y.IL.prtW := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd hP hH hHost hgen hLam
  have e1 := GlobalTheory.T.exists_sphericalEigensystem_firstLift_baseLevel hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost hgen
  have e2 := GlobalTheory.Mem.EigCarry.carries_of_hasEig hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e3 := GlobalTheory.Mem.R3.IsotPart.isot_le_part hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e4 := GlobalTheory.Mem.R3.prt_le_hPart_of_carries hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have e5 := GlobalTheory.Mem.R3.prtW_le_hPart hW hDS hHC hCR D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH hHost
  have hc : Formalism.L2.Col.PairComm (A3.fam3.F.R A3.fam3.F.μ0).op := (hH.ok.ok2.what₂ A3.fam3.F.μ0).comm
  classical

  have hE : ∀ π, HasEig R F Y π (eigOfType R F Y π) := fun π => hasEig_eigOfType (e1 π)
  have hK : ∀ π, ∃ p, R.Carries p (eigOfType R F Y π) := fun π => e2 π _ (hE π)
  let Pi : Type := Set.range (eigOfType R F Y)
  have hPi : ∀ c : Pi, ∃ p, R.Carries p c.1 := by
    rintro ⟨c, π, rfl⟩
    exact hK π
  let labP : Pi → A3.fam3.base3.Ix := fun c => (hPi c).choose
  let E : EigIdx D Xd :=
    { Pi := Pi
      fin := Set.fintypeRange _
      dec := Classical.decEq _
      cOf := fun π => ⟨eigOfType R F Y π, π, rfl⟩
      lam_const := by
        intro j hj π π' e h1 h2 hcc
        have hc' : eigOfType R F Y π = eigOfType R F Y π' := congrArg Subtype.val hcc
        obtain ⟨p, hp⟩ := hK π
        have hp' : R.Carries p (eigOfType R F Y π') := hc' ▸ hp
        have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
        have hk : k < D.R.m := by omega
        have a1 := hLam ⟨k, hk⟩ π p e h1 (e3 π _ p (hE π) hp ⟨k, hk⟩)
        have a2 := hLam ⟨k, hk⟩ π' p e h2 (e3 π' _ p (hE π') hp' ⟨k, hk⟩)
        exact a1.trans a2.symm }
  refine ⟨E, fun c => A3.fam3.toIx2 hc (labP c), Subtype.val, ?_⟩
  refine ⟨fun π => rfl, Subtype.val_injective, ?_, ?_⟩
  · intro π
    exact e4 π _ _ (hE π) (hPi _).choose_spec
  · intro i π
    have h5 := e5 π _ _ (hE π) (hPi (E.cOf π)).choose_spec i
    exact h5

end GlobalTheory.Mem.R3

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partsRow_of_eigensystemIndex_goodCharacters : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D), Pins R F cG → Holds R F → HostHyp D → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → (∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) → Xd.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e))) → ∃ (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PartsRec R.toRealDat F.lv2 Y.tupT Y.hm Y.PY Y.PW Y.eFT E labPi piOf Y.Ish.prt Y.IL.prtW := by
  atlas_forward_decl GlobalTheory.Mem.R3.partsRec_of_eig
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.RecInAt

set_option maxHeartbeats 4000000 in

theorem recIn_parts_exists : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.sat.P → HEq sS q.sat.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : RealIn x R (sS.toSTiesR R)), ∃ r : RecIn y, (realRecOf r).PartsRow := by
  intro hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM R hR sP sS hP hS a x hax y
  obtain rfl := eq_of_heq hax
  classical

  obtain ⟨hC, -, hxi, -⟩ := GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have hmt := GlobalTheory.Mem.R3.Reads.mt_mj_read _ _ _ _ _ _ _ _ q.O.ex a.x R (sS.toSTiesR R) y a.intersectionNumber_baseChange
  have hFr : Top.Fr.at (q.w.st q.Z) q.f = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z :=
    (congrArg (Top.Fr.at (q.w.st q.Z)) q.w.C_eq.symm).trans rfl
  have hchr := hR.s.chr
  have hC' : a.x.R.C = R.T.n.cf := by
    have h1 := eq_of_heq hC
    rw [h1, hFr]
    exact (congrArg Sigma.fst hchr).symm
  have heig := @GlobalTheory.T.partsRow_of_eigensystemIndex_goodCharacters hW hDS hHC hCR _ a.x.G a.x.grp a.x.fin _ _ _ a.x.A3 _ _ _ a.x.alg a.x.R a.x.F a.x.cG q.O.ex.p0 a.x.Y a.x.Z q.O.X a.x.pins a.intersectionNumber_baseChange

  letI := a.x.grp
  letI := a.x.fin
  letI := a.x.alg
  have hHost : HostHyp (q.w.D q.Z) := (hH (q.w.st q.Z) q.x.isOver).1
  have hgen : ∀ χ ∈ a.x.A3.A.X, chiIdem χ * lvlIdem a.x.F.P0 a.x.F.ψ0 ≠ 0 :=
    GlobalTheory.T.geometric_parameter_of_reciprocity hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  have hlam : ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ),
      (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) →
      q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) :=
    GlobalTheory.T.parameter_of_discrete_series_reciprocity hGC hDC hHM hCW hW hDS hHC hCR hGAR hRF hL N Γ p hp hN K q hH hM a
  obtain ⟨E, labPi, piOf, hparts⟩ := heig hHost hgen hlam
  have key : ∀ (c : Formalism.L2.Host.CharFrame (q.w.D q.Z)) (h : R.T.n.cf = c),
      (cast (congrArg (fun c => Formalism.L2.Host.TupTied (q.w.D q.Z) c q.O.ex.nch) h) R.T.n.tp).xi = R.T.n.tp.xi := by
    intro c h; subst h; rfl
  have key2 : ∀ (c1 c2 : Formalism.L2.Host.CharFrame (q.w.D q.Z)) (t1 : Formalism.L2.Host.TupTied (q.w.D q.Z) c1 q.O.ex.nch)
      (t2 : Formalism.L2.Host.TupTied (q.w.D q.Z) c2 q.O.ex.nch), c1 = c2 → HEq t1 t2 → t1.xi = t2.xi := by
    intro c1 c2 t1 t2 h ht; subst h; cases ht; rfl
  obtain ⟨hcf, htp⟩ := Sigma.mk.inj_iff.1 hchr
  have hxiR : R.T.n.tp.xi = q.w.I.xi := (key2 _ _ _ _ hcf htp).trans q.x.n.xi
  have htx : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → a.x.R.toLevCh.xiH (a.x.Y.tupT μ) =
      (cast (congrArg (fun c => Formalism.L2.Host.TupTied (q.w.D q.Z) c q.O.ex.nch) hC'.symm) R.T.n.tp).xi μ := by
    intro μ hμ
    rw [key _ hC'.symm, hxiR]
    exact eq_of_heq (hxi μ hμ).2
  refine ⟨⟨E, labPi, piOf, cast (congrArg (fun c => Formalism.L2.Host.TupTied (q.w.D q.Z) c q.O.ex.nch) hC'.symm) R.T.n.tp, cast_heq _ _, htx, hmt.1, hmt.2⟩, ?_⟩
  exact hparts

end GlobalTheory.Mem.R3.RecInAt

end
end
