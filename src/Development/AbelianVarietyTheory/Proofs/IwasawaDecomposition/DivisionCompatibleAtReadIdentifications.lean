import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeInfKerLeOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeOpEqSpanOfFormsTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumbersEqConcreteNumbersAtBaseLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheoremsStatement

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem bk_eq_of_coordinates (D : D7) (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0) {n nV d a : ℕ}
    (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) (V : Matrix (Fin n) (Fin nV) D.what₂.LL)
    (Pq : Matrix (Fin d) (Fin nV) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) (u : D.what₂.Word)
    (eN : (Fin a → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (P : (Fin a → D.what₂.LL) → (Fin nV → D.what₂.LL) → D.what₂.LL)
    (hB : Formalism.BasicNotions.Rows.BuDefQ D.what₂) (hBR : D.BuRational)
    (hV : D.what₂.V0 μ = Submodule.span ℂ (Set.range fun G => jA (V.mulVec G)))
    (hι : ∀ G, D.what₂.iota μ (jA (V.mulVec G)) = D.jEE (eRR (Pq.mulVec G)))
    (hper : ∀ x G, D.what₂.embLL (P x G) = D.what₂.perCol u μ (D.jN u (eN x)) (jA (V.mulVec G)))
    (hvan : ∀ x G, Pq.mulVec G = 0 → P x G = 0) :
    ∀ x G, D.div.Bk u (eN x) (eRR (Pq.mulVec G)) = P x G := by
  subst hμ
  intro x G
  have key := GlobalTheory.span_range_inf_ker_le_of_basis D.what₂.embLL D.div.RR.b (jA.comp V.mulVecLin) D.jEE
    (D.what₂.iota D.what₂.mu0) (eRR.toLinearMap ∘ₗ Pq.mulVecLin) D.jEE_basis.1 hι
  have hU : D.what₂.Usp D.what₂.mu0 = Submodule.span ℂ ((jA.comp V.mulVecLin) ''
      {x | (eRR.toLinearMap ∘ₗ Pq.mulVecLin) x = 0}) := by
    rw [← key, Formalism.BasicNotions.Rows.Data.Usp, hV]
    rfl
  have hK : ∀ F ∈ D.what₂.Usp D.what₂.mu0, D.what₂.perCol u D.what₂.mu0 (D.jN u (eN x)) F = 0 := by
    intro F hF
    rw [hU] at hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨G', hG', rfl⟩ := hF
      have hG'' : Pq.mulVec G' = 0 := eRR.map_eq_zero_iff.1 hG'
      refine (hper x G').symm.trans ?_
      rw [hvan x G' hG'', map_zero]
    | zero => exact D.perCol_zero u _
    | add F G _ _ hF hG => rw [D.perCol_add, hF, hG, add_zero]
    | smul c F _ hF => rw [GlobalTheory.perCol_base_smul_form, hF, mul_zero]
  have hmem : jA (V.mulVec G) ∈ D.what₂.V0 D.what₂.mu0 := by
    rw [hV]
    exact Submodule.subset_span ⟨G, rfl⟩
  apply D.what₂.embLL.injective
  rw [← hBR u (eN x) (eRR (Pq.mulVec G)), ← hι G, hper x G]
  exact (GlobalTheory.perCol_eq_pairing_of_kills D hB u _ hK _ hmem).symm

theorem pairing_eq_colPairing : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH), Pins R F cG → Holds R F → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → ∀ u x y, D.div.Bk u (C.eNu u x) (Z.eRR y) = (colOf R F sEE).B (C.wU u) x y := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C sEE hPins hHolds hBR hBt u x y
  have hR := complex_data_conditions_base_level_of_primitive_links hHolds.ok hHolds.sep hPins.char hHolds.prim
  have hW := hR.wf true
  have h2 := (hR.what₂ true).1
  have hI := (GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds).1
  have hPq := hW.Pq_surj A3.fam3.base3.μ0
  have hRi := CxData.rinv_spec _ hPq
  have hV := GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (Y.jA A3.fam3.base3.μ0) _ _ _
      (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) (Y.formsA A3.fam3.base3.μ0)
      (GlobalTheory.range_goodProjector_eq_range_goodCoordinates D A3.A 1 hHolds.ok.ok2 F.P1 F.ψ1 A3.fam3.base3.μ0)
  have hι : ∀ G0, D.what₂.iota (Y.tup A3.fam3.base3.μ0) (Y.jA A3.fam3.base3.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0).mulVec G0)) =
      D.jEE (Z.eRR (((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0).mulVec G0)) := by
    intro G0
    have h := hI.iota A3.fam3.base3.μ0 G0
    rw [Formalism.BasicNotions.Examples₂.NZ.sharp_iota] at h
    refine h.trans ?_
    show D.jEE (Z.eRR (((R.toCx3 F).rowMat F.cr true A3.fam3.base3.μ0).mulVec _)) = _
    rw [CxData.rowMat_base _ F.cr true h2]
    exact congrArg (fun v => D.jEE (Z.eRR v)) (Matrix.one_mulVec _)
  have key := bk_eq_of_coordinates D (Y.tup A3.fam3.base3.μ0) Y.tup0 (Y.jA A3.fam3.base3.μ0)
    (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0) Z.eRR u (C.eNu u)
    (fun x G0 => (F.Dc (R.toCx3 F).zs).Pt (C.wU u) A3.fam3.base3.μ0 x G0) Y.bu hBR hV hι
    (fun x G0 => C.pt u A3.fam3.base3.μ0 x G0) ?_
  · have hy : ∀ v : Fin ((lv (F.fc (R.toCx3 F).zs) true).dQ A3.fam3.base3.μ0) → D.what₂.LL,
        ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0).mulVec
          ((CxData.rinv ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0)).mulVec v) = v := by
      intro v
      refine (Matrix.mulVec_mulVec _ _ _).trans ?_
      exact (congrArg (fun M => Matrix.mulVec M v) hRi).trans (Matrix.one_mulVec v)
    refine Eq.trans ?_ (key x ((CxData.rinv ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0)).mulVec y))
    exact congrArg (fun v => D.div.Bk u (C.eNu u x) (Z.eRR v)) (hy y).symm
  · intro x G0 hG0
    apply hBt (C.wU u) x G0
    exact LinearMap.mem_ker.2 hG0

end GlobalTheory.Mem.R3
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPairing_eq_columnPairing : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH), Pins R F cG → Holds R F → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → ∀ u x y, D.div.Bk u (C.eNu u x) (Z.eRR y) = (colOf R F sEE).B (C.wU u) x y := by
  atlas_forward_decl GlobalTheory.Mem.R3.pairing_eq_colPairing
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.divTied3_read : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → (Fintype.card G = D.what₂.restRowsFiniteGroupCard → Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) → GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)) → DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C) ∧ (MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C)) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C sEE Xd JM hP hH hGrp
  obtain ⟨hcard, hidx, hr, ht, hv0⟩ := GlobalTheory.Mem.R3.pins_card_index_ranks D G Pl0 I0 T A3 Ks R F cG hP
  obtain ⟨hsh, hba⟩ := GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  obtain ⟨hth, hthT⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  refine ⟨?_, ?_⟩
  · refine
      { ranks := ⟨rfl, hr, ht⟩
        grp := hGrp hcard hidx
        tup := ⟨Y.tup0, Y.muAt, hv0, Function.LeftInverse.injective (g := Y.tupT) Y.tupT_tup⟩
        mu1 := rfl
        sharp := hsh
        base := hba
        mt := ⟨Y.formsL, Y.latL⟩
        th := hth
        cols := ⟨C.bij, C.nu⟩ }
  · intro hMj hIdx hBu hBt
    obtain ⟨hRR1, hRR0⟩ := GlobalTheory.T.rowLattices_metrics_agree_of_realGroupTheorems hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
    exact
      { sharpRR := hRR1
        baseRR := hRR0
        divisionRows_rationalLift := GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
        thTheta := hthT
        num := GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel D G Pl0 I0 T A3 Ks R F cG X0 Y Z Xd JM hP hH hMj hIdx
        colsBk := GlobalTheory.T.rationalPairing_eq_columnPairing hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z C sEE hP hH hBu hBt }
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionCompatible_at_readIdentifications : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → (Fintype.card G = D.what₂.restRowsFiniteGroupCard → Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) → GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)) → DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C) ∧ (MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → D.BuRational → CxData.BtVanish (fc := F.fc) (R.toCx3 F) → DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (zsOf R F) (s0Of R F) (s1Of R F) X0 (colOf R F sEE) C.NuC (idsOf cG Z C)) := by
  atlas_forward_decl GlobalTheory.divTied3_read
end
