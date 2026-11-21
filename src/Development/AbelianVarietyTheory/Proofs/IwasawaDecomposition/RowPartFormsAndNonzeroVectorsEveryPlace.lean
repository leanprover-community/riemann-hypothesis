import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfParts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionOnAdelicFunctionsEqZeroOfNoLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelVectorGoodTypeStableSubspace
import BuildAid.ForwardExisting

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.RowsAtBase

theorem exists_base_row_of_pins : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false ≠ ⊥ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hP hH _ hG p hp
  have hC := hP.char
  have hE := hH.aux.ex
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hH.ok.ok2.irr
  have key := GlobalTheory.LevelRows.rowsOfLevel_of_models R.toRealDat F.lv2 hC.base.models.HE hC.base.models.gE false
  obtain ⟨u, huU, hu0, hup⟩ := GlobalTheory.Hk3.exists_level_vector D.what₂.embLL A3.A.X F.P0 F.ψ0 R.gE (R.EEp3 p) hX hG
    (fun g => GlobalTheory.RowsSum3.rowTypePart_map_finiteGroup_le R F hC hE p g) hp
    (fun u _ => by simpa [RealDat.eC] using GlobalTheory.ChainScalar.sum_gE hC.base.models.HE hC.base.models.gE u)
  rw [Submodule.ne_bot_iff]
  exact ⟨Tw.mk (twAt D.what₂.embLL A3.A.v0) u, ⟨huU, (key u).2 hup⟩, hu0⟩

end GlobalTheory.RowsAtBase
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseLevelRow_of_nonzero_goodRowsPart : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false ≠ ⊥ := by
  atlas_forward_decl GlobalTheory.RowsAtBase.exists_base_row_of_pins
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RatLift

theorem exists_rat_lift_mem_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ → ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p ∧ x ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hP hH _ _ p _ i hB
  have hRw := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hk : (R.toCx3 F).KForm false := hRw.kForm
  have he : (R.toCx3 F).EWnorm false := hRw.ewNorm
  have hn : 0 < (R.toCx3 F).nP false := hRw.h4pos.2.2 false
  have h5 : (R.toCx3 F).H5 F.cr false := hRw.lifts0.1
  have hr : (R.toCx3 F).RATth F.cr false := hRw.ratTh
  have h3W : (R.toCx3 F).H3W F.cr false := hRw.liftHyp0.h3W
  have ht : (lv (F.fc (R.toCx3 F).zs) false).Types := hRw.types0
  have hK : ∀ y, y ∈ ⨆ q, (R.toCx3 F).WpK false i q := fun y => CxData.liftsK ht hk he hn h5 hr h3W i y
  have hc0 : cpt A3.A.v0.embedding (0 : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) = 0 := by
    funext l; simp [cpt]
  have hWpK : (R.toCx3 F).WpK false i p ≠ ⊥ := by
    intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    let M : Submodule ℂ ((R.toCx3 F).W i) :=
      ⨆ q, ⨆ (_ : q ≠ p), (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)
    have hrat : ∀ y, (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M := by
      intro y
      refine Submodule.iSup_induction _ (motive := fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ M)
        (hK y) ?_ ?_ ?_
      · intro q z hz
        by_cases hq : q = p
        · subst hq
          rw [h0] at hz
          rw [(Submodule.mem_bot _).1 hz, hc0, map_zero]
          exact M.zero_mem
        · exact (le_iSup₂ (f := fun q (_ : q ≠ p) => (R.toCx3 F).Wp i q ⊓ LinearMap.range ((R.toCx3 F).w0C false i)) q hq)
            ⟨hz, ⟨_, rfl⟩⟩
      · rw [hc0, map_zero]
        exact M.zero_mem
      · intro a c ha hc
        have : cpt A3.A.v0.embedding (a + c) = cpt A3.A.v0.embedding a + cpt A3.A.v0.embedding c := by
          funext l; simp [cpt]
        rw [this, map_add]
        exact M.add_mem ha hc
    have hrange : LinearMap.range ((R.toCx3 F).w0C false i) ≤ M := by
      rw [LinearMap.range_eq_map, ← (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i))).span_eq, Submodule.map_span,
        Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have : (Pi.basisFun ℂ (Fin ((R.toCx3 F).dW false i)) k) =
          cpt A3.A.v0.embedding (Pi.single k (1 : D.what₂.LL)) := by
        funext l
        simp only [Pi.basisFun_apply, cpt, Pi.single_apply]
        split_ifs <;> simp
      rw [this]
      exact hrat _
    have hperp : M ≤ (ℂ ∙ w)ᗮ := by
      refine iSup₂_le fun q hq => ?_
      intro v hv
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact (hH.prim.sumW i).1 p q (Ne.symm hq) w hw v hv
    have hww := hperp (hrange hw.2)
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hww
    exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 hww)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWpK
  obtain ⟨x, rfl⟩ := ((R.toCx3 F).liftMat_bij F.cr false hk he hn h5 hr i A3.A.μ0).2 y
  refine ⟨x, ?_, ?_⟩
  · have hy' : (R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding
        ((R.toCx3 F).liftMat F.cr false i A3.A.μ0 *ᵥ x)) ∈ (R.toCx3 F).Wp i p := hy
    rw [(R.toCx3 F).key_lift F.cr false h5 hr i A3.A.μ0 x] at hy'
    exact hy'
  · rintro rfl
    exact hy0 (Matrix.mulVec_zero _)

end GlobalTheory.RatLift
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_rational_lift_mem_base_part : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ → ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, (R.toCx3 F).tC F.cr false i A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp i p ∧ x ≠ 0 := by
  atlas_forward_decl GlobalTheory.RatLift.exists_rat_lift_mem_part
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

open scoped ComplexOrder

namespace GlobalTheory.Mem.FramePos

open Formalism.L2.DIV

theorem majAt_XQ_ne_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 : Type} {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ}
    (h : BlockHyp B ℓ v0 s) (Z : Submodule K B.S.Forms) (v : InfinitePlace K)
    (x : Fin (B.dZ ℓ Z) → K) (hx : x ≠ 0) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x x ≠ 0 := by
  have hP : Function.Surjective (B.Pq ℓ Z).mulVec := fun y =>
    ⟨(B.zE ℓ Z).mulVec y, by rw [Matrix.mulVec_mulVec, (BlockDat.lf_z_proj (Z := Z) h).1, Matrix.one_mulVec]⟩
  have hpos : (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)).PosDef :=
    (quotRestrPosDef _ _ _ (BlockDat.lf_HV_pos h v)).1 _ (map_surj _ _ hP)
  have hf := frameOfSpec _ _ hpos
  rw [majAt_eq]
  have e : B.XQ ℓ Z v = frameOf (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)) := rfl
  rw [e, hf.2]
  have hne : (fun i => v.embedding (x i)) ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa using this
  exact (hpos.dotProduct_mulVec_pos hne).ne'

end GlobalTheory.Mem.FramePos

open GlobalTheory.Mem.FramePos in

theorem GlobalTheory.Mem.R3.framesBase_majAt_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL), v ≠ A3.A.v0 → ∀ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, x ≠ 0 → Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT i A3.A.μ0) v x x ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hH _ _ i v _ x hx
  have hok := hH.ok.ok2
  have hB : Formalism.L2.DIV.BlockHyp (A3.A.fam.L i A3.A.fam.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.fam.v0 1 :=
    ⟨hok.conj, hok.irr, hok.lifts i _⟩
  exact majAt_XQ_ne_zero hB _ v x hx
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_level_frames_hermitian_ne_zero_off_place : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL), v ≠ A3.A.v0 → ∀ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, x ≠ 0 → Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT i A3.A.μ0) v x x ≠ 0 := by
  atlas_forward_decl GlobalTheory.Mem.R3.framesBase_majAt_ne_zero
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RowsLift

theorem rows_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH hM hg p hp i
  have hA := GlobalTheory.T.exists_baseLevelRow_of_nonzero_goodRowsPart D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp
  have hB : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ := by
    intro h0
    apply hA
    rw [← Submodule.finrank_eq_zero, ← hH.prim.dimParts i p, h0, finrank_bot]
  refine ⟨?_, fun v hv => ?_⟩
  · intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    have : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) w ∈ R.Wp3 i p := hw.1
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).2 this
  · obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_nonzero_rational_lift_mem_base_part D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp i hB
    exact ⟨x, hx, GlobalTheory.T.base_level_frames_hermitian_ne_zero_off_place D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg i v hv x hx0⟩

end GlobalTheory.RowsLift
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPart_forms_and_nonzero_vectors_every_place : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v := by
  atlas_forward_decl GlobalTheory.RowsLift.rows_lift
end
