import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipOfWeilConvergenceAndTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionCommutesOnGrid
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionCommutesOnGridStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspStepOfLargeFlipRun
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EndCuspLeadingFormListed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceHorizontalTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftedCuspFormsListed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftedCuspFormsListedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceHorizontalThetaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenFiniteRepresentationChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeInterior
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeInteriorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeBoundary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorRightEdgeCosine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorRightEdgeCosineStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenFiniteRepresentationChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipOfWeilConvergenceAndThetaStatement

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SquareComm
open GlobalTheory.RowClaim
end GlobalTheory.SquareComm
namespace GlobalTheory.SquareComm
open GlobalTheory.RowClaim
theorem square_commutes_with_all : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
      ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t) := by
  intro hPr hWC hK
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ t i j => ?_⟩⟩
  exact commutesWith_of_isSquareConst hWC hK hPr.cuspDecayBound s.core.lev
    (squareStanding_of_setting s s.size.2.1.eleven_le ch.G t) (hch.const i j t)
end GlobalTheory.SquareComm
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_square_commutes : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t) := by
  first | exact @_root_.GlobalTheory.SquareComm.square_commutes_with_all | exact _root_.GlobalTheory.SquareComm.square_commutes_with_all | (intros; apply _root_.GlobalTheory.SquareComm.square_commutes_with_all <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FlipStart.Col
variable {D : D7}
variable {T : Type} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end GlobalTheory.FlipStart.Col
open GlobalTheory.FlipStart GlobalTheory.FlipStart.Col in
theorem GlobalTheory.FlipStart.flipSequence_start_column : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  intro _ _
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t f q hf hq M hM y
  have h := col_top hch.weil s.core.chain s.core.models hq hM y D.R.m rfl (fun j => ch.W.fock (.mu t 0 j) (f j) (q j))
    (fun j => ⟨fun h => ⟨f j, (hf j).1 h, rfl⟩, fun h => ⟨f j, (hf j).2 h, rfl⟩⟩) (formTop ch t y)
    (by unfold formTop; exact cast_fun_heq _ _)
  exact ⟨h.1, eq_of_heq h.2⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipSequence_column_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  first | exact @_root_.GlobalTheory.FlipStart.flipSequence_start_column | exact _root_.GlobalTheory.FlipStart.flipSequence_start_column | (intros; apply _root_.GlobalTheory.FlipStart.flipSequence_start_column <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.StartCusp
open Formalism.IndefR.Mult Matrix Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
variable {D : D7}
end GlobalTheory.StartCusp
namespace GlobalTheory.StartCusp
open Formalism.IndefR.Mult
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem cusp_lift_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  intro hP _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  have hT := GlobalTheory.ProjectedLift.thDn_mem R t y
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D R.θ _ _ (R.MY 0) _ _ _).1 hT
  have hu : ch.cv.lift t y = PiTensorProduct.lift (PiTensorProduct.lift.symm (R.thDn t y)) ch.cv.w := by
    rw [LinearEquiv.apply_symm_apply, ch.cv.thDn_w hS.core.chain]
  rw [hθ, hu]
  refine ⟨GlobalTheory.EndCusp.isAutFunSm_lift hT' _, isCuspFun_lift hT' _, fun τ => ?_⟩
  have h := star_lift_isTypeAt R.θ hP.harishChandraModules (R.MY 0) hT ch.cv.w τ
  rw [show Node.par D ch.sc.cGap (.grid 0 0) τ = (Ptw D).Dpar 0 τ from parV_zero D _ (Nat.zero_le _) τ]
  simp only [parB, dualPar_dualPar, Nat.zero_min] at h
  exact h
end GlobalTheory.StartCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cusp_lift_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  first | exact @_root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList | exact _root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList | (intros; apply _root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList <;> assumption)
end
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.RowStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.RowStart
namespace GlobalTheory.RowStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.RowStart
namespace GlobalTheory.RowStart
theorem theta_tower_first_occurrence_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (Φ : ch.G.Datum) (M : Vol ch.G), M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = liftP ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) := by
  intro hP hLC
  refine ((_root_.GlobalTheory.FlipRun.cuspStep_of_large_flipRun hLC hP).and ((_root_.GlobalTheory.T.twist_cusp_lift_mem_cuspList hP hLC).and (GlobalTheory.T.firstRow_cosetVectors_isLocalThetaVector.and GlobalTheory.T.firstRowSchwartzData_isThetaFunction_largeDepth))).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t Φ M hM y => ?_⟩
  obtain ⟨hstep, hcusp, hloc, hth⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  have H := rowCore ch.W ch.M M ch.rm t ch.ρ Φ (hstep t M hM) (hloc t) (fun i => hth Φ i) hch.vol hM.isRow
    (ch.cv.lift t y) (hcusp t y) D.R.m le_rfl
  exact ⟨H.1, H.2.2⟩
end GlobalTheory.RowStart
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_tower_first_occurrence_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (Φ : ch.G.Datum) (M : Vol ch.G), M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = liftP ch.W M (rowPath T 0 D.R.m) (rowDatum ch.W ch.ρ Φ) (ch.cv.lift t y) := by
  first | exact @_root_.GlobalTheory.RowStart.theta_tower_first_occurrence_exists | exact _root_.GlobalTheory.RowStart.theta_tower_first_occurrence_exists | (intros; apply _root_.GlobalTheory.RowStart.theta_tower_first_occurrence_exists <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainCol
noncomputable section
namespace GlobalTheory.ChainCol
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem chainColumn_inner_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 < D.R.m → HEq g (R.vY t j) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j g hj hg
  exact ⟨1, one_mem _, fun e he Φ => locVec_col s ch hch t j g hj hg e he Φ⟩
end GlobalTheory.ChainCol
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_chainColumn_inner_succ_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 < D.R.m → HEq g (R.vY t j) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  first | exact @_root_.GlobalTheory.ChainCol.chainColumn_inner_succ | exact _root_.GlobalTheory.ChainCol.chainColumn_inner_succ | (intros; apply _root_.GlobalTheory.ChainCol.chainColumn_inner_succ <;> assumption)
end
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipStart
theorem flipStart_highestVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 = D.R.m → HEq g (R.vX t) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j g hj hg
  refine ⟨1, one_mem _, fun e he Φ => ?_⟩
  rw [Units.val_one, one_smul]
  obtain ⟨e', he', hθ⟩ := GlobalTheory.T.rowChain_last_step_vector_eq_theta_of_datum s ch hch t j g hj hg
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hS : IsSelfDualC (ch.G.pS (.mu t 0 j)) (ch.G.latS (.mu t 0 j)) :=
    (colY_isV D T R.toLevCh A.μ0 hL j j.2.le).sd
  have hT : IsSelfDualC (ch.G.pT (.mu t 0 j)) (ch.G.latT (.mu t 0 j)) :=
    (colY_isV D T R.toLevCh A.μ0 hL (j + 1) j.2).sd
  have hv := ch.rm.vT_is t 0 j (Nat.zero_le _) j.2
  have hsub : GlobalTheory.FlipTop.topPl R.toLevCh t ⊆ locPl ch.G t := by
    classical
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces ch.G hL t h)
    · exact Finset.mem_union_right _ h
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isThetaAt_enlarge_placeIdempotent_latticeIndicator hS hT hv he he' hsub (GlobalTheory.T.gridFirstColumnStep_isSchwartzBruhat_half ch.G ch.S.B hL t he' j j.2) hθ
  have hAA : ∀ w ∈ locPl ch.G t, w ∉ GlobalTheory.FlipTop.topPl R.toLevCh t →
      ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
        ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw _
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  rw [GlobalTheory.T.first_column_type_twist_datum_eq_given_function ch.G ch.S.B hL t he he' hAA Φ j j.2] at h1 h2
  exact ⟨h1, h2⟩
end GlobalTheory.FlipStart
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_flipStart_highestVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)), (j : ℕ) + 1 = D.R.m → HEq g (R.vX t) → ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) g := by
  first | exact @_root_.GlobalTheory.FlipStart.flipStart_highestVector | exact _root_.GlobalTheory.FlipStart.flipStart_highestVector | (intros; apply _root_.GlobalTheory.FlipStart.flipStart_highestVector <;> assumption)
end
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.CosetRow in
theorem GlobalTheory.CosetRow.coset_function_isLocalVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsLocVec ch.W (.chi i 0) e (ch.rm.vX i 0) (GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.right i 0)) (ch.W.cosVec i (Φ i)) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi _ => ?_⟩⟩
  intro t e he Φ i
  classical
  have hL := s.core.lev
  obtain ⟨e₀, he₀, hcv⟩ := ch.W.cosVec_is
  obtain ⟨he₁, h01⟩ := GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal he he₀ Finset.subset_union_left
  have hee : e₀ + (e - e₀) = e := add_sub_cancel e₀ e
  have hAA : ∀ w ∈ R.toLevCh.Q t, w ∉ ch.G.pl.W0 → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw _
    refine GlobalTheory.T.host_ideal_unit_at_places_prime_to_level D w (fun h => (hL.Q_off t w hw).1 ?_) (fun h => s.guard.2 t w hw ?_)
    · rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h
    · rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h
  rw [GlobalTheory.T.givenStageFunction_rowArrow_eq_halfExtension hL ch.S.B t Φ he he₀ hAA i, ch.rm.vX_row]
  obtain ⟨dS, dT⟩ := selfDual_chi hL ch.G i i.2
  have h0 := GlobalTheory.PlaceDatum.idemSum_mul_self he₀
  have h1 := GlobalTheory.PlaceDatum.idemSum_mul_self he₁
  have hSB := GlobalTheory.GridWeil.isSBHalf_cosInd dS dT (ch.G.pl.modul_ne_bot _) h0 (GlobalTheory.PlaceDatum.infPart_idemSum he₀) (Φ i)
  have hex := (GlobalTheory.PlaceModelSum.placeModelExistsSum D ch.W.ψ ch.W.ψ_std _ _ _ _ dS dT _ e he _
    (ch.W.vac_is i i.2).2.theta (ch.W.vac_is i i.2).2.lat).1
  rw [← hee] at hex
  have key : IsLocVec ch.W (.chi i 0) (e₀ + (e - e₀)) (ch.W.vac i)
      (extFn e₀ (e - e₀) (latO (ch.G.pS (.chi (i : ℕ) 0)) (ch.G.pT (.chi (i : ℕ) 0)) (ch.G.latS (.chi (i : ℕ) 0) : Set _)
        (ch.G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) (cosInd e₀ (Φ i))) (ch.W.cosVec i (Φ i)) :=
    ⟨GlobalTheory.T.isSBHalf_halfExtensionLatticeIndicatorFn h0 h1 h01 (fun _ hu => smul_mem_latO_idem _ _ h0 hu) (fun _ hu => smul_mem_latO_idem _ _ h1 hu) hSB,
      GlobalTheory.T.isThetaAt_halfExtensionLatticeIndicatorFn h0 h1 h01 (fun _ hu => smul_mem_latO_idem _ _ h0 hu) (fun _ hu => smul_mem_latO_idem _ _ h1 hu)
        (fun t y ht hy => symplO_eq_of_half h01 t y ht hy) hex (hcv i i.2 (Φ i))⟩
  rwa [hee] at key
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_coset_function_isLocalVector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsLocVec ch.W (.chi i 0) e (ch.rm.vX i 0) (GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.right i 0)) (ch.W.cosVec i (Φ i)) := by
  first | exact @_root_.GlobalTheory.CosetRow.coset_function_isLocalVector | exact _root_.GlobalTheory.CosetRow.coset_function_isLocalVector | (intros; apply _root_.GlobalTheory.CosetRow.coset_function_isLocalVector <;> assumption)
end
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
theorem GlobalTheory.FlipStart.theta_first_occurrence_finite_swapped_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)), GlobalTheory.FlipStart.ChainVecs ch t f → ∃ z : ℂˣ, z ∈ xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, RepFin ch.S.B ch.rm t (givenPath t D.R.m) (Finsupp.single (GlobalTheory.FlipStart.givenFin ch.W t f Φ) (z : ℂ)) (fun w => (givenStage t w ch.S.B Φ).tensor) := by
  intro hP
  obtain ⟨C, h⟩ := Big.and (Big.and (_root_.GlobalTheory.T.twist_chainColumn_inner_succ_eq hP) (_root_.GlobalTheory.T.twist_flipStart_highestVector hP)) (_root_.GlobalTheory.T.twist_coset_function_isLocalVector hP)
  refine ⟨C, fun ε CF hC => ?_⟩
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨⟨hc1, hc2⟩, hr⟩ := h D large₂ he hx Γ Pl0 T A Ks R F s ch hi ha
  intro t f hf
  have hc : ∀ j : Fin D.R.m, ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) →
      ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) (f j) := by
    intro j
    by_cases hj : (j : ℕ) + 1 < D.R.m
    · exact hc1 t j (f j) hj ((hf j).1 hj)
    · have hj' : (j : ℕ) + 1 = D.R.m := by have := j.2; omega
      exact hc2 t j (f j) hj' ((hf j).2 hj')
  choose c hcx hcv using hc
  obtain ⟨e, he⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl s.core.lev ch.G t
  refine ⟨(∏ j, c j)⁻¹, Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j _ => hcx j), fun Φ => ?_⟩
  refine GlobalTheory.FlipStart.repFin_of ch.W ch.S.B ch.rm t f Φ e he (fun j => (c j : ℂ)) _ ?_ (fun j => hcv j e he Φ) (hr t e he Φ)
  rw [← Units.coe_prod, ← Units.val_mul, inv_mul_cancel, Units.val_one]
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_theta_first_occurrence_finite_swapped_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)), GlobalTheory.FlipStart.ChainVecs ch t f → ∃ z : ℂˣ, z ∈ xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, RepFin ch.S.B ch.rm t (givenPath t D.R.m) (Finsupp.single (GlobalTheory.FlipStart.givenFin ch.W t f Φ) (z : ℂ)) (fun w => (givenStage t w ch.S.B Φ).tensor) := by
  first | exact @_root_.GlobalTheory.FlipStart.theta_first_occurrence_finite_swapped_pair | exact _root_.GlobalTheory.FlipStart.theta_first_occurrence_finite_swapped_pair | (intros; apply _root_.GlobalTheory.FlipStart.theta_first_occurrence_finite_swapped_pair <;> assumption)
end
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.FlipStart
open GlobalTheory.FlipStart in
theorem GlobalTheory.FlipStart.flipSequence_start_condition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro hP hC
  obtain ⟨a, h⟩ := ((_root_.GlobalTheory.T.flipSequence_column_succ hP hC).and (_root_.GlobalTheory.T.twisted_theta_tower_first_occurrence_exists hP hC)).and (_root_.GlobalTheory.T.twisted_theta_first_occurrence_finite_swapped_pair hP)
  refine ⟨a, fun ε CF hCF => ?_⟩
  obtain ⟨x, h⟩ := h ε CF hCF
  refine ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  obtain ⟨⟨hcol, hrow⟩, hfin⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  obtain ⟨q, hq⟩ := exists_chainPols ch
  refine ⟨Finsupp.single (gPol ch.ρ q) 1, fun t => ?_⟩
  obtain ⟨f, hf⟩ := exists_chainVecs ch t
  obtain ⟨z, hz, hrep⟩ := hfin t f hf
  refine ⟨z, hz, fun Φ => ⟨Finsupp.single (givenFin ch.W t f Φ) (z : ℂ), hrep Φ, fun M hM y => ?_⟩⟩
  obtain ⟨hc1, hc2⟩ := hcol t f q hf hq M hM y
  obtain ⟨hr1, hr2⟩ := hrow t Φ M hM y
  rw [tensE_single]
  refine ⟨fun d hd => ?_, ?_⟩
  · have hd' := Finsupp.support_single_subset hd
    rw [Finset.mem_singleton] at hd'
    subst hd'
    rw [zip_given]
    refine (pathConv_comp ch.W M _ _ _ _ _).2 ⟨hc1, ?_⟩
    rw [hc2]
    exact hr1
  · rw [liftT_single, zip_given]
    unfold givenPath
    rw [pathLift_comp, hc2, ← hr2, smul_smul, inv_mul_cancel₀ (Units.ne_zero z), one_smul]
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipSequence_initial_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  first | exact @_root_.GlobalTheory.FlipStart.flipSequence_start_condition | exact _root_.GlobalTheory.FlipStart.flipSequence_start_condition | (intros; apply _root_.GlobalTheory.FlipStart.flipSequence_start_condition <;> assumption)
end
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipRun
variable {D : D7} {T : Type}
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end GlobalTheory.FlipRun
open GlobalTheory.RowClaim in
theorem GlobalTheory.FlipRun.twist_sign_flip_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.SquareSt.WeilConvergence →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → ConstK → StepFlip := by
  intro hP hLC hWC hTI hCK
  obtain ⟨C0, H⟩ := (((((_root_.GlobalTheory.T.twist_square_commutes hP hWC hTI).and (_root_.GlobalTheory.T.flipRun_cusp_transition hLC hP)).and
    (_root_.GlobalTheory.T.endCusp_leadingForm_listed hP)).and (_root_.GlobalTheory.T.flipSequence_initial_term hP hLC)).and GlobalTheory.T.localFlipStage_isTensor_placeDepth).and hCK
  refine ⟨C0, fun ε CF h => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF h
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact GlobalTheory.FlipRun.flipAt_of s.core.lev ch a b c d f (fun i j t => (g i j t).2)
end
end

section
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_lift_flip_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → ConstK → StepFlip := by
  first | exact @_root_.GlobalTheory.FlipRun.twist_sign_flip_succ | exact _root_.GlobalTheory.FlipRun.twist_sign_flip_succ | (intros; apply _root_.GlobalTheory.FlipRun.twist_sign_flip_succ <;> assumption)
end
end
