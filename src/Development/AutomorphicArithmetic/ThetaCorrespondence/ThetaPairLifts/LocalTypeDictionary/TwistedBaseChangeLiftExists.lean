import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaConvergenceBaseChoice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMatchingOfBaseChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMatchingOfBaseChoiceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaConvergenceBaseChoiceStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowLift
theorem exists_row_lift_matching : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b →
    ∃ G' : GlobalTheory.Grid.GridPre R, G'.Is ∧ GlobalTheory.RowLift.RowMatchS ch G' := by
  intro hP D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hb CF hs
  have hsc : ch.sc.cGap = 1 := by rw [hs]
  obtain ⟨G, hG, hsp, harr⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
    hP.harishChandraModules hS.host hS.size hS.core hsc ch.W hb.weil
  have hfr : ∀ i, i ≤ D.R.m → Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ := by
    rintro (_ | i) hi
    · obtain ⟨c, h⟩ := hS.core.lev.βY 0 (by have := D.R.two_le_m; omega)
      exact h.1
    · obtain ⟨c, h⟩ := (hG.spaces.vert i 0 hi (Nat.zero_le _)).frame
      exact h.1
  obtain ⟨m00, mV, hm, hν, hfd⟩ := GlobalTheory.ColMeas.measCol_of_choice ch G hG.meas hsp hfr hb.vol
  refine ⟨GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX, ⟨GlobalTheory.GridJoin.isSpaces_withMeas hG.spaces,
    GlobalTheory.GridJoin.isChars_withMeas hG.chars, GlobalTheory.GridJoin.isArrows_withMeas hG.arrows, hm,
    GlobalTheory.GridJoin.isData_withMeas hG.data⟩, ⟨fun i hi => (hsp.vert i 0 hi (Nat.zero_le _)).sp, hν, hfd,
    GlobalTheory.RowKer.kernel_row ch (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _
      (hS.core.lev.βY 0 (by have := D.R.two_le_m; omega))) hb.weil G hG ⟨hsp, harr⟩⟩⟩
end GlobalTheory.RowLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_row_lift_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b →
    ∃ G' : GlobalTheory.Grid.GridPre R, G'.Is ∧ GlobalTheory.RowLift.RowMatchS ch G' := by
  first | exact @_root_.GlobalTheory.RowLift.exists_row_lift_matching | exact _root_.GlobalTheory.RowLift.exists_row_lift_matching | (intros; apply _root_.GlobalTheory.RowLift.exists_row_lift_matching <;> assumption)
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowLift
theorem twisted_lift_from_base_field : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b → ∀ (a : Fin ch.n) (u : R.HE.H),
    ThetaConv ch.W ch.M ch.ρ (ch.Phi a) (ch.form u) ∧
      IsAutFun (ch.G.V (.grid D.R.m 0)) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.form u)) := by
  intro hP hL D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hb CF hs a u
  obtain ⟨G', hG', hM⟩ := _root_.GlobalTheory.T.twist_row_lift_exists hP large₂ hS ch hb CF hs
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.CuspAlong G' :=
    hL D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hS.size) Γ Pl0 T A Ks R G' (rowBase_of_core hS.core) hG'
  let C : ∀ i, Set (Fn ch.G (.grid i 0)) := fun i =>
    {φ | ∃ Φ' ∈ (G'.V i 0).Cusp R.θ, ∃ v, HEq (Φ' v) φ}
  have step : ∀ (i : Fin D.R.m) φ, φ ∈ C i → LiftConv ch.W ch.M (.right (i : ℕ) 0) (ch.W.datum ch.ρ (ch.Phi a) i) φ ∧
      liftA ch.W ch.M (.right (i : ℕ) 0) (ch.W.datum ch.ρ (ch.Phi a) i) φ ∈ C ((i : ℕ) + 1) := by
    rintro i φ ⟨Φ', hΦ', v, hv⟩
    obtain ⟨f, hf, p, hK⟩ := hM.ker ch.ρ (ch.Phi a) i
    obtain ⟨F', hF', H⟩ := hC.X A.μ0 i 0 i.2 (Nat.zero_le _) f hf Φ' hΦ'
    rw [G'.meas_zero] at H
    have T := transport_stepS (hM.V i i.2.le) (hM.V (i + 1) i.2) (hM.ν i i.2.le) (hM.fd i i.2.le) hK hv
      (fun h => (H p v h).1) (fun h => (H p v h).2)
    exact ⟨T.1, F', hF', _, T.2⟩
  have h0 : ch.form u ∈ C 0 := ⟨_, start_mem hS.core u, ch.w, HEq.rfl⟩
  obtain ⟨h1, Φ', hΦ', v, hv⟩ := row_induction ch.W ch.M C D.R.m _ step _ h0
  exact ⟨h1, isAutFun_transportS (hM.V _ le_rfl) hv (isAutFun_of_mem_cusp _ R.θ hΦ' v)⟩
end GlobalTheory.RowLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_base_change_lift_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b → ∀ (a : Fin ch.n) (u : R.HE.H),
    ThetaConv ch.W ch.M ch.ρ (ch.Phi a) (ch.form u) ∧
      IsAutFun (ch.G.V (.grid D.R.m 0)) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.form u)) := by
  first | exact @_root_.GlobalTheory.RowLift.twisted_lift_from_base_field | exact _root_.GlobalTheory.RowLift.twisted_lift_from_base_field | (intros; apply _root_.GlobalTheory.RowLift.twisted_lift_from_base_field <;> assumption)
end
end
