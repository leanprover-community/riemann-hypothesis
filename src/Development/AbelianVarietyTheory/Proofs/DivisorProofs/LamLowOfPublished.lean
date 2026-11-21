import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealDataThreeStatement
import Formalism.LocalToGlobal.Divisibility.RecBridgeNum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookProductPosLogEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FloorCastOfInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BTLeFiveQuarters
import BuildAid.ForwardExisting

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowMainTerm

theorem logHook_congr (n : ℕ) (a b : ℕ → ℝ) (h : ∀ i < n, a i = b i) :
    Formalism.BasicNotions.DV.logHook n a = Formalism.BasicNotions.DV.logHook n b := by
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i (Finset.mem_range.mp hi)]
  · refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => ?_
    have hi' := Finset.mem_range.mp hi
    have hl' := (Finset.mem_Ioo.mp hl).2
    rw [h i hi', h l hl']

theorem pW_eq (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ = (D.R.sigW ((j : ℕ) + 1)).1 := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW
  rw [GlobalTheory.RecGaps.sig_Wc]

theorem sigW_fst (D : D7) (j : Fin D.R.m) : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := by
  simp [Formalism.BasicNotions.Ranks.sigW]

theorem hook_term (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    Real.log ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ)
        (Formalism.IndefR.Links.aPl D j (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ) ρ) : ℕ) : ℝ)
      = Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ) := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  rw [pW_eq, sigW_fst]
  have key : ∀ n < D.R.k + (j : ℕ),
      ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ n : ℕ) : ℝ) = Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ n := by
    intro n hn
    have := GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D j ρ n hn
    unfold Formalism.BasicNotions.DV.aPlus
    rw [← this]
    push_cast
    rfl
  have rs := (GlobalTheory.BlockRows.rows_sizes D ((j : ℕ) + 1) h1 h2 ρ).1
  have hanti : ∀ (x y : ℕ), x ≤ y → y < D.R.k + (j : ℕ) →
      Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y ≤ Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x := by
    intro x y hxy hy
    have hx : x < D.R.k + (j : ℕ) := lt_of_le_of_lt hxy hy
    have e : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := sigW_fst D j
    have hy' : y < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hy
    have hx' : x < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hx
    have ha := rs.1 (show (⟨x, hx'⟩ : Fin _) ≤ ⟨y, hy'⟩ from hxy)
    have ex := rs.2.2 ⟨x, hx'⟩
    have ey := rs.2.2 ⟨y, hy'⟩
    have r : ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y : ℕ) : ℝ)
        ≤ ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x : ℕ) : ℝ) := by
      rw [key y hy, key x hx]
      simp only at ex ey
      rw [← ex, ← ey]
      exact_mod_cast ha
    exact_mod_cast r
  rw [(GlobalTheory.HookDiagram.hookOf_pos_log _ _ hanti).2]
  exact logHook_congr _ _ _ key

end GlobalTheory.LowMainTerm

namespace GlobalTheory.LowMainTerm

theorem sum_logHook_eq (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (j : Fin D.R.m) :
    (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) = GlobalTheory.LiftLower.hookPlus D j := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  have e1 : (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ)
      = ∑ z : Bool × G.HH D, Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1
          (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) (tauPl D z)) :=
    Finset.sum_congr rfl fun z _ => Formalism.L2.DIV.NumTieH.logHook_eq D L Del h0 h1 h2 z
  rw [e1, Function.Bijective.sum_comp (tauPl_bijective D)
    (fun τ => Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) τ))]
  unfold GlobalTheory.LiftLower.hookPlus
  exact (Finset.sum_congr rfl fun ρ _ => hook_term D j ρ).symm

theorem main_le_lowB : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (Csz : ℝ) (j : Fin D.R.m), 8 ≤ Csz → Sizes D j L.sc.b → (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) - Csz * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp) ≤ lowB D j L.sc.b := by
  intro D L Del h0 Csz j hC hS
  rw [sum_logHook_eq]
  have hLp : (ofRecord D L Del h0).Lp = GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    rw [Formalism.L2.DIV.NumTieH.Lp_eq]; rfl
  have hpos : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    have := (GlobalTheory.AdelicScalar.SizeBounds.sizes D j L.sc.b hS).1
    linarith
  rw [hLp]
  unfold GlobalTheory.BigOn.lowB
  have hX : 0 ≤ (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by positivity
  nlinarith

end GlobalTheory.LowMainTerm
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hookLogSum_sub_sizeTerm_le_lowerBound : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (Csz : ℝ) (j : Fin D.R.m), 8 ≤ Csz → Sizes D j L.sc.b → (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) - Csz * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp) ≤ lowB D j L.sc.b := by
  atlas_forward_decl GlobalTheory.LowMainTerm.main_le_lowB
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow

theorem weightSizes_along : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x →
    ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.ShNums.size_rel Fm
  refine ⟨x0, fun x hx1 hx i j => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, hw1, hsum⟩ := h0 x hx hx1 i
  have SZ := Fm.sizes x hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := SZ
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hSc := L.Sc_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'.le (by linarith)
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have hwj : ∀ τ, wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    intro τ
    unfold wj
    rw [dif_pos (by omega)]
    rfl
  have hwin : ∀ τ, 0 < wj D (j.1 + 1) τ ∧ wj D (j.1 + 1) τ ≤ 2 * L.sc.b := by
    intro τ
    by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have := L.win_thick (j.1 + 1) (by omega) (by omega) τ h1
      constructor <;> linarith [this.1, this.2]
    by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have a := L.win_top (j.1 + 1) (by omega) (by omega) τ ⟨t, ht⟩ e.symm
      have a3 := L.bT_ge ⟨t, ht⟩
      have a4 := GlobalTheory.Ggeo.bT_le_five_quarters P ⟨t, ht⟩
      constructor <;> linarith [a.1, a.2]
    · have a := L.win_thin (j.1 + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, h2, h1⟩
      constructor <;> linarith [a.1, a.2]
  refine ⟨fun τ => ⟨?_, ?_, fun l => ?_, fun l => ?_⟩, fun l => (hG l l).1⟩
  · rw [← hwj]; exact (hwin τ).1
  · rw [← hwj]; exact (hwin τ).2
  · have := L.cloud_v τ l
    exact ⟨this.1, by linarith [this.2]⟩
  · have := L.be_close τ l j
    push_cast at this
    linarith

end GlobalTheory.LowRow
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_weightSizes_eventually_along_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ (i : Fm.Ix x) j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := by
  atlas_forward_decl GlobalTheory.LowRow.weightSizes_along
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.BigTop

theorem lamLow_of_classicalTheorems : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → GlobalTheory.BigTop.LamLow := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine (Formalism.MainNotions.DIV.closed_Csz_ge FamHyp 8).imp ?_
  intro eps Fm CH _ h8
  obtain ⟨x0, hx0⟩ := GlobalTheory.T.thetaLift_weightSizes_eventually_along_family eps Fm
  refine ⟨x0, fun x hx hle i p hp C => ?_⟩
  have hS : ∀ j, Sizes (Fm.D x i) j (Fm.L x i).sc.b := hx0 x hx hle i
  refine GlobalTheory.T.finiteness_inputs_real_data_three h1 h2 h3 h4 h5 h6 h7 (T := p.T) (R := p.R) (F := p.F) p.κ p.v₀ p.O 1 (Fm.L x i).sc.b C CH
    hp.ok hp.sep p.charW hp.exAt hp.prim p.phsOne p.stdChar p.fw p.bar hp.ioExt p.pins (fun j => (hp.oneMap j).1) p.phase hS
    ?_ ?_ ⟨_, ⟨Fm.params x hx i⟩⟩ p.stdV
  · intro j
    have := GlobalTheory.T.hookLogSum_sub_sizeTerm_le_lowerBound (Fm.D x i) (Fm.L x i) p.Del p.h0 Fm.Csz j h8 (hS j)
    exact this
  · intro j
    show _ - C * 0 ≤ _
    rw [mul_zero, sub_zero]
    exact le_rfl
end GlobalTheory.BigTop
end
