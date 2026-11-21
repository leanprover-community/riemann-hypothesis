import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstK
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdoptedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctorialityStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalRowTestKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipOfWeilConvergenceAndThetaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetsOfOrthogonalSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearIndependenceOfCuspidalLiftsStatement
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemValuationEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingOfCuspidalLiftsStatement

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim.FormulaTwo

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem mem_xiVals {L : LevCh D T} {t : T} {n : ℕ} (hn : (L.xiH t).OrderDvd n) (hL : LocIn D.what₂.embLL (L.xiH t))
    {z : ℂˣ} (hz : z ∈ xiVals L t) : z ^ n = 1 ∧ (z : ℂ) ∈ Set.range D.what₂.embLL := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, x, rfl⟩ := hz
    refine ⟨?_, hL w x⟩
    have : ((L.xiH t) ^ n).loc w x = 1 := by rw [show (L.xiH t) ^ n = 1 from hn]; rfl
    exact this
  | one => exact ⟨one_pow _, 1, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha.2
    obtain ⟨y, hy⟩ := hb.2
    exact ⟨by rw [mul_pow, ha.1, hb.1, one_mul], x * y, by simp [hx, hy]⟩
  | inv a _ ha =>
    obtain ⟨x, hx⟩ := ha.2
    exact ⟨by rw [inv_pow, ha.1, inv_one], x⁻¹, by simp [hx]⟩

theorem Bplus_smul_form {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (c : ℂ) (φ : Fn G (.top 0))
    (F : Fn G (.grid D.R.m 0)) : Bplus W M φ (c • F) = c * Bplus W M φ F := by
  simpa using Bplus_smul W M 1 c φ F

theorem scalar_calc {e z z' c p b s u κ v w : ℂ} (he : e = z * z') (hz : z ≠ 0) (hz' : z' ≠ 0) (hc : c ≠ 0)
    (h1 : p = (z * c)⁻¹ * b) (h2 : b = z'⁻¹ * s * u) (h3 : u = κ * v) (h4 : w = s * v) : e * c * p = κ * w := by
  subst he h1 h2 h3 h4
  field_simp

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 4000000 in

theorem formulaAt_steps (hL : R.toLevCh.Is A.μ0) (hC : R.IsChain) (ch : Choice R) (hP : ProjAt ch) (hF : FlipAt ch)
    (hU : UnfoldAt ch) (hJ : JetsAt ch) (hc : ∀ i j t, ch.c i j t ≠ 0) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hK : ch.FieldOK) : ∃ κ ze, FormulaAt ch κ ze := by
  obtain ⟨τi, z, hF⟩ := hF
  obtain ⟨σ, z', hU⟩ := hU τi
  obtain ⟨hM, hJ⟩ := hJ
  obtain ⟨κ, hJ⟩ := hJ σ
  have key : ∀ t, ∃ e : D.what₂.LL, D.what₂.embLL e = (z t : ℂ) * z' t ∧ ∃ n : ℕ, 0 < n ∧ e ^ n = 1 := fun t => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    obtain ⟨h1, e, he⟩ := mem_xiVals ho (hK.chars.xi t) (mul_mem (hF t).1 (hU t).1)
    refine ⟨e, he, n, hn, D.what₂.embLL.injective ?_⟩
    rw [map_pow, he, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  choose ze hze hzn using key
  refine ⟨κ, ze, hzn, fun t x hx a => ?_⟩
  obtain ⟨τ, hτ, hfl⟩ := (hF t).2 (ch.Phi a)
  obtain ⟨M, hMt⟩ := exists_vol ch.G hL t
  choose Mβ hMβ using hM t (ch.Phi a)
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ch.S.IsExpansion t (ch.Phi a) β
      (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) := fun β hβ => Classical.epsilon_spec ((hS t a).ex β hβ)
  have e1 : psiK ch a (R.Th t (R.jX t x)) =
      Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) (ch.cv.lift t (R.jX t x))) := by
    exact congrArg (fun u => Bplus ch.W ch.M (colFn ch a) (thetaChi ch.W ch.M ch.ρ (ch.Phi a) u))
      ((form_Th ch hC t _).trans (hP t x hx))
  have e2 := (hU t).2 a τ hτ M hMt Mβ (fun β => Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β))
    (fun β hβ => ⟨hMβ β, hex β hβ⟩) (R.jX t x)
  have e3 : (∑ᶠ β ∈ ch.S.supp t (ch.Phi a), (∏ w, ((ch.S.term t (ch.Phi a) β w).coef : ℂ)) *
      defTot t ch.S.toGridChoice (Mβ β) σ (Classical.epsilon (ch.S.IsExpansion t (ch.Phi a) β)) (colFn ch a)
        (formTop ch t (R.jX t x))) = κ * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := by
    rw [(hS t a).vCore_eq _ hex, finsum_mem_eq_finite_toFinset_sum _ (hS t a).fin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hβ' := (Set.Finite.mem_toFinset _).1 hβ
    exact (congrArg (HMul.hMul _) (hJ t a β hβ' (Mβ β) _ (hMβ β) (hex β hβ') (R.jX t x))).trans (mul_left_comm _ _ _)
  have e4 : vK ch t x a = ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) := rfl
  have hct : cTot ch t ≠ 0 := (cTot_ne_zero_iff ch t).2 fun i j => hc i j t
  have e5 := congrArg (Bplus ch.W ch.M (colFn ch a)) (hfl M hMt (R.jX t x)).2
  exact scalar_calc (hze t) (z t).ne_zero (z' t).ne_zero hct (e1.trans (e5.trans (Bplus_smul_form _ _ _ _ _))) e2 e3 e4

theorem formula2K (hP : StepProj) (hF : StepFlip) (hU : StepUnfold) (hJ : StepJets) (hc : ConstK) (hS : SumOKK) :
    Formula2K := by
  obtain ⟨C0, H⟩ := ((((hP.and hF).and hU).and hJ).and hc).and hS
  refine ⟨C0, fun ε CF h => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF h
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j hK => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact formulaAt_steps s.core.lev s.core.chain ch a b c d (fun i j t => (f i j t).2) g hK

example : StepProj → StepFlip → StepUnfold → StepJets → ConstK → SumOKK → Formula2K := formula2K

end GlobalTheory.RowClaim.FormulaTwo

end
end

open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestLiftFormula_principalLevel : StepProj → StepFlip → StepUnfold → StepJets → ConstK → SumOKK → Formula2K := by
  atlas_forward_decl GlobalTheory.RowClaim.FormulaTwo.formula2K
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oppositePathLocalTotalTensor_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ w ∈ locPl ch.G t, ∀ z, Tflip ch.W ch.S.B t Φ w z ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowTest.Tflip_mem_range | exact GlobalTheory.RowTest.Tflip_mem_range | (intros; apply GlobalTheory.RowTest.Tflip_mem_range <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensorFactor_mem_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.MovedField.moved_mem | exact GlobalTheory.MovedField.moved_mem | (intros; apply GlobalTheory.MovedField.moved_mem <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatIntegrand_flippedTensor_locallyConstant_compactSupport : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, IsLocallyConstant (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) ∧ HasCompactSupport (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) := by
  first | exact @GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt | exact GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt | (intros; apply GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unfolding_variables_mem_fieldRange : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (ν : MeasureTheory.Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ {K : Type} [Field K] (σ : K →+* ℂ) (f : Vars G → ℂ), IsLocallyConstant f → HasCompactSupport f → (∀ e, f e ∈ Set.range σ) → ∫ e, f e ∂(varsVol G ν) ∈ Set.range σ := by
  first | exact @GlobalTheory.LCIntegralField.integral_vars_mem_range | exact GlobalTheory.LCIntegralField.integral_vars_mem_range | (intros; apply GlobalTheory.LCIntegralField.integral_vars_mem_range <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest

theorem term_datum_mem_range : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, (ch.S.term t Φ β w).datum X Y ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w X Y
  by_cases h0 : (ch.S.term t Φ β w).datum X Y = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hlc := GlobalTheory.T.flatIntegrand_flippedTensor_locallyConstant_compactSupport ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w X Y
  have hT := GlobalTheory.T.oppositePathLocalTotalTensor_mem_coefficientField ch large₂ F CF b hS hIs hSc hF t Φ hSum w.1 w.2
  have hM := GlobalTheory.T.movedTensorFactor_mem_coeffField ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w _ hT
  show flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) _ X Y ∈ _
  refine GlobalTheory.T.integral_unfolding_variables_mem_fieldRange (unitVol w.1) (isUnitVol_unitVol w.1) D.what₂.embLL _ hlc.1 hlc.2 fun e => ?_
  simp only [flatIntegrand]
  by_cases hm : moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)
      (fill one_le_sLen X Y e) = 0
  · rw [hm, zero_mul]; exact ⟨0, map_zero _⟩
  obtain ⟨a, ha⟩ := hM (fill one_le_sLen X Y e)
  obtain ⟨c, hc⟩ := hF.phases t Φ β hβ w X Y e h0 hm
  refine ⟨a * c⁻¹, ?_⟩
  rw [map_mul, map_inv₀, ha, hc, AddChar.map_neg_eq_inv, Circle.coe_inv]

end GlobalTheory.RowTest
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedFlipTensor_values_mem_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, (ch.S.term t Φ β w).datum X Y ∈ Set.range D.what₂.embLL := by
  atlas_forward_decl GlobalTheory.RowTest.term_datum_mem_range
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coeff

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem coeff_bVV_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (i : VVIdx lam) (m) :
    coeff m ((bVV ℂ lam i : VV ℂ lam) : Pol ℂ ι n) ∈ A := by
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam i
  rw [bVV_coe, hP, coeff_map]
  exact intCast_mem A _

theorem coeff_mem_of_repr_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ i, (bVV ℂ lam).repr v i ∈ A) (m) : coeff m (v : Pol ℂ ι n) ∈ A := by
  have e := congrArg (fun x : VV ℂ lam => coeff m (x : Pol ℂ ι n)) ((bVV ℂ lam).sum_repr v)
  simp only [Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul, smul_eq_mul] at e
  rw [← e]
  exact sum_mem fun i _ => mul_mem (h i) (coeff_bVV_mem A lam i m)

theorem repr_mem_of_coeff_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ m, coeff m (v : Pol ℂ ι n) ∈ A) (i : VVIdx lam) : (bVV ℂ lam).repr v i ∈ A := by
  classical
  choose P hP using fun j => bVVfun_int ℂ lam j
  let s : A →+* ℂ := A.subtype
  let b' : VVIdx lam → MvPolynomial (ι × Fin n × Fin n) A := fun j => map (Int.castRingHom A) (P j)
  have hb' : ∀ j, map s (b' j) = ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) := fun j => by
    rw [bVV_coe, hP, map_map]
    congr 1
  obtain ⟨v', hv'⟩ : ∃ v' : MvPolynomial (ι × Fin n × Fin n) A, map s v' = (v : Pol ℂ ι n) := by
    obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := s)).2 (fun c hc => by
      obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact ⟨⟨_, h m⟩, rfl⟩)
    exact ⟨F', hF'⟩
  have hliC : LinearIndependent ℂ fun j => ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) :=
    (bVV ℂ lam).linearIndependent.map' (VV ℂ lam).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent A b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have e := congrArg (map s) hg
    simp only [map_sum, map_zero, smul_eq_C_mul, map_mul, map_C, hb'] at e
    have e' : ∑ k, (s (g k)) • ((bVV ℂ lam k : VV ℂ lam) : Pol ℂ ι n) = 0 := by
      simpa only [smul_eq_C_mul] using e
    have := Fintype.linearIndependent_iff.1 hliC (fun k => s (g k)) e' j
    exact Subtype.ext this
  have hspan : v' ∈ Submodule.span A (Set.range b') := by
    by_contra hn
    have hopt : LinearIndependent A (fun o : Option (VVIdx lam) => Option.casesOn' o v' b') :=
      (linearIndependent_option' (x := v') (v := b')).2 ⟨hli, hn⟩
    have hC := Formalism.L2.Col.linearIndependent_map s _ hopt
    have hC' : LinearIndependent ℂ (fun o : Option (VVIdx lam) =>
        Option.casesOn' o (map s v') fun j => map s (b' j)) := by
      convert hC using 1
      funext o
      cases o <;> rfl
    obtain ⟨-, hnot⟩ := (linearIndependent_option' (x := map s v') (v := fun j => map s (b' j))).1 hC'
    apply hnot
    rw [hv']
    have hvs := congrArg (fun x : VV ℂ lam => (x : Pol ℂ ι n)) ((bVV ℂ lam).sum_repr v)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hvs
    rw [← hvs]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hb' j⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hspan
  have hvc : v = ∑ j, (s (c j)) • bVV ℂ lam j := by
    apply Subtype.ext
    rw [← hv', ← hc, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, ← hb', smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  rw [hvc, (bVV ℂ lam).repr_sum_self]
  exact (c i).2

theorem coeff_map_mem {ι' : Type} [Fintype ι'] {n' : ℕ} (A : Subfield ℂ) (lam : ι → DomWeight n)
    (mu : ι' → DomWeight n') (f : VV ℂ lam →ₗ[ℂ] VV ℂ mu)
    (hf : ∀ a b, LinearMap.toMatrix (bVV ℂ lam) (bVV ℂ mu) f a b ∈ A) (v : VV ℂ lam)
    (hv : ∀ m, coeff m (v : Pol ℂ ι n) ∈ A) (m) : coeff m ((f v : VV ℂ mu) : Pol ℂ ι' n') ∈ A := by
  classical
  refine coeff_mem_of_repr_mem A mu (f v) (fun a => ?_) m
  rw [← LinearMap.toMatrix_mulVec_repr (bVV ℂ lam) (bVV ℂ mu) f v, Matrix.mulVec, dotProduct]
  exact sum_mem fun b _ => mul_mem (hf a b) (repr_mem_of_coeff_mem A lam v hv b)

theorem coeff_rhoVr_mem {E : Type} [Field E] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (A : Subfield ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (γE : GL (Fin n) E) (v : VV ℂ lam) (hv : ∀ m, coeff m (v : Pol ℂ ι n) ∈ A) (m) :
    coeff m ((rhoVr emb lam γE v : VV ℂ lam) : Pol ℂ ι n) ∈ A := by
  classical
  let R₀ : Subring (Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, coeff m F ∈ A := by
    intro F
    constructor
    · rintro ⟨F', rfl⟩ m
      rw [coeff_map]
      exact (coeff m F').2
    · intro h
      obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := A.subtype)).2 (fun c hc => by
        obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
        exact ⟨⟨_, h m⟩, rfl⟩)
      exact ⟨F', hF'⟩
  have hblock : ∀ M : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ a b, M τ a b ∈ A) → ∀ F ∈ R₀,
      Formalism.GradedWeylDivisibility.blockAct ℂ M F ∈ R₀ := by
    intro M hM F hF
    obtain ⟨F', rfl⟩ := hF
    induction F' using MvPolynomial.induction_on with
    | C a =>
      rw [map_C, Formalism.GradedWeylDivisibility.blockAct, aeval_C]
      exact ⟨C a, by rw [map_C]; rfl⟩
    | add p q hp hq =>
      rw [map_add, map_add]
      exact add_mem hp hq
    | mul_X p w hp =>
      rw [map_mul, map_mul, map_X]
      refine mul_mem hp ?_
      rw [Formalism.GradedWeylDivisibility.blockAct, aeval_X]
      exact sum_mem fun b _ => mul_mem ⟨C ⟨_, hM _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩
  have hent : ∀ τ a b, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b ∈ A := by
    intro τ a b
    show ((((Formalism.UG.bc (emb τ) γE)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
    rw [← map_inv]
    exact hA τ _
  have hdet : ∀ τ, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ∈ A := by
    intro τ
    have e := RingHom.map_det A.subtype (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A))
    rw [show A.subtype.mapMatrix (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A)) =
      ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) from Matrix.ext fun a b => rfl] at e
    rw [← e]
    exact SetLike.coe_mem _
  have hdt : detTwK lam (invTrK (embGL emb γE)) ∈ A := by
    unfold detTwK
    refine prod_mem fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact zpow_mem (hdet τ) _
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show coeff m (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Pol ℂ ι n)) ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end Coeff

theorem chainTo_preserves {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1))
    (P : ∀ j, V j → Prop) (hk : ∀ j v, P j v → P (j + 1) (k j v)) : ∀ N v, P 0 v → P N (GlobalTheory.FunObj.chainTo k N v)
  | 0, _, hv => hv
  | N + 1, v, hv => hk N _ (chainTo_preserves k P hk N v hv)

end GlobalTheory.RowTest.ColField

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (u : VV ℂ (wt ch.G (.top 0))), (∀ m, MvPolynomial.coeff m u.1 ∈ Set.range D.what₂.embLL) → ∀ m, MvPolynomial.coeff m (ch.S.colMap d (ch.S.ptTop c) u).1 ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ _ β hβ τ hτ d hd c u hu
  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have memK : ∀ z : ℂ, z ∈ K ↔ z ∈ Set.range D.what₂.embLL := fun z => Iff.rfl
  have hE : ∀ (σ : D.what₂.Tau) (x : D.host.E), tauE D σ x ∈ K := fun σ x =>
    ⟨labLL D σ x, GlobalTheory.Mem.R3.BrgRead.embLL_labLL_eq σ x⟩
  have hrat := (hF.isRatAt hβ hτ hd c).1
  have hu' : ∀ m, coeff m (u : Pol ℂ D.what₂.Tau (ch.G.V (.top 0)).rank) ∈ K := fun m => (memK _).2 (hu m)
  have h0 := coeff_rhoVr_mem (tauE D) (wt ch.G (.top 0)) K hE (ch.S.N.fr (.top 0))⁻¹ u hu'
  have hchain := chainTo_preserves (V := fun j => VV ℂ (wt ch.G (.top j)))
    (fun j => if h : j < D.R.m then ch.S.Z.kkMap 1 (d.1 ⟨j, h⟩) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) else 0)
    (fun j v => ∀ m, coeff m (v : Pol ℂ D.what₂.Tau (ch.G.V (.top j)).rank) ∈ K) (fun j v hv => by
      by_cases h : j < D.R.m
      · simp only [dif_pos h]
        exact coeff_map_mem K _ _ _ (fun a b => (memK _).2 (hrat ⟨j, h⟩ a b)) v hv
      · simp only [dif_neg h, LinearMap.zero_apply, ZeroMemClass.coe_zero, coeff_zero]
        exact fun _ => zero_mem K) D.R.m _ h0
  intro m
  exact (memK _).1 (hchain m)

end GlobalTheory.RowTest.ColField
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topRow_normalisedKernelChain_preserves_coeffs : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (u : VV ℂ (wt ch.G (.top 0))), (∀ m, MvPolynomial.coeff m u.1 ∈ Set.range D.what₂.embLL) → ∀ m, MvPolynomial.coeff m (ch.S.colMap d (ch.S.ptTop c) u).1 ∈ Set.range D.what₂.embLL := by
  atlas_forward_decl GlobalTheory.RowTest.ColField.colMap_coeff_mem
end

section
section
open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRho

theorem coeff_rhoVr_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, MvPolynomial.coeff m v.1 ∈ Set.range κ) → ∀ m, MvPolynomial.coeff m ((rhoVr emb lam g) v).1 ∈ Set.range κ := by
  classical
  intro ι _ n E _ emb L _ κ hA0 lam γE v hv0 m
  set A : Subfield ℂ := κ.fieldRange with hAdef
  have hA : ∀ τ x, emb τ x ∈ A := fun τ x => RingHom.mem_fieldRange.2 (hA0 τ x)
  have hv : ∀ m, coeff m (v : Formalism.L2.DIV.Pol ℂ ι n) ∈ A := fun m => RingHom.mem_fieldRange.2 (hv0 m)
  rw [← RingHom.coe_fieldRange]
  show coeff m ((rhoVr emb lam γE v : VV ℂ lam) : Formalism.L2.DIV.Pol ℂ ι n) ∈ A
  let R₀ : Subring (Formalism.L2.DIV.Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Formalism.L2.DIV.Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, coeff m F ∈ A := by
    intro F
    constructor
    · rintro ⟨F', rfl⟩ m
      rw [coeff_map]
      exact (coeff m F').2
    · intro h
      obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := A.subtype)).2 (fun c hc => by
        obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
        exact ⟨⟨_, h m⟩, rfl⟩)
      exact ⟨F', hF'⟩
  have hblock : ∀ M : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ a b, M τ a b ∈ A) → ∀ F ∈ R₀,
      Formalism.GradedWeylDivisibility.blockAct ℂ M F ∈ R₀ := by
    intro M hM F hF
    obtain ⟨F', rfl⟩ := hF
    induction F' using MvPolynomial.induction_on with
    | C a =>
      rw [map_C, Formalism.GradedWeylDivisibility.blockAct, aeval_C]
      exact ⟨C a, by rw [map_C]; rfl⟩
    | add p q hp hq =>
      rw [map_add, map_add]
      exact add_mem hp hq
    | mul_X p w hp =>
      rw [map_mul, map_mul, map_X]
      refine mul_mem hp ?_
      rw [Formalism.GradedWeylDivisibility.blockAct, aeval_X]
      exact sum_mem fun b _ => mul_mem ⟨C ⟨_, hM _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩
  have hent : ∀ τ a b, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b ∈ A := by
    intro τ a b
    show ((((Formalism.UG.bc (emb τ) γE)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
    rw [← map_inv]
    exact hA τ _
  have hdet : ∀ τ, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ∈ A := by
    intro τ
    have e := RingHom.map_det A.subtype (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A))
    rw [show A.subtype.mapMatrix (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A)) =
      ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) from Matrix.ext fun a b => rfl] at e
    rw [← e]
    exact SetLike.coe_mem _
  have hdt : detTwK lam (invTrK (embGL emb γE)) ∈ A := by
    unfold detTwK
    refine prod_mem fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact zpow_mem (hdet τ) _
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show coeff m (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n)) ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end GlobalTheory.RowRho
end

open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coefficientSpaceAction_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, MvPolynomial.coeff m v.1 ∈ Set.range κ) → ∀ m, MvPolynomial.coeff m ((rhoVr emb lam g) v).1 ∈ Set.range κ := by
  atlas_forward_decl GlobalTheory.RowRho.coeff_rhoVr_mem_range
end

section
section
open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowFun

theorem coeff_mem_of_mul_eq {s : Type} (K' : Subfield ℂ) (f P Q : MvPolynomial s ℂ) (hP : P ≠ 0)
    (hPK : ∀ m, coeff m P ∈ K') (hQ : ∀ m, coeff m Q ∈ K') (h : f * P = Q) :
    ∀ m, coeff m f ∈ K' := by
  classical
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.RowRat.exists_proj K'
  let g : MvPolynomial s ℂ := ∑ m ∈ f.support, monomial m (φ (coeff m f))
  have hg : ∀ m, coeff m g = φ (coeff m f) := by
    intro m
    simp only [g, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [notMem_support_iff.mp hm, map_zero]
  have key : g * P = f * P := by
    ext m
    have hfix : coeff m (f * P) = φ (coeff m (f * P)) := by
      rw [h]; exact (hφ1 ⟨_, hQ m⟩).symm
    rw [hfix, coeff_mul, coeff_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hg]
    have hs := φ.map_smul (⟨coeff x.2 P, hPK _⟩ : K') (coeff x.1 f)
    rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_eq_mul] at hs
    rw [mul_comm, ← hs, mul_comm]
  have hgf : g = f := mul_right_cancel₀ hP key
  intro m
  rw [← hgf, hg]
  exact hφ2 _

theorem coeff_funOf_mem_range {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type}
    [Field L] (κ : L →+* ℂ) (hR : GlobalTheory.FunObj.ReadOK σ) (F : VV ℂ σ)
    (hF : ∀ m, MvPolynomial.coeff m F.1 ∈ Set.range κ) :
    ∀ m, MvPolynomial.coeff m (GlobalTheory.FunObj.funOf σ F).1 ∈ Set.range κ := by
  classical
  have hf := hR.1 F
  unfold GlobalTheory.FunObj.IsFunForm at hf
  let G : MvPolynomial (ι × Fin n × Fin n) L :=
    ∑ m ∈ (F.1 : MvPolynomial (ι × Fin n × Fin n) ℂ).support,
      monomial m (Function.invFun κ (coeff m F.1))
  have hG : MvPolynomial.map κ G = F.1 := by
    ext m
    rw [coeff_map]
    simp only [G, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · exact Function.invFun_eq (hF m)
    · simp [notMem_support_iff.mp hm]
  have hmem : ∀ (p : MvPolynomial (ι × Fin n × Fin n) L) m,
      coeff m (MvPolynomial.map κ p) ∈ κ.fieldRange := fun p m => by
    rw [coeff_map]; exact RingHom.mem_fieldRange_self κ _
  have hmem_eq₁ : MvPolynomial.map κ (∏ τ, Formalism.L2.Ker.frDet L n τ ^ ∑ a, (σ τ).natW a)
      = ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ ∑ a, (σ τ).natW a := by
    simp only [map_prod, map_pow, GlobalTheory.BrRat.map_frDet]
  have hmem_eq₂ : MvPolynomial.map κ (GlobalTheory.FunObj.dualSubst L ι n G *
      ∏ τ, Formalism.L2.Ker.frDet L n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat)
      = GlobalTheory.FunObj.dualSubst ℂ ι n F.1 *
      ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat := by
    simp only [map_mul, map_prod, map_pow, GlobalTheory.BrRat.map_frDet, GlobalTheory.BrRat.map_dualSubst, hG]
  intro m
  have := coeff_mem_of_mul_eq κ.fieldRange _ _ _
    (Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (GlobalTheory.FunObj.funFrDet_ne_zero τ))
    (fun m => by
      rw [← hmem_eq₁]; exact hmem _ m)
    (fun m => by
      rw [← hmem_eq₂]; exact hmem _ m) hf m
  exact RingHom.mem_fieldRange.mp this

end GlobalTheory.RowFun
end

open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L] (κ : L →+* ℂ), GlobalTheory.FunObj.ReadOK σ → ∀ (F : VV ℂ σ), (∀ m, MvPolynomial.coeff m F.1 ∈ Set.range κ) → ∀ m, MvPolynomial.coeff m (GlobalTheory.FunObj.funOf σ F).1 ∈ Set.range κ := by
  atlas_forward_decl GlobalTheory.RowFun.coeff_funOf_mem_range
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.RowRat
open Formalism.L2.DIV MvPolynomial

theorem embLL_labLL {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem rowMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (v : VV ℂ (listedWt ch.G (.grid 0 D.R.m))), (∀ m, MvPolynomial.coeff m v.1 ∈ Set.range D.what₂.embLL) → ∀ m, MvPolynomial.coeff m (ch.S.rowMap d (ch.S.ptRow c) v).1 ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ hSum β hβ τ hτ d hd c v hv
  have h0 := GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range _ D.what₂.embLL hSum.read.1 v hv
  have h1 := GlobalTheory.T.coeff_coefficientSpaceAction_mem_range (tauE D) D.what₂.embLL (fun τ x => ⟨labLL D τ x, embLL_labLL τ x⟩) _
    (ch.S.N.fr (.grid 0 D.R.m))⁻¹ _ h0
  have gen : ∀ (k : ∀ i, VV ℂ (wt ch.G (.grid i D.R.m)) →ₗ[ℂ] VV ℂ (wt ch.G (.grid (i + 1) D.R.m))),
      (∀ i (w : VV ℂ (wt ch.G (.grid i D.R.m))), (∀ m, coeff m w.1 ∈ Set.range D.what₂.embLL) →
        ∀ m, coeff m (k i w).1 ∈ Set.range D.what₂.embLL) →
      ∀ j (w : VV ℂ (wt ch.G (.grid 0 D.R.m))), (∀ m, coeff m w.1 ∈ Set.range D.what₂.embLL) →
        ∀ m, coeff m (chainTo (V := fun i => VV ℂ (wt ch.G (.grid i D.R.m))) k j w).1 ∈ Set.range D.what₂.embLL := by
    intro k hk j
    induction j with
    | zero => intro w hw; exact hw
    | succ j ih => intro w hw; exact hk j _ (ih w hw)
  simp only [GlobalTheory.FunObj.GridChoice.rowMap, LinearMap.comp_apply]
  refine gen _ (fun i w hw m => ?_) D.R.m _ h1
  split_ifs with h
  · refine coeff_map_mem _ _ (fun a b => ?_) w hw m
    have := (hF.isRatAt hβ hτ hd c).2 ⟨i, h⟩ a b
    simpa [GlobalTheory.FunObj.Normal.IsRatAt, GlobalTheory.FunObj.Normal.IsRatIn, GlobalTheory.FunObj.Normal.kkIn, LinearMap.toMatrix_apply] using this
  · exact ⟨0, by simp⟩

end GlobalTheory.RowRat

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastColumn_normalizedKernelChain_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (v : VV ℂ (listedWt ch.G (.grid 0 D.R.m))), (∀ m, MvPolynomial.coeff m v.1 ∈ Set.range D.what₂.embLL) → ∀ m, MvPolynomial.coeff m (ch.S.rowMap d (ch.S.ptRow c) v).1 ∈ Set.range D.what₂.embLL := by
  atlas_forward_decl GlobalTheory.RowRat.rowMap_coeff_mem
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branchingPairing_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ (U : VV ℂ (wt ch.G (.top D.R.m))) (V : VV ℂ (wt ch.G (.grid D.R.m D.R.m))), (∀ m, MvPolynomial.coeff m U.1 ∈ Set.range D.what₂.embLL) → (∀ m, MvPolynomial.coeff m V.1 ∈ Set.range D.what₂.embLL) → brPair (listedWt ch.G (.grid D.R.m D.R.m)) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) U V ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowClaim.brPair_mem_coefField | exact GlobalTheory.RowClaim.brPair_mem_coefField | (intros; apply GlobalTheory.RowClaim.brPair_mem_coefField <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalForm_coordinates_coeff_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (x : A.fam.amb.FR t) (y : FinPt ch.G (.grid 0 D.R.m)) m, MvPolynomial.coeff m (ch.S.formC t (R.jX t x) y).1 ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.FormCoef.coeff_formC_mem | exact GlobalTheory.FormCoef.coeff_formC_mem | (intros; apply GlobalTheory.FormCoef.coeff_formC_mem <;> assumption)
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest.SumRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem natCast_cpow_half (N : ℕ) (n : ℤ) : (N : ℂ) ^ ((n : ℂ) / 2) = ((Real.sqrt N : ℝ) : ℂ) ^ n := by
  have h1 : (N : ℂ) = ((N : ℝ) : ℂ) := by simp
  rw [h1, show ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; ring

theorem sAA_mem (ch : Choice R) (h : ch.FieldOK) : ch.S.sAA ∈ D.what₂.embLL.fieldRange := by
  classical
  unfold GridChoice.sAA
  refine Subfield.prod_mem _ fun w hw => ?_
  obtain ⟨n, hn, -⟩ := aaScalar_eq_pow ch.W w (hasConductor_psiAt_AA ch.W w)
  have hq : GlobalTheory.SplitWeil.resCard (Kw w) = Ideal.absNorm w.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion w
  have hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨y, hy⟩ := h.sqrt w (Or.inl hw)
    exact ⟨y, hy⟩
  rw [hn, hq, natCast_cpow_half]
  exact zpow_mem hs n

theorem psiC_rat (ch : Choice R) (a : Fin ch.n) (g : FinPt ch.G (.top 0)) (m) :
    MvPolynomial.coeff m (psiC (ch.Psi a) g).1 ∈ Set.range D.what₂.embLL := by
  show MvPolynomial.coeff m ((GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP ch.G) (ch.Psi a (finG (Xp ch.G) g))).1) ∈ _
  simp [GlobalTheory.CoefModel.mapVV, MvPolynomial.coeff_map]

theorem vK_mem (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ) (hS : HidaSetting large₂ R F) (hi : ch.Is)
    (hsc : ch.AtScale CF b) (hK : ch.FieldOK) (hO : ∀ t a, ch.S.SumOK t (ch.Phi a)) (t : T) (x : A.fam.amb.FR t)
    (a : Fin ch.n) : vK ch t x a ∈ D.what₂.embLL.fieldRange := by
  classical
  have hR : ∀ z, z ∈ Set.range D.what₂.embLL → z ∈ D.what₂.embLL.fieldRange := fun z ⟨y, hy⟩ => ⟨y, hy⟩
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have h := hO t a
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ∃ τ, IsCosetExpansion ch.S.toGridChoice t (ch.Phi a) β
      (expDepth ch.S.toGridChoice t (ch.Phi a) β) τ :=
    fun β hβ => exists_cosetExpansion_expDepth hL ch.S.toGridChoice t (ch.Phi a) β (h.ex β hβ)
  let τf : CosFam ch.G t → PureDat ch.G t →₀ ℂ := fun β =>
    if hβ : β ∈ ch.S.supp t (ch.Phi a) then (hex β hβ).choose else 0
  have hτf : ∀ β (hβ : β ∈ ch.S.supp t (ch.Phi a)), IsCosetExpansion ch.S.toGridChoice t (ch.Phi a) β
      (expDepth ch.S.toGridChoice t (ch.Phi a) β) (τf β) := fun β hβ => by
    simp only [τf, dif_pos hβ]; exact (hex β hβ).choose_spec
  show ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) ∈ D.what₂.embLL.fieldRange
  refine mul_mem (sAA_mem ch hK) ?_
  rw [h.vCore_eq τf fun β hβ => (hτf β hβ).2.1]
  refine sum_mem fun β hβ' => ?_
  have hβ : β ∈ ch.S.supp t (ch.Phi a) := (Set.Finite.mem_toFinset _).1 hβ'
  refine mul_mem (prod_mem fun w _ => SubfieldClass.ratCast_mem _ _) ?_
  unfold GridChoice.classSum
  haveI := h.cls β
  haveI := Fintype.ofFinite (ch.S.Classes t (ch.Phi a) β)
  rw [finsum_eq_sum_of_fintype]
  refine sum_mem fun c _ => mul_mem ?_ ?_
  · unfold GridChoice.invGam
    exact mul_mem (prod_mem fun j _ => inv_mem (natCast_mem _ _)) (prod_mem fun i _ => inv_mem (natCast_mem _ _))
  · unfold GridChoice.pairAt
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply, smul_eq_mul]
    refine sum_mem fun d hd => mul_mem ?_ ?_
    · obtain ⟨X, Y, e⟩ := (hτf β hβ).coef_eq hd
      rw [e]
      exact prod_mem fun w _ => hR _ (GlobalTheory.T.unfoldedFlipTensor_values_mem_coeffField ch large₂ F CF b hS hi hsc hK t _ h β hβ w _ _)
    · have hU := GlobalTheory.T.topRow_normalisedKernelChain_preserves_coeffs ch large₂ F hS hi hK t _ h β hβ _ (hτf β hβ) d hd c _ (psiC_rat ch a (ch.S.ptTop c 0))
      have hV := GlobalTheory.T.lastColumn_normalizedKernelChain_coeffField ch large₂ F hS hi hK t _ h β hβ _ (hτf β hβ) d hd c _
        (GlobalTheory.T.rationalForm_coordinates_coeff_mem_coefficientField ch large₂ F hS hi hK t x (ch.S.ptRow c 0))
      exact hR _ (GlobalTheory.T.branchingPairing_mem_coefficientField ch large₂ F hS hi hK t _ h (ch.S.colMap d (ch.S.ptTop c) (psiC (ch.Psi a) (ch.S.ptTop c 0)))
        (ch.S.rowMap d (ch.S.ptRow c) (ch.S.formC t (R.jX t x) (ch.S.ptRow c 0))) hU hV)

end GlobalTheory.RowTest.SumRat

namespace GlobalTheory.RowTest

theorem sumRatK_of_sumOKK : SumOKK → SumRatK := by
  rintro ⟨CF0, h⟩
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx' Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc hK t x a => ?_⟩
  obtain ⟨y, hy⟩ := SumRat.vK_mem ch large₂ F CF large₂.sc.b s hi hsc hK (hx D large₂ e hx' Γ Pl0 T A Ks R F s ch hi hsc) t x a
  exact ⟨y, hy⟩

end GlobalTheory.RowTest

end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful : GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK := by
  atlas_forward_decl GlobalTheory.RowTest.sumRatK_of_sumOKK
end

section
namespace GlobalTheory.RowClaim.Join

theorem fiveClaims : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  intro P K L s1 s2 s3
  have c := GlobalTheory.ConstNZ.constK P K L s1 s2 s3
  have cusp := GlobalTheory.T.lifts_cuspidal_of_functoriality P
  have sum := GlobalTheory.T.row_sum_of_published_inputs P
  exact ⟨sum, c, GlobalTheory.T.linear_independence_of_cuspidal_lifts P cusp,
    GlobalTheory.T.rowTestLiftFormula_principalLevel (GlobalTheory.T.projection_of_functoriality_adopted P) (GlobalTheory.T.flip_of_weil_convergence_and_theta P cusp s1 K c) (GlobalTheory.T.unfolding_of_cuspidal_lifts P cusp sum)
      (GlobalTheory.T.jets_of_orthogonal_sum P sum) c sum,
    GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful sum⟩

end GlobalTheory.RowClaim.Join
end
